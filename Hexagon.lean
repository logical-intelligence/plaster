import Mathlib
import Std.Data.HashMap
import Aesop
import VerifAI.VerifAI

-- Address type
abbrev Address := BitVec 160

-- Special zero address
abbrev zeroAddress : Address := BitVec.ofNat 160 0

-- Define the State monad to track errors
inductive Error
  | InsufficientBalance
  | InsufficientAllowance
  | ZeroAddressTransfer
  | Overflow
  | PendingAllowance
  | Other : String → Error

-- Contract state (without events)
structure ContractState where
  balanceOf_ : Std.HashMap Address (BitVec 256)
  allowance_ : Std.HashMap Address (Std.HashMap Address (BitVec 256))
  currentSupply : BitVec 256
  deriving Inhabited

def ContractState.balanceOf (s : ContractState) (addr : Address) : BitVec 256 :=
  s.balanceOf_.getD addr 0#256

def ContractState.allowance (s : ContractState) (owner : Address) (spender : Address) : BitVec 256 :=
  (s.allowance_.getD owner (Std.HashMap.empty)).getD spender 0#256

def ContractState.updateBalance (s : ContractState) (addr : Address) (f : BitVec 256 → BitVec 256) : ContractState :=
  { s with balanceOf_ := s.balanceOf_.insert addr (f (s.balanceOf addr)) }

def ContractState.updateAllowance (s : ContractState) (owner : Address) (spender : Address) (f : BitVec 256 → BitVec 256) : ContractState :=
  { s with allowance_ := s.allowance_.alter owner (fun m =>
    match m with
    | none => some (Std.HashMap.empty.insert spender (f 0#256))
    | some m => some (m.insert spender (f (m.getD spender 0#256)))
  ) }

-- Events
structure TransferEvent where
  sender : Address
  recipient : Address
  value : BitVec 256

structure BurnEvent where
  sender : Address
  value : BitVec 256

structure ApprovalEvent where
  owner : Address
  spender : Address
  value : BitVec 256

-- Event log type
inductive EventLog
  | transfer : TransferEvent → EventLog
  | burn : BurnEvent → EventLog
  | approval : ApprovalEvent → EventLog

-- Our contract monad: StateT for state + WriterT for events + Except for errors
abbrev ContractM (α : Type) := StateT ContractState (WriterT (List EventLog) (Except Error)) α
instance : Monad (WriterT (List EventLog) (Except Error)) := WriterT.monad [] (· ++ ·)
instance : Monad (ContractM) := StateT.instMonad

namespace ContractM

-- Helper functions for the ContractM monad
def fail {α : Type} (e : Error) : ContractM α :=
  liftM (Except.error e)

def requireM (cond : Bool) (error : Error) : ContractM Unit :=
  if cond then pure () else fail error

def emitEvent (event : EventLog) : ContractM Unit :=
  StateT.lift (tell [event])

-- Run a contract computation with given initial state
def run {α : Type} (m : ContractM α) (initialState : ContractState) :
    Except Error (α × ContractState × List EventLog) :=
  (StateT.run m initialState).run.map (fun x => (x.1.1, x.1.2, x.2))

end ContractM

namespace Hexagon

-- Constants as defined in the Solidity contract
def name : String := "Hexagon"
def symbol : String := "HXG"
def decimals : BitVec 8 := 4#8
def burnPerTransaction : BitVec 256 := 2#256
def initialSupply : BitVec 256 := 420000000000000#256

-- Helper function for transfer
def _transfer (sender recipient : Address) (value : BitVec 256) : ContractM Unit := do
  -- Prevent transfer to 0x0 address. Use burn() instead
  ContractM.requireM (recipient != zeroAddress) Error.ZeroAddressTransfer

  let s ← get

  -- Check if the sender has enough
  ContractM.requireM (s.balanceOf sender >= value + burnPerTransaction) Error.InsufficientBalance
  -- Check for overflows
  ContractM.requireM (s.balanceOf recipient + value > s.balanceOf recipient) Error.Overflow
  ContractM.requireM (value + burnPerTransaction > value) Error.Overflow

  -- Subtract from the sender
  let s := s.updateBalance sender (· - (value + burnPerTransaction))
  -- Add the same to the recipient
  let s := s.updateBalance recipient (· + value)
  -- Apply transaction fee
  let s := s.updateBalance zeroAddress (· + burnPerTransaction)
  -- Update current supply
  let s := { s with currentSupply := s.currentSupply - burnPerTransaction }

  set s

  -- Record events
  ContractM.emitEvent (EventLog.burn { sender := sender, value := burnPerTransaction })
  ContractM.emitEvent (EventLog.transfer { sender := sender, recipient := recipient, value := value })

-- Public functions matching the Solidity contract

-- Constructor
def constructor (creator : Address) : ContractState :=
  let s : ContractState := {
    balanceOf_ := Std.HashMap.empty,
    allowance_ := Std.HashMap.empty,
    currentSupply := initialSupply
  }
  s.updateBalance creator (fun _ => initialSupply)

-- Send tokens
def transfer (sender recipient : Address) (value : BitVec 256) : ContractM Bool := do
  _transfer sender recipient value
  pure true

-- Return current supply
def totalSupply : ContractM (BitVec 256) := do
  let s ← get
  pure s.currentSupply

-- Burn tokens
def burn (sender : Address) (value : BitVec 256) : ContractM Bool := do
  let s ← get

  -- Check if the sender has enough
  ContractM.requireM (s.balanceOf sender >= value) Error.InsufficientBalance
  -- Subtract from the sender
  let s := s.updateBalance sender (· - value)
  -- Update current supply
  let s := { s with currentSupply := s.currentSupply - value }
  -- Send to the black hole
  let s := s.updateBalance zeroAddress (· + value)
  set s

  -- Notify network (add event)
  ContractM.emitEvent (EventLog.burn { sender := sender, value := value })

  pure true

-- Allow someone to spend on your behalf
def approve (owner spender : Address) (value : BitVec 256) : ContractM Bool := do
  let s ← get

  -- Check if the sender has already set an allowance
  ContractM.requireM (value == 0#256 || s.allowance owner spender == 0#256) Error.PendingAllowance
  -- Add to allowance
  let s := s.updateAllowance owner spender (fun _ => value)

  set s

  -- Notify network (add event)
  ContractM.emitEvent (EventLog.approval { owner := owner, spender := spender, value := value })

  pure true

-- Send tokens
def transferFrom (sender senderFrom recipient : Address) (value : BitVec 256) : ContractM Bool := do
  -- Prevent transfer of not allowed tokens
  ContractM.requireM ((← get).allowance senderFrom sender >= value) Error.InsufficientAllowance
  -- Remove tokens from allowance
  set $ (← get).updateAllowance senderFrom sender (· - value)

  _transfer senderFrom recipient value

  pure true

def totalBalance (s : ContractState) : Int :=
  s.balanceOf_.values.foldl (init := 0) (· + ·.toNat)

-- Theorems and proofs about the contract behavior

theorem ContractM.run_bind {m1 : ContractM α} {f : α → ContractM β} :
    ContractM.run (bind m1 f) s = Except.ok (ret, s', events) ↔
    ∃ s₁ ret₁ events₁ events₂,
      ContractM.run m1 s = Except.ok (ret₁, s₁, events₁) ∧
      ContractM.run (f ret₁) s₁ = Except.ok (ret, s', events₂) ∧
      events = events₁ ++ events₂ := by
  simp [bind, StateT.bind, StateT.run, WriterT.run, ContractM.run, Except.map, WriterT.mk, Except.bind, Functor.map]
  constructor
  intro h
  · cases h' : m1 s with
    | error err => simp [h'] at h
    | ok v =>
      simp [h'] at h
      cases h'' : f v.1.1 v.1.2 with
      | error err => simp [h''] at h
      | ok v' =>
        simp [h''] at h
        exists v.1.2, v.1.1, v.2
        constructor
        simp
        exists v'.2
        simp [h'', h]
  · intro h
    rcases h with ⟨s₁, ret₁, events₁, h₁, events₂, h₂, h₃⟩
    cases h' : m1 s with
    | error err => simp [h'] at h₁
    | ok v =>
      simp [h'] at h₁
      simp [h₁]
      cases h'' : f ret₁ s₁ with
      | error err => simp [h''] at h₂
      | ok v' =>
        simp [h''] at h₂
        simp [h₂, h₃]

theorem ContractM.run_pure : ContractM.run (pure a) s = Except.ok (a, s, []) := by rfl

theorem ContractM.run_requireM {cond : Bool} {error : Error} :
    (ContractM.requireM cond error).run s = Except.ok (ret, s', events) ↔ cond ∧ ret = () ∧ events = [] ∧ s = s' := by
  constructor
  intro h
  cases cond with
  | true =>
    have h' : ContractM.run (ContractM.requireM true error) s = Except.ok ((), s, []) := by rfl
    simp [h'] at h
    simp [h]
  | false => contradiction
  intro h
  simp [h]
  rfl

theorem ContractM.run_get : ContractM.run (get) s = Except.ok (s, s, []) := by rfl

theorem ContractM.run_set : ContractM.run (set s') s = Except.ok ((), s', []) := by rfl

theorem ContractM.run_emitEvent : ContractM.run (ContractM.emitEvent event) s = Except.ok ((), s, [event]) := by rfl

def updatedState (s : ContractState) (sender recipient : Address) (value : BitVec 256) :=
  let s := s.updateBalance sender (· - (value + burnPerTransaction))
  let s := s.updateBalance recipient (· + value)
  let s := s.updateBalance zeroAddress (· + burnPerTransaction)
  let s := { s with currentSupply := s.currentSupply - burnPerTransaction }
  s

theorem currentSupply_state_semantics :
    ContractM.run (transfer sender recipient value) s = Except.ok (true, s', events) →
    value + burnPerTransaction ≤ s.balanceOf sender ∧
    s.balanceOf recipient < s.balanceOf recipient + value ∧
    s' = updatedState s sender recipient value := by
  intro h2
  simp [transfer, _transfer] at h2
  rw [ContractM.run_bind] at h2
  rcases h2 with ⟨s₁, ret₁, events₁, events₂, h, h₁, h₂⟩
  rw [ContractM.run_pure] at h₁
  apply Except.ok.inj at h₁; simp at h₁
  simp [h₁] at h₂; simp [h₁, h₂] at h
  rw [ContractM.run_bind] at h
  rcases h with ⟨s₁', ret₁', events₁, events₂, h, h₁⟩
  rw [ContractM.run_requireM] at h
  simp [h] at h₁; rw [←h.2.2.2] at h₁
  have h_nz_recepient := h.1
  rcases h₁ with ⟨h, h₁⟩
  rw [ContractM.run_bind] at h
  rcases h with ⟨s₁', ret₁', events₁, events₂, h, h₁⟩
  rw [ContractM.run_get] at h
  simp at h
  simp [h] at h₁; rw [←h.1, ←h.2.1] at h₁
  rcases h₁ with ⟨h, h₁⟩
  rw [ContractM.run_bind] at h
  rcases h with ⟨s₁', ret₁', events₁, events₂, h, h₁⟩
  simp [ContractM.run_requireM] at h; rw [←h.2.2] at h₁
  have h_req := h.1
  rcases h₁ with ⟨h, h₁⟩
  rw [ContractM.run_bind] at h
  rcases h with ⟨s₁', ret₁', events₁, events₂, h, h₁⟩
  simp [ContractM.run_requireM] at h; rw [←h.2.2] at h₁
  have h_req2 := h.1
  rcases h₁ with ⟨h, h₁⟩
  rw [ContractM.run_bind] at h
  rcases h with ⟨s₁', ret₁', events₁, events₂, h, h₁⟩
  rw [ContractM.run_set] at h
  simp [ContractState.updateBalance, ContractState.balanceOf] at h
  let h_state_update := h.1
  rcases h₁ with ⟨h, h₁⟩
  rw [ContractM.run_bind] at h
  rcases h with ⟨s₁'', ret₁'', events₁, events₂, h, h₁⟩
  simp [ContractM.run_emitEvent] at h
  rw [←h.1] at h₁
  simp [ContractM.run_emitEvent] at h₁
  rw [h₁.1.1] at h_state_update
  clear * - h_req h_req2 h_state_update h_nz_recepient
  unfold updatedState
  exact ⟨h_req, h_req2, Eq.symm h_state_update⟩

end Hexagon
