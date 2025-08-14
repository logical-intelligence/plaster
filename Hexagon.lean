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

  -- Check for burn overflows
  ContractM.requireM (value + burnPerTransaction > value) Error.Overflow
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
    value + burnPerTransaction > value ∧
    recipient != zeroAddress ∧
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
  have h_req3 := h.1
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
  clear * - h_req h_req2 h_req3 h_state_update h_nz_recepient
  unfold updatedState
  exact ⟨h_req, h_req2, h_req3, Eq.symm h_state_update⟩

-- Theorems for overflow checks for bitvecs.
def no_overflow (a b : BitVec w) : Prop :=
  a.toNat + b.toNat < 2^w

theorem mod_ineq (a b : Nat) :
b > 0 → a ≥ b → a % b ≤ a - b := by
  intro h1 h2
  simp [Nat.mod_eq_sub_mod h2, Nat.mod_le]

theorem bitvec_overflow_test_1 (a b : BitVec w) :
a + b ≥ a → no_overflow a b := by
  contrapose!
  unfold no_overflow
  push_neg
  intro h
  rw [BitVec.add_def]
  set x := a.toNat
  set y := b.toNat
  have h2 : a = BitVec.ofNat w x := by
    unfold x
    simp
  rw [h2]
  intro h3
  simp at h3
  have h4 : x % 2 ^ w = x := by
    apply Nat.mod_eq_of_lt
    have g : x = a.toNat := by
      simp [x]
    exact (BitVec.nat_eq_toNat.mp g).left
  simp [h4] at h3
  have h5 : (x + y) % 2^w ≤ x + y - 2^w := by
    simp [h, mod_ineq]
  omega

theorem bitvec_overflow_test_2 (a b : BitVec w) :
no_overflow a b → a + b ≥ a := by
  intro h
  unfold no_overflow at h
  rw [BitVec.add_def]
  set x := a.toNat
  set y := b.toNat
  have h2 : a = BitVec.ofNat w x := by
    unfold x
    simp
  rw [h2]
  simp [BitVec.ofNat_le_ofNat]
  have h4 : x % 2 ^ w = x := by
    apply Nat.mod_eq_of_lt
    have g : x = a.toNat := by
      simp [x]
    exact (BitVec.nat_eq_toNat.mp g).left
  simp [h4]
  rw [Nat.mod_eq_of_lt]
  <;> omega

theorem bitvec_overflow_test_2_swapped (a b : BitVec w) :
no_overflow a b → a + b ≥ b := by
  intro h
  have h2 : no_overflow b a := by
    unfold no_overflow at *
    omega
  apply bitvec_overflow_test_2 at h2
  simp_all [BitVec.add_comm]

-- Theorems about contract valid state/preservation.

def isValid (s : ContractState) : Prop :=
  totalBalance s = initialSupply.toNat

theorem valid_implies_small_balance (h : isValid s) (addr : Address):
s.balanceOf addr ≤ initialSupply := by
  sorry

theorem constructor_is_valid (creator : Address) : isValid (constructor creator) := by
  have hashmap_single_insert_values {α β : Type} [BEq α] [Hashable α] (k : α) (v : β) :
    (Std.HashMap.empty.insert k v).values = [v] := by
    sorry
  unfold isValid constructor totalBalance ContractState.updateBalance
  simp [ContractState.balanceOf, hashmap_single_insert_values]

theorem totalBalance_minus_update (s s': ContractState) (key : Address) (delta : BitVec 256) :
  s' = s.updateBalance key (· - delta) ∧ s.balanceOf key ≥ delta →
  totalBalance s - delta.toNat = totalBalance s' := by sorry

theorem totalBalance_plus_update (s s' : ContractState) (key : Address) (delta : BitVec 256) :
  s' = s.updateBalance key (· + delta) ∧ s.balanceOf key + delta ≥ delta →
  totalBalance s + delta.toNat = totalBalance s' := by sorry

theorem transfer_preserves_validity {sender recipient : Address} {value : BitVec 256} {s s' : ContractState} {events}
    (h_run : ContractM.run (transfer sender recipient value) s = Except.ok (true, s', events))
    (h_valid : isValid s) :
    isValid s' := by
  rcases currentSupply_state_semantics h_run with ⟨h1, h2, h4, h3⟩
  simp [h3]
  unfold updatedState isValid
  dsimp
  set s1 := s.updateBalance sender (· - (value + burnPerTransaction))
  set s2 := s1.updateBalance recipient (· + value)
  set s3 := s2.updateBalance zeroAddress (· + burnPerTransaction)
  set s4 := { s3 with currentSupply := s3.currentSupply - burnPerTransaction }

  have after1 : totalBalance s1 = totalBalance s - (value + burnPerTransaction).toNat := by
    let tmp := totalBalance_minus_update s s1 sender (value + burnPerTransaction)
    unfold s1 at tmp ⊢
    simp only [totalBalance_minus_update, h1] at tmp
    simp_all

  have no_overflow_recipient : s1.balanceOf recipient + value ≥ value := by
    apply bitvec_overflow_test_2_swapped
    unfold no_overflow
    by_cases same_addr : sender == recipient
    -- !!! use ==(double equal), not =(single equal)
    -- cause HashMap theorems use ==
    · unfold s1 ContractState.updateBalance ContractState.balanceOf
      simp only [Std.HashMap.getD_insert, Std.HashMap.getD_insert_self, same_addr, ite_true]
      unfold ContractState.balanceOf at h1
      bv_omega
    · unfold s1 ContractState.updateBalance ContractState.balanceOf
      simp [Std.HashMap.getD_insert, Std.HashMap.getD_insert_self, same_addr, ite_false]
      have aux1 := valid_implies_small_balance h_valid recipient
      unfold ContractState.balanceOf at h1 aux1
      have aux2 : value ≤ initialSupply := by
        have aux3 := valid_implies_small_balance h_valid sender
        unfold ContractState.balanceOf at aux3
        unfold initialSupply at *
        bv_omega

      unfold initialSupply at aux1 aux2
      bv_omega

  have after2 : totalBalance s2 = totalBalance s1 + value.toNat := by
    let tmp := totalBalance_plus_update s1 s2 recipient value
    unfold s2 at tmp ⊢
    simp only [totalBalance_plus_update, no_overflow_recipient] at tmp
    simp_all

  -- TODO: think about how to model this properly.
  -- In Solidity, this is enforced since `sender` argument is "msg.sender" which can't be zero.
  have cant_send_from_zero : sender != zeroAddress := by
    sorry

  have no_overflow_zeroAddress : s2.balanceOf zeroAddress + burnPerTransaction ≥ burnPerTransaction := by
    apply bitvec_overflow_test_2_swapped
    unfold no_overflow s2 s1 ContractState.updateBalance ContractState.balanceOf
    simp [Std.HashMap.getD_insert, Std.HashMap.getD_insert_self, cant_send_from_zero]
    simp_all
    have zero_small := valid_implies_small_balance h_valid zeroAddress
    unfold ContractState.balanceOf at zero_small
    unfold burnPerTransaction
    unfold initialSupply at zero_small
    bv_omega

  have after3 : totalBalance s3 = totalBalance s2 + burnPerTransaction.toNat := by
    let tmp := totalBalance_plus_update s2 s3 zeroAddress burnPerTransaction
    unfold s3 at tmp ⊢
    simp only [totalBalance_plus_update, no_overflow_zeroAddress] at tmp
    simp_all

  have after4 : totalBalance s4 = totalBalance s3 := by
    unfold s4 totalBalance
    simp_all

  rw [after4, after3, after2, after1, h_valid]
  bv_omega

theorem burn_preserves_validity {sender : Address} {value : BitVec 256} {s s' : ContractState} {events}
    (h_run : ContractM.run (burn sender value) s = Except.ok (true, s', events))
    (h_valid : isValid s) :
    isValid s' := by
  sorry

theorem transferFrom_preserves_validity {sender senderFrom recipient : Address} {value : BitVec 256} {s s' : ContractState} {events}
    (h_run : ContractM.run (transferFrom sender senderFrom recipient value) s = Except.ok (true, s', events))
    (h_valid : isValid s) :
    isValid s' := by
  sorry

-- Inductive contract state validity definition
inductive InductiveValid : ContractState → Prop where
  | from_constructor (creator : Address) :
      InductiveValid (constructor creator)

  | from_transfer {sender recipient : Address} {value : BitVec 256} {s s' : ContractState} {events} :
      InductiveValid s →
      ContractM.run (transfer sender recipient value) s = Except.ok (true, s', events) →
      InductiveValid s'

  | from_burn {sender : Address} {value : BitVec 256} {s s' : ContractState} {events} :
      InductiveValid s →
      ContractM.run (burn sender value) s = Except.ok (true, s', events) →
      InductiveValid s'

  | from_approve {owner spender : Address} {value : BitVec 256} {s s' : ContractState} {events} :
      InductiveValid s →
      ContractM.run (approve owner spender value) s = Except.ok (true, s', events) →
      InductiveValid s'

  | from_transferFrom {sender senderFrom recipient : Address} {value : BitVec 256} {s s' : ContractState} {events} :
      InductiveValid s →
      ContractM.run (transferFrom sender senderFrom recipient value) s = Except.ok (true, s', events) →
      InductiveValid s'

theorem inductiveValid_implies_valid
    (s : ContractState) (h_valid_by_construction : InductiveValid s) :
    isValid s := by

  induction h_valid_by_construction with
  | from_constructor creator =>
    apply constructor_is_valid

  | from_transfer ih h_succ_run =>
    apply transfer_preserves_validity h_succ_run
    trivial

  | from_burn ih h_succ_run =>
    apply burn_preserves_validity h_succ_run
    trivial

  | from_approve ih h_succ_run =>
    sorry

  | from_transferFrom ih h_succ_run =>
    apply transferFrom_preserves_validity h_succ_run
    trivial

-- Random theorems

-- This could fail if recipient is 0x0 or if the balance is insufficient, so do isOk instead.
theorem transfer_fails_if_balance_insufficient
    (sender recipient : Address) (value : BitVec 256) (s : ContractState) :
    s.balanceOf sender < value + burnPerTransaction →
    (ContractM.run (transfer sender recipient value) s).isOk = False := by
  intro h
  rw [transfer, _transfer]
  by_cases rec_zero : recipient == zeroAddress
  · simp_all [rec_zero, ContractM.requireM, ContractM.fail]
    simp_all [bind, StateT.bind, StateT.run, WriterT.run, ContractM.run, Except.map, WriterT.mk, Except.bind, Functor.map]
    simp_all [liftM, monadLift]
    simp [MonadLift.monadLift, StateT.lift]
    rw [MonadLift.monadLift]
    simp [WriterT.instMonadLiftOfEmptyCollection]
    simp [WriterT.liftTell, WriterT.mk]
    simp [pure, bind]
    simp_all!
    simp [WriterT.mk]
    trivial
  · simp_all [rec_zero, ContractM.requireM, ContractM.fail]
    -- note that at this point, the `s` in the goal isn't the same as the theorem argument!
    -- so you have to unfold the get part first
    simp_all [bind, StateT.bind, StateT.run, WriterT.run, ContractM.run, Except.map, WriterT.mk, Except.bind, Functor.map]
    simp [pure, StateT.pure, Except.pure]
    simp_all [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure]
    have h2 : ¬value + burnPerTransaction ≤ s.balanceOf sender := by
      bv_omega
    simp [h2, liftM, monadLift]
    simp [MonadLift.monadLift, StateT.lift, pure, Except.pure, bind, WriterT.mk, Except.bind]
    unfold MonadLift.monadLift
    simp [WriterT.instMonadLiftOfEmptyCollection]
    simp [WriterT.liftTell, WriterT.mk]
    trivial

theorem transferFrom_fails_if_allowance_insufficient
    (sender senderFrom recipient : Address) (value : BitVec 256) (s : ContractState) :
    s.allowance senderFrom sender < value →
    ContractM.run (transferFrom sender senderFrom recipient value) s = Except.error Error.InsufficientAllowance := by
  intro h
  unfold transferFrom
  simp_all [ContractM.requireM]
  simp_all [bind, StateT.bind, StateT.run, WriterT.run, ContractM.run, Except.map, WriterT.mk, Except.bind, Functor.map]
  simp_all [get, getThe, MonadStateOf.get, StateT.get, pure, Except.pure]
  have h2 : ¬value ≤ s.allowance senderFrom sender := by
    bv_omega
  simp [h2, ContractM.fail, liftM, monadLift]
  simp [MonadLift.monadLift, StateT.lift, pure, Except.pure]
  simp_all [bind, WriterT.mk, Except.bind]
  unfold MonadLift.monadLift
  simp [WriterT.instMonadLiftOfEmptyCollection]
  simp [WriterT.liftTell, WriterT.mk]


end Hexagon
