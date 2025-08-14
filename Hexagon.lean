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

end Hexagon
