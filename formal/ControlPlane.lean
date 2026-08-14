import formal.Basic
import formal.Audit

namespace Ortho32.ControlPlane

open Ortho32
open Ortho32.Audit

structure ControlCommand where
  commandId : String
  issuer : String
  tenant : TenantId
  action : UInt32
  parametersHash : String
  sequence : CommandSequence
  expiry : UInt64
  signature : String
  deriving Repr, DecidableEq

-- Axiomatized as opaque: signature verification is assumed to be provided by crypto layer
axiom verifySignature : ControlCommand → Bool

structure ControlPlaneState where
  lastSequence : CommandSequence
  deriving Repr, DecidableEq

inductive Executes : ControlCommand → ControlPlaneState → Prop where
  | mk : ∀ (cmd : ControlCommand) (st : ControlPlaneState),
      verifySignature cmd = true → cmd.sequence > st.lastSequence → Executes cmd st

def nextState (cmd : ControlCommand) (_st : ControlPlaneState) : ControlPlaneState :=
  { lastSequence := cmd.sequence }

-- Helper: UInt64 > is irreflexive (reduces to Nat.lt_irrefl via toNat)
private theorem UInt64_gt_irrefl (a : UInt64) : ¬ (a > a) := by
  intro h
  have h' : a.toNat < a.toNat := by simpa using h
  exact Nat.lt_irrefl _ h'

theorem signed_command_required (cmd : ControlCommand) (st : ControlPlaneState)
    (h : Executes cmd st) : verifySignature cmd = true := by
  cases h
  assumption

theorem replay_rejected (st : ControlPlaneState) (cmd1 cmd2 : ControlCommand)
    (h1 : Executes cmd1 st) (hEq : cmd1.sequence = cmd2.sequence) :
    ¬ Executes cmd2 (nextState cmd1 st) := by
  intro h2
  cases h1 with
  | mk _ _ hGt1 =>
    cases h2 with
    | mk _ _ hGt2 =>
      simp [nextState] at hGt2
      have hSelf : cmd2.sequence > cmd2.sequence := hEq ▸ hGt2
      exact UInt64_gt_irrefl _ hSelf

/--
Every executed command produces an audit witness record.
Axiomatized: witness generation is assumed correct. For any command that
executes in a state, there exists a `WitnessRecord` whose sequence,
issuer and requestHash correspond to the command.
-/
axiom command_produces_witness :
  ∀ (cmd : ControlCommand) (st : ControlPlaneState),
    Executes cmd st → ∃ (w : WitnessRecord),
      w.sequence = cmd.sequence ∧ w.issuer = cmd.issuer ∧ w.requestHash = cmd.parametersHash

end Ortho32.ControlPlane
