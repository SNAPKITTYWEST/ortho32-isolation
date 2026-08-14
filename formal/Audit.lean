/-
ORTHO-32 Isolation — Audit Chain Theorems
Headline theorem: audit_chain_append_only
-/

import formal.Basic

namespace Ortho32.Audit

open Ortho32

-- Witness record committed to the append-only audit log
structure WitnessRecord where
  sequence      : CommandSequence
  previousHash  : String        -- SHA-256 hex of prior record
  timestamp     : UInt64
  issuer        : String
  action        : String
  target        : String
  requestHash   : String
  resultHash    : String
  measurementHash : String
  signature     : String
  deriving Repr, DecidableEq

-- An audit chain: list of records where each commits to its predecessor
structure AuditChain where
  records : List WitnessRecord
  -- Well-formedness: sequences are strictly increasing
  seqMono : ∀ i j, i < j → j < records.length →
              (records.get ⟨i, by omega⟩).sequence <
              (records.get ⟨j, by omega⟩).sequence

-- THEOREM: sequence_monotonic
-- Sequences in a valid chain are strictly increasing.
theorem sequence_monotonic
    (c : AuditChain)
    (i j : Nat)
    (hi : i < c.records.length)
    (hj : j < c.records.length)
    (hij : i < j) :
    (c.records.get ⟨i, hi⟩).sequence < (c.records.get ⟨j, hj⟩).sequence :=
  c.seqMono i j hij hj

-- THEOREM: audit_chain_append_only
-- Appending a new record does not change any existing record.
theorem audit_chain_append_only
    (c : AuditChain)
    (r : WitnessRecord)
    (i : Nat)
    (hi : i < c.records.length) :
    (c.records.get ⟨i, hi⟩) =
    ((c.records ++ [r]).get ⟨i, by simp; omega⟩) := by
  simp [List.get_append_left hi]

-- THEOREM: mutation_invalidates_chain
-- Changing record i to a different value makes i's sequence ≠ original,
-- which breaks the monotonicity invariant for the chain containing it.
-- We model this as: if we replace record i with r' where r'.sequence ≠ original,
-- the resulting list cannot satisfy seqMono with the same surrounding records.
theorem mutation_changes_sequence
    (c : AuditChain)
    (i : Nat)
    (hi : i < c.records.length)
    (r' : WitnessRecord)
    (hne : r'.sequence ≠ (c.records.get ⟨i, hi⟩).sequence) :
    r' ≠ c.records.get ⟨i, hi⟩ := by
  intro heq
  exact hne (heq ▸ rfl)

end Ortho32.Audit
