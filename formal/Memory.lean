/-
ORTHO-32 Isolation — Memory Ownership Theorems
Headline theorem: memory_regions_disjoint
-/

import formal.Basic

namespace Ortho32.Memory

open Ortho32

-- Memory ownership map: each frame has at most one owner
structure MemoryOwnership where
  regions : List MemoryRegion
  -- Well-formedness: all regions are pairwise disjoint
  wf : ∀ r1 r2, r1 ∈ regions → r2 ∈ regions → r1 ≠ r2 →
         MemoryRegion.disjoint r1 r2

-- Frame has a unique owner
def MemoryOwnership.ownerOf (m : MemoryOwnership) (f : PhysicalFrame) : Option TenantId :=
  match m.regions.find? (fun r => r.contains f) with
  | some r => some r.owner
  | none   => none

-- THEOREM: memory_regions_disjoint
-- Regions belonging to distinct tenants do not overlap.
theorem memory_regions_disjoint
    (m : MemoryOwnership)
    (r1 r2 : MemoryRegion)
    (h1 : r1 ∈ m.regions)
    (h2 : r2 ∈ m.regions)
    (hne : r1.owner ≠ r2.owner) :
    MemoryRegion.disjoint r1 r2 := by
  -- r1 ≠ r2 because they have different owners
  have hneq : r1 ≠ r2 := fun heq => hne (heq ▸ rfl)
  exact m.wf r1 r2 h1 h2 hneq

-- THEOREM: guest_mapping_confined
-- A guest page mapping must target a frame within the tenant's region.
-- Modelled as: if a mapping is accepted, the frame is in the tenant's region.
def guestMappingValid
    (m : MemoryOwnership) (tenant : TenantId)
    (frame : PhysicalFrame) : Prop :=
  ∃ r ∈ m.regions, r.owner = tenant ∧ r.contains frame

theorem guest_mapping_confined
    (m : MemoryOwnership) (tenant : TenantId) (frame : PhysicalFrame)
    (hvalid : guestMappingValid m tenant frame) :
    ∃ r ∈ m.regions, r.owner = tenant ∧ r.contains frame :=
  hvalid

-- THEOREM: frame_has_unique_owner
-- Under the well-formedness invariant, a frame cannot be owned by two distinct tenants.
theorem frame_unique_owner
    (m : MemoryOwnership)
    (f : PhysicalFrame)
    (r1 r2 : MemoryRegion)
    (h1 : r1 ∈ m.regions) (h2 : r2 ∈ m.regions)
    (hc1 : r1.contains f) (hc2 : r2.contains f) :
    r1.owner = r2.owner := by
  -- If owners differed, regions would be disjoint, contradicting both containing f
  by_contra hne
  have hdisj := m.wf r1 r2 h1 h2 (fun heq => hne (heq ▸ rfl))
  cases hdisj with
  | inl h =>
    have := hc1.2  -- f < r1.base + r1.size
    have := hc2.1  -- r1.base + r1.size ≤ r2.base ≤ f
    omega
  | inr h =>
    have := hc2.2
    have := hc1.1
    omega

end Ortho32.Memory
