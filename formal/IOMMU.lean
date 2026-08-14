import formal.Basic

namespace Ortho32.IOMMU

open Ortho32

structure IOMMUState where
  entries : List IOMMUEntry
  wf : ∀ e1 e2, e1 ∈ entries → e2 ∈ entries → e1.device = e2.device → e1 = e2

def IOMMUState.allowsDMA (s : IOMMUState) (d : DeviceId) (addr : PhysicalFrame) : Prop :=
  ∃ e ∈ s.entries, e.device = d ∧ e.allows addr

def DeviceAssigned (s : IOMMUState) (d : DeviceId) (region : MemoryRegion) : Prop :=
  ∃ e ∈ s.entries, e.device = d ∧ e.allowedBase = region.base ∧ e.allowedSize = region.size

theorem iommu_dma_confined
    (s : IOMMUState) (d : DeviceId) (region : MemoryRegion) (addr : PhysicalFrame)
    (hAssigned : DeviceAssigned s d region)
    (hAllows : s.allowsDMA d addr) :
    region.contains addr := by
  unfold DeviceAssigned at hAssigned
  unfold IOMMUState.allowsDMA at hAllows
  obtain ⟨e1, he1Mem, he1Dev, he1Base, he1Size⟩ := hAssigned
  obtain ⟨e2, he2Mem, he2Dev, he2Allows⟩ := hAllows
  have heq : e1 = e2 := s.wf e1 e2 he1Mem he2Mem (by rw [he1Dev, he2Dev])
  subst heq
  unfold IOMMUEntry.allows at he2Allows
  rw [he1Base, he1Size] at he2Allows
  exact he2Allows

theorem iommu_cross_tenant_blocked
    (s : IOMMUState) (d1 d2 : DeviceId) (tA tB : TenantId) (ra rb : MemoryRegion)
    (hRA : ra.owner = tA) (hRB : rb.owner = tB) (hNe : tA ≠ tB)
    (hDisj : MemoryRegion.disjoint ra rb)
    (hAssigned1 : DeviceAssigned s d1 ra)
    (hAssigned2 : DeviceAssigned s d2 rb)
    (addr : PhysicalFrame)
    (hAllows1 : s.allowsDMA d1 addr) :
    ¬ rb.contains addr := by
  have hConf : ra.contains addr := iommu_dma_confined s d1 ra addr hAssigned1 hAllows1
  intro hRBContains
  unfold MemoryRegion.contains at hConf hRBContains
  unfold MemoryRegion.disjoint at hDisj
  cases hDisj with
  | inl hle => omega
  | inr hle => omega

theorem device_domain_unique
    (s : IOMMUState) (d : DeviceId) (e1 e2 : IOMMUEntry)
    (h1 : e1 ∈ s.entries) (h2 : e2 ∈ s.entries)
    (hD1 : e1.device = d) (hD2 : e2.device = d) :
    e1 = e2 ∧ e1.domain = e2.domain := by
  have heq : e1 = e2 := s.wf e1 e2 h1 h2 (by rw [hD1, hD2])
  constructor
  · exact heq
  · rw [heq]

end Ortho32.IOMMU
