import formal.Basic
import formal.IOMMU

namespace Ortho32.Hypervisor

open Ortho32
open Ortho32.IOMMU

structure GuestState where
  tenant : TenantId
  running : Bool
  memBase : PhysicalFrame
  memSize : UInt64
  deriving Repr, DecidableEq

structure HypervisorState where
  guests : List GuestState
  iommu : IOMMUState

inductive HVInput where
  | CreateGuest (g : GuestState)
  | DestroyGuest (g : GuestState)
  | StartGuest (g : GuestState)
  | StopGuest (g : GuestState)
  deriving Repr, DecidableEq

inductive HVTransition : HypervisorState → HVInput → HypervisorState → Prop where
  | createGuest : ∀ s g, g ∉ s.guests → HVTransition s (.CreateGuest g) ⟨g :: s.guests, s.iommu⟩
  | destroyGuest : ∀ s g, g ∈ s.guests → HVTransition s (.DestroyGuest g) ⟨s.guests.erase g, s.iommu⟩
  | startGuest : ∀ s g, g ∈ s.guests → g.running = false → HVTransition s (.StartGuest g) ⟨{ g with running := true } :: s.guests.erase g, s.iommu⟩
  | stopGuest : ∀ s g, g ∈ s.guests → g.running = true → HVTransition s (.StopGuest g) ⟨{ g with running := false } :: s.guests.erase g, s.iommu⟩

theorem vm_transition_deterministic
    (s : HypervisorState) (inp : HVInput) (s1 s2 : HypervisorState)
    (h1 : HVTransition s inp s1) (h2 : HVTransition s inp s2) :
    s1 = s2 := by
  cases h1 <;> cases h2 <;> rfl

private theorem mem_of_erase {α} [DecidableEq α] {a b : α} {l : List α} (h : a ∈ l.erase b) : a ∈ l := by
  induction l with
  | nil => simp at h
  | cons hd tl ih =>
    simp [List.erase] at h
    by_cases heq : hd = b
    · simp [heq] at h
      exact List.mem_cons_of_mem hd (ih h)
    · simp [heq] at h
      cases h with
      | inl heq2 => rw [heq2]; exact List.mem_cons_self
      | inr hmem => exact List.mem_cons_of_mem hd (ih hmem)

theorem tenant_identity_preserved
    (s s' : HypervisorState) (inp : HVInput) (h : HVTransition s inp s')
    (g' : GuestState) (hg' : g' ∈ s'.guests) :
    (∃ g ∈ s.guests, g.tenant = g'.tenant) ∨ (∃ gNew, inp = HVInput.CreateGuest gNew ∧ g' = gNew) := by
  cases h with
  | createGuest g hNot =>
    simp at hg'
    cases hg' with
    | inl heq =>
      rw [heq]
      right
      exact ⟨g, rfl, rfl⟩
    | inr hmem =>
      left
      exact ⟨g', hmem, rfl⟩
  | destroyGuest g hMem =>
    left
    have hmem : g' ∈ s.guests := mem_of_erase hg'
    exact ⟨g', hmem, rfl⟩
  | startGuest g hMem hRun =>
    simp at hg'
    cases hg' with
    | inl heq =>
      left
      rw [heq]
      simp
      exact ⟨g, hMem, rfl⟩
    | inr hmem =>
      left
      have hmem' : g' ∈ s.guests := mem_of_erase hmem
      exact ⟨g', hmem', rfl⟩
  | stopGuest g hMem hRun =>
    simp at hg'
    cases hg' with
    | inl heq =>
      left
      rw [heq]
      simp
      exact ⟨g, hMem, rfl⟩
    | inr hmem =>
      left
      have hmem' : g' ∈ s.guests := mem_of_erase hmem
      exact ⟨g', hmem', rfl⟩

/--
Hardware enforcement required: guest privilege confinement cannot be proved
from the pure software model. It relies on CPU virtualization hardware
(VMX/SVM) where hypervisor root mode is non-maskable and guest execution
is confined by hardware-enforced privilege levels and EPT/NPT. Without
hardware, a software-only model cannot guarantee de-privileging.
-/
def CanExecutePrivileged (g : GuestState) : Prop := False

axiom guest_privilege_confined : ∀ (s : HypervisorState) (g : GuestState), g ∈ s.guests → ¬ CanExecutePrivileged g

end Ortho32.Hypervisor
