/-
ORTHO-32 Isolation — Basic Types
Primitive definitions for tenant, memory, device, and command model.
Zero Mathlib. Zero sorry in headline chain.
-/

namespace Ortho32

-- Tenant identifier
def MAX_TENANTS : Nat := 256
abbrev TenantId := Fin MAX_TENANTS

-- Physical memory frame (4KB aligned address >> 12)
abbrev PhysicalFrame := UInt64

-- Virtual page number (guest physical address >> 12)
abbrev VirtualPage := UInt64

-- Device identifier
def MAX_DEVICES : Nat := 64
abbrev DeviceId := Fin MAX_DEVICES

-- IOMMU domain identifier (one per device)
abbrev IOMMUDomainId := Fin MAX_DEVICES

-- Monotonic command sequence number
abbrev CommandSequence := UInt64

-- Memory region: contiguous range owned by one tenant
structure MemoryRegion where
  base : PhysicalFrame
  size : UInt64        -- in frames
  owner : TenantId
  deriving Repr, DecidableEq

-- A frame is within a region
def MemoryRegion.contains (r : MemoryRegion) (f : PhysicalFrame) : Prop :=
  r.base ≤ f ∧ f < r.base + r.size

-- Two regions are disjoint
def MemoryRegion.disjoint (r1 r2 : MemoryRegion) : Prop :=
  r1.base + r1.size ≤ r2.base ∨ r2.base + r2.size ≤ r1.base

-- IOMMU entry: maps device to domain and allowed range
structure IOMMUEntry where
  device : DeviceId
  domain : IOMMUDomainId
  allowedBase : PhysicalFrame
  allowedSize : UInt64
  deriving Repr

def IOMMUEntry.allows (e : IOMMUEntry) (addr : PhysicalFrame) : Prop :=
  e.allowedBase ≤ addr ∧ addr < e.allowedBase + e.allowedSize

-- Capability tag carried on each fabric transaction
structure CapabilityTag where
  tenant   : TenantId
  action   : UInt32
  resource : UInt64
  expiry   : UInt64
  deriving Repr

end Ortho32
