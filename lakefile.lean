import Lake
open Lake DSL

package «ortho32-isolation» where
  name := `ortho32-isolation

lean_lib «Ortho32Isolation» where
  roots := #[`formal.Basic, `formal.Tenant, `formal.Memory,
             `formal.IOMMU, `formal.Hypervisor, `formal.DPU,
             `formal.ControlPlane, `formal.Audit]
