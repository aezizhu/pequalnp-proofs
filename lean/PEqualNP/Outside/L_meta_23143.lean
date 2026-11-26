import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23143 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14127 : ℕ).testBit (6 * u.val + v.val)) 10) := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [5, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 3] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 4] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 2] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 7] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [13, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [11, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [16, 17] }], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
