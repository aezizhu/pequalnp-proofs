import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19500 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7586614 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [2, 8]⟩,
    ⟨.or, [1, 9]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [13, 14]⟩, ⟨.and, [12, 16]⟩,
    ⟨.not, [17]⟩, ⟨.and, [15, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
