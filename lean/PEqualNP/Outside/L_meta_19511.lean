import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19511 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236691 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [1, 8]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [0, 9]⟩,
    ⟨.or, [12, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [15, 16]⟩,
    ⟨.not, [17]⟩, ⟨.and, [14, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
