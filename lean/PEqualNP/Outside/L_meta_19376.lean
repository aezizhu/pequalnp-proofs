import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19376 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7597924 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [10, 11]⟩,
    ⟨.or, [7, 13]⟩, ⟨.and, [12, 13]⟩, ⟨.not, [15]⟩, ⟨.and, [14, 16]⟩], 17⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide
