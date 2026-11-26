import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19503 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7644377 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [6, 7]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [14, 12]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [15, 16]⟩, ⟨.not, [13]⟩, ⟨.or, [18, 17]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
