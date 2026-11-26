import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19526 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12059857 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [12, 13]⟩, ⟨.not, [14]⟩, ⟨.and, [10, 16]⟩, ⟨.and, [11, 15]⟩, ⟨.or, [17, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
