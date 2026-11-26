import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19495 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3315386 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [1, 6]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [7, 10]⟩, ⟨.and, [13, 11]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.and, [12, 15]⟩, ⟨.not, [17]⟩, ⟨.and, [16, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
