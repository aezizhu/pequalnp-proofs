import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19467 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7644982 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.and, [11, 15]⟩, ⟨.not, [17]⟩, ⟨.and, [16, 18]⟩], 19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
