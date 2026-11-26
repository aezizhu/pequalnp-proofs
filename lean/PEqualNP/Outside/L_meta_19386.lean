import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19386 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3320506 : ℕ).testBit (5 * u.val + v.val)) 15) := by
  refine ⟨⟨[⟨.or, [6, 1]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [2, 7]⟩,
    ⟨.or, [11, 13]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [10, 12]⟩, ⟨.and, [11, 12]⟩,
    ⟨.or, [15, 3]⟩, ⟨.or, [17, 16]⟩, ⟨.and, [14, 18]⟩, ⟨.or, [20, 19]⟩], 21⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
