import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19398 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 13) := by
  refine ⟨⟨[⟨.or, [9, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [6, 1]⟩,
    ⟨.or, [2, 8]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [11, 3]⟩, ⟨.and, [15, 12]⟩,
    ⟨.or, [13, 16]⟩, ⟨.and, [10, 18]⟩, ⟨.or, [19, 17]⟩], 20⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
