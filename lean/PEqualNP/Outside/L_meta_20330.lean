import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20330

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 1, 12), (true, 2, 11), (true, 3, 15), (true, 4, 8), (true, 5, 14), (true, 6, 10), (true, 16, 17), (true, 16, 21), (true, 9, 20), (true, 10, 18), (true, 17, 19), (true, 0, 13), (true, 18, 22), (true, 9, 22), (true, 20, 21), (false, 23, 24), (false, 25, 26), (false, 27, 28), (false, 29, 7), (false, 19, 30), (true, 31, 32), (true, 36, 33), (true, 37, 34), (true, 38, 35)]

def circuit : Circuit := ⟨codes.map asGate, 39⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20330

open PEqualNP.Outside.L_meta_20330 in
theorem PEqualNP.Outside.L_meta_20330 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1892380200682152600 : ℕ).testBit (8 * u.val + v.val)) 24) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
