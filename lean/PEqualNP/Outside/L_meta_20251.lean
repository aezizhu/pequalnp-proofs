import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20251

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 2, 9), (true, 6, 15), (true, 3, 14), (true, 7, 13), (true, 1, 17), (true, 5, 11), (true, 0, 12), (true, 22, 20), (true, 3, 16), (true, 24, 21), (true, 0, 21), (true, 10, 18), (true, 27, 19), (true, 4, 19), (true, 8, 14), (true, 30, 16), (true, 31, 20), (true, 1, 2), (true, 33, 12), (true, 34, 18), (true, 4, 6), (true, 36, 8), (true, 37, 10), (false, 23, 25), (false, 26, 28), (false, 29, 32), (false, 35, 38), (true, 39, 40), (true, 43, 41), (true, 44, 42)]

def circuit : Circuit := ⟨codes.map asGate, 45⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20251

open PEqualNP.Outside.L_meta_20251 in
theorem PEqualNP.Outside.L_meta_20251 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14662300726579244910 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
