import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20244

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 4, 10), (true, 7, 12), (true, 2, 8), (true, 3, 9), (true, 5, 15), (true, 16, 17), (true, 0, 19), (true, 14, 19), (true, 0, 11), (true, 24, 17), (true, 14, 21), (true, 6, 13), (true, 18, 21), (true, 11, 18), (true, 16, 20), (false, 20, 22), (false, 23, 25), (false, 1, 26), (false, 27, 28), (false, 29, 30), (true, 31, 32), (true, 36, 33), (true, 37, 34), (true, 38, 35)]

def circuit : Circuit := ⟨codes.map asGate, 39⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20244

open PEqualNP.Outside.L_meta_20244 in
theorem PEqualNP.Outside.L_meta_20244 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7067567463510332610 : ℕ).testBit (8 * u.val + v.val)) 24) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
