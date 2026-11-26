import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19837

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 2, 5), (true, 0, 4), (true, 6, 7), (true, 1, 18), (true, 16, 19), (true, 17, 19), (true, 3, 17), (true, 16, 22), (true, 5, 19), (true, 3, 24), (true, 2, 22), (true, 6, 26), (true, 16, 18), (true, 0, 28), (true, 7, 22), (true, 1, 30), (true, 3, 16), (true, 4, 32), (true, 1, 33), (false, 8, 20), (false, 9, 34), (false, 10, 27), (false, 11, 25), (false, 12, 29), (false, 13, 23), (false, 14, 31), (false, 15, 21), (true, 35, 36), (true, 43, 37), (true, 44, 38), (true, 45, 39), (true, 46, 40), (true, 47, 41), (true, 48, 42)]

def circuit : Circuit := ⟨codes.map asGate, 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_19837

open PEqualNP.Outside.L_meta_19837 in
theorem PEqualNP.Outside.L_meta_19837 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15680755338451602420 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
