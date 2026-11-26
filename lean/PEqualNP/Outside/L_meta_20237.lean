import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20237

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 3, 13), (true, 5, 15), (true, 0, 10), (true, 9, 17), (true, 2, 12), (true, 7, 11), (true, 16, 18), (true, 8, 9), (true, 19, 20), (true, 6, 8), (true, 6, 18), (true, 26, 19), (true, 27, 21), (true, 1, 14), (true, 17, 22), (true, 20, 21), (true, 0, 23), (true, 22, 23), (false, 24, 25), (false, 28, 29), (false, 30, 31), (false, 16, 32), (false, 4, 33), (true, 34, 35), (true, 39, 36), (true, 40, 37), (true, 41, 38)]

def circuit : Circuit := ⟨codes.map asGate, 42⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20237

open PEqualNP.Outside.L_meta_20237 in
theorem PEqualNP.Outside.L_meta_20237 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16488339210259238520 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
