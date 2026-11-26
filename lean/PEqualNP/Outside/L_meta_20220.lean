import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20220

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 2, 14), (true, 3, 10), (true, 4, 13), (true, 7, 8), (true, 5, 14), (true, 20, 15), (true, 21, 17), (true, 0, 11), (true, 23, 19), (true, 16, 18), (true, 17, 19), (true, 6, 9), (true, 27, 16), (true, 0, 1), (true, 29, 12), (true, 30, 15), (true, 1, 5), (true, 32, 9), (true, 33, 11), (true, 6, 12), (true, 35, 18), (false, 22, 24), (false, 25, 26), (false, 28, 31), (false, 34, 36), (true, 37, 38), (true, 41, 39), (true, 42, 40)]

def circuit : Circuit := ⟨codes.map asGate, 43⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20220

open PEqualNP.Outside.L_meta_20220 in
theorem PEqualNP.Outside.L_meta_20220 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16472541325419705030 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
