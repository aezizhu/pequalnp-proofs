import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20105

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def asGate (t : Bool × Nat × Nat) : Gate :=
  ⟨if t.1 then .or else .and, [t.2.1, t.2.2]⟩

def codes : List (Bool × Nat × Nat) := [(true, 1, 6), (true, 2, 5), (true, 16, 17), (true, 3, 4), (true, 17, 19), (true, 0, 19), (true, 2, 21), (true, 6, 21), (true, 7, 16), (true, 2, 24), (true, 3, 24), (true, 5, 7), (true, 0, 27), (true, 1, 28), (true, 4, 28), (false, 8, 26), (false, 9, 20), (false, 10, 18), (false, 11, 30), (false, 12, 25), (false, 13, 22), (false, 14, 29), (false, 15, 23), (true, 31, 32), (true, 39, 33), (true, 40, 34), (true, 41, 35), (true, 42, 36), (true, 43, 37), (true, 44, 38)]

def circuit : Circuit := ⟨codes.map asGate, 45⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  obtain ⟨⟨b, i, j⟩, _, rfl⟩ := List.mem_map.mp (show g ∈ codes.map asGate from hg)
  cases b <;> simp [asGate]

end PEqualNP.Outside.L_meta_20105

open PEqualNP.Outside.L_meta_20105 in
theorem PEqualNP.Outside.L_meta_20105 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6455152135695128040 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  exact ⟨circuit, mono, by decide, by decide +kernel⟩
