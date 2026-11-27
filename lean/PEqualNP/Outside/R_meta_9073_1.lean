import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9073_1
    (hDiffList :
      ∀ (p l : Fin (13 : ℕ)),
        (p = l ∨ p = l + (1 : Fin (13 : ℕ)) ∨ p = l + (3 : Fin (13 : ℕ)) ∨ p = l + (9 : Fin (13 : ℕ))) ↔
        (p - l).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)])
    (hDiffBounded9073 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        (26 : ℕ) ≤ C.output →
        C.output < (26 : ℕ) + C.size →
        PEqualNP.TopForm.IsAO2 (26 : ℕ) C →
        (∀ (x : Fin (26 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
          ∃ (p l : Fin (13 : ℕ)),
            (p - l).val ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
            p ≠ (0 : Fin (13 : ℕ)) ∧
            x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧
            x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (59 : ℕ) ≤ C.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (26 : ℕ) ≤ x1.output → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro C hOutGe hAO2 hSpec
  have hWiresLen : (C.wires (List.ofFn fun (_ : Fin 26) => true)).length = 26 + C.size := by
    have hGen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
        (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).length =
        w.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro w; rfl
      | cons g t ih =>
        intro w
        rw [List.foldl_cons, ih]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
    exact hGen C.gates (List.ofFn fun (_ : Fin 26) => true)
  have hOutLt : C.output < 26 + C.size := by
    by_contra hGe
    have hGe' : (C.wires (List.ofFn fun (_ : Fin 26) => true)).length ≤ C.output := by omega
    have hFalse : C.eval (List.ofFn fun (_ : Fin 26) => true) = false := by
      dsimp only [PEqualNP.CircuitLowerBounds.Circuit.eval]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hGe']
      rfl
    have hTrue : C.eval (List.ofFn fun (_ : Fin 26) => true) = true :=
      (hSpec (fun _ => true)).mpr ⟨1, 1, Or.inl rfl, by decide, rfl, rfl⟩
    rw [hTrue] at hFalse
    cases hFalse
  refine hDiffBounded9073 C hOutGe hOutLt hAO2 ?_
  intro x
  refine (hSpec x).trans (exists_congr fun p => exists_congr fun l => ?_)
  exact and_congr_left' (hDiffList p l)
