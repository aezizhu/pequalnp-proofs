import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27699

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def witnessX (w : Fin 9) (i : Fin 9) : Bool :=
  match w.val with
  | 0 => decide (i.val = 0 ∨ i.val = 1 ∨ i.val = 4 ∨ i.val = 8)
  | 1 => decide (i.val = 1 ∨ i.val = 0 ∨ i.val = 3 ∨ i.val = 8)
  | 2 => decide (i.val = 2 ∨ i.val = 3 ∨ i.val = 7)
  | 3 => decide (i.val = 3 ∨ i.val = 1 ∨ i.val = 8)
  | 4 => decide (i.val = 4 ∨ i.val = 0 ∨ i.val = 8)
  | 5 => decide (i.val = 5 ∨ i.val = 1 ∨ i.val = 6 ∨ i.val = 8)
  | 6 => decide (i.val = 6 ∨ i.val = 1 ∨ i.val = 5)
  | 7 => decide (i.val = 7 ∨ i.val = 0 ∨ i.val = 5)
  | _ => decide (i.val = 8 ∨ i.val = 0 ∨ i.val = 4 ∨ i.val = 5)

def witnessY (w : Fin 9) (i : Fin 9) : Bool :=
  if i = w then false else witnessX w i

def stepWire (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma witness_pm3_ne : ∀ w : Fin 9, pm3 (witnessX w) ≠ pm3 (witnessY w) := by
  decide

lemma stepWire_two_agree : ∀ wf : Fin 9,
    let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩
    let g1 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩
    let u0 := stepWire (stepWire (List.ofFn (witnessX wf)) g0) g1
    let v0 := stepWire (stepWire (List.ofFn (witnessY wf)) g0) g1
    u0.length = 11 ∧ v0.length = 11 ∧
      ∀ i : Fin 11, i.val ≠ wf.val → u0.getD i.val false = v0.getD i.val false := by
  decide

lemma getD_append_singleton (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with hlt | heq | hgt
  · simp [hlt, List.getElem?_append_left hlt]
  · subst heq
    simp
  · have hle : l.length ≤ i := hgt.le
    have hne : i ≠ l.length := hgt.ne'
    have hnot : ¬ i < l.length := Nat.not_lt.mpr hle
    have hpos : 1 ≤ i - l.length := Nat.sub_pos_of_lt hgt
    rw [List.getElem?_append_right hle]
    have hnone : ([b] : List Bool)[i - l.length]? = none := by
      rw [List.getElem?_eq_none_iff]
      simpa using hpos
    simp [hnot, hne, hnone]

lemma foldl_stepWire_agree (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : ℕ)
    (hw : w ∉ gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs) :
    ∀ (u v : List Bool), u.length = v.length →
      (∀ i : ℕ, i ≠ w → u.getD i false = v.getD i false) →
      ∀ i : ℕ, i ≠ w →
        (gs.foldl stepWire u).getD i false = (gs.foldl stepWire v).getD i false := by
  induction gs with
  | nil =>
    intro u v _ huv i hi
    exact huv i hi
  | cons g gs ih =>
    intro u v hlen huv i hi
    simp only [List.flatMap_cons, List.mem_append, not_or] at hw
    have hmap : g.inputs.map (fun j => u.getD j false) = g.inputs.map (fun j => v.getD j false) := by
      apply List.map_congr_left
      intro j hj
      exact huv j (fun h => hw.1 (h ▸ hj))
    have hlen' : (stepWire u g).length = (stepWire v g).length := by
      simp [stepWire, hlen]
    have huv' : ∀ k : ℕ, k ≠ w → (stepWire u g).getD k false = (stepWire v g).getD k false := by
      intro k hk
      simp only [stepWire, hmap]
      rw [getD_append_singleton, getD_append_singleton, hlen]
      by_cases hlt : k < v.length
      · simp only [hlt, ↓reduceIte]
        exact huv k hk
      · simp only [hlt, ↓reduceIte]
    exact ih hw.2 (stepWire u g) (stepWire v g) hlen' huv' i hi

lemma length_flatMap_le (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have hg := h g (by simp)
    have ih' := ih (fun g' hg' => h g' (by simp [hg']))
    omega

end PEqualNP.Outside.L_meta_27699

theorem PEqualNP.Outside.L_meta_27699 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩)) := by
  intro ⟨C, hfan, hsz, heval, hout, _, _, hused, h0, h1⟩
  rcases hgates : C.gates with _ | ⟨g0, _ | ⟨g1, gs⟩⟩
  · simp [hgates] at h0
  · simp [hgates] at h1
  · simp only [hgates, List.head?_cons, List.tail_cons, Option.some.injEq] at h0 h1
    subst h0
    subst h1
    have hsize : C.size = 2 + gs.length := by
      simp [PEqualNP.CircuitLowerBounds.Circuit.size, hgates]
      omega
    have hgs_len : gs.length ≤ 9 := by omega
    have hcov : Finset.range (10 + gs.length) ⊆
        (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset := by
      intro w hw
      rw [Finset.mem_range] at hw
      rw [List.mem_toFinset]
      by_cases hw9 : w < 9
      · by_contra hnot
        let wf : Fin 9 := ⟨w, hw9⟩
        have hpm3 := PEqualNP.Outside.L_meta_27699.witness_pm3_ne wf
        obtain ⟨hu0, hv0, hagree⟩ := PEqualNP.Outside.L_meta_27699.stepWire_two_agree wf
        let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩
        let g1 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [5, 8]⟩
        let x := PEqualNP.Outside.L_meta_27699.witnessX wf
        let y := PEqualNP.Outside.L_meta_27699.witnessY wf
        let u0 := PEqualNP.Outside.L_meta_27699.stepWire (PEqualNP.Outside.L_meta_27699.stepWire (List.ofFn x) g0) g1
        let v0 := PEqualNP.Outside.L_meta_27699.stepWire (PEqualNP.Outside.L_meta_27699.stepWire (List.ofFn y) g0) g1
        have hlen_eq : u0.length = v0.length := hu0.trans hv0.symm
        have hinit_agree : ∀ i : ℕ, i ≠ w → u0.getD i false = v0.getD i false := by
          intro i hi
          by_cases hlt : i < 11
          · exact hagree ⟨i, hlt⟩ hi
          · have hun : u0[i]? = none := List.getElem?_eq_none (by rw [hu0]; omega)
            have hvn : v0[i]? = none := List.getElem?_eq_none (by rw [hv0]; omega)
            simp [List.getD_eq_getElem?_getD, hun, hvn]
        have hout_ne : C.output ≠ w := by omega
        have heval_eq : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
          simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,
            PEqualNP.CircuitLowerBounds.Circuit.wires, hgates, List.foldl_cons]
          exact PEqualNP.Outside.L_meta_27699.foldl_stepWire_agree gs w hnot u0 v0 hlen_eq hinit_agree C.output hout_ne
        rw [heval x, heval y] at heval_eq
        exact hpm3 heval_eq
      · have hw9_ge : 9 ≤ w := Nat.le_of_not_lt hw9
        let j : ℕ := w - 9
        have hj_lt : j + 1 < C.gates.length := by
          rw [hgates]
          simp only [List.length_cons]
          omega
        have hj_fin : j < C.gates.length := by omega
        obtain ⟨k, hjk, hmem⟩ := hused ⟨j, hj_fin⟩ hj_lt
        obtain ⟨kv, hkl⟩ := k
        dsimp only at hjk hmem
        have hk_ge2 : 2 ≤ kv := by
          by_cases hj0 : j = 0
          · have hk_ge1 : 1 ≤ kv := by omega
            by_contra hlt2
            have hk1 : kv = 1 := by omega
            have hmem1 : 9 + 0 ∈ (C.gates.get ⟨1, by rw [hgates]; simp⟩).inputs := by
              have hk_eq : (⟨kv, hkl⟩ : Fin C.gates.length) = ⟨1, by rw [hgates]; simp⟩ := Fin.ext hk1
              rw [hk_eq] at hmem
              simpa [hj0] using hmem
            simp [hgates] at hmem1
          · omega
        have hk_sub : kv - 2 < gs.length := by
          rw [hgates] at hkl
          simp only [List.length_cons] at hkl
          omega
        have hgs_eq : C.gates.get ⟨kv, hkl⟩ = gs[kv - 2] := by
          simp only [hgates, List.get_eq_getElem]
          rcases kv with _ | _ | m
          · omega
          · omega
          · rfl
        rw [List.mem_flatMap]
        refine ⟨gs[kv - 2], List.getElem_mem hk_sub, ?_⟩
        rw [← hgs_eq]
        have hw_eq : 9 + j = w := by omega
        rwa [← hw_eq]
    have hcard : 10 + gs.length ≤ (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length := by
      calc 10 + gs.length
          = (Finset.range (10 + gs.length)).card := (Finset.card_range _).symm
        _ ≤ (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset.card := Finset.card_le_card hcov
        _ ≤ (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length := List.toFinset_card_le _
    have hbound : (gs.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length ≤ 2 * gs.length := by
      apply PEqualNP.Outside.L_meta_27699.length_flatMap_le
      intro g hg
      exact (hfan g (by simp [hgates, hg])).2
    omega
