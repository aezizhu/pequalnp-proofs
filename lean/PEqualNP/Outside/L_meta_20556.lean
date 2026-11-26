import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20556_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem spec (f : ℕ → Bool) : ∀ (gs : List Gate) (x : List Bool),
    (∀ i < x.length, x.getD i false = f i) →
    (∀ k (h : k < gs.length), (∀ i ∈ gs[k].inputs, i < x.length + k) ∧
      gs[k].op.eval (gs[k].inputs.map f) = f (x.length + k)) →
    ∀ i < x.length + gs.length, (gs.foldl stp x).getD i false = f i := by
  intro gs
  induction gs with
  | nil => intro x hx _ i hi; exact hx i (by simpa using hi)
  | cons g gs ih =>
    intro x hx hg i hi
    obtain ⟨h1, h2⟩ := hg 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at h1 h2
    have hl : (stp x g).length = x.length + 1 := by simp [stp]
    have hx' : ∀ i < (stp x g).length, (stp x g).getD i false = f i := by
      intro i hi
      rw [stp, getD_snoc]
      split_ifs with h3 h4
      · exact hx i h3
      · subst h4; rw [← h2]; congr 1
        exact List.map_congr_left fun j hj => hx j (by have := h1 j hj; omega)
      · omega
    refine ih (stp x g) hx' (fun k hk => ?_) i (by simp at hi; omega)
    obtain ⟨h5, h6⟩ := hg (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at h5 h6
    exact ⟨fun j hj => by have := h5 j hj; omega, by rw [h6, hl]; congr 1; omega⟩

def val (n u v k : ℕ) : Bool :=
  if k = 0 then decide (u = 0 ∧ v = 1)
  else if k = 1 then decide (u = 1 ∧ v = 0)
  else if k = 2 then decide ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0))
  else if k ≤ n then decide ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (2 ≤ u ∧ u ≤ k - 1))
  else decide ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (2 ≤ u ∧ u ≤ n - 1) ∨ (2 ≤ v ∧ v ≤ k - n + 1))

def f (n u v w : ℕ) : Bool :=
  if w < n then decide (u = w)
  else if w < 2 * n then decide (v + n = w)
  else val n u v (w - 2 * n)

def gate (n k : ℕ) : Gate :=
  if k = 0 then ⟨GateOp.and, [0, n + 1]⟩
  else if k = 1 then ⟨GateOp.and, [1, n]⟩
  else if k = 2 then ⟨GateOp.or, [2 * n, 2 * n + 1]⟩
  else if k ≤ n then ⟨GateOp.or, [2 * n + k - 1, k - 1]⟩
  else ⟨GateOp.or, [2 * n + k - 1, k + 1]⟩

def circ (n : ℕ) : Circuit :=
  ⟨List.ofFn (fun k : Fin (2 * n - 1) => gate n k.val), 4 * n - 2⟩

theorem mono_circ (n : ℕ) : Monotone2 (circ n) := by
  intro g hg
  simp only [circ, List.mem_ofFn] at hg
  obtain ⟨k, rfl⟩ := hg
  unfold gate
  split_ifs <;> simp

theorem size_circ (n : ℕ) : (circ n).size ≤ 2 * n - 1 := by
  simp [Circuit.size, circ]

theorem oe_eq (n : ℕ) (u v : Fin n) (i : ℕ) (hi : i < (oneEach u v).length) :
    (oneEach u v).getD i false = f n u.val v.val i := by
  simp only [oneEach, List.length_append, List.length_ofFn] at hi
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn, f]
  by_cases h1 : i < n
  · simp [h1, Fin.ext_iff, eq_comm]
  · have h2 : i - n < n := by omega
    have h3 : i < 2 * n := by omega
    simp only [h1, h2, h3, ↓reduceIte, Fin.ext_iff]
    by_cases h : v.val + n = i
    · have : i - n = v.val := by omega
      simp [h, this]
    · have : i - n ≠ v.val := by omega
      simp [h, this]

theorem gate_ok (n : ℕ) (hn : 2 ≤ n) (u v : Fin n) (k : ℕ) (hk : k < 2 * n - 1) :
    (∀ i ∈ (gate n k).inputs, i < 2 * n + k) ∧
      (gate n k).op.eval ((gate n k).inputs.map (f n u.val v.val)) = f n u.val v.val (2 * n + k) := by
  have hu : u.val < n := u.isLt
  have hv : v.val < n := v.isLt
  unfold gate
  split_ifs with h0 h1 h2 h3
  · subst h0
    refine ⟨by simp; omega, ?_⟩
    simp only [List.map, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, f, val]
    have c1 : (0 : ℕ) < n := by omega
    have c2 : ¬ n + 1 < n := by omega
    have c3 : n + 1 < 2 * n := by omega
    have c4 : ¬ 2 * n + 0 < n := by omega
    have c5 : ¬ 2 * n + 0 < 2 * n := by omega
    simp only [c1, c2, c3, c4, c5, ↓reduceIte, Nat.add_sub_cancel_left]
    by_cases e1 : u.val = 0 <;> by_cases e2 : v.val = 1 <;> simp [e1, e2] <;> omega
  · subst h1
    refine ⟨by simp; omega, ?_⟩
    simp only [List.map, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true, f, val]
    have c1 : (1 : ℕ) < n := by omega
    have c2 : ¬ n < n := by omega
    have c3 : n < 2 * n := by omega
    have c4 : ¬ 2 * n + 1 < n := by omega
    have c5 : ¬ 2 * n + 1 < 2 * n := by omega
    simp only [c1, c2, c3, c4, c5, ↓reduceIte, Nat.add_sub_cancel_left]
    by_cases e1 : u.val = 1 <;> by_cases e2 : v.val = 0 <;> simp [e1, e2]
  · subst h2
    refine ⟨by simp, ?_⟩
    simp only [List.map, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, f, val]
    have c1 : ¬ 2 * n < n := by omega
    have c2 : ¬ 2 * n < 2 * n := by omega
    have c3 : ¬ 2 * n + 1 < n := by omega
    have c4 : ¬ 2 * n + 1 < 2 * n := by omega
    have c5 : ¬ 2 * n + 2 < n := by omega
    have c6 : ¬ 2 * n + 2 < 2 * n := by omega
    simp only [c1, c2, c3, c4, c5, c6, ↓reduceIte, Nat.sub_self, Nat.add_sub_cancel_left]
    by_cases e1 : u.val = 0 ∧ v.val = 1 <;> by_cases e2 : u.val = 1 ∧ v.val = 0 <;> simp [e1, e2]
  · refine ⟨by simp; omega, ?_⟩
    simp only [List.map, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, f]
    have c1 : ¬ 2 * n + k - 1 < n := by omega
    have c2 : ¬ 2 * n + k - 1 < 2 * n := by omega
    have c3 : k - 1 < n := by omega
    have c4 : ¬ 2 * n + k < n := by omega
    have c5 : ¬ 2 * n + k < 2 * n := by omega
    have e1 : 2 * n + k - 1 - 2 * n = k - 1 := by omega
    have e2 : 2 * n + k - 2 * n = k := by omega
    simp only [c1, c2, c3, c4, c5, e1, e2, ↓reduceIte, val, h0, h1, h2, h3]
    by_cases hk3 : k = 3
    · subst hk3
      simp only [show (3 - 1 : ℕ) = 2 by rfl, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
      by_cases eA : (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) <;> by_cases eB : u.val = 2 <;> simp [eA, eB] <;> omega
    · have hk4 : 4 ≤ k := by omega
      have d0 : ¬ k - 1 = 0 := by omega
      have d1 : ¬ k - 1 = 1 := by omega
      have d2 : ¬ k - 1 = 2 := by omega
      have d3 : k - 1 ≤ n := by omega
      simp only [d0, d1, d2, d3, ↓reduceIte]
      by_cases eA : (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) <;>
        by_cases eB : 2 ≤ u.val ∧ u.val ≤ k - 1 - 1 <;>
        by_cases eC : u.val = k - 1 <;> simp [eA, eB, eC] <;> omega
  · refine ⟨by simp; omega, ?_⟩
    simp only [List.map, GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, f]
    have c1 : ¬ 2 * n + k - 1 < n := by omega
    have c2 : ¬ 2 * n + k - 1 < 2 * n := by omega
    have c3 : ¬ k + 1 < n := by omega
    have c4 : k + 1 < 2 * n := by omega
    have c5 : ¬ 2 * n + k < n := by omega
    have c6 : ¬ 2 * n + k < 2 * n := by omega
    have e1 : 2 * n + k - 1 - 2 * n = k - 1 := by omega
    have e2 : 2 * n + k - 2 * n = k := by omega
    simp only [c1, c2, c3, c4, c5, c6, e1, e2, ↓reduceIte, val, h0, h1, h2, h3]
    have hn3 : 3 ≤ n := by omega
    have d0 : ¬ k - 1 = 0 := by omega
    have d1 : ¬ k - 1 = 1 := by omega
    have d2 : ¬ k - 1 = 2 := by omega
    by_cases hkn : k = n + 1
    · subst hkn
      have d3 : n + 1 - 1 ≤ n := by omega
      have d4 : n + 1 - 1 - 1 = n - 1 := by omega
      have d5 : n + 1 - n + 1 = 2 := by omega
      simp only [d0, d1, d2, d3, d4, d5, ↓reduceIte]
      by_cases eA : (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) <;>
        by_cases eB : 2 ≤ u.val ∧ u.val ≤ n - 1 <;>
        by_cases eC : v.val + n = n + 1 + 1 <;> simp [eA, eB, eC] <;> omega
    · have d3 : ¬ k - 1 ≤ n := by omega
      simp only [d0, d1, d2, d3, ↓reduceIte]
      by_cases eA : (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) <;>
        by_cases eB : 2 ≤ u.val ∧ u.val ≤ n - 1 <;>
        by_cases eC : 2 ≤ v.val ∧ v.val ≤ k - 1 - n + 1 <;>
        by_cases eD : v.val + n = k + 1 <;> simp [eA, eB, eC, eD] <;> omega

theorem rep_circ (n : ℕ) (hn : 2 ≤ n) :
    Represents (fun u v : Fin n => !(decide (u = v) && decide (u.val < 2))) (circ n) := by
  intro u v
  simp only [Circuit.eval, Circuit.wires]
  change ((circ n).gates.foldl stp (oneEach u v)).getD (4 * n - 2) false = _
  have hlen : (oneEach u v).length = 2 * n := by simp [oneEach]; omega
  have hglen : (circ n).gates.length = 2 * n - 1 := by simp [circ]
  have hev := spec (f n u.val v.val) (circ n).gates (oneEach u v)
    (fun i hi => oe_eq n u v i hi)
    (fun k hk => by
      have hk' : k < 2 * n - 1 := by simpa [hglen] using hk
      have hgk : (circ n).gates[k] = gate n k := by simp [circ]
      rw [hgk, hlen]
      exact gate_ok n hn u v k hk')
    (4 * n - 2) (by omega)
  rw [hev]
  have hu : u.val < n := u.isLt
  have hv : v.val < n := v.isLt
  simp only [f]
  have c1 : ¬ 4 * n - 2 < n := by omega
  have c2 : ¬ 4 * n - 2 < 2 * n := by omega
  have e1 : 4 * n - 2 - 2 * n = 2 * n - 2 := by omega
  simp only [c1, c2, e1, ↓reduceIte, val]
  by_cases hn2 : n = 2
  · subst hn2
    simp only [show (2 * 2 - 2 : ℕ) = 2 by rfl, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
    fin_cases u <;> fin_cases v <;> decide
  · have d0 : ¬ 2 * n - 2 = 0 := by omega
    have d1 : ¬ 2 * n - 2 = 1 := by omega
    have d2 : ¬ 2 * n - 2 = 2 := by omega
    have d3 : ¬ 2 * n - 2 ≤ n := by omega
    simp only [d0, d1, d2, d3, ↓reduceIte]
    by_cases heq : u = v
    · subst heq
      by_cases hlt : u.val < 2 <;> simp [hlt] <;> omega
    · have hne : u.val ≠ v.val := fun h => heq (Fin.ext h)
      by_cases hlt : u.val < 2 <;> simp [heq, hlt] <;> omega

end PEqualNP.Outside.L_meta_20556_aux

theorem PEqualNP.Outside.L_meta_20556 : (∀ n : ℕ, 2 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => !(decide (u = v) && decide (u.val < 2))) (2 * n - 1)) := by
  intro n hn
  exact ⟨PEqualNP.Outside.L_meta_20556_aux.circ n,
    PEqualNP.Outside.L_meta_20556_aux.mono_circ n,
    PEqualNP.Outside.L_meta_20556_aux.size_circ n,
    PEqualNP.Outside.L_meta_20556_aux.rep_circ n hn⟩
