import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_718

open Classical

def parityDef {n : ℕ} (w : Fin n → ℕ) (y : ((i : Fin n) × Fin (w i)) → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i, j⟩ = true)).card)

def shapeDef (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧
  (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
  ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def traceDef {V : Type} (ask : List Bool → V) (p : List Bool) : List V :=
  List.ofFn (fun j : Fin p.length => ask (p.take j.val))

def consistentDef {V : Type} (ask : List Bool → V) (p : List Bool) (x : V → Bool) : Prop :=
  ∀ j : Fin p.length, x (ask (p.take j.val)) = p.get j

def wasteDef {n : ℕ} (w : Fin n → ℕ) (ask : List Bool → (i : Fin n) × Fin (w i)) (p : List Bool) : ℕ :=
  let bank := (traceDef ask p).map Sigma.fst
  ∑ i : Fin n, if bank.count i < w i then bank.count i else 0

lemma nodup_map_fst_count_le {n : ℕ} {w : Fin n → ℕ}
    (L : List ((i : Fin n) × Fin (w i))) (hL : L.Nodup) (i : Fin n) :
    (L.map Sigma.fst).count i ≤ w i := by
  have hcount : (L.map Sigma.fst).count i = (L.toFinset.filter (fun r => r.1 = i)).card := by
    induction L with
    | nil => simp
    | cons r tl ih =>
      rw [List.nodup_cons] at hL
      have h1 := ih hL.2
      simp only [List.map_cons, List.count_cons, List.toFinset_cons, Finset.filter_insert]
      by_cases hr : r.1 = i
      · have hr_not : r ∉ tl.toFinset.filter (fun x => x.1 = i) := by
          simp [hL.1]
        simp [hr, hr_not, h1]
      · simp [hr, h1]
  rw [hcount]
  have hinj : Set.InjOn (fun r : (a : Fin n) × Fin (w a) => (r.2 : ℕ))
      (↑(L.toFinset.filter (fun r => r.1 = i)) : Set ((a : Fin n) × Fin (w a))) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, List.mem_toFinset] at ha hb
    cases a with
    | mk a1 a2 =>
      cases b with
      | mk b1 b2 =>
        dsimp only at ha hb hab
        have h1 : a1 = b1 := ha.2.trans hb.2.symm
        subst h1
        have h2 : a2 = b2 := Fin.ext hab
        subst h2
        rfl
  calc
    (L.toFinset.filter (fun r => r.1 = i)).card
        = ((L.toFinset.filter (fun r => r.1 = i)).image (fun r => (r.2 : ℕ))).card :=
          (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (w i)).card := by
      refine Finset.card_le_card ?_
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset, Finset.mem_range] at hx ⊢
      rcases hx with ⟨r, ⟨_, hr1⟩, rfl⟩
      cases r with
      | mk r1 r2 =>
        dsimp at hr1 ⊢
        subst hr1
        exact r2.isLt
    _ = w i := Finset.card_range (w i)

lemma list_length_eq_sum_count {n : ℕ} (L : List (Fin n)) :
    L.length = ∑ i : Fin n, L.count i := by
  induction L with
  | nil => simp
  | cons a tl ih =>
    simp only [List.length_cons, List.count_cons, ih]
    have h2 : ∑ i : Fin n, (if a == i then 1 else 0) = 1 := by
      have : (fun i : Fin n => if a == i then 1 else 0) = fun i => if i = a then 1 else 0 := by
        ext i
        by_cases h : i = a
        · subst h; simp
        · simp [h, Ne.symm h]
      rw [this]
      simp
    calc
      (∑ i : Fin n, tl.count i) + 1
          = (∑ i : Fin n, tl.count i) + ∑ i : Fin n, (if a == i then 1 else 0) := by rw [h2]
      _ = ∑ i : Fin n, (tl.count i + if a == i then 1 else 0) := Finset.sum_add_distrib.symm

lemma list_exists_idx_of_count_lt {α : Type} [DecidableEq α] (L : List α) (a : α) (k : ℕ)
    (hk : k < L.count a) :
    ∃ s : Fin L.length, L.get s = a ∧ (L.take s.val).count a = k := by
  induction L generalizing k with
  | nil => simp at hk
  | cons x tl ih =>
    simp only [List.count_cons] at hk
    by_cases hxa : x = a
    · simp [hxa] at hk
      cases k with
      | zero =>
        refine ⟨⟨0, by simp⟩, ?_, ?_⟩
        · simp [hxa]
        · simp
      | succ k' =>
        have hk' : k' < tl.count a := by omega
        obtain ⟨s', hs1, hs2⟩ := ih k' hk'
        refine ⟨s'.succ, ?_, ?_⟩
        · simpa using hs1
        · simp [List.take_succ_cons, hxa, hs2]
    · simp [hxa] at hk
      have hk' : k < tl.count a := by omega
      obtain ⟨s', hs1, hs2⟩ := ih k hk'
      refine ⟨s'.succ, ?_, ?_⟩
      · simpa using hs1
      · simp [List.take_succ_cons, hxa, hs2]

lemma list_count_take_lt_of_get_eq {α : Type} [DecidableEq α] (L : List α) (a : α)
    (s : Fin L.length) (hs : L.get s = a) :
    (L.take s.val).count a < L.count a := by
  have hpref : L.take s.val ++ [a] <+: L := by
    rw [← hs]
    exact ⟨L.drop (s.val + 1), by
      have h1 : L.take (s.val + 1) = L.take s.val ++ [L.get s] := by
        simp [List.get_eq_getElem]
      calc
        L.take s.val ++ [L.get s] ++ L.drop (s.val + 1)
            = L.take (s.val + 1) ++ L.drop (s.val + 1) := by rw [h1]
        _ = L := List.take_append_drop (s.val + 1) L⟩
  obtain ⟨r, hr⟩ := hpref
  have hcount : L.count a = (L.take s.val).count a + 1 + r.count a := by
    conv_lhs => rw [← hr]
    simp [List.count_append]
    omega
  omega

lemma list_count_take_strict_mono {α : Type} [DecidableEq α] (L : List α) (a : α)
    {s₁ s₂ : Fin L.length} (hlt : s₁ < s₂) (h1 : L.get s₁ = a) (_h2 : L.get s₂ = a) :
    (L.take s₁.val).count a < (L.take s₂.val).count a := by
  have hle : s₁.val + 1 ≤ s₂.val := hlt
  have hpref : L.take s₁.val ++ [a] <+: L.take s₂.val := by
    have h1' : L.take (s₁.val + 1) = L.take s₁.val ++ [L.get s₁] := by
      simp [List.get_eq_getElem]
    rw [← h1, ← h1']
    exact ⟨(L.take s₂.val).drop (s₁.val + 1), by
      have hdrop := List.take_append_drop (s₁.val + 1) (L.take s₂.val)
      rwa [List.take_take, Nat.min_eq_left hle] at hdrop⟩
  obtain ⟨r, hr⟩ := hpref
  have hc : (L.take s₂.val).count a = (L.take s₁.val).count a + 1 + r.count a := by
    conv_lhs => rw [← hr]
    simp [List.count_append]
    omega
  omega

lemma decide_odd_add_ite_bool (k : ℕ) (b : Bool) :
    decide (Odd (k + if b = true then 1 else 0)) = xor (decide (Odd k)) b := by
  cases b
  · simp
  · simp only [↓reduceIte, Bool.xor_true]
    by_cases hk : Odd k
    · have hev : ¬ Odd (k + 1) := by
        rcases hk with ⟨m, rfl⟩
        intro ⟨t, ht⟩
        omega
      simp [hk, hev]
    · have hodd : Odd (k + 1) := by
        rw [Nat.not_odd_iff_even] at hk
        rcases hk with ⟨m, rfl⟩
        exact ⟨m, by omega⟩
      simp [hk, hodd]

lemma decide_odd_flip_coord {m : ℕ} (f : Fin m → Bool) (j₀ : Fin m) :
    decide (Odd ((Finset.univ : Finset (Fin m)).filter (fun j => (if j = j₀ then !(f j₀) else f j) = true)).card) =
      !(decide (Odd ((Finset.univ : Finset (Fin m)).filter (fun j => f j = true)).card)) := by
  set S := (Finset.univ : Finset (Fin m)).filter (fun j => f j = true)
  set S' := (Finset.univ : Finset (Fin m)).filter (fun j => (if j = j₀ then !(f j₀) else f j) = true)
  have hcard : S'.card = if f j₀ = true then S.card - 1 else S.card + 1 := by
    cases hf : f j₀
    · have hS' : S' = insert j₀ S := by
        ext j
        simp only [S', S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        by_cases hj : j = j₀
        · subst hj; simp [hf]
        · simp [hj]
      have hj0 : j₀ ∉ S := by simp [S, hf]
      rw [hS', Finset.card_insert_of_notMem hj0]
      simp
    · have hS' : S' = S.erase j₀ := by
        ext j
        simp only [S', S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        by_cases hj : j = j₀
        · subst hj; simp [hf]
        · simp [hj]
      have hj0 : j₀ ∈ S := by simp [S, hf]
      rw [hS', Finset.card_erase_of_mem hj0]
      simp
  rw [hcard]
  cases hf : f j₀
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have h1 := decide_odd_add_ite_bool S.card true
    simpa using h1
  · simp only [↓reduceIte]
    have hj0 : j₀ ∈ S := by simp [S, hf]
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨j₀, hj0⟩
    have h1 := decide_odd_add_ite_bool (S.card - 1) true
    have h2 : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hpos
    simp only [ite_true, h2] at h1
    cases hodd : decide (Odd (S.card - 1)) <;> simp_all

structure Ctx where
  n : ℕ
  hn : 0 < n
  w : Fin n → ℕ
  hw : ∀ i, 0 < w i
  H : ℕ
  N : Finset (List Bool)
  J : Finset (List Bool)
  ask : List Bool → (i : Fin n) × Fin (w i)
  hshape : shapeDef N J
  hN : ∀ p ∈ N, (traceDef ask p).Nodup ∧ p.length ≤ H

namespace Ctx

def bank (c : Ctx) (p : List Bool) : List (Fin c.n) :=
  (traceDef c.ask p).map Sigma.fst

lemma bank_length (c : Ctx) (p : List Bool) : (c.bank p).length = p.length := by
  simp [bank, traceDef]

lemma trace_take (c : Ctx) (p : List Bool) (k : ℕ) (hk : k ≤ p.length) :
    traceDef c.ask (p.take k) = (traceDef c.ask p).take k := by
  apply List.ext_getElem
  · simp [traceDef, hk]
  · intro j hj1 hj2
    have hjk : j < k := by simpa [traceDef, hk] using hj1
    simp only [traceDef, List.getElem_take, List.getElem_ofFn]
    congr 1
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjk)]

lemma bank_take (c : Ctx) (p : List Bool) (k : ℕ) (hk : k ≤ p.length) :
    c.bank (p.take k) = (c.bank p).take k := by
  simp [bank, c.trace_take p k hk, List.map_take]

lemma trace_append_singleton (c : Ctx) (p : List Bool) (b : Bool) :
    traceDef c.ask (p ++ [b]) = traceDef c.ask p ++ [c.ask p] := by
  unfold traceDef
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    have hj_lt : j < p.length + 1 := by
      simpa using hj1
    rw [List.getElem_ofFn]
    by_cases hjp : j < p.length
    · have hlen_tr : j < (List.ofFn fun j : Fin p.length => c.ask (p.take j.val)).length := by
        simp [hjp]
      rw [List.getElem_append_left hlen_tr, List.getElem_ofFn]
      have htake : (p ++ [b]).take j = p.take j := List.take_append_of_le_length (Nat.le_of_lt hjp)
      rw [htake]
    · have hj_eq : j = p.length := by omega
      subst hj_eq
      have hlen_tr : (List.ofFn fun j : Fin p.length => c.ask (p.take j.val)).length = p.length := by
        simp
      rw [List.getElem_append_right (by omega)]
      simp [hlen_tr]

lemma bank_append_singleton (c : Ctx) (p : List Bool) (b : Bool) :
    c.bank (p ++ [b]) = c.bank p ++ [(c.ask p).1] := by
  simp [bank, c.trace_append_singleton]

lemma take_mem_N_and_J (c : Ctx) {p : List Bool} (hp : p ∈ c.N) :
    (∀ k ≤ p.length, p.take k ∈ c.N) ∧ (∀ k < p.length, p.take k ∈ c.J) := by
  have hmain : ∀ d k, k + d = p.length → p.take k ∈ c.N ∧ (0 < d → p.take k ∈ c.J) := by
    intro d
    induction d with
    | zero =>
      intro k hk
      have hkp : k = p.length := by omega
      subst hkp
      simp [hp]
    | succ d ih =>
      intro k hk
      have hlt : k < p.length := by omega
      have hsucc : p.take (k + 1) ∈ c.N := (ih (k + 1) (by omega)).1
      have htake : p.take (k + 1) = p.take k ++ [p[k]] := by simp
      rw [htake] at hsucc
      have hJ : p.take k ∈ c.J := c.hshape.2.2.1 (p.take k) p[k] hsucc
      exact ⟨c.hshape.2.1 hJ, fun _ => hJ⟩
  constructor
  · intro k hk
    exact (hmain (p.length - k) k (by omega)).1
  · intro k hk
    exact (hmain (p.length - k) k (by omega)).2 (by omega)

lemma prefix_mem_N (c : Ctx) {q p : List Bool} (hq : q <+: p) (hp : p ∈ c.N) : q ∈ c.N := by
  obtain ⟨r, rfl⟩ := hq
  have hlen : q.length ≤ (q ++ r).length := by simp
  have h1 := (c.take_mem_N_and_J hp).1 q.length hlen
  simpa using h1

lemma prefix_mem_J (c : Ctx) {q p : List Bool} (hq : q <+: p) (hlt : q.length < p.length)
    (hp : p ∈ c.N) : q ∈ c.J := by
  obtain ⟨r, rfl⟩ := hq
  have h1 := (c.take_mem_N_and_J hp).2 q.length hlt
  simpa using h1

lemma bank_count_le (c : Ctx) {p : List Bool} (hp : p ∈ c.N) (i : Fin c.n) :
    (c.bank p).count i ≤ c.w i :=
  nodup_map_fst_count_le (traceDef c.ask p) (c.hN p hp).1 i

lemma count_lt_of_mem_J (c : Ctx) {p : List Bool} (hp : p ∈ c.J) :
    (c.bank p).count (c.ask p).1 < c.w (c.ask p).1 := by
  have hN : p ++ [false] ∈ c.N := (c.hshape.2.2.2 p hp).1
  have hle := c.bank_count_le hN (c.ask p).1
  rw [c.bank_append_singleton, List.count_append] at hle
  simp at hle
  omega

lemma length_lt_H_of_mem_J (c : Ctx) {p : List Bool} (hp : p ∈ c.J) : p.length < c.H := by
  have hN : p ++ [false] ∈ c.N := (c.hshape.2.2.2 p hp).1
  have hle := (c.hN (p ++ [false]) hN).2
  simp at hle
  omega

def Coin (c : Ctx) : Type := (i : Fin c.n) → Fin (c.w i - 1) → Bool

def bias (c : Ctx) (t : c.Coin) (i : Fin c.n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin (c.w i - 1))).filter (fun k => t i k = true)).card)

noncomputable def follow (c : Ctx) (t : c.Coin) (p : List Bool) : List Bool :=
  if hp : p ∈ c.J ∧ p.length < c.H ∧ (c.bank p).count (c.ask p).1 < c.w (c.ask p).1 - 1 then
    c.follow t (p ++ [t (c.ask p).1 ⟨(c.bank p).count (c.ask p).1, hp.2.2⟩])
  else p
termination_by c.H - p.length
decreasing_by
  simp_wf
  have := hp.2.1
  omega

lemma follow_eq (c : Ctx) (t : c.Coin) (p : List Bool) :
    c.follow t p =
      if hp : p ∈ c.J ∧ p.length < c.H ∧ (c.bank p).count (c.ask p).1 < c.w (c.ask p).1 - 1 then
        c.follow t (p ++ [t (c.ask p).1 ⟨(c.bank p).count (c.ask p).1, hp.2.2⟩])
      else p := by
  conv_lhs => unfold follow

lemma follow_mem (c : Ctx) (t : c.Coin) (p : List Bool) (hp : p ∈ c.N) :
    c.follow t p ∈ c.N := by
  have hfeq := c.follow_eq t p
  split_ifs at hfeq with h
  · rw [hfeq]
    have hnext : p ++ [t (c.ask p).1 ⟨(c.bank p).count (c.ask p).1, h.2.2⟩] ∈ c.N := by
      cases t (c.ask p).1 ⟨(c.bank p).count (c.ask p).1, h.2.2⟩
      · exact (c.hshape.2.2.2 p h.1).1
      · exact (c.hshape.2.2.2 p h.1).2
    exact c.follow_mem t _ hnext
  · rw [hfeq]
    exact hp
termination_by c.H - p.length
decreasing_by
  simp_wf
  have := h.2.1
  omega

lemma follow_prefix (c : Ctx) (t : c.Coin) (p : List Bool) :
    p <+: c.follow t p := by
  have hfeq := c.follow_eq t p
  split_ifs at hfeq with h
  · rw [hfeq]
    exact List.IsPrefix.trans (List.prefix_append p _) (c.follow_prefix t _)
  · rw [hfeq]
termination_by c.H - p.length
decreasing_by
  simp_wf
  have := h.2.1
  omega

lemma follow_stop (c : Ctx) (t : c.Coin) (p : List Bool) (_hp : p ∈ c.N)
    (hJ : c.follow t p ∈ c.J) :
    (c.bank (c.follow t p)).count (c.ask (c.follow t p)).1 = c.w (c.ask (c.follow t p)).1 - 1 := by
  have hfeq := c.follow_eq t p
  split_ifs at hfeq with h
  · have hnext : p ++ [t (c.ask p).1 ⟨(c.bank p).count (c.ask p).1, h.2.2⟩] ∈ c.N := by
      cases t (c.ask p).1 ⟨(c.bank p).count (c.ask p).1, h.2.2⟩
      · exact (c.hshape.2.2.2 p h.1).1
      · exact (c.hshape.2.2.2 p h.1).2
    rw [hfeq] at hJ ⊢
    exact c.follow_stop t _ hnext hJ
  · rw [hfeq] at hJ ⊢
    have hlt := c.count_lt_of_mem_J hJ
    have hH := c.length_lt_H_of_mem_J hJ
    have hnot : ¬ (c.bank p).count (c.ask p).1 < c.w (c.ask p).1 - 1 := by
      intro hlt2
      exact h ⟨hJ, hH, hlt2⟩
    omega
termination_by c.H - p.length
decreasing_by
  simp_wf
  have := h.2.1
  omega

lemma coin_eq_of_eq (c : Ctx) (t : c.Coin) {p1 p2 : List Bool} (hp : p1 = p2)
    (h1 : (c.bank p1).count (c.ask p1).1 < c.w (c.ask p1).1 - 1)
    (h2 : (c.bank p2).count (c.ask p2).1 < c.w (c.ask p2).1 - 1) :
    t (c.ask p1).1 ⟨(c.bank p1).count (c.ask p1).1, h1⟩ =
    t (c.ask p2).1 ⟨(c.bank p2).count (c.ask p2).1, h2⟩ := by
  subst hp
  rfl

lemma follow_step_spec (c : Ctx) (t : c.Coin) (p : List Bool) (s : ℕ)
    (hs1 : p.length ≤ s) (hs2 : s < (c.follow t p).length) :
    ∃ hk : (c.bank ((c.follow t p).take s)).count (c.ask ((c.follow t p).take s)).1 <
        c.w (c.ask ((c.follow t p).take s)).1 - 1,
      (c.follow t p)[s] =
        t (c.ask ((c.follow t p).take s)).1
          ⟨(c.bank ((c.follow t p).take s)).count (c.ask ((c.follow t p).take s)).1, hk⟩ := by
  have hfeq := c.follow_eq t p
  split_ifs at hfeq with h
  · set b := t (c.ask p).1 ⟨(c.bank p).count (c.ask p).1, h.2.2⟩
    set p1 := p ++ [b]
    have hp1_pref : p1 <+: c.follow t p1 := c.follow_prefix t p1
    by_cases hsp : s = p.length
    · subst hsp
      have htake : (c.follow t p).take p.length = p := by
        rw [hfeq]
        have hpp1 : p <+: c.follow t p1 := List.IsPrefix.trans (List.prefix_append p [b]) hp1_pref
        obtain ⟨tl, htl⟩ := hpp1
        rw [← htl, List.take_left]
      have hget : (c.follow t p)[p.length]'hs2 = b := by
        have hlen1 : p.length < p1.length := by simp [p1]
        have helem := hp1_pref.getElem hlen1
        have hp1_eq : p1[p.length] = b := by simp [p1]
        rw [hp1_eq] at helem
        simpa only [hfeq] using helem.symm
      refine ⟨by rw [htake]; exact h.2.2, ?_⟩
      rw [hget]
      exact c.coin_eq_of_eq t htake.symm h.2.2 _
    · have hs_ge : p1.length ≤ s := by
        simp only [p1, List.length_append, List.length_singleton]
        omega
      have hs2' : s < (c.follow t p1).length := by rw [← hfeq]; exact hs2
      obtain ⟨hk, heq⟩ := follow_step_spec c t p1 s hs_ge hs2'
      have htake_eq : (c.follow t p).take s = (c.follow t p1).take s := by rw [hfeq]
      refine ⟨by rw [htake_eq]; exact hk, ?_⟩
      have hget_eq : (c.follow t p)[s]'hs2 = (c.follow t p1)[s]'hs2' := by simp_rw [hfeq]
      rw [hget_eq, heq]
      exact c.coin_eq_of_eq t htake_eq.symm hk _
  · rw [hfeq] at hs2
    omega
termination_by c.H - p.length
decreasing_by
  simp_wf
  have := h.2.1
  omega

noncomputable def runFrom (c : Ctx) (t : c.Coin) (p u : List Bool) : Option (List Bool) :=
  let p' := c.follow t p
  match u with
  | [] => some p'
  | b :: u' =>
    if p' ∈ c.J then
      c.runFrom t (p' ++ [xor b (c.bias t (c.ask p').1)]) u'
    else
      none

lemma runFrom_mem (c : Ctx) (t : c.Coin) (u p r : List Bool) (hp : p ∈ c.N)
    (hr : c.runFrom t p u = some r) : r ∈ c.N := by
  induction u generalizing p with
  | nil =>
    simp only [runFrom, Option.some.injEq] at hr
    rw [← hr]
    exact c.follow_mem t p hp
  | cons b u' ih =>
    simp only [runFrom] at hr
    split_ifs at hr with hJ
    have hnext : c.follow t p ++ [xor b (c.bias t (c.ask (c.follow t p)).1)] ∈ c.N := by
      cases xor b (c.bias t (c.ask (c.follow t p)).1)
      · exact (c.hshape.2.2.2 _ hJ).1
      · exact (c.hshape.2.2.2 _ hJ).2
    exact ih _ hnext hr

lemma runFrom_prefix (c : Ctx) (t : c.Coin) (u p r : List Bool)
    (hr : c.runFrom t p u = some r) : p <+: r := by
  induction u generalizing p with
  | nil =>
    simp only [runFrom, Option.some.injEq] at hr
    rw [← hr]
    exact c.follow_prefix t p
  | cons b u' ih =>
    simp only [runFrom] at hr
    split_ifs at hr with hJ
    have h1 := c.follow_prefix t p
    have h2 := List.prefix_append (c.follow t p) [xor b (c.bias t (c.ask (c.follow t p)).1)]
    have h3 := ih _ hr
    exact List.IsPrefix.trans h1 (List.IsPrefix.trans h2 h3)

lemma runFrom_length (c : Ctx) (t : c.Coin) (u p r : List Bool)
    (hr : c.runFrom t p u = some r) : (c.follow t p).length + u.length ≤ r.length := by
  induction u generalizing p with
  | nil =>
    simp only [runFrom, Option.some.injEq] at hr
    rw [← hr]
    simp
  | cons b u' ih =>
    simp only [runFrom] at hr
    split_ifs at hr with hJ
    have h1 := ih _ hr
    have h2 : (c.follow t p).length + 1 ≤
        (c.follow t (c.follow t p ++ [xor b (c.bias t (c.ask (c.follow t p)).1)])).length := by
      have hpref := c.follow_prefix t (c.follow t p ++ [xor b (c.bias t (c.ask (c.follow t p)).1)])
      simpa using hpref.length_le
    simp only [List.length_cons]
    omega

lemma runFrom_append_cons (c : Ctx) (t : c.Coin) (u₁ : List Bool) (b : Bool) (u₂ p : List Bool) :
    c.runFrom t p (u₁ ++ b :: u₂) =
      match c.runFrom t p u₁ with
      | some p₁ =>
        if p₁ ∈ c.J then c.runFrom t (p₁ ++ [xor b (c.bias t (c.ask p₁).1)]) u₂
        else none
      | none => none := by
  induction u₁ generalizing p with
  | nil =>
    simp only [List.nil_append, runFrom]
  | cons a u₁' ih =>
    simp only [List.cons_append, runFrom]
    split_ifs with hJ
    · exact ih _
    · rfl

lemma runFrom_append_singleton (c : Ctx) (t : c.Coin) (u p : List Bool) (b : Bool) :
    c.runFrom t p (u ++ [b]) =
      match c.runFrom t p u with
      | some p' =>
        if p' ∈ c.J then some (c.follow t (p' ++ [xor b (c.bias t (c.ask p').1)]))
        else none
      | none => none := by
  simpa [runFrom] using c.runFrom_append_cons t u b [] p

noncomputable def allLists (H : ℕ) : Finset (List Bool) :=
  (Finset.range (H + 1)).biUnion fun len =>
    (Finset.univ : Finset (Fin len → Bool)).image List.ofFn

lemma mem_allLists {H : ℕ} {u : List Bool} : u ∈ allLists H ↔ u.length ≤ H := by
  simp only [allLists, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨len, hlen, f, _, rfl⟩
    simp only [List.length_ofFn]
    omega
  · intro hu
    refine ⟨u.length, by omega, fun j => u.get j, ?_⟩
    simp

noncomputable def M (c : Ctx) (t : c.Coin) : Finset (List Bool) :=
  (allLists c.H).filter (fun u => (c.runFrom t [] u).isSome)

noncomputable def A (c : Ctx) (t : c.Coin) : Finset (List Bool) :=
  (c.M t).filter (fun u => match c.runFrom t [] u with | some p' => p' ∈ c.J | none => false)

lemma mem_M (c : Ctx) (t : c.Coin) (u : List Bool) :
    u ∈ c.M t ↔ (c.runFrom t [] u).isSome := by
  simp only [M, Finset.mem_filter, mem_allLists, and_iff_right_iff_imp]
  intro hsome
  cases h : c.runFrom t [] u with
  | none => simp [h] at hsome
  | some r =>
    have hrN := c.runFrom_mem t u [] r c.hshape.1 h
    have hrH := (c.hN r hrN).2
    have hlen := c.runFrom_length t u [] r h
    omega

lemma mem_A (c : Ctx) (t : c.Coin) (u : List Bool) :
    u ∈ c.A t ↔ ∃ p', c.runFrom t [] u = some p' ∧ p' ∈ c.J := by
  simp only [A, Finset.mem_filter, mem_M]
  constructor
  · rintro ⟨_, h⟩
    cases hrun : c.runFrom t [] u with
    | none => simp [hrun] at h
    | some p' =>
      rw [hrun] at h
      exact ⟨p', rfl, by simpa using h⟩
  · rintro ⟨p', hrun, hJ⟩
    refine ⟨by simp [hrun], ?_⟩
    simpa [hrun] using hJ

lemma mem_M_sdiff_A (c : Ctx) (t : c.Coin) (u : List Bool) :
    u ∈ c.M t \ c.A t ↔ ∃ p', c.runFrom t [] u = some p' ∧ p' ∈ c.N \ c.J := by
  simp only [Finset.mem_sdiff, mem_M, mem_A]
  constructor
  · rintro ⟨hsome, hnotA⟩
    cases hrun : c.runFrom t [] u with
    | none => simp [hrun] at hsome
    | some p' =>
      refine ⟨p', rfl, ?_, ?_⟩
      · exact c.runFrom_mem t u [] p' c.hshape.1 hrun
      · intro hJ
        exact hnotA ⟨p', hrun, hJ⟩
  · rintro ⟨p', hrun, hp'⟩
    refine ⟨by simp [hrun], ?_⟩
    rintro ⟨p'', hrun2, hJ⟩
    rw [hrun] at hrun2
    cases hrun2
    exact hp'.2 hJ

lemma shape_MA (c : Ctx) (t : c.Coin) : shapeDef (c.M t) (c.A t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_M]
    simp [runFrom]
  · intro u hu
    rw [mem_A] at hu
    rw [mem_M]
    rcases hu with ⟨p', hrun, _⟩
    simp [hrun]
  · intro u b hub
    rw [mem_M] at hub
    rw [mem_A]
    rw [c.runFrom_append_singleton] at hub
    cases hrun : c.runFrom t [] u with
    | none => simp [hrun] at hub
    | some p' =>
      rw [hrun] at hub
      dsimp at hub
      split_ifs at hub with hJ
      · exact ⟨p', rfl, hJ⟩
      · simp at hub
  · intro u hu
    rw [mem_A] at hu
    rcases hu with ⟨p', hrun, hJ⟩
    constructor <;> rw [mem_M, c.runFrom_append_singleton, hrun] <;> simp [hJ]

noncomputable def q (c : Ctx) (t : c.Coin) (u : List Bool) : Fin c.n :=
  match c.runFrom t [] u with
  | some p' => (c.ask p').1
  | none => ⟨0, c.hn⟩

def Matches (c : Ctx) (t : c.Coin) (p : List Bool) : Prop :=
  ∀ s : Fin p.length,
    let q := p.take s.val
    let i := (c.ask q).1
    let k := (c.bank q).count i
    ∀ hk : k < c.w i - 1, t i ⟨k, hk⟩ = p.get s

lemma runFrom_partition (c : Ctx) (t : c.Coin) (p u r : List Bool)
    (hp : p ∈ c.N) (hrun : c.runFrom t p u = some r) :
    (∀ j : Fin u.length, ∃ pj, c.runFrom t p (u.take j.val) = some pj ∧ pj ∈ c.J ∧
      pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)] <+: r ∧
      (c.bank pj).count (c.ask pj).1 = c.w (c.ask pj).1 - 1) ∧
    (∀ s : Fin r.length, p.length ≤ s.val →
      (∃ j : Fin u.length, ∃ pj, c.runFrom t p (u.take j.val) = some pj ∧ s.val = pj.length) ∨
      (∃ hk : (c.bank (r.take s.val)).count (c.ask (r.take s.val)).1 <
          c.w (c.ask (r.take s.val)).1 - 1,
        r.get s = t (c.ask (r.take s.val)).1
          ⟨(c.bank (r.take s.val)).count (c.ask (r.take s.val)).1, hk⟩)) := by
  induction u generalizing p with
  | nil =>
    simp only [runFrom, Option.some.injEq] at hrun
    subst hrun
    refine ⟨fun j => Fin.elim0 j, ?_⟩
    intro s hs
    right
    have hsp := c.follow_step_spec t p s.val hs s.isLt
    simpa [List.get_eq_getElem] using hsp
  | cons b u' ih =>
    simp only [runFrom] at hrun
    split_ifs at hrun with hJ
    set p' := c.follow t p
    set p1 := p' ++ [xor b (c.bias t (c.ask p').1)]
    have hp1N : p1 ∈ c.N := by
      change p' ++ [xor b (c.bias t (c.ask p').1)] ∈ c.N
      cases xor b (c.bias t (c.ask p').1)
      · exact (c.hshape.2.2.2 p' hJ).1
      · exact (c.hshape.2.2.2 p' hJ).2
    obtain ⟨ih1, ih2⟩ := ih p1 hp1N hrun
    have hp1_pref : p1 <+: r := c.runFrom_prefix t u' p1 r hrun
    have hp'_pref : p' <+: r := List.IsPrefix.trans (List.prefix_append p' _) hp1_pref
    have hstop : (c.bank p').count (c.ask p').1 = c.w (c.ask p').1 - 1 :=
      c.follow_stop t p hp hJ
    constructor
    · intro j
      refine Fin.cases ?_ ?_ j
      · refine ⟨p', ?_, hJ, hp1_pref, hstop⟩
        simp [runFrom, p']
      · intro j'
        obtain ⟨pj, hrunj, hjJ, hjpref, hjstop⟩ := ih1 j'
        refine ⟨pj, ?_, hjJ, hjpref, hjstop⟩
        simpa [runFrom, p', p1, hJ] using hrunj
    · intro s hs
      by_cases hlt : s.val < p'.length
      · right
        have htake : r.take s.val = p'.take s.val := by
          obtain ⟨tl, htl⟩ := hp'_pref
          have h1 : (p' ++ tl).take s.val = p'.take s.val :=
            List.take_append_of_le_length (Nat.le_of_lt hlt)
          rwa [htl] at h1
        have hget : r.get s = p'[s.val] := by
          simpa [List.get_eq_getElem] using (hp'_pref.getElem hlt).symm
        obtain ⟨hk, heq⟩ := c.follow_step_spec t p s.val hs hlt
        refine ⟨by rw [htake]; exact hk, ?_⟩
        rw [hget, heq]
        exact c.coin_eq_of_eq t htake.symm hk _
      · by_cases heq : s.val = p'.length
        · left
          refine ⟨0, p', ?_, heq⟩
          simp [runFrom, p']
        · have hs1 : p1.length ≤ s.val := by
            simp only [p1, List.length_append, List.length_singleton]
            omega
          rcases ih2 s hs1 with ⟨j', pj, hrunj, hsj⟩ | hforced
          · left
            refine ⟨j'.succ, pj, ?_, hsj⟩
            simpa [runFrom, p', p1, hJ] using hrunj
          · exact Or.inr hforced

lemma runFrom_matches (c : Ctx) (t : c.Coin) {u r : List Bool}
    (hr : c.runFrom t [] u = some r) : c.Matches t r := by
  obtain ⟨hpart1, hpart2⟩ := c.runFrom_partition t [] u r c.hshape.1 hr
  intro s
  dsimp only
  intro hk
  rcases hpart2 s (Nat.zero_le _) with ⟨j, pj, hrunj, hsj⟩ | ⟨hk', heq⟩
  · obtain ⟨pj', hrunj', _, hpref, hstop⟩ := hpart1 j
    rw [hrunj] at hrunj'
    cases hrunj'
    have hpj_pref : pj <+: r := List.IsPrefix.trans (List.prefix_append pj _) hpref
    have htake : r.take s.val = pj := by
      rw [hsj]
      obtain ⟨tl, htl⟩ := hpj_pref
      have h1 : (pj ++ tl).take pj.length = pj := List.take_left
      rwa [htl] at h1
    rw [htake, hstop] at hk
    omega
  · exact heq.symm

lemma runFrom_inj (c : Ctx) (t : c.Coin) :
    ∀ (u₁ u₂ p r : List Bool), c.runFrom t p u₁ = some r → c.runFrom t p u₂ = some r → u₁ = u₂ := by
  intro u₁
  induction u₁ with
  | nil =>
    intro u₂ p r h1 h2
    simp only [runFrom, Option.some.injEq] at h1
    cases u₂ with
    | nil => rfl
    | cons b u₂' =>
      have hlen := c.runFrom_length t (b :: u₂') p r h2
      rw [← h1] at hlen
      simp at hlen
  | cons b₁ u₁' ih =>
    intro u₂ p r h1 h2
    cases u₂ with
    | nil =>
      simp only [runFrom, Option.some.injEq] at h2
      have hlen := c.runFrom_length t (b₁ :: u₁') p r h1
      rw [← h2] at hlen
      simp at hlen
    | cons b₂ u₂' =>
      simp only [runFrom] at h1 h2
      split_ifs at h1 with hJ
      split_ifs at h2
      set p' := c.follow t p
      have hp1 : p' ++ [xor b₁ (c.bias t (c.ask p').1)] <+: r := c.runFrom_prefix t u₁' _ r h1
      have hp2 : p' ++ [xor b₂ (c.bias t (c.ask p').1)] <+: r := c.runFrom_prefix t u₂' _ r h2
      have hlt1 : p'.length < (p' ++ [xor b₁ (c.bias t (c.ask p').1)]).length := by simp
      have hlt2 : p'.length < (p' ++ [xor b₂ (c.bias t (c.ask p').1)]).length := by simp
      have helem : xor b₁ (c.bias t (c.ask p').1) = xor b₂ (c.bias t (c.ask p').1) := by
        have e1 := hp1.getElem hlt1
        have e2 := hp2.getElem hlt2
        simp only [List.getElem_append_right (le_refl p'.length), Nat.sub_self,
          List.getElem_singleton] at e1 e2
        exact e1.trans e2.symm
      have hb : b₁ = b₂ := by
        cases b₁ <;> cases b₂ <;> cases c.bias t (c.ask p').1 <;> simp_all
      subst hb
      congr 1
      exact ih u₂' _ r h1 h2

lemma follow_prefix_of_matches (c : Ctx) (t : c.Coin) {p : List Bool}
    (hp : p ∈ c.N \ c.J) (hm : c.Matches t p) (p0 : List Bool) (hp0 : p0 <+: p) :
    c.follow t p0 <+: p := by
  have hfeq := c.follow_eq t p0
  split_ifs at hfeq with h
  · rw [hfeq]
    have hlt : p0.length < p.length := by
      by_contra hge
      have heq : p0 = p := by
        obtain ⟨tl, htl⟩ := hp0
        have htl0 : tl = [] := List.eq_nil_of_length_eq_zero (by
          have := congrArg List.length htl
          simp only [List.length_append] at this
          omega)
        rw [htl0, List.append_nil] at htl
        exact htl
      rw [heq] at h
      exact (Finset.mem_sdiff.mp hp).2 h.1
    have htake : p.take p0.length = p0 := by
      obtain ⟨tl, htl⟩ := hp0
      rw [← htl, List.take_left]
    have hmatch := hm ⟨p0.length, hlt⟩
    dsimp only at hmatch
    rw [htake] at hmatch
    have hbit := hmatch h.2.2
    have hnext_pref : p0 ++ [t (c.ask p0).1 ⟨(c.bank p0).count (c.ask p0).1, h.2.2⟩] <+: p := by
      rw [hbit]
      obtain ⟨tl, htl⟩ := hp0
      cases tl with
      | nil =>
        have := congrArg List.length htl
        simp at this
        omega
      | cons a tl' =>
        refine ⟨tl', ?_⟩
        have ha : p.get ⟨p0.length, hlt⟩ = a := by
          simp [List.get_eq_getElem, ← htl]
        rw [ha]
        simpa [List.append_assoc] using htl
    exact c.follow_prefix_of_matches t hp hm _ hnext_pref
  · rw [hfeq]
    exact hp0
termination_by c.H - p0.length
decreasing_by
  simp_wf
  have := h.2.1
  omega

lemma exists_u_of_matches_aux (c : Ctx) (t : c.Coin) {p : List Bool}
    (hp : p ∈ c.N \ c.J) (hm : c.Matches t p) (p0 : List Bool) (hp0 : p0 <+: p) :
    ∃ u, c.runFrom t p0 u = some p := by
  have hp' : c.follow t p0 <+: p := c.follow_prefix_of_matches t hp hm p0 hp0
  by_cases hlen : (c.follow t p0).length = p.length
  · refine ⟨[], ?_⟩
    simp only [runFrom, Option.some.injEq]
    obtain ⟨tl, htl⟩ := hp'
    have htl0 : tl = [] := List.eq_nil_of_length_eq_zero (by
      have := congrArg List.length htl
      simp only [List.length_append] at this
      omega)
    rw [htl0, List.append_nil] at htl
    exact htl
  · have hlt : (c.follow t p0).length < p.length :=
      lt_of_le_of_ne hp'.length_le hlen
    have hJ : c.follow t p0 ∈ c.J :=
      c.prefix_mem_J hp' hlt (Finset.mem_sdiff.mp hp).1
    set p' := c.follow t p0
    set b := xor (p.get ⟨p'.length, hlt⟩) (c.bias t (c.ask p').1)
    have hxor : xor b (c.bias t (c.ask p').1) = p.get ⟨p'.length, hlt⟩ := by
      dsimp only [b]
      cases p.get ⟨p'.length, hlt⟩ <;> cases c.bias t (c.ask p').1 <;> rfl
    have hp1_pref : p' ++ [xor b (c.bias t (c.ask p').1)] <+: p := by
      rw [hxor]
      obtain ⟨tl, htl⟩ := hp'
      cases tl with
      | nil =>
        have := congrArg List.length htl
        simp at this
        omega
      | cons a tl' =>
        refine ⟨tl', ?_⟩
        have ha : p.get ⟨p'.length, hlt⟩ = a := by
          simp [List.get_eq_getElem, ← htl]
        rw [ha]
        simpa [List.append_assoc] using htl
    have hp_dec : p.length - (p' ++ [xor b (c.bias t (c.ask p').1)]).length < p.length - p0.length := by
      have hp0_le : p0.length ≤ p'.length := (c.follow_prefix t p0).length_le
      simp only [List.length_append, List.length_singleton]
      omega
    obtain ⟨u', hu'⟩ := exists_u_of_matches_aux c t hp hm (p' ++ [xor b (c.bias t (c.ask p').1)]) hp1_pref
    refine ⟨b :: u', ?_⟩
    dsimp only [p'] at hu'
    rw [runFrom]
    split_ifs with h_if
    · exact hu'
    · exact absurd hJ h_if
termination_by p.length - p0.length
decreasing_by
  simp_wf
  have hdec := hp_dec
  simp only [p', List.length_append, List.length_singleton] at hdec
  exact hdec

lemma exists_u_of_matches (c : Ctx) (t : c.Coin) {p : List Bool}
    (hp : p ∈ c.N \ c.J) (hm : c.Matches t p) :
    ∃ u ∈ c.M t \ c.A t, c.runFrom t [] u = some p := by
  obtain ⟨u, hu⟩ := c.exists_u_of_matches_aux t hp hm [] (List.nil_prefix)
  refine ⟨u, ?_, hu⟩
  rw [mem_M_sdiff_A]
  exact ⟨p, hu, hp⟩

lemma trace_q_nodup_and_mem (c : Ctx) (t : c.Coin) {u r : List Bool}
    (hr : c.runFrom t [] u = some r) :
    (traceDef (c.q t) u).Nodup ∧
    ∀ i : Fin c.n, i ∈ traceDef (c.q t) u ↔ (c.bank r).count i = c.w i := by
  have hrN := c.runFrom_mem t u [] r c.hshape.1 hr
  obtain ⟨hpart1, hpart2⟩ := c.runFrom_partition t [] u r c.hshape.1 hr
  have hq_eq : ∀ j : Fin u.length, ∃ pj, c.runFrom t [] (u.take j.val) = some pj ∧
      c.q t (u.take j.val) = (c.ask pj).1 ∧
      pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)] <+: r ∧
      (c.bank pj).count (c.ask pj).1 = c.w (c.ask pj).1 - 1 := by
    intro j
    obtain ⟨pj, hrunj, _, hpref, hstop⟩ := hpart1 j
    refine ⟨pj, hrunj, ?_, hpref, hstop⟩
    simp [q, hrunj]
  have hpj_pref_step : ∀ {j₁ j₂ : Fin u.length}, j₁ < j₂ →
      ∀ {p₁ p₂}, c.runFrom t [] (u.take j₁.val) = some p₁ →
      c.runFrom t [] (u.take j₂.val) = some p₂ →
      p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)] <+: p₂ := by
    intro j₁ j₂ hlt p₁ p₂ h1 h2
    have hsplit : u.take j₂.val = u.take j₁.val ++ u.get j₁ :: ((u.take j₂.val).drop (j₁.val + 1)) := by
      have hd := List.take_append_drop (j₁.val + 1) (u.take j₂.val)
      rw [List.take_take, Nat.min_eq_left (by omega)] at hd
      have h1' : u.take (j₁.val + 1) = u.take j₁.val ++ [u.get j₁] := by
        simp [List.get_eq_getElem]
      rw [h1', List.append_assoc] at hd
      exact hd.symm
    rw [hsplit, c.runFrom_append_cons, h1] at h2
    dsimp only at h2
    split_ifs at h2 with hJ
    exact c.runFrom_prefix t _ _ p₂ h2
  have hnodup : (traceDef (c.q t) u).Nodup := by
    have haux : ∀ (j₁ j₂ : Fin u.length), j₁ < j₂ →
        c.q t (u.take j₁.val) = c.q t (u.take j₂.val) → False := by
      intro j₁ j₂ hlt heq
      obtain ⟨p₁, hrun1, hq1, _, hstop1⟩ := hq_eq j₁
      obtain ⟨p₂, hrun2, hq2, _, hstop2⟩ := hq_eq j₂
      have hpref := hpj_pref_step hlt hrun1 hrun2
      set i := c.q t (u.take j₁.val)
      have hi1 : (c.ask p₁).1 = i := hq1.symm
      have hi2 : (c.ask p₂).1 = i := hq2.symm.trans heq.symm
      have hpref_len : (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)]).length ≤ p₂.length := hpref.length_le
      have htake_p2 : p₂.take (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)]).length =
          p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)] := by
        obtain ⟨tl, htl⟩ := hpref
        rw [← htl, List.take_left]
      have hbank_pref : c.bank (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)]) <+: c.bank p₂ := by
        have hb1 : c.bank (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)]) =
            (c.bank p₂).take (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)]).length := by
          calc
            c.bank (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)])
                = c.bank (p₂.take (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)]).length) := by rw [htake_p2]
            _ = (c.bank p₂).take (p₁ ++ [xor (u.get j₁) (c.bias t (c.ask p₁).1)]).length :=
                c.bank_take p₂ _ hpref_len
        rw [hb1]
        exact List.take_prefix _ _
      obtain ⟨tl, htl⟩ := hbank_pref
      have hcnt : (c.bank p₂).count i = (c.bank p₁).count i + 1 + tl.count i := by
        rw [← htl, c.bank_append_singleton, List.count_append, List.count_append, hi1]
        simp
      rw [hi1] at hstop1
      rw [hi2] at hstop2
      omega
    unfold traceDef
    rw [List.nodup_ofFn]
    intro j₁ j₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact haux j₁ j₂ hlt heq
    · exact haux j₂ j₁ hlt heq.symm
  refine ⟨hnodup, ?_⟩
  intro i
  constructor
  · intro hi
    unfold traceDef at hi
    rw [List.mem_ofFn] at hi
    obtain ⟨j, hj⟩ := hi
    obtain ⟨pj, _, hq, hpref, hstop⟩ := hq_eq j
    have hpi : (c.ask pj).1 = i := hq.symm.trans hj
    have hpref_len : (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)]).length ≤ r.length := hpref.length_le
    have htake_r : r.take (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)]).length =
        pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)] := by
      obtain ⟨tl, htl⟩ := hpref
      rw [← htl, List.take_left]
    have hbank_pref : c.bank (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)]) <+: c.bank r := by
      have hb1 : c.bank (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)]) =
          (c.bank r).take (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)]).length := by
        calc
          c.bank (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)])
              = c.bank (r.take (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)]).length) := by rw [htake_r]
          _ = (c.bank r).take (pj ++ [xor (u.get j) (c.bias t (c.ask pj).1)]).length :=
              c.bank_take r _ hpref_len
      rw [hb1]
      exact List.take_prefix _ _
    obtain ⟨tl, htl⟩ := hbank_pref
    have hge : c.w i ≤ (c.bank r).count i := by
      rw [← htl, c.bank_append_singleton, List.count_append, List.count_append, hpi]
      rw [hpi] at hstop
      have hwi := c.hw i
      simp
      omega
    have hle := c.bank_count_le hrN i
    omega
  · intro hcnt
    have hwi := c.hw i
    have hlt : c.w i - 1 < (c.bank r).count i := by omega
    obtain ⟨s, hs_get, hs_cnt⟩ := list_exists_idx_of_count_lt (c.bank r) i (c.w i - 1) hlt
    have hs_lt : s.val < r.length := by
      have hbl := c.bank_length r
      have := s.isLt
      omega
    let s' : Fin r.length := ⟨s.val, hs_lt⟩
    have hs_ask : (c.ask (r.take s'.val)).1 = i := by
      rw [List.get_eq_getElem] at hs_get
      simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn] at hs_get
      exact hs_get
    have hs_bank : (c.bank (r.take s'.val)).count i = c.w i - 1 := by
      rw [c.bank_take r s'.val (Nat.le_of_lt hs_lt)]
      exact hs_cnt
    rcases hpart2 s' (Nat.zero_le _) with ⟨j, pj, hrunj, hsj⟩ | ⟨hk, _⟩
    · obtain ⟨pj', hrunj', _, hpref, _⟩ := hq_eq j
      rw [hrunj] at hrunj'
      cases hrunj'
      have hpj_pref : pj <+: r := List.IsPrefix.trans (List.prefix_append pj _) hpref
      have htake : r.take s'.val = pj := by
        have hval : s'.val = pj.length := hsj
        rw [hval]
        obtain ⟨tl, htl⟩ := hpj_pref
        rw [← htl, List.take_left]
      have hqi : c.q t (u.take j.val) = i := by
        simp only [q, hrunj]
        rw [← htake]
        exact hs_ask
      rw [← hqi]
      unfold traceDef
      rw [List.mem_ofFn]
      exact ⟨j, rfl⟩
    · rw [hs_ask, hs_bank] at hk
      omega

instance (c : Ctx) : Fintype c.Coin :=
  inferInstanceAs (Fintype ((i : Fin c.n) → Fin (c.w i - 1) → Bool))

instance (c : Ctx) : DecidableEq c.Coin :=
  inferInstanceAs (DecidableEq ((i : Fin c.n) → Fin (c.w i - 1) → Bool))

instance (c : Ctx) : Nonempty c.Coin := ⟨fun _ _ => false⟩

lemma list_nodup_map_sum {α : Type} [DecidableEq α] (L : List α) (hL : L.Nodup) (f : α → ℕ) :
    (L.map f).sum = ∑ a ∈ L.toFinset, f a := by
  induction L with
  | nil => simp
  | cons x tl ih =>
    rw [List.nodup_cons] at hL
    have hx : x ∉ tl.toFinset := by simp [hL.1]
    simp [List.toFinset_cons, Finset.sum_insert hx, ih hL.2]

lemma list_count_eq_card_filter {α : Type} [DecidableEq α] (L : List α) (a : α) :
    L.count a = (Finset.univ.filter (fun s : Fin L.length => L.get s = a)).card := by
  induction L with
  | nil => simp
  | cons x tl ih =>
    rw [List.count_cons, ih]
    have hsplit : (Finset.univ.filter (fun s : Fin (x :: tl).length => (x :: tl).get s = a)).card =
        (if x = a then 1 else 0) +
        (Finset.univ.filter (fun s : Fin tl.length => tl.get s = a)).card := by
      have hmap : Finset.univ.filter (fun s : Fin (x :: tl).length => (x :: tl).get s = a) =
          (if x = a then {(0 : Fin (x :: tl).length)} else ∅) ∪
          (Finset.univ.filter (fun s : Fin tl.length => tl.get s = a)).image Fin.succ := by
        ext s
        refine Fin.cases ?_ ?_ s
        · by_cases hxa : x = a <;> simp [hxa, Fin.succ_ne_zero]
        · intro s'
          by_cases hxa : x = a <;> simp [hxa, Fin.succ_inj]
      rw [hmap, Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ (@Fin.succ_injective tl.length)]
        split_ifs <;> simp
      · split_ifs
        · simp [Fin.succ_ne_zero]
        · simp
    rw [hsplit]
    by_cases hxa : x = a
    · simp [hxa, add_comm]
    · have hb : (x == a) = false := beq_false_of_ne hxa
      simp [hxa, hb]

lemma card_fin_filter_lt (M K : ℕ) :
    (Finset.univ.filter (fun k : Fin M => k.val < K)).card = min K M := by
  have himg : (Finset.univ.filter (fun k : Fin M => k.val < K)).image Fin.val =
      Finset.range (min K M) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact lt_min hk k.isLt
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le hx (min_le_right _ _)⟩, lt_of_lt_of_le hx (min_le_left _ _), rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

noncomputable def out (c : Ctx) {m : ℕ} (ans : List Bool → Fin m) (t : c.Coin) (u : List Bool) : Fin m :=
  match c.runFrom t [] u with
  | some p' => ans p'
  | none => ans []

def satCount (c : Ctx) (r : List Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin c.n => (c.bank r).count i = c.w i)).card

def sumW (c : Ctx) (r : List Bool) : ℕ :=
  ∑ i : Fin c.n, if (c.bank r).count i = c.w i then c.w i else 0

lemma sum_w_add_waste (c : Ctx) (t : c.Coin) {u r : List Bool}
    (hr : c.runFrom t [] u = some r) :
    ((traceDef (c.q t) u).map c.w).sum = c.sumW r ∧
    u.length = c.satCount r ∧
    c.sumW r + wasteDef c.w c.ask r = r.length ∧
    ((traceDef (c.q t) u).map c.w).sum ≤ c.H ∧
    u.length ≤ c.sumW r := by
  have hrN := c.runFrom_mem t u [] r c.hshape.1 hr
  obtain ⟨hnodup, hmem⟩ := c.trace_q_nodup_and_mem t hr
  have htofinset : (traceDef (c.q t) u).toFinset =
      Finset.univ.filter (fun i => (c.bank r).count i = c.w i) := by
    ext i
    simp [hmem i]
  have hsum_eq : ((traceDef (c.q t) u).map c.w).sum = c.sumW r := by
    rw [list_nodup_map_sum _ hnodup c.w, htofinset, sumW, Finset.sum_filter]
  have hulen : u.length = c.satCount r := by
    have h1 : (traceDef (c.q t) u).length = u.length := by simp [traceDef]
    rw [← h1, ← List.toFinset_card_of_nodup hnodup, htofinset, satCount]
  have hsum_waste : c.sumW r + wasteDef c.w c.ask r = r.length := by
    have hlen : r.length = ∑ i : Fin c.n, (c.bank r).count i := by
      rw [← c.bank_length r, list_length_eq_sum_count]
    rw [hlen, sumW, wasteDef, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hle := c.bank_count_le hrN i
    change (if (c.bank r).count i = c.w i then c.w i else 0) +
      (if (c.bank r).count i < c.w i then (c.bank r).count i else 0) = (c.bank r).count i
    split_ifs <;> omega
  have hH : ((traceDef (c.q t) u).map c.w).sum ≤ c.H := by
    rw [hsum_eq]
    have hrH := (c.hN r hrN).2
    omega
  have hle_sum : u.length ≤ c.sumW r := by
    rw [← hsum_eq, list_nodup_map_sum _ hnodup c.w]
    have h1 : u.length = ∑ _i ∈ (traceDef (c.q t) u).toFinset, 1 := by
      have htr : (traceDef (c.q t) u).length = u.length := by simp [traceDef]
      rw [← htr, ← List.toFinset_card_of_nodup hnodup]
      simp
    rw [h1]
    exact Finset.sum_le_sum (fun i _ => c.hw i)
  exact ⟨hsum_eq, hulen, hsum_waste, hH, hle_sum⟩

lemma exists_y_of_consistent (c : Ctx) {m : ℕ} (R : (Fin c.n → Bool) → Fin m → Prop)
    (ans : List Bool → Fin m)
    (hR : ∀ p ∈ c.N \ c.J, ∀ y, consistentDef c.ask p y → R (parityDef c.w y) (ans p))
    (t : c.Coin) {u : List Bool} (hu : u ∈ c.M t \ c.A t)
    {x : Fin c.n → Bool} (hx : consistentDef (c.q t) u x) :
    R x (c.out ans t u) := by
  rw [mem_M_sdiff_A] at hu
  rcases hu with ⟨r, hr, hrNJ⟩
  have hrN : r ∈ c.N := (Finset.mem_sdiff.mp hrNJ).1
  have hout : c.out ans t u = ans r := by simp [out, hr]
  rw [hout]
  have hnodup_r : (traceDef c.ask r).Nodup := (c.hN r hrN).1
  let y0 : ((i : Fin c.n) × Fin (c.w i)) → Bool :=
    fun v => if h : ∃ s : Fin r.length, c.ask (r.take s.val) = v then r.get (Classical.choose h) else false
  have hy0_trace : ∀ s : Fin r.length, y0 (c.ask (r.take s.val)) = r.get s := by
    intro s
    have hex : ∃ s' : Fin r.length, c.ask (r.take s'.val) = c.ask (r.take s.val) := ⟨s, rfl⟩
    simp only [y0, hex, ↓reduceDIte]
    have hspec := Classical.choose_spec hex
    have hinj := (List.nodup_iff_injective_get.mp hnodup_r)
    have hlen_tr : (traceDef c.ask r).length = r.length := by simp [traceDef]
    let s1 : Fin (traceDef c.ask r).length := ⟨(Classical.choose hex).val, by rw [hlen_tr]; exact (Classical.choose hex).isLt⟩
    let s2 : Fin (traceDef c.ask r).length := ⟨s.val, by rw [hlen_tr]; exact s.isLt⟩
    have hget_eq : (traceDef c.ask r).get s1 = (traceDef c.ask r).get s2 := by
      simpa [traceDef, s1, s2] using hspec
    have hs_eq : Classical.choose hex = s := by
      have := congrArg Fin.val (hinj hget_eq)
      exact Fin.ext (by simpa [s1, s2] using this)
    rw [hs_eq]
  have h_ask_y0 : ∀ s : Fin r.length, y0 (c.ask (r.take s.val)) = r.get s := hy0_trace
  have hmiss_ex : ∀ i : Fin c.n, (c.bank r).count i < c.w i →
      ∃ j0 : Fin (c.w i), ¬ ∃ s : Fin r.length, c.ask (r.take s.val) = ⟨i, j0⟩ := by
    intro i hlt
    let Si : Finset (Fin r.length) := Finset.univ.filter (fun s => (c.ask (r.take s.val)).1 = i)
    let fj : Fin r.length → Fin (c.w i) :=
      fun s => if h : (c.ask (r.take s.val)).1 = i then cast (by rw [h]) (c.ask (r.take s.val)).2 else ⟨0, c.hw i⟩
    have hSi_card : Si.card = (c.bank r).count i := by
      rw [list_count_eq_card_filter (c.bank r) i]
      refine Finset.card_bij (fun s _ => ⟨s.val, by have hbl := c.bank_length r; have := s.isLt; omega⟩) ?_ ?_ ?_
      · intro s hs
        simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        rw [List.get_eq_getElem]
        simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn]
        exact hs
      · intro s₁ _ s₂ _ h
        exact Fin.ext (Fin.mk.inj h)
      · intro s hs
        refine ⟨⟨s.val, by have hbl := c.bank_length r; have := s.isLt; omega⟩, ?_, Fin.ext rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
        rw [List.get_eq_getElem] at hs
        simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn] at hs
        simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hs
    have hcard_lt : (Si.image fj).card < (Finset.univ : Finset (Fin (c.w i))).card := by
      have h1 : (Si.image fj).card ≤ Si.card := Finset.card_image_le
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    have hsub : ∃ j0 ∈ (Finset.univ : Finset (Fin (c.w i))), j0 ∉ Si.image fj :=
      Finset.exists_mem_notMem_of_card_lt_card hcard_lt
    rcases hsub with ⟨j0, _, hj0⟩
    refine ⟨j0, ?_⟩
    rintro ⟨s, hs⟩
    apply hj0
    rw [Finset.mem_image]
    refine ⟨s, ?_, ?_⟩
    · simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hs]
    · have hfj_val : ∀ (v : (a : Fin c.n) × Fin (c.w a)) (_hv : v = ⟨i, j0⟩),
          (if h : v.1 = i then cast (by rw [h]) v.2 else ⟨0, c.hw i⟩) = j0 := by
        rintro _ rfl
        simp
      exact hfj_val _ hs
  let miss (i : Fin c.n) (h : (c.bank r).count i < c.w i) : Fin (c.w i) :=
    Classical.choose (hmiss_ex i h)
  let y : ((i : Fin c.n) × Fin (c.w i)) → Bool := fun v =>
    if h : (c.bank r).count v.1 < c.w v.1 then
      if parityDef c.w y0 v.1 = x v.1 then y0 v
      else if v.2 = miss v.1 h then !(y0 ⟨v.1, miss v.1 h⟩) else y0 v
    else y0 v
  have hy_cons : consistentDef c.ask r y := by
    intro s
    have hs_y0 := h_ask_y0 s
    change y (c.ask (r.take s.val)) = r.get s
    dsimp only [y]
    split_ifs with h1 h2 h3
    · exact hs_y0
    · exfalso
      have hspec := Classical.choose_spec (hmiss_ex (c.ask (r.take s.val)).1 h1)
      apply hspec
      refine ⟨s, Sigma.ext rfl (heq_of_eq h3)⟩
    · exact hs_y0
    · exact hs_y0
  have hy_par : parityDef c.w y = x := by
    ext i
    by_cases hlt : (c.bank r).count i < c.w i
    · by_cases hpar : parityDef c.w y0 i = x i
      · have hy_eq : ∀ j : Fin (c.w i), y ⟨i, j⟩ = y0 ⟨i, j⟩ := by
          intro j
          simp [y, hlt, hpar]
        simp only [parityDef, hy_eq]
        exact hpar
      · have hy_eq : ∀ j : Fin (c.w i), y ⟨i, j⟩ =
            if j = miss i hlt then !(y0 ⟨i, miss i hlt⟩) else y0 ⟨i, j⟩ := by
          intro j
          simp [y, hlt, hpar]
        have hflip := decide_odd_flip_coord (fun j : Fin (c.w i) => y0 ⟨i, j⟩) (miss i hlt)
        have hpar_y : parityDef c.w y i = !(parityDef c.w y0 i) := by
          simp only [parityDef, hy_eq]
          exact hflip
        rw [hpar_y]
        cases h0 : parityDef c.w y0 i <;> cases h1 : x i <;> simp_all
    · have hle := c.bank_count_le hrN i
      have hcnt : (c.bank r).count i = c.w i := by omega
      have hy_eq : ∀ j : Fin (c.w i), y ⟨i, j⟩ = y0 ⟨i, j⟩ := by
        intro j
        simp [y, hlt]
      simp only [parityDef, hy_eq]
      have hi_mem : i ∈ traceDef (c.q t) u := (c.trace_q_nodup_and_mem t hr).2 i |>.mpr hcnt
      unfold traceDef at hi_mem
      rw [List.mem_ofFn] at hi_mem
      rcases hi_mem with ⟨j0, hj0⟩
      obtain ⟨hpart1, _⟩ := c.runFrom_partition t [] u r c.hshape.1 hr
      obtain ⟨pj, hrunj, _, hpref, hstop⟩ := hpart1 j0
      have hqj0 : c.q t (u.take j0.val) = (c.ask pj).1 := by simp [q, hrunj]
      have hpi : (c.ask pj).1 = i := hqj0.symm.trans hj0
      have hpj_pref : pj <+: r := List.IsPrefix.trans (List.prefix_append pj _) hpref
      have hpj_lt : pj.length < r.length := by
        have := hpref.length_le
        simp only [List.length_append, List.length_singleton] at this
        omega
      let s_last : Fin r.length := ⟨pj.length, hpj_lt⟩
      have htake_last : r.take s_last.val = pj := by
        change r.take pj.length = pj
        obtain ⟨tl, htl⟩ := hpj_pref
        rw [← htl, List.take_left]
      have hget_last : r.get s_last = xor (x i) (c.bias t i) := by
        have hlen1 : pj.length < (pj ++ [xor (u.get j0) (c.bias t (c.ask pj).1)]).length := by simp
        have helem := hpref.getElem hlen1
        simp only [List.getElem_append_right (le_refl pj.length), Nat.sub_self,
          List.getElem_singleton] at helem
        have hux : u[j0.val] = x i := by
          rw [← hj0, ← List.get_eq_getElem]
          exact (hx j0).symm
        rw [List.get_eq_getElem]
        simpa [s_last, hpi, hux] using helem.symm
      let Si : Finset (Fin r.length) := Finset.univ.filter (fun s => (c.ask (r.take s.val)).1 = i)
      let fj : Fin r.length → Fin (c.w i) :=
        fun s => if h : (c.ask (r.take s.val)).1 = i then cast (by rw [h]) (c.ask (r.take s.val)).2 else ⟨0, c.hw i⟩
      have hfj_eq : ∀ s ∈ Si, (⟨i, fj s⟩ : (a : Fin c.n) × Fin (c.w a)) = c.ask (r.take s.val) := by
        intro s hs
        simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        have hpair : ∀ (v : (a : Fin c.n) × Fin (c.w a)) (_hv : v.1 = i),
            (⟨i, if h : v.1 = i then cast (by rw [h]) v.2 else ⟨0, c.hw i⟩⟩ :
              (a : Fin c.n) × Fin (c.w a)) = v := by
          rintro ⟨a, b⟩ rfl
          simp
        exact hpair _ hs
      have hfj_inj : Set.InjOn fj ↑Si := by
        intro s₁ hs₁ s₂ hs₂ hfeq
        have heq_ask : c.ask (r.take s₁.val) = c.ask (r.take s₂.val) := by
          rw [← hfj_eq s₁ hs₁, ← hfj_eq s₂ hs₂, hfeq]
        have hinj := (List.nodup_iff_injective_get.mp hnodup_r)
        have hlen_tr : (traceDef c.ask r).length = r.length := by simp [traceDef]
        let a₁ : Fin (traceDef c.ask r).length := ⟨s₁.val, by rw [hlen_tr]; exact s₁.isLt⟩
        let a₂ : Fin (traceDef c.ask r).length := ⟨s₂.val, by rw [hlen_tr]; exact s₂.isLt⟩
        have hget_eq : (traceDef c.ask r).get a₁ = (traceDef c.ask r).get a₂ := by
          simpa [traceDef, a₁, a₂] using heq_ask
        exact Fin.ext (by simpa [a₁, a₂] using congrArg Fin.val (hinj hget_eq))
      have hSi_card : Si.card = c.w i := by
        rw [← hcnt, list_count_eq_card_filter (c.bank r) i]
        refine Finset.card_bij (fun s _ => ⟨s.val, by have hbl := c.bank_length r; have := s.isLt; omega⟩) ?_ ?_ ?_
        · intro s hs
          simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
          rw [List.get_eq_getElem]
          simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn]
          exact hs
        · intro s₁ _ s₂ _ h
          exact Fin.ext (Fin.mk.inj h)
        · intro s hs
          refine ⟨⟨s.val, by have hbl := c.bank_length r; have := s.isLt; omega⟩, ?_, Fin.ext rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
          rw [List.get_eq_getElem] at hs
          simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn] at hs
          simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hs
      have hSi_img : Si.image fj = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [Finset.card_image_of_injOn hfj_inj, hSi_card, Fintype.card_fin]
      have hcard_y0 : ((Finset.univ : Finset (Fin (c.w i))).filter (fun j => y0 ⟨i, j⟩ = true)).card =
          (Si.filter (fun s => r.get s = true)).card := by
        have himg_filt : (Finset.univ : Finset (Fin (c.w i))).filter (fun j => y0 ⟨i, j⟩ = true) =
            (Si.filter (fun s => r.get s = true)).image fj := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hj
            have hj_mem : j ∈ Si.image fj := by rw [hSi_img]; exact Finset.mem_univ j
            rw [Finset.mem_image] at hj_mem
            rcases hj_mem with ⟨s, hs, rfl⟩
            refine ⟨s, ⟨hs, ?_⟩, rfl⟩
            rw [← hy0_trace s, ← hfj_eq s hs]
            exact hj
          · rintro ⟨s, ⟨hs, hget⟩, rfl⟩
            rw [hfj_eq s hs, hy0_trace s]
            exact hget
        rw [himg_filt]
        exact Finset.card_image_of_injOn (hfj_inj.mono (Finset.filter_subset _ _))
      have hslast_mem : s_last ∈ Si := by
        simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and, htake_last, hpi]
      have hsplit_Si : (Si.filter (fun s => r.get s = true)).card =
          ((Si.erase s_last).filter (fun s => r.get s = true)).card +
          (if r.get s_last = true then 1 else 0) := by
        have h1 : Si.filter (fun s => r.get s = true) =
            (if r.get s_last = true then {s_last} else ∅) ∪
            ((Si.erase s_last).filter (fun s => r.get s = true)) := by
          ext s
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_erase]
          by_cases hss : s = s_last
          · subst hss
            by_cases hr1 : r[s_last.val] = true <;> simp [hslast_mem, hr1, List.get_eq_getElem]
          · by_cases hr1 : r[s_last.val] = true <;> simp [hss, hr1, List.get_eq_getElem]
        rw [h1, Finset.card_union_of_disjoint]
        · split_ifs <;> simp [add_comm]
        · split_ifs
          · simp
          · simp
      have hcard_erase : ((Si.erase s_last).filter (fun s => r.get s = true)).card =
          ((Finset.univ : Finset (Fin (c.w i - 1))).filter (fun k => t i k = true)).card := by
        by_cases hw1 : c.w i = 1
        · have hcard0 : (Si.erase s_last).card = 0 := by
            rw [Finset.card_erase_of_mem hslast_mem, hSi_card, hw1]
          have hempty : Si.erase s_last = ∅ := Finset.card_eq_zero.mp hcard0
          have hfin0 : (Finset.univ : Finset (Fin (c.w i - 1))) = ∅ := by
            apply Finset.card_eq_zero.mp
            rw [Finset.card_univ, Fintype.card_fin, hw1]
          simp [hempty, hfin0]
        · have hw_gt : 1 < c.w i := by have := c.hw i; omega
          have hbank_get : ∀ s ∈ Si, (c.bank r).get ⟨s.val, by simp [c.bank_length]⟩ = i := by
            intro s hs
            simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hs
            rw [List.get_eq_getElem]
            simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn]
            exact hs
          have hs_lt_last : ∀ s ∈ Si.erase s_last, s < s_last := by
            intro s hs
            rw [Finset.mem_erase] at hs
            rcases lt_trichotomy s s_last with h1 | h2 | h3
            · exact h1
            · exact absurd h2 hs.1
            · exfalso
              have hmono := list_count_take_strict_mono (c.bank r) i h3
                (hbank_get s_last hslast_mem) (hbank_get s hs.2)
              have hlt_tot := list_count_take_lt_of_get_eq (c.bank r) i
                ⟨s.val, by simp [c.bank_length]⟩ (hbank_get s hs.2)
              have hlast_cnt : ((c.bank r).take s_last.val).count i = c.w i - 1 := by
                rw [← c.bank_take r s_last.val (Nat.le_of_lt s_last.isLt), htake_last]
                rw [hpi] at hstop
                exact hstop
              dsimp at hmono hlt_tot
              omega
          have hs_cnt_lt : ∀ s ∈ Si.erase s_last, (c.bank (r.take s.val)).count i < c.w i - 1 := by
            intro s hs
            have hlt := hs_lt_last s hs
            have hmono := list_count_take_strict_mono (c.bank r) i hlt
              (hbank_get s (Finset.mem_of_mem_erase hs)) (hbank_get s_last hslast_mem)
            have hlast_cnt : ((c.bank r).take s_last.val).count i = c.w i - 1 := by
              rw [← c.bank_take r s_last.val (Nat.le_of_lt s_last.isLt), htake_last]
              rw [hpi] at hstop
              exact hstop
            rw [← c.bank_take r s.val (Nat.le_of_lt s.isLt)] at hmono
            dsimp at hmono
            omega
          let fk : Fin r.length → Fin (c.w i - 1) := fun s =>
            if h : (c.bank (r.take s.val)).count i < c.w i - 1 then
              ⟨(c.bank (r.take s.val)).count i, h⟩
            else ⟨0, by omega⟩
          have hfk_inj : Set.InjOn fk ↑(Si.erase s_last) := by
            intro s₁ hs₁ s₂ hs₂ hfeq
            have h1 := hs_cnt_lt s₁ hs₁
            have h2 := hs_cnt_lt s₂ hs₂
            have hval : (c.bank (r.take s₁.val)).count i = (c.bank (r.take s₂.val)).count i := by
              have := congrArg Fin.val hfeq
              simpa [fk, h1, h2] using this
            rcases lt_trichotomy s₁ s₂ with hlt | heq | hgt
            · exfalso
              have hmono := list_count_take_strict_mono (c.bank r) i hlt
                (hbank_get s₁ (Finset.mem_of_mem_erase hs₁))
                (hbank_get s₂ (Finset.mem_of_mem_erase hs₂))
              rw [← c.bank_take r s₁.val (Nat.le_of_lt s₁.isLt),
                ← c.bank_take r s₂.val (Nat.le_of_lt s₂.isLt)] at hmono
              omega
            · exact heq
            · exfalso
              have hmono := list_count_take_strict_mono (c.bank r) i hgt
                (hbank_get s₂ (Finset.mem_of_mem_erase hs₂))
                (hbank_get s₁ (Finset.mem_of_mem_erase hs₁))
              rw [← c.bank_take r s₁.val (Nat.le_of_lt s₁.isLt),
                ← c.bank_take r s₂.val (Nat.le_of_lt s₂.isLt)] at hmono
              omega
          have h_erase_card : (Si.erase s_last).card = c.w i - 1 := by
            rw [Finset.card_erase_of_mem hslast_mem, hSi_card]
          have h_erase_img : (Si.erase s_last).image fk = Finset.univ := by
            apply Finset.eq_univ_of_card
            rw [Finset.card_image_of_injOn hfk_inj, h_erase_card, Fintype.card_fin]
          have hmatches := c.runFrom_matches t hr
          have hget_match : ∀ s ∈ Si.erase s_last, r.get s = t i (fk s) := by
            intro s hs
            have hcnt_lt := hs_cnt_lt s hs
            have hs_ask : (c.ask (r.take s.val)).1 = i := by
              have hm := Finset.mem_of_mem_erase hs
              simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hm
              exact hm
            have hm_s := hmatches s
            dsimp only at hm_s
            have hcnt_lt' : (c.bank (r.take s.val)).count (c.ask (r.take s.val)).1 <
                c.w (c.ask (r.take s.val)).1 - 1 := by
              rw [hs_ask]
              exact hcnt_lt
            have hbit := hm_s hcnt_lt'
            rw [← hbit]
            simp only [fk, hcnt_lt, ↓reduceDIte]
            have hcongr : ∀ (a : Fin c.n) (ha : a = i) (k1 k2 : ℕ)
                (hk1 : k1 < c.w a - 1) (hk2 : k2 < c.w i - 1) (_hk : k1 = k2),
                t a ⟨k1, hk1⟩ = t i ⟨k2, hk2⟩ := by
              rintro _ rfl _ _ _ _ rfl
              rfl
            exact hcongr _ hs_ask _ _ hcnt_lt' hcnt_lt (by rw [hs_ask])
          have himg_filt : (Finset.univ : Finset (Fin (c.w i - 1))).filter (fun k => t i k = true) =
              ((Si.erase s_last).filter (fun s => r.get s = true)).image fk := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
            constructor
            · intro hk
              have hk_mem : k ∈ (Si.erase s_last).image fk := by
                rw [h_erase_img]; exact Finset.mem_univ k
              rw [Finset.mem_image] at hk_mem
              rcases hk_mem with ⟨s, hs, rfl⟩
              refine ⟨s, ⟨hs, ?_⟩, rfl⟩
              rw [hget_match s hs]
              exact hk
            · rintro ⟨s, ⟨hs, hget⟩, rfl⟩
              rw [← hget_match s hs]
              exact hget
          rw [himg_filt]
          exact (Finset.card_image_of_injOn (hfk_inj.mono (Finset.filter_subset _ _))).symm
      rw [hcard_y0, hsplit_Si, hcard_erase, hget_last]
      rw [decide_odd_add_ite_bool]
      change xor (c.bias t i) (xor (x i) (c.bias t i)) = x i
      cases x i <;> cases c.bias t i <;> rfl
  exact hR r hrNJ y hy_cons |> fun h => by rwa [hy_par] at h

def coinEquiv (c : Ctx) : c.Coin ≃ (((i : Fin c.n) × Fin (c.w i - 1)) → Bool) where
  toFun t x := t x.1 x.2
  invFun f i k := f ⟨i, k⟩
  left_inv _ := rfl
  right_inv _ := rfl

def restrictEquiv {U : Type} [DecidableEq U] (S : Finset U) (g : U → Bool) :
    {f : U → Bool // ∀ x ∈ S, f x = g x} ≃ ({x : U // x ∉ S} → Bool) where
  toFun f x := f.1 x.1
  invFun h := ⟨fun u => if hu : u ∈ S then g u else h ⟨u, hu⟩, fun u hu => by simp [hu]⟩
  left_inv f := by
    ext u
    by_cases hu : u ∈ S
    · simp [hu, f.2 u hu]
    · simp [hu]
  right_inv h := by
    ext ⟨u, hu⟩
    simp [hu]

lemma card_coin (c : Ctx) :
    Fintype.card c.Coin = 2 ^ ((∑ i : Fin c.n, c.w i) - c.n) := by
  rw [Fintype.card_congr c.coinEquiv, Fintype.card_fun, Fintype.card_bool, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  congr 1
  have hsum : (∑ i : Fin c.n, (c.w i - 1)) + c.n = ∑ i : Fin c.n, c.w i := by
    have h1 : (∑ i : Fin c.n, (c.w i - 1)) + ∑ _i : Fin c.n, 1 = ∑ i : Fin c.n, c.w i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      have := c.hw i
      omega
    simpa using h1
  omega

lemma card_matches (c : Ctx) {r : List Bool} (hr : r ∈ c.N) :
    (Finset.univ.filter (fun t : c.Coin => c.Matches t r)).card =
      2 ^ (((∑ i : Fin c.n, c.w i) - c.n) - (r.length - c.satCount r)) ∧
    r.length - c.satCount r ≤ (∑ i : Fin c.n, c.w i) - c.n := by
  let U := (i : Fin c.n) × Fin (c.w i - 1)
  let Fixed : Finset U := Finset.univ.filter (fun x => x.2.val < (c.bank r).count x.1)
  have hex_s : ∀ x : U, x ∈ Fixed →
      ∃ s : Fin (c.bank r).length, (c.bank r).get s = x.1 ∧ ((c.bank r).take s.val).count x.1 = x.2.val := by
    intro x hx
    simp only [Fixed, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact list_exists_idx_of_count_lt (c.bank r) x.1 x.2.val hx
  let bitOf : U → Bool := fun x =>
    if h : x ∈ Fixed then
      let s := Classical.choose (hex_s x h)
      r.get ⟨s.val, by rw [← c.bank_length r]; exact s.isLt⟩
    else false
  have hmatches_iff : ∀ t : c.Coin, c.Matches t r ↔ ∀ x ∈ Fixed, (c.coinEquiv t) x = bitOf x := by
    intro t
    constructor
    · intro hm x hx
      simp only [bitOf, hx, ↓reduceDIte]
      set s := Classical.choose (hex_s x hx)
      have hs_spec := Classical.choose_spec (hex_s x hx)
      have hs_lt : s.val < r.length := by have := s.isLt; simp [c.bank_length] at this; exact this
      let s' : Fin r.length := ⟨s.val, hs_lt⟩
      have hm_s := hm s'
      dsimp only at hm_s
      have h_ask : (c.ask (r.take s'.val)).1 = x.1 := by
        have hg := hs_spec.1
        rw [List.get_eq_getElem] at hg
        simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn] at hg
        exact hg
      have h_cnt : (c.bank (r.take s'.val)).count (c.ask (r.take s'.val)).1 = x.2.val := by
        rw [h_ask, c.bank_take r s'.val (Nat.le_of_lt hs_lt)]
        exact hs_spec.2
      have h_lt_w : (c.bank (r.take s'.val)).count (c.ask (r.take s'.val)).1 <
          c.w (c.ask (r.take s'.val)).1 - 1 := by
        rw [h_cnt, h_ask]
        exact x.2.isLt
      have hbit := hm_s h_lt_w
      simp only [coinEquiv]
      rw [← hbit]
      have hpair : ∀ (a : Fin c.n) (_ha : a = x.1) (k1 : ℕ) (hk1 : k1 < c.w a - 1)
          (_hk : k1 = x.2.val), t a ⟨k1, hk1⟩ = t x.1 x.2 := by
        rintro _ rfl _ _ hk
        congr 1
        exact Fin.ext hk
      exact (hpair _ h_ask _ h_lt_w h_cnt).symm
    · intro hfix s
      dsimp only
      intro hk
      set i := (c.ask (r.take s.val)).1
      set k := (c.bank (r.take s.val)).count i
      have hs_lt : s.val < (c.bank r).length := by rw [c.bank_length r]; exact s.isLt
      let sb : Fin (c.bank r).length := ⟨s.val, hs_lt⟩
      have hsb_get : (c.bank r).get sb = i := by
        rw [List.get_eq_getElem]
        simp only [bank, traceDef, List.getElem_map, List.getElem_ofFn]
        rfl
      have hsb_cnt : ((c.bank r).take sb.val).count i = k := by
        rw [← c.bank_take r s.val (Nat.le_of_lt s.isLt)]
      have hlt_cnt : k < (c.bank r).count i := by
        rw [← hsb_cnt]
        exact list_count_take_lt_of_get_eq (c.bank r) i sb hsb_get
      let x : U := ⟨i, ⟨k, hk⟩⟩
      have hx_mem : x ∈ Fixed := by
        simp only [Fixed, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlt_cnt
      have hx_eq := hfix x hx_mem
      simp only [coinEquiv, bitOf, hx_mem, ↓reduceDIte] at hx_eq
      set s2 := Classical.choose (hex_s x hx_mem)
      have hs2_spec := Classical.choose_spec (hex_s x hx_mem)
      have hs2_eq : s2.val = sb.val := by
        rcases lt_trichotomy s2 sb with h1 | h2 | h3
        · exfalso
          have hmono := list_count_take_strict_mono (c.bank r) i h1 hs2_spec.1 hsb_get
          have hspec2 := hs2_spec.2
          dsimp [x] at hspec2
          rw [hspec2, hsb_cnt] at hmono
          omega
        · exact congrArg Fin.val h2
        · exfalso
          have hmono := list_count_take_strict_mono (c.bank r) i h3 hsb_get hs2_spec.1
          have hspec2 := hs2_spec.2
          dsimp [x] at hspec2
          rw [hspec2, hsb_cnt] at hmono
          omega
      have hr_eq : r.get ⟨s2.val, by rw [← c.bank_length r]; exact s2.isLt⟩ = r.get s := by
        congr 1
        exact Fin.ext hs2_eq
      rw [← hr_eq]
      exact hx_eq
  have hFixed_eq : Fixed = (Finset.univ : Finset (Fin c.n)).sigma
      (fun i => Finset.univ.filter (fun k : Fin (c.w i - 1) => k.val < (c.bank r).count i)) := by
    ext ⟨i, k⟩
    dsimp only [Fixed]
    rw [Finset.mem_filter, Finset.mem_sigma]
    simp
  have hFixed_card : Fixed.card = ∑ i : Fin c.n, min ((c.bank r).count i) (c.w i - 1) := by
    rw [hFixed_eq, Finset.card_sigma]
    refine Finset.sum_congr rfl ?_
    intro i _
    exact card_fin_filter_lt (c.w i - 1) ((c.bank r).count i)
  have hFixed_sat : Fixed.card + c.satCount r = r.length := by
    rw [hFixed_card, satCount, Finset.card_filter, ← Finset.sum_add_distrib]
    have hlen : r.length = ∑ i : Fin c.n, (c.bank r).count i := by
      rw [← c.bank_length r, list_length_eq_sum_count]
    rw [hlen]
    refine Finset.sum_congr rfl ?_
    intro i _
    have hle := c.bank_count_le hr i
    have hwi := c.hw i
    by_cases h : (c.bank r).count i = c.w i <;> simp [h] <;> omega
  have hFixed_le_U : Fixed.card ≤ Fintype.card U := by
    rw [← Finset.card_univ]
    exact Finset.card_le_univ Fixed
  have hU_card : Fintype.card U = (∑ i : Fin c.n, c.w i) - c.n := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    have hsum : (∑ i : Fin c.n, (c.w i - 1)) + c.n = ∑ i : Fin c.n, c.w i := by
      have h1 : (∑ i : Fin c.n, (c.w i - 1)) + ∑ _i : Fin c.n, 1 = ∑ i : Fin c.n, c.w i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        have := c.hw i
        omega
      simpa using h1
    omega
  have hcard_matches : (Finset.univ.filter (fun t : c.Coin => c.Matches t r)).card =
      2 ^ (Fintype.card U - Fixed.card) := by
    have h1 : (Finset.univ.filter (fun t : c.Coin => c.Matches t r)).card =
        Fintype.card {f : U → Bool // ∀ x ∈ Fixed, f x = bitOf x} := by
      rw [Fintype.card_subtype]
      refine Finset.card_bij (fun t _ => c.coinEquiv t) ?_ ?_ ?_
      · intro t ht
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
        exact (hmatches_iff t).mp ht
      · intro t₁ _ t₂ _ h
        exact c.coinEquiv.injective h
      · intro f hf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
        refine ⟨c.coinEquiv.symm f, ?_, c.coinEquiv.apply_symm_apply f⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hmatches_iff _).mpr (by simpa using hf)
    rw [h1, Fintype.card_congr (restrictEquiv Fixed bitOf), Fintype.card_fun, Fintype.card_bool]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_coe]
  rw [hcard_matches, hU_card]
  have hFixed_sub : Fixed.card = r.length - c.satCount r := by omega
  rw [hFixed_sub]
  exact ⟨rfl, by rw [← hFixed_sub, ← hU_card]; exact hFixed_le_U⟩

lemma exists_good_coin (c : Ctx) {m : ℕ} (price : Fin m → ℕ) (ans : List Bool → Fin m) :
    ∃ t : c.Coin,
      2 ^ (∑ i : Fin c.n, c.w i) *
          (c.M t \ c.A t).sum (fun u => price (c.out ans t u) * 2 ^ (((traceDef (c.q t) u).map c.w).sum - u.length)) ≤
        (c.N \ c.J).sum (fun r => price (ans r) * 2 ^ ((∑ i : Fin c.n, c.w i) - wasteDef c.w c.ask r)) := by
  set D := ∑ i : Fin c.n, c.w i
  let lhsVal (t : c.Coin) : ℕ :=
    2 ^ D * (c.M t \ c.A t).sum (fun u => price (c.out ans t u) * 2 ^ (((traceDef (c.q t) u).map c.w).sum - u.length))
  set rhsVal := (c.N \ c.J).sum (fun r => price (ans r) * 2 ^ (D - wasteDef c.w c.ask r))
  have hsum_t : ∀ t : c.Coin, lhsVal t =
      ((c.N \ c.J).filter (fun r => c.Matches t r)).sum
        (fun r => 2 ^ D * (price (ans r) * 2 ^ (c.sumW r - c.satCount r))) := by
    intro t
    dsimp only [lhsVal]
    rw [Finset.mul_sum]
    refine Finset.sum_bij'
      (fun u hu => (c.runFrom t [] u).get ((c.mem_M t u).mp (Finset.sdiff_subset hu)))
      (fun r hr => Classical.choose (c.exists_u_of_matches t (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2))
      ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu' := hu
      rw [mem_M_sdiff_A] at hu'
      rcases hu' with ⟨r, hr, hrNJ⟩
      have hget : (c.runFrom t [] u).get ((c.mem_M t u).mp (Finset.sdiff_subset hu)) = r := by
        simp [hr]
      rw [hget]
      exact Finset.mem_filter.mpr ⟨hrNJ, c.runFrom_matches t hr⟩
    · intro r hr
      rw [Finset.mem_filter] at hr
      exact (Classical.choose_spec (c.exists_u_of_matches t hr.1 hr.2)).1
    · intro u hu
      have hu' := hu
      rw [mem_M_sdiff_A] at hu'
      rcases hu' with ⟨r, hr, hrNJ⟩
      have hget : (c.runFrom t [] u).get ((c.mem_M t u).mp (Finset.sdiff_subset hu)) = r := by
        simp [hr]
      simp only [hget]
      have hspec := Classical.choose_spec (c.exists_u_of_matches t hrNJ (c.runFrom_matches t hr))
      exact c.runFrom_inj t _ u [] r hspec.2 hr
    · intro r hr
      have hspec := Classical.choose_spec (c.exists_u_of_matches t (Finset.mem_filter.mp hr).1 (Finset.mem_filter.mp hr).2)
      have h2 := hspec.2
      have hopt : ∀ (x : Option (List Bool)) (hx : x.isSome) (r' : List Bool), x = some r' → x.get hx = r' := by
        rintro _ _ _ rfl
        rfl
      exact hopt _ _ r h2
    · intro u hu
      have hu' := hu
      rw [mem_M_sdiff_A] at hu'
      rcases hu' with ⟨r, hr, _⟩
      have hget : (c.runFrom t [] u).get ((c.mem_M t u).mp (Finset.sdiff_subset hu)) = r := by
        simp [hr]
      rw [hget]
      obtain ⟨hsum, hlen, _, _, _⟩ := c.sum_w_add_waste t hr
      have hout : c.out ans t u = ans r := by simp [out, hr]
      rw [hout, hsum, hlen]
  have hsum_eq : (∑ t : c.Coin, lhsVal t) = 2 ^ (D - c.n) * rhsVal := by
    calc
      ∑ t : c.Coin, lhsVal t
          = ∑ t : c.Coin, ((c.N \ c.J).filter (fun r => c.Matches t r)).sum
              (fun r => 2 ^ D * (price (ans r) * 2 ^ (c.sumW r - c.satCount r))) := by
            refine Finset.sum_congr rfl ?_
            intro t _
            exact hsum_t t
      _ = ∑ t : c.Coin, ∑ r ∈ c.N \ c.J,
            if c.Matches t r then 2 ^ D * (price (ans r) * 2 ^ (c.sumW r - c.satCount r)) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro t _
          rw [Finset.sum_filter]
      _ = ∑ r ∈ c.N \ c.J, ∑ t : c.Coin,
            if c.Matches t r then 2 ^ D * (price (ans r) * 2 ^ (c.sumW r - c.satCount r)) else 0 :=
          Finset.sum_comm
      _ = ∑ r ∈ c.N \ c.J, (Finset.univ.filter (fun t : c.Coin => c.Matches t r)).card *
            (2 ^ D * (price (ans r) * 2 ^ (c.sumW r - c.satCount r))) := by
          refine Finset.sum_congr rfl ?_
          intro r _
          simp [Finset.sum_ite]
      _ = ∑ r ∈ c.N \ c.J, 2 ^ (D - c.n) * (price (ans r) * 2 ^ (D - wasteDef c.w c.ask r)) := by
          refine Finset.sum_congr rfl ?_
          intro r hrNJ
          have hrN : r ∈ c.N := (Finset.mem_sdiff.mp hrNJ).1
          obtain ⟨hcard, hle_sub⟩ := c.card_matches hrN
          rw [hcard]
          have hwaste_le : wasteDef c.w c.ask r ≤ D := by
            refine Finset.sum_le_sum ?_
            intro i _
            have := c.bank_count_le hrN i
            split_ifs <;> omega
          have hlen_sum : c.sumW r + wasteDef c.w c.ask r = r.length := by
            have hlen : r.length = ∑ i : Fin c.n, (c.bank r).count i := by
              rw [← c.bank_length r, list_length_eq_sum_count]
            rw [hlen, sumW, wasteDef, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro i _
            have hle := c.bank_count_le hrN i
            change (if (c.bank r).count i = c.w i then c.w i else 0) +
              (if (c.bank r).count i < c.w i then (c.bank r).count i else 0) = (c.bank r).count i
            split_ifs <;> omega
          have hsat_le : c.satCount r ≤ c.sumW r := by
            rw [satCount, Finset.card_filter, sumW]
            refine Finset.sum_le_sum ?_
            intro i _
            have := c.hw i
            split_ifs <;> omega
          have hsat_le_len : c.satCount r ≤ r.length := by omega
          have hD_ge_n : c.n ≤ D := by
            have : ∑ _i : Fin c.n, 1 ≤ D := Finset.sum_le_sum (fun i _ => c.hw i)
            simpa using this
          have hexp : ((D - c.n) - (r.length - c.satCount r)) + D + (c.sumW r - c.satCount r) =
              (D - c.n) + (D - wasteDef c.w c.ask r) := by omega
          calc
            2 ^ ((D - c.n) - (r.length - c.satCount r)) *
                (2 ^ D * (price (ans r) * 2 ^ (c.sumW r - c.satCount r)))
                = price (ans r) * (2 ^ ((D - c.n) - (r.length - c.satCount r)) * 2 ^ D *
                    2 ^ (c.sumW r - c.satCount r)) := by ring
            _ = price (ans r) * 2 ^ (((D - c.n) - (r.length - c.satCount r)) + D +
                  (c.sumW r - c.satCount r)) := by
                rw [← pow_add, ← pow_add]
            _ = price (ans r) * 2 ^ ((D - c.n) + (D - wasteDef c.w c.ask r)) := by rw [hexp]
            _ = 2 ^ (D - c.n) * (price (ans r) * 2 ^ (D - wasteDef c.w c.ask r)) := by
                rw [pow_add]; ring
      _ = 2 ^ (D - c.n) * rhsVal := by
          rw [Finset.mul_sum]
  by_contra h
  push Not at h
  have hlt : (∑ _t : c.Coin, rhsVal) < ∑ t : c.Coin, lhsVal t :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun t _ => h t)
  rw [Finset.sum_const, Finset.card_univ, c.card_coin, smul_eq_mul, hsum_eq] at hlt
  exact lt_irrefl _ hlt

end Ctx

end PEqualNP.Outside.L_lib_718

theorem PEqualNP.Outside.L_lib_718 : (∀ (n : ℕ) (hn : 0 < n) (w : Fin n → ℕ), (∀ i, 0 < w i) →
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let trace := fun {V : Type} (ask : List Bool → V) (p : List Bool) =>
    List.ofFn (fun j : Fin p.length => ask (p.take j.val))
  let consistent := fun {V : Type} (ask : List Bool → V) (p : List Bool) (x : V → Bool) =>
    ∀ j : Fin p.length, x (ask (p.take j.val)) = p.get j
  ∀ (m : ℕ) (R : (Fin n → Bool) → Fin m → Prop) (price : Fin m → ℕ) (H : ℕ)
    (N J : Finset (List Bool)) (ask : List Bool → Raw) (ans : List Bool → Fin m),
    shape N J → (∀ p ∈ N, (trace ask p).Nodup ∧ p.length ≤ H) →
    (∀ p ∈ N \ J, ∀ y, consistent ask p y → R (parity y) (ans p)) →
    let D := ∑ i, w i
    let waste := fun p : List Bool =>
      let bank := (trace ask p).map Sigma.fst
      ∑ i : Fin n, if bank.count i < w i then bank.count i else 0
    ∃ (M A : Finset (List Bool)) (q : List Bool → Fin n) (out : List Bool → Fin m),
      shape M A ∧ (∀ p ∈ M, (trace q p).Nodup ∧ ((trace q p).map w).sum ≤ H) ∧
      (∀ p ∈ M \ A, ∀ x, consistent q p x → R x (out p)) ∧
      2^D * (M \ A).sum (fun p => price (out p) * 2^(((trace q p).map w).sum - p.length)) ≤
        (N \ J).sum (fun p => price (ans p) * 2^(D-waste p))) := by
  intro n _hn w hw Raw parity shape trace consistent m R price H N J ask ans hshape hN hR D waste
  let c : PEqualNP.Outside.L_lib_718.Ctx := ⟨n, _hn, w, hw, H, N, J, ask, hshape, hN⟩
  obtain ⟨t, ht⟩ := c.exists_good_coin price ans
  refine ⟨c.M t, c.A t, c.q t, c.out ans t, c.shape_MA t, ?_, ?_, ht⟩
  · intro u hu
    rw [PEqualNP.Outside.L_lib_718.Ctx.mem_M] at hu
    cases hrun : c.runFrom t [] u with
    | none => simp [hrun] at hu
    | some r =>
      have hnd := (c.trace_q_nodup_and_mem t hrun).1
      have hH := (c.sum_w_add_waste t hrun).2.2.2.1
      exact ⟨hnd, hH⟩
  · intro u hu x hx
    exact c.exists_y_of_consistent R ans hR t hu hx
