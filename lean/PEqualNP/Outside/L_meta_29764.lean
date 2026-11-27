import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29764

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

abbrev F := ZMod 2

def b2z (b : Bool) : F := if b then 1 else 0

lemma b2z_decide_eq_one (t : F) : b2z (decide (t = 1)) = t := by
  revert t
  decide

lemma b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  revert a b h
  decide

lemma b2z_not (b : Bool) : b2z (!b) = b2z b + 1 := by
  revert b
  decide

lemma b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  revert a b
  decide

lemma b2z_or (a b : Bool) : b2z (a || b) = b2z a + b2z b + b2z a * b2z b := by
  revert a b
  decide

lemma b2z_mod2_nil : b2z (decide (([] : List Bool).count true % 2 = 0)) = 1 := by
  decide

lemma b2z_mod2_one (a : Bool) : b2z (decide ([a].count true % 2 = 0)) = b2z a + 1 := by
  revert a
  decide

lemma b2z_mod2_two (a b : Bool) :
    b2z (decide ([a, b].count true % 2 = 0)) = b2z a + b2z b + 1 := by
  revert a b
  decide

lemma zmod2_cases (t : F) : t = 0 ∨ t = 1 := by
  revert t
  decide

lemma zmod2_ne_zero (t : F) (h : t ≠ 0) : t = 1 := by
  revert t h
  decide

lemma zmod2_add_self (t : F) : t + t = 0 := by
  revert t
  decide

def bits (n : ℕ) (u : Fin n → F) : List Bool :=
  List.ofFn (fun j : Fin n => decide (u j = 1))

def inpVec {k t : ℕ} (x y : Fin k → F) (z : Fin t → F) : List Bool :=
  bits k x ++ bits k y ++ bits t z

lemma inpVec_length {k t : ℕ} (x y : Fin k → F) (z : Fin t → F) :
    (inpVec x y z).length = 2 * k + t := by
  simp only [inpVec, bits, List.length_append, List.length_ofFn]
  omega

lemma getD_inpVec_x {k t : ℕ} (x y : Fin k → F) (z : Fin t → F) (w : ℕ) (hw : w < k) :
    b2z ((inpVec x y z).getD w false) = x ⟨w, hw⟩ := by
  simp only [inpVec, bits, List.getD_eq_getElem?_getD]
  have h1 : w < (List.ofFn (fun j : Fin k => decide (x j = 1)) ++
      List.ofFn (fun j : Fin k => decide (y j = 1))).length := by
    simp only [List.length_append, List.length_ofFn]
    omega
  rw [List.getElem?_append_left h1, List.getElem?_append_left (by simp [hw])]
  simp [hw, b2z_decide_eq_one]

lemma getD_inpVec_y {k t : ℕ} (x y : Fin k → F) (z : Fin t → F) (w : ℕ)
    (hw1 : k ≤ w) (hw2 : w < 2 * k) :
    b2z ((inpVec x y z).getD w false) = y ⟨w - k, by omega⟩ := by
  simp only [inpVec, bits, List.getD_eq_getElem?_getD]
  have h1 : w < (List.ofFn (fun j : Fin k => decide (x j = 1)) ++
      List.ofFn (fun j : Fin k => decide (y j = 1))).length := by
    simp only [List.length_append, List.length_ofFn]
    omega
  rw [List.getElem?_append_left h1, List.getElem?_append_right (by simp [hw1])]
  simp only [List.length_ofFn, List.getElem?_ofFn]
  split_ifs with h
  · simp [b2z_decide_eq_one]
  · omega

lemma getD_inpVec_z {k t : ℕ} (x y : Fin k → F) (z : Fin t → F) (w : ℕ)
    (hw1 : 2 * k ≤ w) (hw2 : w < 2 * k + t) :
    b2z ((inpVec x y z).getD w false) = z ⟨w - 2 * k, by omega⟩ := by
  simp only [inpVec, bits, List.getD_eq_getElem?_getD]
  have h1 : (List.ofFn (fun j : Fin k => decide (x j = 1)) ++
      List.ofFn (fun j : Fin k => decide (y j = 1))).length ≤ w := by
    simp only [List.length_append, List.length_ofFn]
    omega
  rw [List.getElem?_append_right h1]
  simp only [List.length_append, List.length_ofFn, List.getElem?_ofFn]
  have hlen : w - (k + k) = w - 2 * k := by omega
  rw [hlen]
  split_ifs with h
  · simp [b2z_decide_eq_one]
  · omega

lemma getD_inpVec_ge {k t : ℕ} (x y : Fin k → F) (z : Fin t → F) (w : ℕ)
    (hw : 2 * k + t ≤ w) :
    b2z ((inpVec x y z).getD w false) = 0 := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none]
  · rfl
  · rw [inpVec_length]; exact hw

def wiresOf (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

lemma wiresOf_length (gs : List Gate) (inp : List Bool) :
    (wiresOf gs inp).length = inp.length + gs.length := by
  unfold wiresOf
  induction gs generalizing inp with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega

lemma wiresOf_append_singleton (gs : List Gate) (g : Gate) (inp : List Bool) :
    wiresOf (gs ++ [g]) inp =
      wiresOf gs inp ++ [g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false)] := by
  unfold wiresOf
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma getD_append_singleton_lt (l : List Bool) (v : Bool) (w : ℕ) (hw : w < l.length) :
    (l ++ [v]).getD w false = l.getD w false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hw]

lemma getD_append_singleton_eq (l : List Bool) (v : Bool) :
    (l ++ [v]).getD l.length false = v := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  simp

lemma getD_append_singleton_gt (l : List Bool) (v : Bool) (w : ℕ) (hw : l.length < w) :
    (l ++ [v]).getD w false = false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_none]
  · rfl
  · rw [List.length_append, List.length_singleton]
    omega

lemma wiresOf_append_getD (gs suf : List Gate) (inp : List Bool) (w : ℕ)
    (hw : w < inp.length + gs.length) :
    (wiresOf (gs ++ suf) inp).getD w false = (wiresOf gs inp).getD w false := by
  induction suf using List.reverseRecOn with
  | nil => simp
  | append_singleton suf g ih =>
    rw [← List.append_assoc, wiresOf_append_singleton, getD_append_singleton_lt]
    · exact ih
    · rw [wiresOf_length, List.length_append]; omega

lemma wiresOf_append_val {n : ℕ} (gs : List Gate) (g : Gate) (inp : List Bool)
    (hinp : inp.length = n) :
    (wiresOf (gs ++ [g]) inp).getD (n + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false) := by
  rw [wiresOf_append_singleton, ← hinp, ← wiresOf_length gs inp, getD_append_singleton_eq]

def LegalGate (h : Gate) : Prop :=
  h.inputs.length ≤ 2 ∧
    (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1))

noncomputable def isPaid (h : Gate) : Bool :=
  @decide ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _)

noncomputable def gateCost (gs : List Gate) : ℕ :=
  gs.countP isPaid

lemma gateCost_append_singleton (gs : List Gate) (g : Gate) :
    gateCost (gs ++ [g]) = gateCost gs + if isPaid g = true then 1 else 0 := by
  unfold gateCost
  rw [List.countP_append, List.countP_cons, List.countP_nil]
  split_ifs with h
  · simp
  · simp

def affFun {k t : ℕ} (f : (Fin k → F) → (Fin t → F) → F) : Prop :=
  ∃ (a : Fin k → F) (b : Fin t → F) (c : F),
    ∀ y z, f y z = c + dotProduct a y + dotProduct b z

lemma affFun_zero {k t : ℕ} : affFun (fun (_ : Fin k → F) (_ : Fin t → F) => (0 : F)) :=
  ⟨0, 0, 0, fun _ _ => by simp⟩

lemma affFun_one {k t : ℕ} : affFun (fun (_ : Fin k → F) (_ : Fin t → F) => (1 : F)) :=
  ⟨0, 0, 1, fun _ _ => by simp⟩

lemma affFun_const {k t : ℕ} (c : F) :
    affFun (fun (_ : Fin k → F) (_ : Fin t → F) => c) :=
  ⟨0, 0, c, fun _ _ => by simp⟩

lemma affFun_y {k t : ℕ} (i : Fin k) :
    affFun (fun (y : Fin k → F) (_ : Fin t → F) => y i) :=
  ⟨Pi.single i 1, 0, 0, fun y _ => by simp [dotProduct, Pi.single_apply]⟩

lemma affFun_z {k t : ℕ} (j : Fin t) :
    affFun (fun (_ : Fin k → F) (z : Fin t → F) => z j) :=
  ⟨0, Pi.single j 1, 0, fun _ z => by simp [dotProduct, Pi.single_apply]⟩

lemma affFun_add {k t : ℕ} {f g : (Fin k → F) → (Fin t → F) → F}
    (hf : affFun f) (hg : affFun g) :
    affFun (fun y z => f y z + g y z) := by
  rcases hf with ⟨af, bf, cf, hf⟩
  rcases hg with ⟨ag, bg, cg, hg⟩
  refine ⟨af + ag, bf + bg, cf + cg, fun y z => ?_⟩
  dsimp only
  rw [hf, hg, add_dotProduct, add_dotProduct]
  ring

lemma affFun_smul {k t : ℕ} (s : F) {f : (Fin k → F) → (Fin t → F) → F}
    (hf : affFun f) :
    affFun (fun y z => s * f y z) := by
  rcases hf with ⟨af, bf, cf, hf⟩
  refine ⟨s • af, s • bf, s * cf, fun y z => ?_⟩
  dsimp only
  rw [hf, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

lemma affFun_add_const {k t : ℕ} {f : (Fin k → F) → (Fin t → F) → F}
    (hf : affFun f) (c : F) :
    affFun (fun y z => f y z + c) :=
  affFun_add hf (affFun_const c)

def SpanAff {k t : ℕ} (u0 v0 f : (Fin k → F) → (Fin t → F) → F) : Prop :=
  ∃ (f0 : (Fin k → F) → (Fin t → F) → F) (c : F),
    affFun f0 ∧ ∀ y z, f y z = f0 y z + c * u0 y z * v0 y z

lemma SpanAff_of_aff {k t : ℕ} (u0 v0 : (Fin k → F) → (Fin t → F) → F)
    {f : (Fin k → F) → (Fin t → F) → F} (hf : affFun f) :
    SpanAff u0 v0 f :=
  ⟨f, 0, hf, fun y z => by simp⟩

lemma SpanAff_add {k t : ℕ} {u0 v0 f g : (Fin k → F) → (Fin t → F) → F}
    (hf : SpanAff u0 v0 f) (hg : SpanAff u0 v0 g) :
    SpanAff u0 v0 (fun y z => f y z + g y z) := by
  rcases hf with ⟨f0, cf, hfa, hfe⟩
  rcases hg with ⟨g0, cg, hga, hge⟩
  refine ⟨fun y z => f0 y z + g0 y z, cf + cg, affFun_add hfa hga, fun y z => ?_⟩
  dsimp only
  rw [hfe, hge]
  ring

lemma SpanAff_smul {k t : ℕ} (s : F) {u0 v0 f : (Fin k → F) → (Fin t → F) → F}
    (hf : SpanAff u0 v0 f) :
    SpanAff u0 v0 (fun y z => s * f y z) := by
  rcases hf with ⟨f0, cf, hfa, hfe⟩
  refine ⟨fun y z => s * f0 y z, s * cf, affFun_smul s hfa, fun y z => ?_⟩
  dsimp only
  rw [hfe]
  ring

lemma SpanAff_add_const {k t : ℕ} {u0 v0 f : (Fin k → F) → (Fin t → F) → F}
    (hf : SpanAff u0 v0 f) (c : F) :
    SpanAff u0 v0 (fun y z => f y z + c) :=
  SpanAff_add hf (SpanAff_of_aff u0 v0 (affFun_const c))

lemma finrank_ker_inter {k : ℕ} (U : Submodule F (Fin k → F))
    (la : (Fin k → F) →ₗ[F] F) (e : Fin k → F) (heU : e ∈ U) (hle : la e = 1) :
    Module.finrank F (U ⊓ LinearMap.ker la : Submodule F (Fin k → F)) + 1 =
      Module.finrank F U := by
  let ψ : U →ₗ[F] F := la.comp U.subtype
  have hrange : LinearMap.range ψ = ⊤ := by
    rw [eq_top_iff]
    intro c _
    rcases zmod2_cases c with rfl | rfl
    · exact ⟨0, map_zero ψ⟩
    · exact ⟨⟨e, heU⟩, hle⟩
  have hmap : (LinearMap.ker ψ).map U.subtype = U ⊓ LinearMap.ker la := by
    ext x
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.coe_subtype,
      Submodule.mem_inf, ψ, LinearMap.comp_apply]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨hxU, hxla⟩
      exact ⟨⟨x, hxU⟩, hxla, rfl⟩
  have hker : Module.finrank F (LinearMap.ker ψ) =
      Module.finrank F (U ⊓ LinearMap.ker la : Submodule F (Fin k → F)) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective U.subtype (Submodule.injective_subtype U)
      (LinearMap.ker ψ)).finrank_eq
  have hrk := LinearMap.finrank_range_add_finrank_ker ψ
  rw [hrange, finrank_top, Module.finrank_self, hker] at hrk
  omega

def coordLin {k : ℕ} (i : Fin k) : (Fin k → F) →ₗ[F] F where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma gates_forward_inv {k t : ℕ} (gs : List Gate)
    (hgs : ∀ g ∈ gs, LegalGate g) :
    ∃ (U : Submodule F (Fin k → F))
      (φ : (Fin k → F) → (Fin t → F) → (Fin k → F))
      (r q : ℕ)
      (lam : ℕ → (Fin k → F) →ₗ[F] F)
      (phiW : ℕ → (Fin k → F) → (Fin t → F) → F)
      (u0 v0 : (Fin k → F) → (Fin t → F) → F),
      Module.finrank F U + r = k ∧
      r + q = gateCost gs ∧
      (∀ w, 2 * k + t + gs.length ≤ w → lam w = 0 ∧ phiW w = 0) ∧
      (∀ u ∈ U, ∀ y z w,
        b2z ((wiresOf gs (inpVec (u + φ y z) y z)).getD w false) =
          lam w u + phiW w y z) ∧
      (q = 0 → (∀ i, affFun (fun y z => φ y z i)) ∧ ∀ w, affFun (phiW w)) ∧
      (q = 1 → affFun u0 ∧ affFun v0 ∧
        (∀ i, SpanAff u0 v0 (fun y z => φ y z i)) ∧
        ∀ w, SpanAff u0 v0 (phiW w)) := by
  induction gs using List.reverseRecOn with
  | nil =>
    let lam0 : ℕ → (Fin k → F) →ₗ[F] F := fun w =>
      if h : w < k then coordLin ⟨w, h⟩ else 0
    let phiW0 : ℕ → (Fin k → F) → (Fin t → F) → F := fun w y z =>
      if h1 : k ≤ w ∧ w < 2 * k then y ⟨w - k, by omega⟩
      else if h2 : 2 * k ≤ w ∧ w < 2 * k + t then z ⟨w - 2 * k, by omega⟩
      else 0
    refine ⟨⊤, fun _ _ => 0, 0, 0, lam0, phiW0, fun _ _ => 0, fun _ _ => 0,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [finrank_top]
    · simp [gateCost]
    · intro w hw
      refine ⟨?_, ?_⟩
      · simp only [lam0, dite_eq_right (by omega : ¬ w < k)]
      · funext y z
        simp only [phiW0, dite_eq_right (by omega : ¬ (k ≤ w ∧ w < 2 * k)),
          dite_eq_right (by omega : ¬ (2 * k ≤ w ∧ w < 2 * k + t))]
        rfl
    · intro u _ y z w
      unfold wiresOf
      rw [List.foldl_nil, add_zero]
      by_cases hw1 : w < k
      · rw [getD_inpVec_x u y z w hw1]
        simp [lam0, phiW0, hw1, coordLin, show ¬ (k ≤ w ∧ w < 2 * k) by omega,
          show ¬ (2 * k ≤ w ∧ w < 2 * k + t) by omega]
      · by_cases hw2 : w < 2 * k
        · rw [getD_inpVec_y u y z w (by omega) hw2]
          simp [lam0, phiW0, hw1, show k ≤ w ∧ w < 2 * k by omega]
        · by_cases hw3 : w < 2 * k + t
          · rw [getD_inpVec_z u y z w (by omega) hw3]
            simp [lam0, phiW0, hw1, show ¬ (k ≤ w ∧ w < 2 * k) by omega,
              show 2 * k ≤ w ∧ w < 2 * k + t by omega]
          · rw [getD_inpVec_ge u y z w (by omega)]
            simp [lam0, phiW0, hw1, show ¬ (k ≤ w ∧ w < 2 * k) by omega,
              show ¬ (2 * k ≤ w ∧ w < 2 * k + t) by omega]
    · intro _
      refine ⟨fun i => affFun_zero, fun w => ?_⟩
      by_cases h1 : k ≤ w ∧ w < 2 * k
      · simp only [phiW0, dite_eq_left h1]
        exact affFun_y ⟨w - k, by omega⟩
      · by_cases h2 : 2 * k ≤ w ∧ w < 2 * k + t
        · simp only [phiW0, dite_eq_right h1, dite_eq_left h2]
          exact affFun_z ⟨w - 2 * k, by omega⟩
        · simp only [phiW0, dite_eq_right h1, dite_eq_right h2]
          exact affFun_zero
    · intro hq; omega
  | append_singleton gs g ih =>
    have hgs' : ∀ h ∈ gs, LegalGate h := fun h hh => hgs h (List.mem_append_left [g] hh)
    have hg : LegalGate g := hgs g (List.mem_append_right gs (List.mem_singleton_self g))
    obtain ⟨U, φ, r, q, lam, phiW, u0, v0, hdim, hcost, hzero, hwire, hq0, hq1⟩ := ih hgs'
    let idx := 2 * k + t + gs.length
    have hlen_inp : ∀ u y z, (wiresOf gs (inpVec (u + φ y z) y z)).length = idx := by
      intro u y z
      rw [wiresOf_length, inpVec_length]
    have hstep_same :
        ∀ (lnew : (Fin k → F) →ₗ[F] F) (pnew : (Fin k → F) → (Fin t → F) → F)
          (hc : isPaid g = false)
          (haff_new : q = 0 → affFun pnew)
          (hspan_new : q = 1 → SpanAff u0 v0 pnew),
        (∀ u ∈ U, ∀ y z,
          b2z (g.op.eval (g.inputs.map fun i =>
            (wiresOf gs (inpVec (u + φ y z) y z)).getD i false)) = lnew u + pnew y z) →
        ∃ (U' : Submodule F (Fin k → F))
          (φ' : (Fin k → F) → (Fin t → F) → (Fin k → F))
          (r' q' : ℕ)
          (lam' : ℕ → (Fin k → F) →ₗ[F] F)
          (phiW' : ℕ → (Fin k → F) → (Fin t → F) → F)
          (u0' v0' : (Fin k → F) → (Fin t → F) → F),
          Module.finrank F U' + r' = k ∧
          r' + q' = gateCost (gs ++ [g]) ∧
          (∀ w, 2 * k + t + (gs ++ [g]).length ≤ w → lam' w = 0 ∧ phiW' w = 0) ∧
          (∀ u ∈ U', ∀ y z w,
            b2z ((wiresOf (gs ++ [g]) (inpVec (u + φ' y z) y z)).getD w false) =
              lam' w u + phiW' w y z) ∧
          (q' = 0 → (∀ i, affFun (fun y z => φ' y z i)) ∧ ∀ w, affFun (phiW' w)) ∧
          (q' = 1 → affFun u0' ∧ affFun v0' ∧
            (∀ i, SpanAff u0' v0' (fun y z => φ' y z i)) ∧
            ∀ w, SpanAff u0' v0' (phiW' w)) := by
      intro lnew pnew hc haff_new hspan_new heval
      refine ⟨U, φ, r, q, Function.update lam idx lnew, Function.update phiW idx pnew, u0, v0,
        hdim, ?_, ?_, ?_, ?_, ?_⟩
      · rw [gateCost_append_singleton, hc]; simpa using hcost
      · intro w hw
        have hw' : idx < w := by
          simp only [idx, List.length_append, List.length_singleton] at hw ⊢
          omega
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hzero w (by simp only [idx] at hw'; omega)
      · intro u hu y z w
        rw [wiresOf_append_singleton]
        by_cases hw : w < idx
        · rw [getD_append_singleton_lt _ _ _ (by rw [hlen_inp]; exact hw)]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hwire u hu y z w
        · by_cases heq : w = idx
          · subst heq
            rw [← hlen_inp u y z, getD_append_singleton_eq]
            simp only [Function.update_self]
            exact heval u hu y z
          · rw [getD_append_singleton_gt _ _ _ (by rw [hlen_inp]; omega)]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            have hz := hzero w (by simp only [idx] at hw heq ⊢; omega)
            rw [hz.1, hz.2]
            simp [b2z]
      · intro hq
        obtain ⟨hφ, hpw⟩ := hq0 hq
        refine ⟨hφ, fun w => ?_⟩
        by_cases heq : w = idx
        · subst heq; simp only [Function.update_self]; exact haff_new hq
        · rw [Function.update_of_ne heq]; exact hpw w
      · intro hq
        obtain ⟨hu0, hv0, hφ, hpw⟩ := hq1 hq
        refine ⟨hu0, hv0, hφ, fun w => ?_⟩
        by_cases heq : w = idx
        · subst heq; simp only [Function.update_self]; exact hspan_new hq
        · rw [Function.update_of_ne heq]; exact hpw w
    by_cases hpaid : isPaid g = true
    · have hp : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
        simpa [isPaid] using hpaid
      rcases hgi : g.inputs with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
      · simp [hgi] at hp
      · simp [hgi] at hp
      · by_cases hconst : (∀ u ∈ U, lam w1 u = 0) ∧ (∀ u ∈ U, lam w2 u = 0)
        · let pnew : (Fin k → F) → (Fin t → F) → F := match g.op with
            | .and => fun y z => phiW w1 y z * phiW w2 y z
            | _ => fun y z => phiW w1 y z + phiW w2 y z + phiW w1 y z * phiW w2 y z
          let u0' := if q = 0 then phiW w1 else u0
          let v0' := if q = 0 then phiW w2 else v0
          refine ⟨U, φ, r, q + 1, Function.update lam idx 0, Function.update phiW idx pnew,
            u0', v0', hdim, ?_, ?_, ?_, ?_, ?_⟩
          · rw [gateCost_append_singleton, hpaid]
            simp only [ite_true]
            omega
          · intro w hw
            have hw' : idx < w := by
              simp only [idx, List.length_append, List.length_singleton] at hw ⊢
              omega
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hzero w (by simp only [idx] at hw'; omega)
          · intro u hu y z w
            rw [wiresOf_append_singleton]
            by_cases hw : w < idx
            · rw [getD_append_singleton_lt _ _ _ (by rw [hlen_inp]; exact hw)]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hwire u hu y z w
            · by_cases heq : w = idx
              · subst heq
                rw [← hlen_inp u y z, getD_append_singleton_eq, hgi]
                simp only [Function.update_self, LinearMap.zero_apply, zero_add]
                have hw1 := hwire u hu y z w1
                have hw2 := hwire u hu y z w2
                rw [hconst.1 u hu, zero_add] at hw1
                rw [hconst.2 u hu, zero_add] at hw2
                rcases hp.1 with hop | hop
                · simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
                    List.all_nil, id_eq, Bool.and_true, pnew]
                  rw [b2z_and, hw1, hw2]
                · simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
                    List.any_nil, id_eq, Bool.or_false, pnew]
                  rw [b2z_or, hw1, hw2]
              · rw [getD_append_singleton_gt _ _ _ (by rw [hlen_inp]; omega)]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                have hz := hzero w (by simp only [idx] at hw heq ⊢; omega)
                rw [hz.1, hz.2]
                simp [b2z]
          · intro hq; omega
          · intro hq
            have hqz : q = 0 := by omega
            obtain ⟨hφ, hpw⟩ := hq0 hqz
            have hu0' : u0' = phiW w1 := by simp [u0', hqz]
            have hv0' : v0' = phiW w2 := by simp [v0', hqz]
            rw [hu0', hv0']
            refine ⟨hpw w1, hpw w2, fun i => SpanAff_of_aff _ _ (hφ i), fun w => ?_⟩
            by_cases heq : w = idx
            · subst heq
              simp only [Function.update_self]
              rcases hp.1 with hop | hop
              · refine ⟨fun _ _ => 0, 1, affFun_zero, fun y z => ?_⟩
                simp [pnew, hop]
              · refine ⟨fun y z => phiW w1 y z + phiW w2 y z, 1,
                  affFun_add (hpw w1) (hpw w2), fun y z => ?_⟩
                simp [pnew, hop, one_mul]
            · rw [Function.update_of_ne heq]
              exact SpanAff_of_aff _ _ (hpw w)
        · have hex : ∃ wa wb : ℕ, ∃ e ∈ U, lam wa e = 1 ∧
              ∀ val : ℕ → Bool,
                g.op.eval [val w1, val w2] = g.op.eval [val wa, val wb] := by
            by_cases h1 : ∀ u ∈ U, lam w1 u = 0
            · have h2 : ∃ e ∈ U, lam w2 e ≠ 0 := by
                by_contra hno
                apply hconst
                refine ⟨h1, fun u hu => ?_⟩
                by_contra hne
                exact hno ⟨u, hu, hne⟩
              obtain ⟨e, heU, hne⟩ := h2
              refine ⟨w2, w1, e, heU, zmod2_ne_zero _ hne, fun val => ?_⟩
              rcases hp.1 with hop | hop <;>
                simp [hop, GateOp.eval, Bool.and_comm, Bool.or_comm]
            · obtain ⟨e, heU, hne⟩ : ∃ e ∈ U, lam w1 e ≠ 0 := by
                by_contra hno
                apply h1
                intro u hu
                by_contra hne
                exact hno ⟨u, hu, hne⟩
              refine ⟨w1, w2, e, heU, zmod2_ne_zero _ hne, fun _ => rfl⟩
          obtain ⟨wa, wb, e, heU, hla, hswap_eval⟩ := hex
          let la := lam wa
          let lb := lam wb
          let pa := phiW wa
          let U' : Submodule F (Fin k → F) := U ⊓ LinearMap.ker la
          let φ' : (Fin k → F) → (Fin t → F) → (Fin k → F) := fun y z => φ y z + pa y z • e
          let shiftPhiW : ℕ → (Fin k → F) → (Fin t → F) → F :=
            fun w y z => phiW w y z + lam w e * pa y z
          let lnew : (Fin k → F) →ₗ[F] F := match g.op with
            | .and => 0
            | _ => lb
          let pnew : (Fin k → F) → (Fin t → F) → F := match g.op with
            | .and => fun _ _ => 0
            | _ => shiftPhiW wb
          refine ⟨U', φ', r + 1, q, Function.update lam idx lnew,
            Function.update shiftPhiW idx pnew, u0, v0, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · have hfk := finrank_ker_inter U la e heU hla
            change Module.finrank F U' + 1 = Module.finrank F U at hfk
            omega
          · rw [gateCost_append_singleton, hpaid]
            simp only [ite_true]
            omega
          · intro w hw
            have hw' : idx < w := by
              simp only [idx, List.length_append, List.length_singleton] at hw ⊢
              omega
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            have hz := hzero w (by simp only [idx] at hw'; omega)
            refine ⟨hz.1, ?_⟩
            funext y z
            simp only [shiftPhiW, hz.1, hz.2, LinearMap.zero_apply, zero_mul, add_zero]
          · intro u' hu' y z w
            have huU : u' ∈ U := hu'.1
            have hua : la u' = 0 := hu'.2
            let u := u' + pa y z • e
            have hu_mem : u ∈ U := U.add_mem huU (U.smul_mem _ heU)
            have hadd_eq : u' + φ' y z = u + φ y z := by
              simp only [φ', u]
              abel
            rw [wiresOf_append_singleton, hadd_eq]
            by_cases hw : w < idx
            · rw [getD_append_singleton_lt _ _ _ (by rw [hlen_inp]; exact hw)]
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              have hw_val := hwire u hu_mem y z w
              rw [hw_val]
              simp only [u, map_add, map_smul, smul_eq_mul, shiftPhiW]
              ring
            · by_cases heq : w = idx
              · subst heq
                rw [← hlen_inp u y z, getD_append_singleton_eq, hgi]
                simp only [Function.update_self, List.map_cons, List.map_nil]
                have hwa_zero : b2z ((wiresOf gs (inpVec (u + φ y z) y z)).getD wa false) = 0 := by
                  rw [hwire u hu_mem y z wa]
                  simp only [u, map_add, map_smul, smul_eq_mul]
                  change la u' + pa y z * la e + pa y z = 0
                  rw [hua, hla, mul_one, zero_add]
                  exact zmod2_add_self _
                have hwa_false : (wiresOf gs (inpVec (u + φ y z) y z)).getD wa false = false :=
                  b2z_inj hwa_zero
                have hwb_val : b2z ((wiresOf gs (inpVec (u + φ y z) y z)).getD wb false) =
                    lb u' + shiftPhiW wb y z := by
                  rw [hwire u hu_mem y z wb]
                  simp only [u, map_add, map_smul, smul_eq_mul, shiftPhiW]
                  change lb u' + pa y z * lb e + phiW wb y z =
                    lb u' + (phiW wb y z + lb e * pa y z)
                  ring
                have hsw := hswap_eval
                  (fun i => (wiresOf gs (inpVec (u + φ y z) y z)).getD i false)
                rw [hsw]
                simp only [hwa_false]
                rcases hp.1 with hop | hop
                · simp [hop, GateOp.eval, lnew, pnew, b2z]
                · simp only [hop, GateOp.eval, List.any_cons, List.any_nil, id_eq,
                    Bool.false_or, Bool.or_false, lnew, pnew]
                  exact hwb_val
              · rw [getD_append_singleton_gt _ _ _ (by rw [hlen_inp]; omega)]
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                have hz := hzero w (by simp only [idx] at hw heq ⊢; omega)
                simp [shiftPhiW, hz.1, hz.2, b2z]
          · intro hq
            obtain ⟨hφ, hpw⟩ := hq0 hq
            have hshift : ∀ w, affFun (shiftPhiW w) := fun w =>
              affFun_add (hpw w) (affFun_smul (lam w e) (hpw wa))
            refine ⟨fun i => ?_, fun w => ?_⟩
            · have hcomp : (fun y z => φ' y z i) = fun y z => φ y z i + e i * pa y z := by
                funext y z
                simp [φ', Pi.smul_apply, smul_eq_mul, mul_comm]
              rw [hcomp]
              exact affFun_add (hφ i) (affFun_smul (e i) (hpw wa))
            · by_cases heq : w = idx
              · subst heq
                simp only [Function.update_self]
                rcases hp.1 with hop | hop
                · simp only [pnew, hop]; exact affFun_zero
                · simp only [pnew, hop]; exact hshift wb
              · rw [Function.update_of_ne heq]; exact hshift w
          · intro hq
            obtain ⟨hu0, hv0, hφ, hpw⟩ := hq1 hq
            have hshift : ∀ w, SpanAff u0 v0 (shiftPhiW w) := fun w =>
              SpanAff_add (hpw w) (SpanAff_smul (lam w e) (hpw wa))
            refine ⟨hu0, hv0, fun i => ?_, fun w => ?_⟩
            · have hcomp : (fun y z => φ' y z i) = fun y z => φ y z i + e i * pa y z := by
                funext y z
                simp [φ', Pi.smul_apply, smul_eq_mul, mul_comm]
              rw [hcomp]
              exact SpanAff_add (hφ i) (SpanAff_smul (e i) (hpw wa))
            · by_cases heq : w = idx
              · subst heq
                simp only [Function.update_self]
                rcases hp.1 with hop | hop
                · simp only [pnew, hop]; exact SpanAff_of_aff u0 v0 affFun_zero
                · simp only [pnew, hop]; exact hshift wb
              · rw [Function.update_of_ne heq]; exact hshift w
      · simp [hgi] at hp
    · have hpaid_f : isPaid g = false := Bool.eq_false_iff.mpr hpaid
      have hlen_le : g.inputs.length ≤ 2 := hg.1
      rcases hg.2 with hop | hop | hop | ⟨hop, hlen1⟩
      · have hne2 : g.inputs.length ≠ 2 := by
          intro h2
          apply hpaid
          simp [isPaid, hop, h2]
        rcases hgi : g.inputs with _ | ⟨w1, _ | ⟨w2, _⟩⟩
        · refine hstep_same 0 (fun _ _ => 1) hpaid_f (fun _ => affFun_one)
            (fun _ => SpanAff_of_aff _ _ affFun_one) ?_
          intro u _ y z
          simp [hop, hgi, GateOp.eval, b2z]
        · refine hstep_same (lam w1) (phiW w1) hpaid_f
            (fun hq => (hq0 hq).2 w1) (fun hq => (hq1 hq).2.2.2 w1) ?_
          intro u hu y z
          simp only [hop, hgi, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
            List.all_nil, id_eq, Bool.and_true]
          exact hwire u hu y z w1
        · rw [hgi] at hne2 hlen_le
          simp only [List.length_cons] at hne2 hlen_le
          omega
      · have hne2 : g.inputs.length ≠ 2 := by
          intro h2
          apply hpaid
          simp [isPaid, hop, h2]
        rcases hgi : g.inputs with _ | ⟨w1, _ | ⟨w2, _⟩⟩
        · refine hstep_same 0 (fun _ _ => 0) hpaid_f (fun _ => affFun_zero)
            (fun _ => SpanAff_of_aff _ _ affFun_zero) ?_
          intro u _ y z
          simp [hop, hgi, GateOp.eval, b2z]
        · refine hstep_same (lam w1) (phiW w1) hpaid_f
            (fun hq => (hq0 hq).2 w1) (fun hq => (hq1 hq).2.2.2 w1) ?_
          intro u hu y z
          simp only [hop, hgi, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
            List.any_nil, id_eq, Bool.or_false]
          exact hwire u hu y z w1
        · rw [hgi] at hne2 hlen_le
          simp only [List.length_cons] at hne2 hlen_le
          omega
      · rcases hgi : g.inputs with _ | ⟨w1, _ | ⟨w2, _ | _⟩⟩
        · refine hstep_same 0 (fun _ _ => 1) hpaid_f (fun _ => affFun_one)
            (fun _ => SpanAff_of_aff _ _ affFun_one) ?_
          intro u _ y z
          simp [hop, hgi, GateOp.eval, b2z]
        · refine hstep_same (lam w1) (fun y z => phiW w1 y z + 1) hpaid_f
            (fun hq => affFun_add_const ((hq0 hq).2 w1) 1)
            (fun hq => SpanAff_add_const ((hq1 hq).2.2.2 w1) 1) ?_
          intro u hu y z
          simp only [hop, hgi, List.map_cons, List.map_nil, GateOp.eval]
          rw [b2z_mod2_one, hwire u hu y z w1]
          ring
        · refine hstep_same (lam w1 + lam w2) (fun y z => phiW w1 y z + phiW w2 y z + 1) hpaid_f
            (fun hq => affFun_add_const (affFun_add ((hq0 hq).2 w1) ((hq0 hq).2 w2)) 1)
            (fun hq => SpanAff_add_const
              (SpanAff_add ((hq1 hq).2.2.2 w1) ((hq1 hq).2.2.2 w2)) 1) ?_
          intro u hu y z
          simp only [hop, hgi, List.map_cons, List.map_nil, GateOp.eval, LinearMap.add_apply]
          rw [b2z_mod2_two, hwire u hu y z w1, hwire u hu y z w2]
          ring
        · simp [hgi] at hlen_le
      · rcases hgi : g.inputs with _ | ⟨w1, _ | _⟩
        · simp [hgi] at hlen1
        · refine hstep_same (lam w1) (fun y z => phiW w1 y z + 1) hpaid_f
            (fun hq => affFun_add_const ((hq0 hq).2 w1) 1)
            (fun hq => SpanAff_add_const ((hq1 hq).2.2.2 w1) 1) ?_
          intro u hu y z
          simp only [hop, hgi, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
          rw [b2z_not, hwire u hu y z w1]
          ring
        · simp [hgi] at hlen1

lemma forward_dir {k t : ℕ} (g : (Fin k → F) → (Fin t → F) → F)
    (C : Circuit) (hlegal : ∀ h ∈ C.gates, LegalGate h)
    (hcost : gateCost C.gates ≤ k + 1)
    (heval : ∀ x y z, C.eval (inpVec x y z) = decide (dotProduct x y + g y z = 1)) :
    ∃ (f u v : (Fin k → F) → (Fin t → F) → F)
      (p : Fin k → (Fin k → F) → (Fin t → F) → F) (a : Fin k → F) (b : F),
      affFun f ∧ affFun u ∧ affFun v ∧ (∀ i, affFun (p i)) ∧
      ∀ y z, g y z = f y z + (∑ i : Fin k, y i * p i y z) +
        (b + dotProduct a y) * u y z * v y z := by
  obtain ⟨U, φ, r, q, lam, phiW, u0, v0, hdim, hgc, _, hwire, hq0, hq1⟩ :=
    gates_forward_inv C.gates hlegal
  let L := lam C.output
  let Φ := phiW C.output
  have hrel : ∀ u ∈ U, ∀ y z,
      dotProduct u y + dotProduct (φ y z) y + g y z = L u + Φ y z := by
    intro u hu y z
    have h1 := hwire u hu y z C.output
    have h2 : (wiresOf C.gates (inpVec (u + φ y z) y z)).getD C.output false =
        C.eval (inpVec (u + φ y z) y z) := rfl
    rw [h2, heval, b2z_decide_eq_one, add_dotProduct] at h1
    exact h1
  have h0 : (0 : Fin k → F) ∈ U := U.zero_mem
  have hrel0 : ∀ y z, dotProduct (φ y z) y + g y z = Φ y z := by
    intro y z
    have h := hrel 0 h0 y z
    simpa [L] using h
  have hL : ∀ u ∈ U, ∀ y : Fin k → F, dotProduct u y = L u := by
    intro u hu y
    have hz0 : Fin t → F := 0
    have h1 := hrel u hu y hz0
    have h2 := hrel0 y hz0
    rw [add_assoc, h2] at h1
    have h3 : dotProduct u y + Φ y hz0 + Φ y hz0 = L u + Φ y hz0 + Φ y hz0 := by
      rw [h1]
    rw [add_assoc, zmod2_add_self, add_zero, add_assoc, zmod2_add_self, add_zero] at h3
    exact h3
  have hL_zero : ∀ u ∈ U, L u = 0 := by
    intro u hu
    have h := hL u hu 0
    simpa using h.symm
  have hU_bot : U = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    change u = 0
    ext i
    have h := hL u hu (Pi.single i 1)
    rw [hL_zero u hu] at h
    simpa [dotProduct, Pi.single_apply] using h
  have hrank : Module.finrank F U = 0 := by
    rw [hU_bot]
    exact finrank_bot F (Fin k → F)
  have hrk : r = k := by omega
  have hqle : q ≤ 1 := by omega
  have hg_eq : ∀ y z, g y z = Φ y z + dotProduct (φ y z) y := by
    intro y z
    have h := hrel0 y z
    have h2 : dotProduct (φ y z) y + g y z + dotProduct (φ y z) y =
        Φ y z + dotProduct (φ y z) y := by
      rw [h]
    rw [add_comm (dotProduct (φ y z) y) (g y z), add_assoc, zmod2_add_self, add_zero] at h2
    exact h2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hqle with hqz | hqo
  · obtain ⟨hφ, hpw⟩ := hq0 hqz
    refine ⟨Φ, fun _ _ => 0, fun _ _ => 0, fun i y z => φ y z i, 0, 0,
      hpw C.output, affFun_zero, affFun_zero, hφ, fun y z => ?_⟩
    rw [hg_eq]
    simp only [dotProduct, add_zero, mul_zero]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · obtain ⟨hu0, hv0, hφ, hpw⟩ := hq1 hqo
    obtain ⟨f, b, hfa, hfe⟩ := hpw C.output
    have hpc : ∀ i : Fin k, ∃ (pi : (Fin k → F) → (Fin t → F) → F) (ai : F),
        affFun pi ∧ ∀ y z, φ y z i = pi y z + ai * u0 y z * v0 y z := hφ
    choose p a hpa hpe using hpc
    refine ⟨f, u0, v0, p, a, b, hfa, hu0, hv0, hpa, fun y z => ?_⟩
    rw [hg_eq]
    dsimp only [Φ]
    rw [hfe]
    have hdot : dotProduct (φ y z) y =
        (∑ i : Fin k, y i * p i y z) + dotProduct a y * u0 y z * v0 y z := by
      simp only [dotProduct]
      calc ∑ i : Fin k, φ y z i * y i
          = ∑ i : Fin k, (p i y z * y i + a i * y i * (u0 y z * v0 y z)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hpe i y z]
              ring
        _ = (∑ i : Fin k, p i y z * y i) + ∑ i : Fin k, a i * y i * (u0 y z * v0 y z) :=
              Finset.sum_add_distrib
        _ = (∑ i : Fin k, y i * p i y z) + (∑ i : Fin k, a i * y i) * (u0 y z * v0 y z) := by
              congr 1
              · refine Finset.sum_congr rfl fun i _ => mul_comm _ _
              · rw [← Finset.sum_mul]
        _ = (∑ i : Fin k, y i * p i y z) + dotProduct a y * u0 y z * v0 y z := by
              simp [dotProduct, mul_assoc]
    rw [hdot]
    ring

def ValidPrefix (n : ℕ) (gs : List Gate) : Prop :=
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨.or, []⟩).inputs, i < n + j) ∧
  (∀ h ∈ gs, LegalGate h)

lemma validPrefix_nil (n : ℕ) : ValidPrefix n [] :=
  ⟨fun _ hj => by simp at hj, fun _ hh => by simp at hh⟩

lemma validPrefix_readsBack {n : ℕ} {C : Circuit} (h : ValidPrefix n C.gates) :
    ReadsBack n C := fun j hj i hi => h.1 j hj i hi

lemma validPrefix_append_singleton {n : ℕ} {gs : List Gate} {g : Gate}
    (hgs : ValidPrefix n gs) (hg : LegalGate g)
    (hinp : ∀ i ∈ g.inputs, i < n + gs.length) :
    ValidPrefix n (gs ++ [g]) := by
  refine ⟨fun j hj i hi => ?_, fun h hh => ?_⟩
  · by_cases hjlt : j < gs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjlt] at hi
      exact hgs.1 j hjlt i hi
    · have hjeq : j = gs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst hjeq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self] at hi
      simp only [List.getElem?_cons_zero, Option.getD_some] at hi
      exact hinp i hi
  · rcases List.mem_append.mp hh with h1 | h2
    · exact hgs.2 h h1
    · simp only [List.mem_singleton] at h2
      subst h2
      exact hg

def Extends (n : ℕ) (gs0 gs1 : List Gate) (dc : ℕ) : Prop :=
  (∃ suf, gs1 = gs0 ++ suf) ∧
  (ValidPrefix n gs0 → ValidPrefix n gs1) ∧
  gateCost gs1 = gateCost gs0 + dc

lemma extends_refl (n : ℕ) (gs : List Gate) : Extends n gs gs 0 :=
  ⟨⟨[], by simp⟩, fun h => h, by simp⟩

lemma extends_trans {n : ℕ} {gs0 gs1 gs2 : List Gate} {d1 d2 : ℕ}
    (h1 : Extends n gs0 gs1 d1) (h2 : Extends n gs1 gs2 d2) :
    Extends n gs0 gs2 (d1 + d2) := by
  rcases h1 with ⟨⟨s1, rfl⟩, hv1, hc1⟩
  rcases h2 with ⟨⟨s2, rfl⟩, hv2, hc2⟩
  refine ⟨⟨s1 ++ s2, by simp [List.append_assoc]⟩, fun h => hv2 (hv1 h), ?_⟩
  omega

lemma extends_len {n : ℕ} {gs0 gs1 : List Gate} {dc : ℕ}
    (h : Extends n gs0 gs1 dc) : gs0.length ≤ gs1.length := by
  rcases h.1 with ⟨suf, rfl⟩
  simp

lemma extends_wire {n : ℕ} {gs0 gs1 : List Gate} {dc : ℕ}
    (h : Extends n gs0 gs1 dc) {inp : List Bool} (hinp : inp.length = n)
    {w : ℕ} (hw : w < n + gs0.length) :
    (wiresOf gs1 inp).getD w false = (wiresOf gs0 inp).getD w false := by
  rcases h.1 with ⟨suf, rfl⟩
  exact wiresOf_append_getD gs0 suf inp w (by rw [hinp]; exact hw)

def addGate (n : ℕ) (gs : List Gate) (g : Gate) : List Gate × ℕ :=
  (gs ++ [g], n + gs.length)

lemma addGate_extends {n : ℕ} (gs : List Gate) (g : Gate)
    (hg : LegalGate g) (hinp : ∀ i ∈ g.inputs, i < n + gs.length) :
    Extends n gs (addGate n gs g).1 (if isPaid g = true then 1 else 0) :=
  ⟨⟨[g], rfl⟩, fun h => validPrefix_append_singleton h hg hinp,
    gateCost_append_singleton gs g⟩

lemma addGate_lt {n : ℕ} (gs : List Gate) (g : Gate) :
    (addGate n gs g).2 < n + (addGate n gs g).1.length := by
  simp [addGate]

lemma addGate_val {n : ℕ} (gs : List Gate) (g : Gate) {inp : List Bool}
    (hinp : inp.length = n) :
    b2z ((wiresOf (addGate n gs g).1 inp).getD (addGate n gs g).2 false) =
      b2z (g.op.eval (g.inputs.map fun i => (wiresOf gs inp).getD i false)) := by
  simp only [addGate]
  rw [wiresOf_append_val gs g inp hinp]

lemma isPaid_empty (op : GateOp) : isPaid ⟨op, []⟩ = false := by
  simp [isPaid]

lemma isPaid_mod2 (ws : List ℕ) : isPaid ⟨.mod 2, ws⟩ = false := by
  simp [isPaid]

lemma isPaid_not (w : ℕ) : isPaid ⟨.not, [w]⟩ = false := by
  simp [isPaid]

lemma isPaid_and2 (w1 w2 : ℕ) : isPaid ⟨.and, [w1, w2]⟩ = true := by
  simp [isPaid]

def mkConst (n : ℕ) (gs : List Gate) (c : F) : List Gate × ℕ :=
  if c = 0 then addGate n gs ⟨.or, []⟩ else addGate n gs ⟨.and, []⟩

lemma mkConst_spec (n : ℕ) (gs : List Gate) (c : F) :
    Extends n gs (mkConst n gs c).1 0 ∧
    (mkConst n gs c).2 < n + (mkConst n gs c).1.length ∧
    ∀ {inp : List Bool}, inp.length = n →
      b2z ((wiresOf (mkConst n gs c).1 inp).getD (mkConst n gs c).2 false) = c := by
  rcases zmod2_cases c with rfl | rfl
  · simp only [mkConst, ↓reduceIte]
    refine ⟨?_, addGate_lt _ _, fun hinp => ?_⟩
    · simpa [isPaid_empty] using addGate_extends gs ⟨.or, []⟩
        ⟨by simp, Or.inr (Or.inl rfl)⟩ (by simp)
    · rw [addGate_val gs _ hinp]
      simp [GateOp.eval, b2z]
  · simp only [mkConst, show (1 : F) ≠ 0 by decide, ↓reduceIte]
    refine ⟨?_, addGate_lt _ _, fun hinp => ?_⟩
    · simpa [isPaid_empty] using addGate_extends gs ⟨.and, []⟩
        ⟨by simp, Or.inl rfl⟩ (by simp)
    · rw [addGate_val gs _ hinp]
      simp [GateOp.eval, b2z]

def mkXor (n : ℕ) (gs : List Gate) (w1 w2 : ℕ) : List Gate × ℕ :=
  let r1 := addGate n gs ⟨.mod 2, [w1, w2]⟩
  addGate n r1.1 ⟨.not, [r1.2]⟩

lemma mkXor_spec {n : ℕ} (gs : List Gate) {w1 w2 : ℕ}
    (hw1 : w1 < n + gs.length) (hw2 : w2 < n + gs.length) :
    Extends n gs (mkXor n gs w1 w2).1 0 ∧
    (mkXor n gs w1 w2).2 < n + (mkXor n gs w1 w2).1.length ∧
    ∀ {inp : List Bool}, inp.length = n →
      b2z ((wiresOf (mkXor n gs w1 w2).1 inp).getD (mkXor n gs w1 w2).2 false) =
        b2z ((wiresOf gs inp).getD w1 false) + b2z ((wiresOf gs inp).getD w2 false) := by
  let r1 := addGate n gs ⟨.mod 2, [w1, w2]⟩
  have hr1_ext : Extends n gs r1.1 0 := by
    have h := @addGate_extends n gs ⟨.mod 2, [w1, w2]⟩
      ⟨by simp, Or.inr (Or.inr (Or.inl rfl))⟩ (by simp [hw1, hw2])
    simpa [isPaid_mod2] using h
  have hr1_lt : r1.2 < n + r1.1.length := addGate_lt gs _
  have hr2_ext : Extends n r1.1 (addGate n r1.1 ⟨.not, [r1.2]⟩).1 0 := by
    have h := @addGate_extends n r1.1 ⟨.not, [r1.2]⟩
      ⟨by simp, Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩ (by simp [hr1_lt])
    simpa [isPaid_not] using h
  refine ⟨extends_trans hr1_ext hr2_ext, addGate_lt r1.1 _, fun {inp} hinp => ?_⟩
  change b2z ((wiresOf (addGate n r1.1 ⟨.not, [r1.2]⟩).1 inp).getD
    (addGate n r1.1 ⟨.not, [r1.2]⟩).2 false) = _
  rw [addGate_val r1.1 _ hinp]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
  rw [b2z_not]
  rw [addGate_val gs _ hinp]
  simp only [List.map_cons, List.map_nil, GateOp.eval]
  rw [b2z_mod2_two]
  have htwo : (1 : F) + 1 = 0 := by decide
  calc
    b2z ((wiresOf gs inp).getD w1 false) + b2z ((wiresOf gs inp).getD w2 false) + 1 + 1
        = b2z ((wiresOf gs inp).getD w1 false) + b2z ((wiresOf gs inp).getD w2 false) +
            ((1 : F) + 1) := by ring
    _ = b2z ((wiresOf gs inp).getD w1 false) + b2z ((wiresOf gs inp).getD w2 false) := by
            rw [htwo, add_zero]

def mkAnd (n : ℕ) (gs : List Gate) (w1 w2 : ℕ) : List Gate × ℕ :=
  addGate n gs ⟨.and, [w1, w2]⟩

lemma mkAnd_spec {n : ℕ} (gs : List Gate) {w1 w2 : ℕ}
    (hw1 : w1 < n + gs.length) (hw2 : w2 < n + gs.length) :
    Extends n gs (mkAnd n gs w1 w2).1 1 ∧
    (mkAnd n gs w1 w2).2 < n + (mkAnd n gs w1 w2).1.length ∧
    ∀ {inp : List Bool}, inp.length = n →
      b2z ((wiresOf (mkAnd n gs w1 w2).1 inp).getD (mkAnd n gs w1 w2).2 false) =
        b2z ((wiresOf gs inp).getD w1 false) * b2z ((wiresOf gs inp).getD w2 false) := by
  refine ⟨?_, addGate_lt gs _, fun hinp => ?_⟩
  · have h := @addGate_extends n gs ⟨.and, [w1, w2]⟩
      ⟨by simp, Or.inl rfl⟩ (by simp [hw1, hw2])
    simpa [mkAnd, isPaid_and2] using h
  · dsimp only [mkAnd]
    rw [addGate_val gs _ hinp]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    exact b2z_and _ _

def mkXorList (n : ℕ) (gs : List Gate) : List ℕ → List Gate × ℕ
  | [] => mkConst n gs 0
  | w :: rest =>
    let r := mkXorList n gs rest
    mkXor n r.1 w r.2

lemma mkXorList_spec {n : ℕ} (gs : List Gate) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < n + gs.length) :
    Extends n gs (mkXorList n gs ws).1 0 ∧
    (mkXorList n gs ws).2 < n + (mkXorList n gs ws).1.length ∧
    ∀ {inp : List Bool}, inp.length = n →
      b2z ((wiresOf (mkXorList n gs ws).1 inp).getD (mkXorList n gs ws).2 false) =
        (ws.map fun w => b2z ((wiresOf gs inp).getD w false)).sum := by
  induction ws with
  | nil =>
    obtain ⟨hext, hlt, hval⟩ := mkConst_spec n gs 0
    refine ⟨hext, hlt, fun hinp => ?_⟩
    dsimp only [mkXorList]
    rw [hval hinp]
    simp
  | cons w rest ih =>
    have hw : w < n + gs.length := hws w List.mem_cons_self
    have hrest : ∀ u ∈ rest, u < n + gs.length := fun u hu => hws u (List.mem_cons_of_mem _ hu)
    obtain ⟨hext1, hlt1, hval1⟩ := ih hrest
    let r := mkXorList n gs rest
    have hw' : w < n + r.1.length :=
      Nat.lt_of_lt_of_le hw (Nat.add_le_add_left (extends_len hext1) n)
    obtain ⟨hext2, hlt2, hval2⟩ := mkXor_spec r.1 hw' hlt1
    refine ⟨extends_trans hext1 hext2, hlt2, fun {inp} hinp => ?_⟩
    change b2z ((wiresOf (mkXor n r.1 w r.2).1 inp).getD (mkXor n r.1 w r.2).2 false) = _
    rw [hval2 hinp, extends_wire hext1 hinp hw, hval1 hinp]
    simp

lemma sum_map_filterMap_wires {α : Type*} (L : List α) (a : α → F) (idx : α → ℕ) (val : ℕ → F) :
    (((L.filterMap fun i => if a i = 1 then some (idx i) else none)).map val).sum =
      (L.map fun i => a i * val (idx i)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rcases zmod2_cases (a x) with hx | hx
    · simp [hx, ih]
    · simp [hx, ih]

lemma sum_map_finRange {n : ℕ} (f : Fin n → F) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.map_cons, List.map_map, List.sum_cons, Fin.sum_univ_succ]
    exact congrArg (f 0 + ·) (ih _)

lemma wiresOf_ext_inp {gs : List Gate} {x y : Fin k → F} {z : Fin t → F}
    {w : ℕ} (hw : w < 2 * k + t) :
    (wiresOf gs (inpVec x y z)).getD w false = (inpVec x y z).getD w false := by
  have h := wiresOf_append_getD [] gs (inpVec x y z) w (by rw [inpVec_length]; simp; exact hw)
  simpa [wiresOf] using h

def mkAffine (k t : ℕ) (gs : List Gate) (c : F) (a : Fin k → F) (b : Fin t → F) :
    List Gate × ℕ :=
  let n := 2 * k + t
  let rc := mkConst n gs c
  let wsY : List ℕ :=
    (List.finRange k).filterMap (fun i => if a i = 1 then some (k + i.val) else none)
  let wsZ : List ℕ :=
    (List.finRange t).filterMap (fun j => if b j = 1 then some (2 * k + j.val) else none)
  mkXorList n rc.1 (rc.2 :: (wsY ++ wsZ))

lemma mkAffine_spec {k t : ℕ} (gs : List Gate) (c : F) (a : Fin k → F) (b : Fin t → F) :
    Extends (2 * k + t) gs (mkAffine k t gs c a b).1 0 ∧
    (mkAffine k t gs c a b).2 < 2 * k + t + (mkAffine k t gs c a b).1.length ∧
    ∀ (x y : Fin k → F) (z : Fin t → F),
      b2z ((wiresOf (mkAffine k t gs c a b).1 (inpVec x y z)).getD
        (mkAffine k t gs c a b).2 false) = c + dotProduct a y + dotProduct b z := by
  let n := 2 * k + t
  let rc := mkConst n gs c
  let wsY : List ℕ :=
    (List.finRange k).filterMap (fun i => if a i = 1 then some (k + i.val) else none)
  let wsZ : List ℕ :=
    (List.finRange t).filterMap (fun j => if b j = 1 then some (2 * k + j.val) else none)
  obtain ⟨hcext, hclt, hcval⟩ := mkConst_spec n gs c
  have hws : ∀ w ∈ rc.2 :: (wsY ++ wsZ), w < n + rc.1.length := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hclt
    · rcases List.mem_append.mp hw with hwY | hwZ
      · simp only [wsY, List.mem_filterMap] at hwY
        rcases hwY with ⟨i, _, hi⟩
        split_ifs at hi with h
        simp only [Option.some.injEq] at hi
        subst hi
        omega
      · simp only [wsZ, List.mem_filterMap] at hwZ
        rcases hwZ with ⟨j, _, hj⟩
        split_ifs at hj with h
        simp only [Option.some.injEq] at hj
        subst hj
        omega
  obtain ⟨hxext, hxlt, hxval⟩ := mkXorList_spec rc.1 (rc.2 :: (wsY ++ wsZ)) hws
  refine ⟨extends_trans hcext hxext, hxlt, fun x y z => ?_⟩
  change b2z ((wiresOf (mkXorList n rc.1 (rc.2 :: (wsY ++ wsZ))).1 (inpVec x y z)).getD
    (mkXorList n rc.1 (rc.2 :: (wsY ++ wsZ))).2 false) = _
  rw [hxval (inpVec_length x y z)]
  simp only [List.map_cons, List.map_append, List.sum_cons, List.sum_append]
  rw [hcval (inpVec_length x y z)]
  have hY : (wsY.map fun w => b2z ((wiresOf rc.1 (inpVec x y z)).getD w false)).sum =
      dotProduct a y := by
    simp only [wsY]
    rw [sum_map_filterMap_wires]
    have hcongr : (List.finRange k).map
        (fun i => a i * b2z ((wiresOf rc.1 (inpVec x y z)).getD (k + i.val) false)) =
        (List.finRange k).map (fun i => a i * y i) := by
      refine List.map_congr_left fun i _ => ?_
      rw [wiresOf_ext_inp (by omega), getD_inpVec_y x y z (k + i.val) (by omega) (by omega)]
      congr 2
      ext
      simp
    rw [hcongr, sum_map_finRange]
    rfl
  have hZ : (wsZ.map fun w => b2z ((wiresOf rc.1 (inpVec x y z)).getD w false)).sum =
      dotProduct b z := by
    simp only [wsZ]
    rw [sum_map_filterMap_wires]
    have hcongr : (List.finRange t).map
        (fun j => b j * b2z ((wiresOf rc.1 (inpVec x y z)).getD (2 * k + j.val) false)) =
        (List.finRange t).map (fun j => b j * z j) := by
      refine List.map_congr_left fun j _ => ?_
      rw [wiresOf_ext_inp (by omega), getD_inpVec_z x y z (2 * k + j.val) (by omega) (by omega)]
      congr 2
      ext
      simp
    rw [hcongr, sum_map_finRange]
    rfl
  rw [hY, hZ]
  ring

def buildTerms (k t : ℕ) (cp : Fin k → F) (ap : Fin k → Fin k → F)
    (bp : Fin k → Fin t → F) (a : Fin k → F) (wuv : ℕ) :
    List Gate → List (Fin k) → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, i :: rest =>
    let n := 2 * k + t
    let rp := mkAffine k t gs (cp i) (ap i) (bp i)
    let ws := [i.val, rp.2] ++ (if a i = 1 then [wuv] else [])
    let rq := mkXorList n rp.1 ws
    let rm := mkAnd n rq.1 (k + i.val) rq.2
    let rrest := buildTerms k t cp ap bp a wuv rm.1 rest
    (rrest.1, rm.2 :: rrest.2)

lemma buildTerms_spec {k t : ℕ} (cp : Fin k → F) (ap : Fin k → Fin k → F)
    (bp : Fin k → Fin t → F) (a : Fin k → F) (wuv : ℕ)
    (gs : List Gate) (l : List (Fin k))
    (hwuv : wuv < 2 * k + t + gs.length) :
    Extends (2 * k + t) gs (buildTerms k t cp ap bp a wuv gs l).1 l.length ∧
    (∀ w ∈ (buildTerms k t cp ap bp a wuv gs l).2,
      w < 2 * k + t + (buildTerms k t cp ap bp a wuv gs l).1.length) ∧
    ∀ (x y : Fin k → F) (z : Fin t → F),
      ((buildTerms k t cp ap bp a wuv gs l).2.map fun w =>
        b2z ((wiresOf (buildTerms k t cp ap bp a wuv gs l).1 (inpVec x y z)).getD w false)).sum =
        (l.map fun i => y i * (x i + (cp i + dotProduct (ap i) y + dotProduct (bp i) z) +
          a i * b2z ((wiresOf gs (inpVec x y z)).getD wuv false))).sum := by
  induction l generalizing gs with
  | nil =>
    refine ⟨extends_refl _ _, fun _ hw => by simp [buildTerms] at hw, fun _ _ _ => by simp [buildTerms]⟩
  | cons i rest ih =>
    let n := 2 * k + t
    let rp := mkAffine k t gs (cp i) (ap i) (bp i)
    let ws := [i.val, rp.2] ++ (if a i = 1 then [wuv] else [])
    let rq := mkXorList n rp.1 ws
    let rm := mkAnd n rq.1 (k + i.val) rq.2
    let rrest := buildTerms k t cp ap bp a wuv rm.1 rest
    obtain ⟨hpext, hplt, hpval⟩ := mkAffine_spec gs (cp i) (ap i) (bp i)
    have hwuv_rp : wuv < n + rp.1.length :=
      Nat.lt_of_lt_of_le hwuv (Nat.add_le_add_left (extends_len hpext) n)
    have hws : ∀ w ∈ ws, w < n + rp.1.length := by
      intro w hw
      simp only [ws, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with (rfl | rfl) | htail
      · omega
      · exact hplt
      · split_ifs at htail with hai
        · simp only [List.mem_singleton] at htail
          subst htail
          exact hwuv_rp
        · simp at htail
    obtain ⟨hqext, hqlt, hqval⟩ := mkXorList_spec rp.1 ws hws
    have hy_lt : k + i.val < n + rq.1.length := by omega
    obtain ⟨hmext, hmlt, hmval⟩ := mkAnd_spec rq.1 hy_lt hqlt
    have hext_step : Extends n gs rm.1 1 := by
      have h1 := extends_trans hpext hqext
      have h2 := extends_trans h1 hmext
      simpa using h2
    have hwuv_rm : wuv < n + rm.1.length :=
      Nat.lt_of_lt_of_le hwuv (Nat.add_le_add_left (extends_len hext_step) n)
    obtain ⟨hrext, hrlt, hrval⟩ := ih rm.1 hwuv_rm
    refine ⟨?_, fun w hw => ?_, fun x y z => ?_⟩
    · dsimp only [buildTerms]
      rw [List.length_cons, Nat.add_comm rest.length 1]
      exact extends_trans hext_step hrext
    · simp only [buildTerms, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact Nat.lt_of_lt_of_le hmlt (Nat.add_le_add_left (extends_len hrext) n)
      · exact hrlt w hw
    · change b2z ((wiresOf rrest.1 (inpVec x y z)).getD rm.2 false) +
          (rrest.2.map fun w => b2z ((wiresOf rrest.1 (inpVec x y z)).getD w false)).sum = _
      rw [extends_wire hrext (inpVec_length x y z) hmlt, hrval x y z]
      rw [hmval (inpVec_length x y z)]
      have hy_val : b2z ((wiresOf rq.1 (inpVec x y z)).getD (k + i.val) false) = y i := by
        rw [wiresOf_ext_inp (by omega), getD_inpVec_y x y z (k + i.val) (by omega) (by omega)]
        exact congrArg y (Fin.ext (by simp))
      have hq_val : b2z ((wiresOf rq.1 (inpVec x y z)).getD rq.2 false) =
          x i + (cp i + dotProduct (ap i) y + dotProduct (bp i) z) +
            a i * b2z ((wiresOf gs (inpVec x y z)).getD wuv false) := by
        rw [hqval (inpVec_length x y z)]
        simp only [ws, List.map_append, List.map_cons, List.map_nil, List.sum_append,
          List.sum_cons, List.sum_nil, add_zero]
        have hx_val : b2z ((wiresOf rp.1 (inpVec x y z)).getD i.val false) = x i := by
          rw [wiresOf_ext_inp (by omega), getD_inpVec_x x y z i.val i.isLt]
        have hwuv_val :
            (if a i = 1 then
              [b2z ((wiresOf rp.1 (inpVec x y z)).getD wuv false)]
            else []).sum =
              a i * b2z ((wiresOf gs (inpVec x y z)).getD wuv false) := by
          rcases zmod2_cases (a i) with hai | hai
          · simp [hai]
          · have hite : (if (1 : F) = 1 then
                [b2z ((wiresOf rp.1 (inpVec x y z)).getD wuv false)]
              else []) = [b2z ((wiresOf rp.1 (inpVec x y z)).getD wuv false)] := by simp
            rw [hai, hite, List.sum_singleton,
              extends_wire hpext (inpVec_length x y z) hwuv, one_mul]
        have hif : (if a i = 1 then [wuv] else []).map
            (fun w => b2z ((wiresOf rp.1 (inpVec x y z)).getD w false)) =
            if a i = 1 then [b2z ((wiresOf rp.1 (inpVec x y z)).getD wuv false)] else [] := by
          split_ifs <;> simp
        rw [hif, hx_val, hpval x y z, hwuv_val]
      have hcongr_rest :
          (rest.map fun j => y j * (x j + (cp j + dotProduct (ap j) y + dotProduct (bp j) z) +
            a j * b2z ((wiresOf rm.1 (inpVec x y z)).getD wuv false))).sum =
          (rest.map fun j => y j * (x j + (cp j + dotProduct (ap j) y + dotProduct (bp j) z) +
            a j * b2z ((wiresOf gs (inpVec x y z)).getD wuv false))).sum := by
        congr 1
        refine List.map_congr_left fun j _ => ?_
        rw [extends_wire hext_step (inpVec_length x y z) hwuv]
      rw [hy_val, hq_val, hcongr_rest]
      simp

lemma eq_decide_of_b2z_eq {B : Bool} {t : F} (h : b2z B = t) : B = decide (t = 1) := by
  subst h
  revert B
  decide

lemma backward_dir {k t : ℕ} (g : (Fin k → F) → (Fin t → F) → F)
    (f u v : (Fin k → F) → (Fin t → F) → F)
    (p : Fin k → (Fin k → F) → (Fin t → F) → F) (a : Fin k → F) (b : F)
    (hf : affFun f) (hu : affFun u) (hv : affFun v) (hp : ∀ i, affFun (p i))
    (hg : ∀ y z, g y z = f y z + (∑ i : Fin k, y i * p i y z) +
      (b + dotProduct a y) * u y z * v y z) :
    ∃ C : Circuit, ReadsBack (2 * k + t) C ∧
      (∀ h ∈ C.gates, LegalGate h) ∧
      gateCost C.gates ≤ k + 1 ∧
      ∀ x y z, C.eval (inpVec x y z) = decide (dotProduct x y + g y z = 1) := by
  rcases hf with ⟨af, bf, cf, hfe⟩
  rcases hu with ⟨au, bu, cu, hue⟩
  rcases hv with ⟨av, bv, cv, hve⟩
  choose ap bp cp hpe using hp
  let n := 2 * k + t
  let r1 := mkAffine k t [] cf af bf
  let r2 := mkAffine k t r1.1 cu au bu
  let r3 := mkAffine k t r2.1 cv av bv
  obtain ⟨h1ext, h1lt, h1val⟩ := mkAffine_spec ([] : List Gate) cf af bf
  obtain ⟨h2ext, h2lt, h2val⟩ := mkAffine_spec r1.1 cu au bu
  obtain ⟨h3ext, h3lt, h3val⟩ := mkAffine_spec r2.1 cv av bv
  have h1ext_3 : Extends n [] r3.1 0 := extends_trans h1ext (extends_trans h2ext h3ext)
  have h2ext_3 : Extends n r1.1 r3.1 0 := extends_trans h2ext h3ext
  have hw_u : r2.2 < n + r3.1.length :=
    Nat.lt_of_lt_of_le h2lt (Nat.add_le_add_left (extends_len h3ext) n)
  let r4 := mkAnd n r3.1 r2.2 r3.2
  obtain ⟨h4ext, h4lt, h4val⟩ := mkAnd_spec r3.1 hw_u h3lt
  have h1ext_4 : Extends n [] r4.1 1 := by simpa using extends_trans h1ext_3 h4ext
  let r5 := buildTerms k t cp ap bp a r4.2 r4.1 (List.finRange k)
  obtain ⟨h5ext, h5lt, h5val⟩ := buildTerms_spec cp ap bp a r4.2 r4.1 (List.finRange k) h4lt
  have h1ext_5 : Extends n [] r5.1 (1 + k) := by
    simpa [List.length_finRange] using extends_trans h1ext_4 h5ext
  have hwf_5 : r1.2 < n + r5.1.length :=
    Nat.lt_of_lt_of_le h1lt (Nat.add_le_add_left (extends_len (extends_trans h2ext_3 (extends_trans h4ext h5ext))) n)
  have hwuv_5 : r4.2 < n + r5.1.length :=
    Nat.lt_of_lt_of_le h4lt (Nat.add_le_add_left (extends_len h5ext) n)
  let finalWs := [r1.2] ++ (if b = 1 then [r4.2] else []) ++ r5.2
  have hfinalWs : ∀ w ∈ finalWs, w < n + r5.1.length := by
    intro w hw
    simp only [finalWs, List.mem_append, List.mem_singleton] at hw
    rcases hw with (rfl | hmid) | htail
    · exact hwf_5
    · split_ifs at hmid with hb
      · simp only [List.mem_singleton] at hmid
        subst hmid
        exact hwuv_5
      · simp at hmid
    · exact h5lt w htail
  let r6 := mkXorList n r5.1 finalWs
  obtain ⟨h6ext, _, h6val⟩ := mkXorList_spec r5.1 finalWs hfinalWs
  have htotal : Extends n [] r6.1 (k + 1) := by
    simpa [Nat.add_comm 1 k] using extends_trans h1ext_5 h6ext
  have hvp : ValidPrefix n r6.1 := htotal.2.1 (validPrefix_nil n)
  refine ⟨⟨r6.1, r6.2⟩, validPrefix_readsBack hvp, hvp.2, ?_, fun x y z => ?_⟩
  · have hc := htotal.2.2
    simp only [gateCost, List.countP_nil, zero_add] at hc
    exact Nat.le_of_eq hc
  · apply eq_decide_of_b2z_eq
    change b2z ((wiresOf r6.1 (inpVec x y z)).getD r6.2 false) = _
    rw [h6val (inpVec_length x y z)]
    simp only [finalWs, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero]
    have hwf_val : b2z ((wiresOf r5.1 (inpVec x y z)).getD r1.2 false) = f y z := by
      have hext_1_5 : Extends n r1.1 r5.1 (1 + k) := by
        simpa [List.length_finRange] using extends_trans h2ext_3 (extends_trans h4ext h5ext)
      rw [extends_wire hext_1_5 (inpVec_length x y z) h1lt, h1val x y z, hfe]
    have hwuv_val : b2z ((wiresOf r4.1 (inpVec x y z)).getD r4.2 false) = u y z * v y z := by
      rw [h4val (inpVec_length x y z), extends_wire h3ext (inpVec_length x y z) h2lt,
        h2val x y z, h3val x y z, hue, hve]
    have hmid_val :
        ((if b = 1 then [r4.2] else []).map
          (fun w => b2z ((wiresOf r5.1 (inpVec x y z)).getD w false))).sum =
          b * (u y z * v y z) := by
      rcases zmod2_cases b with rfl | rfl
      · simp
      · have hite : (if (1 : F) = 1 then [r4.2] else []) = [r4.2] := by simp
        rw [hite, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero, extends_wire h5ext (inpVec_length x y z) h4lt, hwuv_val, one_mul]
    have h5_eq : (r5.2.map fun w => b2z ((wiresOf r5.1 (inpVec x y z)).getD w false)).sum =
        ∑ i : Fin k, y i * (x i + p i y z + a i * (u y z * v y z)) := by
      rw [h5val x y z, hwuv_val]
      have hcongr : (List.finRange k).map (fun i => y i * (x i + (cp i + dotProduct (ap i) y +
          dotProduct (bp i) z) + a i * (u y z * v y z))) =
          (List.finRange k).map (fun i => y i * (x i + p i y z + a i * (u y z * v y z))) := by
        refine List.map_congr_left fun i _ => ?_
        rw [hpe i y z]
      rw [hcongr, sum_map_finRange]
    rw [hwf_val, hmid_val, h5_eq, hg y z]
    have hsum_split : (∑ i : Fin k, y i * (x i + p i y z + a i * (u y z * v y z))) =
        dotProduct x y + (∑ i : Fin k, y i * p i y z) + dotProduct a y * u y z * v y z := by
      calc ∑ i : Fin k, y i * (x i + p i y z + a i * (u y z * v y z))
          = ∑ i : Fin k, (x i * y i + y i * p i y z + a i * y i * (u y z * v y z)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
        _ = (∑ i : Fin k, x i * y i) + (∑ i : Fin k, y i * p i y z) +
              ∑ i : Fin k, a i * y i * (u y z * v y z) := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ = dotProduct x y + (∑ i : Fin k, y i * p i y z) + dotProduct a y * u y z * v y z := by
              simp only [dotProduct, Finset.sum_mul, mul_assoc]
    rw [hsum_split]
    ring

end PEqualNP.Outside.L_meta_29764

theorem PEqualNP.Outside.L_meta_29764 : (∀ (k t : ℕ),
  let Circ := PEqualNP.CircuitLowerBounds.Circuit
  let F := ZMod 2
  let legal := fun (n : ℕ) (C : Circ) =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧
      (∀ h ∈ C.gates, h.inputs.length ≤ 2 ∧
        (h.op = .and ∨ h.op = .or ∨ h.op = .mod 2 ∨ (h.op = .not ∧ h.inputs.length = 1)))
  let cost := fun (C : Circ) => C.gates.countP (fun h => @decide
    ((h.op = .and ∨ h.op = .or) ∧ h.inputs.length = 2) (Classical.propDecidable _))
  let bits := fun (n : ℕ) (u : Fin n → F) => List.ofFn (fun j : Fin n => decide (u j = 1))
  let V := Fin k → F
  let Z := Fin t → F
  let fits := fun (g : V → Z → F) (s : ℕ) =>
    ∃ C : Circ, legal (2*k+t) C ∧ cost C ≤ s ∧
      ∀ (x y : V) (z : Z), C.eval (bits k x ++ bits k y ++ bits t z) =
        decide (dotProduct x y + g y z = 1)
  let aff := fun (f : V → Z → F) =>
    ∃ (a : V) (b : Z) (c : F), ∀ y z, f y z = c + dotProduct a y + dotProduct b z
  ∀ g : V → Z → F, fits g (k+1) ↔
    ∃ (f u v : V → Z → F) (p : Fin k → V → Z → F) (a : V) (b : F),
      aff f ∧ aff u ∧ aff v ∧ (∀ i, aff (p i)) ∧
      ∀ y z, g y z = f y z + (∑ i : Fin k, y i * p i y z) +
        (b + dotProduct a y) * u y z * v y z) := by
  intro k t
  dsimp only
  intro g
  constructor
  · rintro ⟨C, ⟨_, hlegal⟩, hcost, heval⟩
    exact PEqualNP.Outside.L_meta_29764.forward_dir g C hlegal hcost heval
  · rintro ⟨f, u, v, p, a, b, hf, hu, hv, hp, hg⟩
    obtain ⟨C, hrb, hlegal, hcost, heval⟩ :=
      PEqualNP.Outside.L_meta_29764.backward_dir g f u v p a b hf hu hv hp hg
    exact ⟨C, ⟨hrb, hlegal⟩, hcost, heval⟩
