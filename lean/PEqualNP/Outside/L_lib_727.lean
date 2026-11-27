import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_727

lemma zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  fin_cases c <;> rfl

lemma zmod2_vec_add_self {k : ℕ} (x : Fin k → ZMod 2) : x + x = 0 := by
  ext i
  exact zmod2_add_self (x i)

lemma zmod2_mat_add_self {k : ℕ} (M : Matrix (Fin k) (Fin k) (ZMod 2)) : M + M = 0 := by
  ext i j
  exact zmod2_add_self (M i j)

lemma rank_add_le {k : ℕ} (A B : Matrix (Fin k) (Fin k) (ZMod 2)) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hmul : (A + B).mulVecLin = A.mulVecLin + B.mulVecLin := by
    apply LinearMap.ext
    intro x
    ext i
    simp
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro y ⟨x, rfl⟩
    rw [hmul, LinearMap.add_apply]
    exact Submodule.add_mem_sup (LinearMap.mem_range.mpr ⟨x, rfl⟩)
      (LinearMap.mem_range.mpr ⟨x, rfl⟩)
  calc
    (A + B).rank = Module.finrank (ZMod 2) (LinearMap.range (A + B).mulVecLin) := rfl
    _ ≤ Module.finrank (ZMod 2) ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin) :=
      Submodule.finrank_mono hle
    _ ≤ Module.finrank (ZMod 2) (LinearMap.range A.mulVecLin) +
        Module.finrank (ZMod 2) (LinearMap.range B.mulVecLin) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _

lemma forward_dir (k p q r : ℕ) (A B C : Matrix (Fin k) (Fin k) (ZMod 2))
    (hA : A.rank = k) (hB : B.rank = k) (hAB : (A + B).rank = k)
    (hC : C.rank ≤ p) (hAC : (A + C).rank ≤ q) (hBC : (B + C).rank ≤ r) :
    k ≤ p + q ∧ k ≤ p + r ∧ k ≤ q + r := by
  have h1 : A = C + (A + C) := by
    calc
      A = (C + C) + A := by rw [zmod2_mat_add_self C, zero_add]
      _ = C + (A + C) := by abel
  have h2 : B = C + (B + C) := by
    calc
      B = (C + C) + B := by rw [zmod2_mat_add_self C, zero_add]
      _ = C + (B + C) := by abel
  have h3 : A + B = (A + C) + (B + C) := by
    calc
      A + B = A + (C + C) + B := by rw [zmod2_mat_add_self C, add_zero]
      _ = (A + C) + (B + C) := by ac_rfl
  refine ⟨?_, ?_, ?_⟩
  · have := rank_add_le C (A + C)
    rw [← h1, hA] at this
    omega
  · have := rank_add_le C (B + C)
    rw [← h2, hB] at this
    omega
  · have := rank_add_le (A + C) (B + C)
    rw [← h3, hAB] at this
    omega

def matrixOfLin {k : ℕ} (P : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Matrix (Fin k) (Fin k) (ZMod 2) :=
  fun i j => P (Pi.single j 1) i

lemma matrixOfLin_mulVecLin {k : ℕ}
    (P : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    (matrixOfLin P).mulVecLin = P := by
  apply LinearMap.ext
  intro x
  ext i
  change (matrixOfLin P).mulVec x i = P x i
  conv_rhs => rw [pi_eq_sum_univ x]
  rw [map_sum, Finset.sum_apply]
  simp only [Matrix.mulVec, dotProduct, matrixOfLin, map_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpi : (fun m => if j = m then (1 : ZMod 2) else 0) = Pi.single j 1 := by
    ext m
    simp [Pi.single_apply, eq_comm]
  rw [hpi, mul_comm]

lemma mul_mulVecLin {k : ℕ} (M N : Matrix (Fin k) (Fin k) (ZMod 2)) :
    (M * N).mulVecLin = M.mulVecLin.comp N.mulVecLin := by
  apply LinearMap.ext
  intro x
  ext i
  simp [Matrix.mulVec_mulVec]

lemma one_mulVecLin {k : ℕ} :
    (1 : Matrix (Fin k) (Fin k) (ZMod 2)).mulVecLin = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp

lemma add_mulVecLin {k : ℕ} (M N : Matrix (Fin k) (Fin k) (ZMod 2)) :
    (M + N).mulVecLin = M.mulVecLin + N.mulVecLin := by
  apply LinearMap.ext
  intro x
  ext i
  simp

lemma eq_of_mulVecLin_eq {k : ℕ} {M N : Matrix (Fin k) (Fin k) (ZMod 2)}
    (h : M.mulVecLin = N.mulVecLin) : M = N := by
  ext i j
  have h1 := congrFun (LinearMap.congr_fun h (Pi.single j 1)) i
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply] using h1

lemma bijective_of_rank_eq {k : ℕ} (M : Matrix (Fin k) (Fin k) (ZMod 2))
    (hM : M.rank = k) : Function.Bijective M.mulVecLin := by
  have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  have hrank : Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) = k := hM
  rw [hrank, Module.finrank_fin_fun] at hrn
  have hker0 : Module.finrank (ZMod 2) (LinearMap.ker M.mulVecLin) = 0 := by omega
  have hker : LinearMap.ker M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hker0
  have hinj : Function.Injective M.mulVecLin := LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

lemma inv_of_rank_eq {k : ℕ} (A : Matrix (Fin k) (Fin k) (ZMod 2))
    (hA : A.rank = k) :
    ∃ A_inv : Matrix (Fin k) (Fin k) (ZMod 2), A_inv * A = 1 ∧ A * A_inv = 1 := by
  have hbij := bijective_of_rank_eq A hA
  let e := LinearEquiv.ofBijective A.mulVecLin hbij
  refine ⟨matrixOfLin e.symm.toLinearMap, ?_, ?_⟩
  · apply eq_of_mulVecLin_eq
    rw [mul_mulVecLin, matrixOfLin_mulVecLin, one_mulVecLin]
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  · apply eq_of_mulVecLin_eq
    rw [mul_mulVecLin, matrixOfLin_mulVecLin, one_mulVecLin]
    apply LinearMap.ext
    intro x
    exact e.apply_symm_apply x

lemma rank_mul_left_of_bijective {k : ℕ} (A M : Matrix (Fin k) (Fin k) (ZMod 2))
    (hA : Function.Bijective A.mulVecLin) : (A * M).rank = M.rank := by
  let e := LinearEquiv.ofBijective A.mulVecLin hA
  have hrng : LinearMap.range (A * M).mulVecLin =
      (LinearMap.range M.mulVecLin).map e.toLinearMap := by
    rw [mul_mulVecLin, LinearMap.range_comp]
    rfl
  change Module.finrank (ZMod 2) (LinearMap.range (A * M).mulVecLin) =
    Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin)
  rw [hrng]
  exact LinearEquiv.finrank_map_eq e (LinearMap.range M.mulVecLin)

lemma finrank_comap_of_bijective {k : ℕ}
    (f : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2)) (hf : Function.Bijective f)
    (W : Submodule (ZMod 2) (Fin k → ZMod 2)) :
    Module.finrank (ZMod 2) (W.comap f) = Module.finrank (ZMod 2) W := by
  let e := LinearEquiv.ofBijective f hf
  have hmap : (W.comap f).map e.toLinearMap = W :=
    Submodule.map_comap_eq_of_surjective hf.2 W
  conv_rhs => rw [← hmap]
  exact (LinearEquiv.finrank_map_eq e (W.comap f)).symm

lemma step_U {k : ℕ} (T : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hT : Function.Bijective T)
    (h1T : Function.Bijective (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T))
    (U : Submodule (ZMod 2) (Fin k → ZMod 2))
    (hdisj : Disjoint U (U.map T))
    (hlt : 2 * Module.finrank (ZMod 2) U + 2 ≤ k) :
    ∃ U' : Submodule (ZMod 2) (Fin k → ZMod 2),
      Disjoint U' (U'.map T) ∧
      Module.finrank (ZMod 2) U' = Module.finrank (ZMod 2) U + 1 := by
  classical
  let W := U ⊔ U.map T
  let W₁ := W.comap T
  let W₂ := W.comap (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T)
  have hW_fin : Module.finrank (ZMod 2) W ≤ k - 2 := by
    have hadd := Submodule.finrank_add_le_finrank_add_finrank U (U.map T)
    have hmap : Module.finrank (ZMod 2) (U.map T) ≤ Module.finrank (ZMod 2) U :=
      Submodule.finrank_map_le T U
    dsimp only [W]
    omega
  have hW1_fin : Module.finrank (ZMod 2) W₁ ≤ k - 2 := by
    rw [finrank_comap_of_bijective T hT W]
    exact hW_fin
  have hW2_fin : Module.finrank (ZMod 2) W₂ ≤ k - 2 := by
    rw [finrank_comap_of_bijective (LinearMap.id + T) h1T W]
    exact hW_fin
  have hcard_sub : ∀ X : Submodule (ZMod 2) (Fin k → ZMod 2),
      (Finset.univ.filter (· ∈ X)).card = 2 ^ Module.finrank (ZMod 2) X := by
    intro X
    calc
      (Finset.univ.filter (· ∈ X)).card = Fintype.card ↥X :=
        (Fintype.card_subtype (fun x => x ∈ X)).symm
      _ = (Fintype.card (ZMod 2)) ^ Module.finrank (ZMod 2) ↥X :=
        Module.card_eq_pow_finrank
      _ = 2 ^ Module.finrank (ZMod 2) ↥X := by rw [ZMod.card]
  let S₀ : Finset (Fin k → ZMod 2) := Finset.univ.filter (· ∈ W)
  let S₁ : Finset (Fin k → ZMod 2) := Finset.univ.filter (· ∈ W₁)
  let S₂ : Finset (Fin k → ZMod 2) := Finset.univ.filter (· ∈ W₂)
  have hk2 : 2 ≤ k := by omega
  have hpow : 3 * 2 ^ (k - 2) < 2 ^ k := by
    have heq : 2 ^ k = 4 * 2 ^ (k - 2) := by
      calc
        2 ^ k = 2 ^ ((k - 2) + 2) := by rw [Nat.sub_add_cancel hk2]
        _ = 2 ^ (k - 2) * 2 ^ 2 := Nat.pow_add 2 (k - 2) 2
        _ = 4 * 2 ^ (k - 2) := by ring
    have hpos : 0 < 2 ^ (k - 2) := Nat.pos_of_ne_zero (by positivity)
    omega
  have hS_card : (S₀ ∪ S₁ ∪ S₂).card < Fintype.card (Fin k → ZMod 2) := by
    have hc0 : S₀.card ≤ 2 ^ (k - 2) := by
      dsimp only [S₀]
      rw [hcard_sub W]
      exact Nat.pow_le_pow_right (by norm_num) hW_fin
    have hc1 : S₁.card ≤ 2 ^ (k - 2) := by
      dsimp only [S₁]
      rw [hcard_sub W₁]
      exact Nat.pow_le_pow_right (by norm_num) hW1_fin
    have hc2 : S₂.card ≤ 2 ^ (k - 2) := by
      dsimp only [S₂]
      rw [hcard_sub W₂]
      exact Nat.pow_le_pow_right (by norm_num) hW2_fin
    have hcardV : Fintype.card (Fin k → ZMod 2) = 2 ^ k := by
      rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
    have hle : (S₀ ∪ S₁ ∪ S₂).card ≤ S₀.card + S₁.card + S₂.card := by
      calc
        (S₀ ∪ S₁ ∪ S₂).card ≤ (S₀ ∪ S₁).card + S₂.card := Finset.card_union_le _ _
        _ ≤ S₀.card + S₁.card + S₂.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    omega
  have hne : S₀ ∪ S₁ ∪ S₂ ≠ Finset.univ := by
    intro h
    rw [h] at hS_card
    exact Nat.lt_irrefl _ hS_card
  have hex : ∃ v : Fin k → ZMod 2, v ∉ S₀ ∪ S₁ ∪ S₂ := by
    by_contra h
    push Not at h
    exact hne (Finset.eq_univ_iff_forall.mpr h)
  obtain ⟨v, hv⟩ := hex
  have hvW : v ∉ W := by
    intro h
    apply hv
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩))
  have hvW1 : v ∉ W₁ := by
    intro h
    apply hv
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩))
  have hvW2 : v ∉ W₂ := by
    intro h
    apply hv
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ v, h⟩)
  have hvU : v ∉ U := fun h => hvW (Submodule.mem_sup_left h)
  have hv0 : v ≠ 0 := fun h => hvU (h ▸ U.zero_mem)
  refine ⟨U ⊔ Submodule.span (ZMod 2) {v}, ?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxU' hxTU'
    rw [Submodule.mem_sup] at hxU'
    obtain ⟨u₁, hu₁, w₁, hw₁, rfl⟩ := hxU'
    rw [Submodule.mem_span_singleton] at hw₁
    obtain ⟨c₁, rfl⟩ := hw₁
    rw [Submodule.mem_map] at hxTU'
    obtain ⟨y, hyU', hyx⟩ := hxTU'
    rw [Submodule.mem_sup] at hyU'
    obtain ⟨u₂, hu₂, w₂, hw₂, rfl⟩ := hyU'
    rw [Submodule.mem_span_singleton] at hw₂
    obtain ⟨c₂, rfl⟩ := hw₂
    rw [map_add, map_smul] at hyx
    rcases zmod2_cases c₁ with rfl | rfl <;> rcases zmod2_cases c₂ with rfl | rfl
    · simp only [zero_smul, add_zero] at hyx ⊢
      exact (Submodule.disjoint_def.mp hdisj) u₁ hu₁ ⟨u₂, hu₂, hyx⟩
    · simp only [zero_smul, add_zero, one_smul] at hyx
      exfalso
      apply hvW1
      change T v ∈ W
      have hTv : T v = u₁ - T u₂ := by
        rw [← hyx]
        abel
      rw [hTv]
      exact W.sub_mem (Submodule.mem_sup_left hu₁)
        (Submodule.mem_sup_right ⟨u₂, hu₂, rfl⟩)
    · simp only [one_smul, zero_smul, add_zero] at hyx
      exfalso
      apply hvW
      have hv_eq : v = T u₂ - u₁ := by
        rw [hyx]
        abel
      rw [hv_eq]
      exact W.sub_mem (Submodule.mem_sup_right ⟨u₂, hu₂, rfl⟩)
        (Submodule.mem_sup_left hu₁)
    · simp only [one_smul] at hyx
      exfalso
      apply hvW2
      change (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T) v ∈ W
      have h1Tv : (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T) v = v + T v := rfl
      have hsum : v + T v = T u₂ + u₁ := by
        have hadd : (u₁ + v) + (u₁ + T v) = (T u₂ + T v) + (u₁ + T v) := by rw [hyx]
        have hl : (u₁ + v) + (u₁ + T v) = v + T v := by
          calc
            (u₁ + v) + (u₁ + T v) = (u₁ + u₁) + (v + T v) := by abel
            _ = 0 + (v + T v) := by rw [zmod2_vec_add_self]
            _ = v + T v := zero_add _
        have hr : (T u₂ + T v) + (u₁ + T v) = T u₂ + u₁ := by
          calc
            (T u₂ + T v) + (u₁ + T v) = (T v + T v) + (T u₂ + u₁) := by abel
            _ = 0 + (T u₂ + u₁) := by rw [zmod2_vec_add_self]
            _ = T u₂ + u₁ := zero_add _
        rw [hl, hr] at hadd
        exact hadd
      rw [h1Tv, hsum]
      exact W.add_mem (Submodule.mem_sup_right ⟨u₂, hu₂, rfl⟩)
        (Submodule.mem_sup_left hu₁)
  · have hinf : U ⊓ Submodule.span (ZMod 2) {v} = ⊥ := by
      rw [eq_bot_iff]
      intro z ⟨hzU, hzspan⟩
      change z ∈ U at hzU
      change z ∈ Submodule.span (ZMod 2) {v} at hzspan
      rw [Submodule.mem_span_singleton] at hzspan
      obtain ⟨c, rfl⟩ := hzspan
      rcases zmod2_cases c with rfl | rfl
      · simp
      · rw [one_smul] at hzU
        exact absurd hzU hvU
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq U (Submodule.span (ZMod 2) {v})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0] at hsup
    exact hsup

lemma exists_disjoint_subspace {k : ℕ}
    (T : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hT : Function.Bijective T)
    (h1T : Function.Bijective (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T)) :
    ∀ d : ℕ, 2 * d ≤ k →
      ∃ U : Submodule (ZMod 2) (Fin k → ZMod 2),
        Module.finrank (ZMod 2) U = d ∧ Disjoint U (U.map T) := by
  intro d hd
  induction d with
  | zero =>
    refine ⟨⊥, finrank_bot _ _, ?_⟩
    rw [Submodule.map_bot]
    exact disjoint_bot_left
  | succ d ih =>
    obtain ⟨U, hUfin, hUdisj⟩ := ih (by omega)
    obtain ⟨U', hU'disj, hU'fin⟩ := step_U T hT h1T U hUdisj (by omega)
    exact ⟨U', by omega, hU'disj⟩

lemma aux_one (k p q r : ℕ) (hpq : p ≤ q) (hpr : p ≤ r)
    (hk_pq : k ≤ p + q) (hk_pr : k ≤ p + r)
    (T : Matrix (Fin k) (Fin k) (ZMod 2))
    (hT : T.rank = k) (h1T : (1 + T).rank = k) :
    ∃ C₀ : Matrix (Fin k) (Fin k) (ZMod 2),
      C₀.rank ≤ p ∧ (1 + C₀).rank ≤ q ∧ (T + C₀).rank ≤ r := by
  have hT_bij : Function.Bijective T.mulVecLin := bijective_of_rank_eq T hT
  have h1T_bij : Function.Bijective
      (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T.mulVecLin) := by
    have heq : LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T.mulVecLin =
        (1 + T).mulVecLin := by
      rw [add_mulVecLin, one_mulVecLin]
    rw [heq]
    exact bijective_of_rank_eq (1 + T) h1T
  let d := min p (k / 2)
  have hd_le : 2 * d ≤ k := by omega
  obtain ⟨U, hUfin, hUdisj⟩ := exists_disjoint_subspace T.mulVecLin hT_bij h1T_bij d hd_le
  let U₁ := U.map (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T.mulVecLin)
  let U₂ := U.map T.mulVecLin
  have hU12_disj : Disjoint U₁ U₂ := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    rw [Submodule.mem_map] at hx1 hx2
    obtain ⟨u₁, hu₁, rfl⟩ := hx1
    obtain ⟨u₂, hu₂, hu₂eq⟩ := hx2
    have hdiff : u₁ ∈ U₂ := by
      have hsub : T.mulVecLin (u₂ - u₁) = u₁ := by
        rw [map_sub, hu₂eq]
        change (u₁ + T.mulVecLin u₁) - T.mulVecLin u₁ = u₁
        calc
          (u₁ + T.mulVecLin u₁) - T.mulVecLin u₁ = u₁ + (T.mulVecLin u₁ - T.mulVecLin u₁) := by abel
          _ = u₁ + 0 := by rw [sub_self]
          _ = u₁ := add_zero u₁
      rw [← hsub]
      exact ⟨u₂ - u₁, U.sub_mem hu₂ hu₁, rfl⟩
    have hu1_zero : u₁ = 0 := (Submodule.disjoint_def.mp hUdisj) u₁ hu₁ hdiff
    rw [hu1_zero, map_zero]
  obtain ⟨R, hR⟩ := Submodule.exists_isCompl (U₁ ⊔ U₂)
  have hcomp : IsCompl U₂ (U₁ ⊔ R) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hx2 hx1R
      rw [Submodule.mem_sup] at hx1R
      obtain ⟨u₁, hu₁, t, ht, rfl⟩ := hx1R
      have ht12 : t ∈ U₁ ⊔ U₂ := by
        have ht_eq : t = (u₁ + t) - u₁ := by abel
        rw [ht_eq]
        exact (U₁ ⊔ U₂).sub_mem (Submodule.mem_sup_right hx2) (Submodule.mem_sup_left hu₁)
      have ht0 : t = 0 := (Submodule.disjoint_def.mp hR.disjoint) t ht12 ht
      rw [ht0, add_zero] at hx2 ⊢
      exact (Submodule.disjoint_def.mp hU12_disj) u₁ hu₁ hx2
    · rw [codisjoint_iff]
      calc
        U₂ ⊔ (U₁ ⊔ R) = (U₁ ⊔ U₂) ⊔ R := by
          rw [← sup_assoc, sup_comm U₂ U₁]
        _ = ⊤ := hR.codisjoint.eq_top
  let P : (Fin k → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) :=
    U₂.subtype.comp (U₂.projectionOnto (U₁ ⊔ R) hcomp)
  have hP_rng : LinearMap.range P ≤ U₂ := by
    rintro y ⟨x, rfl⟩
    exact (U₂.projectionOnto (U₁ ⊔ R) hcomp x).2
  have hP_on_U2 : ∀ y ∈ U₂, P y = y := by
    intro y hy
    change (U₂.projectionOnto (U₁ ⊔ R) hcomp y).1 = y
    have hproj := Submodule.projectionOnto_apply_left hcomp ⟨y, hy⟩
    exact congrArg Subtype.val hproj
  have hP_on_U1 : ∀ z ∈ U₁, P z = 0 := by
    intro z hz
    change (U₂.projectionOnto (U₁ ⊔ R) hcomp z).1 = 0
    have hz' : z ∈ U₁ ⊔ R := Submodule.mem_sup_left hz
    have hproj := Submodule.projectionOnto_apply_right hcomp ⟨z, hz'⟩
    exact congrArg Subtype.val hproj
  have hU2_fin : Module.finrank (ZMod 2) U₂ = d := by
    let e := LinearEquiv.ofBijective T.mulVecLin hT_bij
    change Module.finrank (ZMod 2) (U.map e.toLinearMap) = d
    rw [LinearEquiv.finrank_map_eq e U, hUfin]
  let C₀ := matrixOfLin P
  have hC0_lin : C₀.mulVecLin = P := matrixOfLin_mulVecLin P
  refine ⟨C₀, ?_, ?_, ?_⟩
  · change Module.finrank (ZMod 2) (LinearMap.range C₀.mulVecLin) ≤ p
    rw [hC0_lin]
    calc
      Module.finrank (ZMod 2) (LinearMap.range P) ≤ Module.finrank (ZMod 2) U₂ :=
        Submodule.finrank_mono hP_rng
      _ = d := hU2_fin
      _ ≤ p := min_le_left p (k / 2)
  · have hker : U₂ ≤ LinearMap.ker (1 + C₀).mulVecLin := by
      intro y hy
      rw [LinearMap.mem_ker, add_mulVecLin, one_mulVecLin, hC0_lin]
      change y + P y = 0
      rw [hP_on_U2 y hy, zmod2_vec_add_self]
    have hrn := LinearMap.finrank_range_add_finrank_ker (1 + C₀).mulVecLin
    rw [Module.finrank_fin_fun] at hrn
    have hle := Submodule.finrank_mono hker
    rw [hU2_fin] at hle
    change Module.finrank (ZMod 2) (LinearMap.range (1 + C₀).mulVecLin) ≤ q
    omega
  · have hker : U ≤ LinearMap.ker (T + C₀).mulVecLin := by
      intro u hu
      rw [LinearMap.mem_ker, add_mulVecLin, hC0_lin]
      change T.mulVecLin u + P u = 0
      have hu_decomp : u =
          (LinearMap.id (R := ZMod 2) (M := Fin k → ZMod 2) + T.mulVecLin) u +
            T.mulVecLin u := by
        change u = (u + T.mulVecLin u) + T.mulVecLin u
        rw [add_assoc, zmod2_vec_add_self, add_zero]
      have hPu : P u = T.mulVecLin u := by
        conv_lhs => rw [hu_decomp, map_add]
        rw [hP_on_U1 _ ⟨u, hu, rfl⟩, zero_add, hP_on_U2 _ ⟨u, hu, rfl⟩]
      rw [hPu, zmod2_vec_add_self]
    have hrn := LinearMap.finrank_range_add_finrank_ker (T + C₀).mulVecLin
    rw [Module.finrank_fin_fun] at hrn
    have hle := Submodule.finrank_mono hker
    rw [hUfin] at hle
    change Module.finrank (ZMod 2) (LinearMap.range (T + C₀).mulVecLin) ≤ r
    omega

lemma aux_min (k p q r : ℕ) (hpq : p ≤ q) (hpr : p ≤ r)
    (hk_pq : k ≤ p + q) (hk_pr : k ≤ p + r)
    (A B : Matrix (Fin k) (Fin k) (ZMod 2))
    (hA : A.rank = k) (hB : B.rank = k) (hAB : (A + B).rank = k) :
    ∃ C : Matrix (Fin k) (Fin k) (ZMod 2),
      C.rank ≤ p ∧ (A + C).rank ≤ q ∧ (B + C).rank ≤ r := by
  obtain ⟨A_inv, hinvL, hinvR⟩ := inv_of_rank_eq A hA
  have hAbij : Function.Bijective A.mulVecLin := bijective_of_rank_eq A hA
  have hAinv_rank : A_inv.rank = k := by
    have h1 := rank_mul_left_of_bijective A A_inv hAbij
    rw [hinvR] at h1
    have h1_rank : (1 : Matrix (Fin k) (Fin k) (ZMod 2)).rank = k := by
      change Module.finrank (ZMod 2) (LinearMap.range (1 : Matrix (Fin k) (Fin k) (ZMod 2)).mulVecLin) = k
      rw [one_mulVecLin, LinearMap.range_id, finrank_top, Module.finrank_fin_fun]
    rw [h1_rank] at h1
    exact h1.symm
  have hAinv_bij : Function.Bijective A_inv.mulVecLin := bijective_of_rank_eq A_inv hAinv_rank
  let T := A_inv * B
  have hT : T.rank = k := by
    rw [rank_mul_left_of_bijective A_inv B hAinv_bij, hB]
  have h1T : (1 + T).rank = k := by
    have heq : A_inv * (A + B) = 1 + T := by
      rw [Matrix.mul_add, hinvL]
    rw [← heq, rank_mul_left_of_bijective A_inv (A + B) hAinv_bij, hAB]
  obtain ⟨C₀, hC0, h1C0, hTC0⟩ := aux_one k p q r hpq hpr hk_pq hk_pr T hT h1T
  refine ⟨A * C₀, ?_, ?_, ?_⟩
  · rw [rank_mul_left_of_bijective A C₀ hAbij]
    exact hC0
  · have heq : A + A * C₀ = A * (1 + C₀) := by
      rw [Matrix.mul_add, Matrix.mul_one]
    rw [heq, rank_mul_left_of_bijective A (1 + C₀) hAbij]
    exact h1C0
  · have heq : B + A * C₀ = A * (T + C₀) := by
      rw [Matrix.mul_add]
      dsimp [T]
      rw [← Matrix.mul_assoc, hinvR, Matrix.one_mul]
    rw [heq, rank_mul_left_of_bijective A (T + C₀) hAbij]
    exact hTC0

lemma backward_dir (k p q r : ℕ) (A B : Matrix (Fin k) (Fin k) (ZMod 2))
    (hA : A.rank = k) (hB : B.rank = k) (hAB : (A + B).rank = k)
    (hk_pq : k ≤ p + q) (hk_pr : k ≤ p + r) (hk_qr : k ≤ q + r) :
    ∃ C : Matrix (Fin k) (Fin k) (ZMod 2),
      C.rank ≤ p ∧ (A + C).rank ≤ q ∧ (B + C).rank ≤ r := by
  by_cases hpq : p ≤ q
  · by_cases hpr : p ≤ r
    · exact aux_min k p q r hpq hpr hk_pq hk_pr A B hA hB hAB
    · have hrp : r ≤ p := by omega
      have hrq : r ≤ q := by omega
      have hBAB : (B + (A + B)).rank = k := by
        have heq : B + (A + B) = A := by
          calc
            B + (A + B) = A + (B + B) := by abel
            _ = A + 0 := by rw [zmod2_mat_add_self]
            _ = A := add_zero A
        rw [heq, hA]
      obtain ⟨C', hC', hBC', hABC'⟩ :=
        aux_min k r p q hrp hrq (by omega) (by omega) B (A + B) hB hAB hBAB
      refine ⟨B + C', hBC', ?_, ?_⟩
      · have heq : A + (B + C') = (A + B) + C' := by abel
        rw [heq]
        exact hABC'
      · have heq : B + (B + C') = C' := by
          rw [← add_assoc, zmod2_mat_add_self, zero_add]
        rw [heq]
        exact hC'
  · by_cases hqr : q ≤ r
    · have hqp : q ≤ p := by omega
      have hAAB : (A + (A + B)).rank = k := by
        have heq : A + (A + B) = B := by
          rw [← add_assoc, zmod2_mat_add_self, zero_add]
        rw [heq, hB]
      obtain ⟨C', hC', hAC', hABC'⟩ :=
        aux_min k q p r hqp hqr (by omega) (by omega) A (A + B) hA hAB hAAB
      refine ⟨A + C', hAC', ?_, ?_⟩
      · have heq : A + (A + C') = C' := by
          rw [← add_assoc, zmod2_mat_add_self, zero_add]
        rw [heq]
        exact hC'
      · have heq : B + (A + C') = (A + B) + C' := by abel
        rw [heq]
        exact hABC'
    · have hrp : r ≤ p := by omega
      have hrq : r ≤ q := by omega
      have hBAB : (B + (A + B)).rank = k := by
        have heq : B + (A + B) = A := by
          calc
            B + (A + B) = A + (B + B) := by abel
            _ = A + 0 := by rw [zmod2_mat_add_self]
            _ = A := add_zero A
        rw [heq, hA]
      obtain ⟨C', hC', hBC', hABC'⟩ :=
        aux_min k r p q hrp hrq (by omega) (by omega) B (A + B) hB hAB hBAB
      refine ⟨B + C', hBC', ?_, ?_⟩
      · have heq : A + (B + C') = (A + B) + C' := by abel
        rw [heq]
        exact hABC'
      · have heq : B + (B + C') = C' := by
          rw [← add_assoc, zmod2_mat_add_self, zero_add]
        rw [heq]
        exact hC'

end PEqualNP.Outside.L_lib_727

theorem PEqualNP.Outside.L_lib_727 : (∀ (k p q r : ℕ) (A B : Matrix (Fin k) (Fin k) (ZMod 2)),
  A.rank = k → B.rank = k → (A+B).rank = k →
  ((∃ C : Matrix (Fin k) (Fin k) (ZMod 2),
    C.rank ≤ p ∧ (A+C).rank ≤ q ∧ (B+C).rank ≤ r) ↔
    (k ≤ p+q ∧ k ≤ p+r ∧ k ≤ q+r))) := by
  intro k p q r A B hA hB hAB
  constructor
  · rintro ⟨C, hC, hAC, hBC⟩
    exact PEqualNP.Outside.L_lib_727.forward_dir k p q r A B C hA hB hAB hC hAC hBC
  · rintro ⟨hk_pq, hk_pr, hk_qr⟩
    exact PEqualNP.Outside.L_lib_727.backward_dir k p q r A B hA hB hAB hk_pq hk_pr hk_qr
