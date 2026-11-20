import Formalism.LocalToGlobal.Columns.CoefModB
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaRoundFreeHolds
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section One

variable {n : ℕ} (ν : Fin n → ℕ)

instance sdFintype : Fintype (Formalism.GradedWeylDivisibility.ssIdx n n ν) := @Fintype.ofFinite _ (Formalism.GradedWeylDivisibility.sSIdxFinite n n ν).to_subtype

def sdBeta : Formalism.GradedWeylDivisibility.ssIdx n n ν → MvPolynomial (Fin n × Fin n) ℤ := (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose

def sdBetaQ (i : Formalism.GradedWeylDivisibility.ssIdx n n ν) : MvPolynomial (Fin n × Fin n) ℚ := map (Int.castRingHom ℚ) (sdBeta ν i)

/- English proof (translation)
The claim follows from `(Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1.2.1`.
-/
theorem sd_beta_span : Submodule.span ℤ (Set.range (sdBeta ν)) = Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν :=
  (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1.2.1

/- English proof (translation)
Establish `h` using `Formalism.GradedWeylDivisibility.nablaLKBasis ℤ ℚ Int.cast_injective n n ν (sdBeta ν) _ (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1 1 (by simp)`. Establish `e : (fun i => Formalism.GradedWeylDivisibility.rowAct ℚ (1 : Matrix (Fin n) (Fin n) ℚ)⁻¹ (map (algebraMap ℤ ℚ) (sdBeta ν i))) = sdBetaQ ν`. Use function extensionality and compare the values at `i`. Rewrite using `[inv_one, rd_rowAct_one]`. Both sides reduce to the same expression.

Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem sd_betaQ_spec : LinearIndependent ℚ (sdBetaQ ν) ∧
    Submodule.span ℚ (Set.range (sdBetaQ ν)) = Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν := by
  have h := Formalism.GradedWeylDivisibility.nablaLKBasis ℤ ℚ Int.cast_injective n n ν (sdBeta ν) _
    (Formalism.GradedWeylDivisibility.sSBasis ℤ n n ν).choose_spec.1 1 (by simp)
  have e : (fun i => Formalism.GradedWeylDivisibility.rowAct ℚ (1 : Matrix (Fin n) (Fin n) ℚ)⁻¹ (map (algebraMap ℤ ℚ) (sdBeta ν i))) =
      sdBetaQ ν := by
    funext i
    rw [inv_one, rd_rowAct_one]
    rfl
  rwa [e] at h

/- English proof (translation)
Simplify using `[fockB, Formalism.GradedWeylDivisibility.fockQ, mfact]`.
-/
theorem sd_fockB_rat {σ : Type} (f g : MvPolynomial σ ℚ) : fockB f g = Formalism.GradedWeylDivisibility.fockQ f g := by
  simp [fockB, Formalism.GradedWeylDivisibility.fockQ, mfact]

def sdC : ℚ := Formalism.GradedWeylDivisibility.fockQ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν) (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν)

/- English proof (translation)
The claim follows from `ne_of_gt ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl ν))`.
-/
theorem sdC_ne : sdC ν ≠ 0 :=
  ne_of_gt ((Formalism.GradedWeylDivisibility.fockQPos _ _ (Formalism.GradedWeylDivisibility.hw ℚ (le_refl n) ν)).2 (Formalism.GradedWeylDivisibility.hwNe ℚ n n le_rfl ν))

def sdGram : Matrix (Formalism.GradedWeylDivisibility.ssIdx n n ν) (Formalism.GradedWeylDivisibility.ssIdx n n ν) ℚ :=
  Matrix.of fun i j => Formalism.GradedWeylDivisibility.fockQ (sdBetaQ ν i) (sdBetaQ ν j)

def sdDelta (i : Formalism.GradedWeylDivisibility.ssIdx n n ν) : MvPolynomial (Fin n × Fin n) ℚ :=
  sdC ν • ∑ j, (sdGram ν)⁻¹ i j • sdBetaQ ν j

/- English proof (translation)
Unfold `sdDelta`. Use `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)` and prove the remaining obligations. Rewrite using `[← (sd_betaQ_spec ν).2]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem sd_delta_mem (i : Formalism.GradedWeylDivisibility.ssIdx n n ν) : sdDelta ν i ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν := by
  unfold sdDelta
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
  rw [← (sd_betaQ_spec ν).2]
  exact Submodule.subset_span ⟨j, rfl⟩

/- English proof (translation)
Establish `hdet : IsUnit (sdGram ν).det`. Rewrite using `[isUnit_iff_ne_zero]`. Conclude with `ps_gram_det_ne (sdBetaQ ν) (sd_betaQ_spec ν).1`. Establish `h1 : ∀ j, fockBL (sdBetaQ ν j) (sdBetaQ ν k) = sdGram ν j k` using `fun j => by`. Rewrite using `[fockBL_apply, sd_fockB_rat]`.

Both sides reduce to the same expression. Unfold `sdDelta`. Simplify using `only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, h1, smul_eq_mul]`. Establish `h2 : ∑ j, (sdGram ν)⁻¹ i j * sdGram ν j k = ((sdGram ν)⁻¹ * sdGram ν) i k` using `(Matrix.mul_apply ..).symm`. Rewrite using `[h2, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sd_delta_beta (i k : Formalism.GradedWeylDivisibility.ssIdx n n ν) :
    fockBL (sdDelta ν i) (sdBetaQ ν k) = if i = k then sdC ν else 0 := by
  have hdet : IsUnit (sdGram ν).det := by
    rw [isUnit_iff_ne_zero]
    exact ps_gram_det_ne (sdBetaQ ν) (sd_betaQ_spec ν).1
  have h1 : ∀ j, fockBL (sdBetaQ ν j) (sdBetaQ ν k) = sdGram ν j k := fun j => by
    rw [fockBL_apply, sd_fockB_rat]; rfl
  unfold sdDelta
  simp only [map_smul, map_sum, LinearMap.smul_apply, LinearMap.sum_apply, h1, smul_eq_mul]
  have h2 : ∑ j, (sdGram ν)⁻¹ i j * sdGram ν j k = ((sdGram ν)⁻¹ * sdGram ν) i k := (Matrix.mul_apply ..).symm
  rw [h2, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `P ⟨hP, hPQ⟩`. Establish `hz : ∀ k, ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ P (sdBetaQ ν k) = z * sdC ν` using `fun k => hPQ _ ⟨sdBeta ν k, by rw [← sd_beta_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩`. Use `choose z hz using hz`. Establish `hR : P - ∑ k, z k • sdDelta ν k ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν` using `Submodule.sub_mem _ hP (Submodule.sum_mem _ fun k _ => by`.

Rewrite using `[← Int.cast_smul_eq_zsmul ℚ]`. Conclude with `Submodule.smul_mem _ _ (sd_delta_mem ν k))`. Establish `h0 : ∀ k, fockBL (P - ∑ j, z j • sdDelta ν j) (sdBetaQ ν k) = 0`. Introduce `k`. Simplify using `only [map_sub, map_sum, map_zsmul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, sd_delta_beta]`.

Rewrite using `[fockBL_apply, sd_fockB_rat, hz k]`. Simplify using the standard rewrite rules. Establish `h1 : ∀ y ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν, fockBL (P - ∑ j, z j • sdDelta ν j) y = 0`. Introduce `y hy`. Rewrite `hy` using `[← (sd_betaQ_spec ν).2]`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => obtain ⟨k, rfl⟩ := hy`. Conclude with `h0 k`. Consider the case `zero => exact map_zero _`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]`.

Consider the case `smul c x _ hx => rw [map_smul, hx, smul_zero]`. Establish `h2 : P - ∑ k, z k • sdDelta ν k = 0`. Assume the negation of the conclusion as `hne`. Use `(Formalism.GradedWeylDivisibility.fockQPos _ _ (P - ∑ k, z k • sdDelta ν k)).2 hne` as an intermediate fact. Rewrite `this` using `[← sd_fockB_rat, ← fockBL_apply, h1 _ hR]`.

Conclude with `lt_irrefl _ this`. Rewrite using `[sub_eq_zero.mp h2]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Use `⟨sd_delta_mem ν i, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨Q0, hQ0, rfl⟩`. Rewrite `hQ0` using `[SetLike.mem_coe, ← sd_beta_span]`. Proceed by induction on `hQ0 using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨k, rfl⟩` from `hy`. Use `⟨if i = k then 1 else 0, ?_⟩` and prove the remaining obligations. Use `sd_delta_beta ν i k` as an intermediate fact. Rewrite `this` using `[fockBL_apply, sd_fockB_rat]`. Use `show Formalism.GradedWeylDivisibility.fockQ (sdDelta ν i) (sdBetaQ ν k) = _`.

Rewrite using `[this]`. Apply the tactic sequence `split_ifs <;> simp [sdC]`. Consider the case `zero => exact ⟨0, by rw [map_zero, ← sd_fockB_rat, ← fockBL_apply, map_zero]; simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`.

Take `⟨b, hb⟩` from `hy`. Use `⟨a + b, ?_⟩` and prove the remaining obligations. Rewrite `ha`, `hb`, the goal using `[← sd_fockB_rat, ← fockBL_apply]`. Rewrite using `[map_add, map_add, ha, hb]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`. Use `⟨c * a, ?_⟩` and prove the remaining obligations. Rewrite `ha`, the goal using `[← sd_fockB_rat, ← fockBL_apply]`.

Rewrite using `[map_zsmul, map_zsmul, ha]`. Simplify using `[mul_assoc]`.
-/
theorem sd_bDual : Formalism.GradedWeylDivisibility.bDual n n le_rfl ν ((Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν).map (Formalism.GradedWeylDivisibility.intQ n n)) =
    Submodule.span ℤ (Set.range (sdDelta ν)) := by
  apply le_antisymm
  · rintro P ⟨hP, hPQ⟩
    have hz : ∀ k, ∃ z : ℤ, Formalism.GradedWeylDivisibility.fockQ P (sdBetaQ ν k) = z * sdC ν := fun k =>
      hPQ _ ⟨sdBeta ν k, by rw [← sd_beta_span]; exact Submodule.subset_span ⟨k, rfl⟩, rfl⟩
    choose z hz using hz
    have hR : P - ∑ k, z k • sdDelta ν k ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν :=
      Submodule.sub_mem _ hP (Submodule.sum_mem _ fun k _ => by
        rw [← Int.cast_smul_eq_zsmul ℚ]; exact Submodule.smul_mem _ _ (sd_delta_mem ν k))
    have h0 : ∀ k, fockBL (P - ∑ j, z j • sdDelta ν j) (sdBetaQ ν k) = 0 := by
      intro k
      simp only [map_sub, map_sum, map_zsmul, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        sd_delta_beta]
      rw [fockBL_apply, sd_fockB_rat, hz k]
      simp
    have h1 : ∀ y ∈ Formalism.GradedWeylDivisibility.dualWeyl ℚ n n ν, fockBL (P - ∑ j, z j • sdDelta ν j) y = 0 := by
      intro y hy
      rw [← (sd_betaQ_spec ν).2] at hy
      induction hy using Submodule.span_induction with
      | mem y hy => obtain ⟨k, rfl⟩ := hy; exact h0 k
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul c x _ hx => rw [map_smul, hx, smul_zero]
    have h2 : P - ∑ k, z k • sdDelta ν k = 0 := by
      by_contra hne
      have := (Formalism.GradedWeylDivisibility.fockQPos _ _ (P - ∑ k, z k • sdDelta ν k)).2 hne
      rw [← sd_fockB_rat, ← fockBL_apply, h1 _ hR] at this
      exact lt_irrefl _ this
    rw [sub_eq_zero.mp h2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨sd_delta_mem ν i, ?_⟩
    rintro _ ⟨Q0, hQ0, rfl⟩
    rw [SetLike.mem_coe, ← sd_beta_span] at hQ0
    induction hQ0 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      refine ⟨if i = k then 1 else 0, ?_⟩
      have := sd_delta_beta ν i k
      rw [fockBL_apply, sd_fockB_rat] at this
      show Formalism.GradedWeylDivisibility.fockQ (sdDelta ν i) (sdBetaQ ν k) = _
      rw [this]
      split_ifs <;> simp [sdC]
    | zero => exact ⟨0, by rw [map_zero, ← sd_fockB_rat, ← fockBL_apply, map_zero]; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      refine ⟨a + b, ?_⟩
      rw [← sd_fockB_rat, ← fockBL_apply] at ha hb ⊢
      rw [map_add, map_add, ha, hb]
      push_cast; ring
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨c * a, ?_⟩
      rw [← sd_fockB_rat, ← fockBL_apply] at ha ⊢
      rw [map_zsmul, map_zsmul, ha]
      simp [mul_assoc]

end One

section Abstract

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx' clear hx`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Rewrite using `[h]`.

Use `split_ifs`. Conclude with `Submodule.one_le.mp le_rfl`. Conclude with `Submodule.zero_mem _`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add y y' _ _ hy hy' => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hy'`. Consider the case `smul r y _ hy => rw [LinearMap.map_smul_of_tower]`. Conclude with `Submodule.smul_mem _ r hy`. Consider the case `zero => intro y _`.

Rewrite using `[map_zero, LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x x' _ _ hx hx'`. Introduce `y hy`. Rewrite using `[map_add, LinearMap.add_apply]`.

Conclude with `Submodule.add_mem _ (hx y hy) (hx' y hy)`. Consider the case `smul r x _ hx`. Introduce `y hy`. Rewrite using `[LinearMap.map_smul_of_tower, LinearMap.smul_apply]`. Conclude with `Submodule.smul_mem _ r (hx y hy)`.

Introduce `hy`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 hx`. Establish `h1 : ∀ j, b (∑ i, a i • u i) (v j) = a j`. Introduce `j`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Establish `h2 : ∀ j, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = a j` using `fun j => by`. Use `hy (v j) (Submodule.subset_span ⟨j, rfl⟩)` as an intermediate fact. Rewrite `this` using `[h1 j]`. Conclude with `(lc_mem_one_iff _).1 this`. Use `choose r hr using h2`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← hr i, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem sd_dual_bases {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {κ : Type} [Fintype κ] [DecidableEq κ] (b : V →ₗ[K] V →ₗ[K] K) (u v : κ → V)
    (h : ∀ i j, b (u i) (v j) = if i = j then 1 else 0) (x : V) (hx : x ∈ Submodule.span K (Set.range u)) :
    x ∈ Submodule.span (𝓞 K) (Set.range u) ↔
      ∀ y ∈ Submodule.span (𝓞 K) (Set.range v), b x y ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro hx'
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        rw [h]
        split_ifs
        · exact Submodule.one_le.mp le_rfl
        · exact Submodule.zero_mem _
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
      | smul r y _ hy => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ r hy
    | zero => intro y _; rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
    | add x x' _ _ hx hx' =>
      intro y hy
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hx y hy) (hx' y hy)
    | smul r x _ hx =>
      intro y hy
      rw [LinearMap.map_smul_of_tower, LinearMap.smul_apply]
      exact Submodule.smul_mem _ r (hx y hy)
  · intro hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have h1 : ∀ j, b (∑ i, a i • u i) (v j) = a j := by
      intro j
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have h2 : ∀ j, ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = a j := fun j => by
      have := hy (v j) (Submodule.subset_span ⟨j, rfl⟩)
      rw [h1 j] at this
      exact (lc_mem_one_iff _).1 this
    choose r hr using h2
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← hr i, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Rewrite using `[← Submodule.span_span_of_tower ℤ (𝓞 K) (φ '' S), ← Submodule.span_span_of_tower ℤ (𝓞 K) (φ '' S'), ← Submodule.map_span, ← Submodule.map_span, h]`.
-/
theorem sd_span_image {A B : Type} [AddCommGroup A] [AddCommGroup B] [Module (𝓞 K) B] (φ : A →ₗ[ℤ] B) (S S' : Set A)
    (h : Submodule.span ℤ S = Submodule.span ℤ S') :
    Submodule.span (𝓞 K) (φ '' S) = Submodule.span (𝓞 K) (φ '' S') := by
  rw [← Submodule.span_span_of_tower ℤ (𝓞 K) (φ '' S), ← Submodule.span_span_of_tower ℤ (𝓞 K) (φ '' S'),
    ← Submodule.map_span, ← Submodule.map_span, h]

end Abstract

section BaseChange

variable (K : Type) [Field K] [NumberField K] {n : ℕ}

def sdQK (σ : Type) : MvPolynomial σ ℚ →ₗ[ℤ] MvPolynomial σ K :=
  (MvPolynomial.map (algebraMap ℚ K)).toAddMonoidHom.toIntLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sdQK_apply {σ : Type} (f : MvPolynomial σ ℚ) : sdQK K σ f = MvPolynomial.map (algebraMap ℚ K) f := rfl

/- English proof (translation)
Unfold `nbWord`. Rewrite using `[← Set.range_comp]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Simplify using `only [Function.comp, sdQK_apply]`.

Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`.
-/
theorem sd_word_image (ν : Fin n → ℕ) : nbWord K ν = sdQK K _ '' nbWord ℚ ν := by
  unfold nbWord
  rw [← Set.range_comp]
  congr 1
  funext w
  simp only [Function.comp, sdQK_apply]
  rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

/- English proof (translation)
Use extensionality with `f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨N, sz, hsz, I, h, rfl⟩`. Conclude with `⟨_, ⟨N, sz, hsz, I, h, rfl⟩, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩`. Introduce and unpack `⟨_, ⟨N, sz, hsz, I, h, rfl⟩, rfl⟩`.

Conclude with `⟨N, sz, hsz, I, h, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩`.
-/
theorem sd_bid_image (ν : Fin n → ℕ) : bideterminantsOfShape K ν = sdQK K _ '' bideterminantsOfShape ℚ ν := by
  ext f
  constructor
  · rintro ⟨N, sz, hsz, I, h, rfl⟩
    exact ⟨_, ⟨N, sz, hsz, I, h, rfl⟩, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩
  · rintro ⟨_, ⟨N, sz, hsz, I, h, rfl⟩, rfl⟩
    exact ⟨N, sz, hsz, I, h, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩

/- English proof (translation)
Unfold `Formalism.GradedWeylDivisibility.weyl nbWord`. Rewrite using `[Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `w`. Use `show _ = MvPolynomial.map (Int.castRingHom ℚ) _`.

Rewrite using `[← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]`.
-/
theorem sd_span_word (ν : Fin n → ℕ) :
    Submodule.span ℤ (nbWord ℚ ν) = (Formalism.GradedWeylDivisibility.weyl ℤ n n le_rfl ν).map (Formalism.GradedWeylDivisibility.intQ n n) := by
  unfold Formalism.GradedWeylDivisibility.weyl nbWord
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext w
  show _ = MvPolynomial.map (Int.castRingHom ℚ) _
  rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

/- English proof (translation)
Establish `h1 : Submodule.span ℤ (bideterminantsOfShape ℚ ν) = (Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν).map (Formalism.GradedWeylDivisibility.intQ n n)`. Rewrite using `[Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℤ n n ν, Submodule.map_span]`. Use `congr 1`. Use extensionality with `f`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨N, sz, hsz, I, h, rfl⟩`. Conclude with `⟨_, ⟨N, sz, hsz, I, h, rfl⟩, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩`. Introduce and unpack `⟨_, ⟨N, sz, hsz, I, h, rfl⟩, rfl⟩`. Conclude with `⟨N, sz, hsz, I, h, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩`. Rewrite using `[h1, ← sd_beta_span, Submodule.map_span, ← Set.range_comp]`.

Both sides reduce to the same expression.
-/
theorem sd_span_bid (ν : Fin n → ℕ) :
    Submodule.span ℤ (bideterminantsOfShape ℚ ν) = Submodule.span ℤ (Set.range (sdBetaQ ν)) := by
  have h1 : Submodule.span ℤ (bideterminantsOfShape ℚ ν) = (Formalism.GradedWeylDivisibility.dualWeyl ℤ n n ν).map (Formalism.GradedWeylDivisibility.intQ n n) := by
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain ℤ n n ν, Submodule.map_span]
    congr 1
    ext f
    constructor
    · rintro ⟨N, sz, hsz, I, h, rfl⟩
      exact ⟨_, ⟨N, sz, hsz, I, h, rfl⟩, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩
    · rintro ⟨_, ⟨N, sz, hsz, I, h, rfl⟩, rfl⟩
      exact ⟨N, sz, hsz, I, h, Formalism.GradedWeylDivisibility.ldlat_map_bidet _ _ _ _⟩
  rw [h1, ← sd_beta_span, Submodule.map_span, ← Set.range_comp]
  rfl

def sdBetaK (ν : Fin n → ℕ) (i : Formalism.GradedWeylDivisibility.ssIdx n n ν) : MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.map (algebraMap ℚ K) (sdBetaQ ν i)

def sdDeltaK (ν : Fin n → ℕ) (i : Formalism.GradedWeylDivisibility.ssIdx n n ν) : MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.map (algebraMap ℚ K) (sdDelta ν i)

/- English proof (translation)
Rewrite using `[sd_bid_image, sd_span_image (sdQK K _) _ _ (sd_span_bid ν), ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem sd_span_bidK (ν : Fin n → ℕ) :
    Submodule.span (𝓞 K) (bideterminantsOfShape K ν) = Submodule.span (𝓞 K) (Set.range (sdBetaK K ν)) := by
  rw [sd_bid_image, sd_span_image (sdQK K _) _ _ (sd_span_bid ν), ← Set.range_comp]
  rfl

/- English proof (translation)
Establish `h : Submodule.span ℤ (nbWord ℚ ν) = Submodule.span ℤ (Set.range (sdDelta ν))`. Rewrite using `[sd_span_word, hE n n le_rfl ν hν, sd_bDual]`. Rewrite using `[sd_word_image, sd_span_image (sdQK K _) _ _ h, ← Set.range_comp]`. Both sides reduce to the same expression.
-/
theorem sd_span_wordK (hE : Formalism.GradedWeylDivisibility.WeylEqDualNabla) (ν : Fin n → ℕ) (hν : Antitone ν) :
    Submodule.span (𝓞 K) (nbWord K ν) = Submodule.span (𝓞 K) (Set.range (sdDeltaK K ν)) := by
  have h : Submodule.span ℤ (nbWord ℚ ν) = Submodule.span ℤ (Set.range (sdDelta ν)) := by
    rw [sd_span_word, hE n n le_rfl ν hν, sd_bDual]
  rw [sd_word_image, sd_span_image (sdQK K _) _ _ h, ← Set.range_comp]
  rfl

end BaseChange

section Tensor

variable (K : Type) [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

omit [NumberField K] in
/- English proof (translation)
Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg, rfl⟩ choose i hi using hg`. Conclude with `⟨i, congrArg ten (funext hi)⟩`. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `⟨_, fun τ => ⟨i τ, rfl⟩, rfl⟩`.
-/
theorem sd_gen_range {κ : ι → Type} (f : ∀ τ : ι, κ τ → MvPolynomial (Fin n × Fin n) K) :
    nbGen (fun τ => Set.range (f τ)) = Set.range fun i : (∀ τ, κ τ) => ten fun τ => f τ (i τ) := by
  ext P
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose i hi using hg
    exact ⟨i, congrArg ten (funext hi)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨_, fun τ => ⟨i τ, rfl⟩, rfl⟩

def sdU (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n := ten fun τ => sdDeltaK K (lam τ).natW (i τ)

def sdV (lam : ι → DomWeight n) (i : VVIdx lam) : Pol K ι n := ten fun τ => sdBetaK K (lam τ).natW (i τ)

/- English proof (translation)
Establish `h : (fun τ => (nablaSq (𝓞 K) n (lam τ)).map (toK K _)) = fun τ => Submodule.span (𝓞 K) (Set.range (sdBetaK K (lam τ).natW))`. Use function extensionality and compare the values at `fun τ => (nb_map_nablaSq (𝓞 K) (lam τ)).trans (sd_span_bidK K _)`. Rewrite using `[nabStd, h, nb_tensorLat_span, sd_gen_range]`. Both sides reduce to the same expression.
-/
theorem sd_nabStd (lam : ι → DomWeight n) : nabStd K lam = Submodule.span (𝓞 K) (Set.range (sdV K lam)) := by
  have h : (fun τ => (nablaSq (𝓞 K) n (lam τ)).map (toK K _)) =
      fun τ => Submodule.span (𝓞 K) (Set.range (sdBetaK K (lam τ).natW)) :=
    funext fun τ => (nb_map_nablaSq (𝓞 K) (lam τ)).trans (sd_span_bidK K _)
  rw [nabStd, h, nb_tensorLat_span, sd_gen_range]
  rfl

/- English proof (translation)
Establish `h : (fun τ => (delSq (𝓞 K) n (lam τ)).map (toK K _)) = fun τ => Submodule.span (𝓞 K) (Set.range (sdDeltaK K (lam τ).natW))`. Use function extensionality and compare the values at `fun τ => (nb_map_delSq (𝓞 K) (lam τ)).trans (sd_span_wordK K hE _ (natW_antitone (lam τ)))`. Rewrite using `[delStd, h, nb_tensorLat_span, sd_gen_range]`. Both sides reduce to the same expression.
-/
theorem sd_delStd (hE : Formalism.GradedWeylDivisibility.WeylEqDualNabla) (lam : ι → DomWeight n) :
    delStd K lam = Submodule.span (𝓞 K) (Set.range (sdU K lam)) := by
  have h : (fun τ => (delSq (𝓞 K) n (lam τ)).map (toK K _)) =
      fun τ => Submodule.span (𝓞 K) (Set.range (sdDeltaK K (lam τ).natW)) :=
    funext fun τ => (nb_map_delSq (𝓞 K) (lam τ)).trans (sd_span_wordK K hE _ (natW_antitone (lam τ)))
  rw [delStd, h, nb_tensorLat_span, sd_gen_range]
  rfl

omit [NumberField K] in
/- English proof (translation)
The claim follows from `@fockSymTensor_holds K _ starRingOfComm ι _ n f g`.
-/
theorem sd_fockB_ten (f g : ι → MvPolynomial (Fin n × Fin n) K) : fockB (ten f) (ten g) = ∏ τ, fockB (f τ) (g τ) :=
  @fockSymTensor_holds K _ starRingOfComm ι _ n f g

/- English proof (translation)
The claim follows from `@fockSQ K _ starRingOfComm _ σ P Q`.
-/
theorem sd_fockB_map {σ : Type} (P Q : MvPolynomial σ ℚ) :
    fockB (MvPolynomial.map (algebraMap ℚ K) P) (MvPolynomial.map (algebraMap ℚ K) Q) =
      algebraMap ℚ K (Formalism.GradedWeylDivisibility.fockQ P Q) :=
  @fockSQ K _ starRingOfComm _ σ P Q

/- English proof (translation)
Unfold `extNormB`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← map_extremal (algebraMap ℚ K), sd_fockB_map]`. Both sides reduce to the same expression.
-/
theorem sd_extNormB (lam : ι → DomWeight n) : extNormB K lam = ∏ τ, algebraMap ℚ K (sdC (lam τ).natW) := by
  unfold extNormB
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← map_extremal (algebraMap ℚ K), sd_fockB_map]
  rfl

/- English proof (translation)
Establish `h : ∀ τ, fockB (sdDeltaK K (lam τ).natW (i τ)) (sdBetaK K (lam τ).natW (j τ)) = algebraMap ℚ K (if i τ = j τ then sdC (lam τ).natW else 0)`. Introduce `τ`. Rewrite using `[sdDeltaK, sdBetaK, sd_fockB_map, ← sd_fockB_rat, ← fockBL_apply, sd_delta_beta]`. Rewrite using `[pairB_apply, sdU, sdV, sd_fockB_ten, sd_extNormB]`. Simplify using `only [h]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [if_true]`. Conclude with `inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => by`. Simplify using `using sdC_ne (lam τ).natW)`.

Rewrite using `[if_neg hij]`. Take `⟨τ, hτ⟩` from `Function.ne_iff.mp hij`. Establish `h0 : ∏ x, (algebraMap ℚ K) (if i x = j x then sdC (lam x).natW else 0) = 0` using `Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg hτ, map_zero])`. Rewrite using `[h0, mul_zero]`.
-/
theorem sd_pair (lam : ι → DomWeight n) [DecidableEq (VVIdx lam)] (i j : VVIdx lam) :
    pairB lam (sdU K lam i) (sdV K lam j) = if i = j then 1 else 0 := by
  have h : ∀ τ, fockB (sdDeltaK K (lam τ).natW (i τ)) (sdBetaK K (lam τ).natW (j τ)) =
      algebraMap ℚ K (if i τ = j τ then sdC (lam τ).natW else 0) := by
    intro τ
    rw [sdDeltaK, sdBetaK, sd_fockB_map, ← sd_fockB_rat, ← fockBL_apply, sd_delta_beta]
  rw [pairB_apply, sdU, sdV, sd_fockB_ten, sd_extNormB]
  simp only [h]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => by
      simpa using sdC_ne (lam τ).natW)
  · rw [if_neg hij]
    obtain ⟨τ, hτ⟩ := Function.ne_iff.mp hij
    have h0 : ∏ x, (algebraMap ℚ K) (if i x = j x then sdC (lam x).natW else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [if_neg hτ, map_zero])
    rw [h0, mul_zero]

end Tensor

/- English proof (translation)
Introduce `K _ _ ι _ n lam x hx`. Establish `hVu : VV K lam = Submodule.span K (Set.range (sdU K lam))`. Rewrite using `[nb_VV_eq_word, ← Submodule.span_span_of_tower (𝓞 K) K, ← nb_delStd_eq, sd_delStd K hE, Submodule.span_span_of_tower]`. Establish `hVv : VV K lam = Submodule.span K (Set.range (sdV K lam))`. Rewrite using `[nb_VV_eq_bid, ← Submodule.span_span_of_tower (𝓞 K) K, ← nb_nabStd_eq, sd_nabStd K, Submodule.span_span_of_tower]`.

Rewrite using `[sd_delStd K hE lam, sd_nabStd K lam]`. Prove the components needed by the constructor for the conclusion. Conclude with `sd_dual_bases (pairB lam) (sdU K lam) (sdV K lam) (sd_pair K lam) x (hVu ▸ hx)`. Establish `h` using `sd_dual_bases (pairB lam).flip (sdV K lam) (sdU K lam) (fun i j => by`. Rewrite using `[LinearMap.flip_apply, sd_pair]`.

Simplify using `only [eq_comm]) x (hVv ▸ hx)`. Use `h.trans (forall₂_congr fun y _ => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.flip_apply, pairingBSymm_holds K ι n lam y x]`.
-/
theorem pairBDualStd_of (hE : Formalism.GradedWeylDivisibility.WeylEqDualNabla) : PairBDualStd := by
  classical
  intro K _ _ ι _ n lam x hx
  have hVu : VV K lam = Submodule.span K (Set.range (sdU K lam)) := by
    rw [nb_VV_eq_word, ← Submodule.span_span_of_tower (𝓞 K) K, ← nb_delStd_eq, sd_delStd K hE,
      Submodule.span_span_of_tower]
  have hVv : VV K lam = Submodule.span K (Set.range (sdV K lam)) := by
    rw [nb_VV_eq_bid, ← Submodule.span_span_of_tower (𝓞 K) K, ← nb_nabStd_eq, sd_nabStd K,
      Submodule.span_span_of_tower]
  rw [sd_delStd K hE lam, sd_nabStd K lam]
  constructor
  · exact sd_dual_bases (pairB lam) (sdU K lam) (sdV K lam) (sd_pair K lam) x (hVu ▸ hx)
  · have h := sd_dual_bases (pairB lam).flip (sdV K lam) (sdU K lam) (fun i j => by
      rw [LinearMap.flip_apply, sd_pair]
      simp only [eq_comm]) x (hVv ▸ hx)
    refine h.trans (forall₂_congr fun y _ => ?_)
    rw [LinearMap.flip_apply, pairingBSymm_holds K ι n lam y x]

end Formalism.L2.DIV
