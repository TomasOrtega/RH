import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

/- English proof (translation)
Establish `hT : (T x)ᵀ.BlockTriangular id` using `fun i j hij => h0.self_of_nhds j i hij`. Establish `hu' : IsUnit (T x)ᵀ.det`. Rewrite using `[Matrix.det_of_isUpperTriangular hT]`. Conclude with `(Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit`. Establish `hu : IsUnit (T x).det` using `by rwa [Matrix.det_transpose] at hu'`.

Establish `hD : (mdel T x ξ)ᵀ.BlockTriangular id` using `fun i j hij => by`. Rewrite using `[Matrix.transpose_apply, mdel_apply, del_congr (g := fun _ => (0 : ℂ)) (h0.mono fun y hy => hy j i hij)]`. Simplify using the standard rewrite rules. Use `letI := Matrix.invertibleOfIsUnitDet _ hu'`. Establish `hc : (conn T x ξ).BlockTriangular id` using `(Matrix.blockTriangular_inv_of_blockTriangular hT).mul hD`.

Use `⟨fun i j hij => hc hij, fun i => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (congrFun (transpose_mul_conn hu ξ) i) i`. Rewrite `h` using `[Matrix.mul_apply, Finset.sum_eq_single i, Matrix.transpose_apply, Matrix.transpose_apply, mdel_apply]`. Rewrite using `[← h, inv_mul_cancel_left₀ (hd i)]`. Introduce `k _ hk`.

Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Rewrite using `[hT (show id k < id i from hk), zero_mul]`. Rewrite using `[hc (show id i < id k from hk), mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem conn_lowerTriangular {n s : ℕ} {T : V n → Matrix (Fin s) (Fin s) ℂ} {x : V n}
    (h0 : ∀ᶠ y in 𝓝 x, ∀ i j, i < j → T y i j = 0) (hd : ∀ i, T x i i ≠ 0) (ξ : V n) :
    (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
  have hT : (T x)ᵀ.BlockTriangular id := fun i j hij => h0.self_of_nhds j i hij
  have hu' : IsUnit (T x)ᵀ.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    exact (Finset.prod_ne_zero_iff.2 fun i _ => hd i).isUnit
  have hu : IsUnit (T x).det := by rwa [Matrix.det_transpose] at hu'
  have hD : (mdel T x ξ)ᵀ.BlockTriangular id := fun i j hij => by
    rw [Matrix.transpose_apply, mdel_apply,
      del_congr (g := fun _ => (0 : ℂ)) (h0.mono fun y hy => hy j i hij)]
    simp
  letI := Matrix.invertibleOfIsUnitDet _ hu'
  have hc : (conn T x ξ).BlockTriangular id :=
    (Matrix.blockTriangular_inv_of_blockTriangular hT).mul hD
  refine ⟨fun i j hij => hc hij, fun i => ?_⟩
  have h := congrFun (congrFun (transpose_mul_conn hu ξ) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, Matrix.transpose_apply, Matrix.transpose_apply,
    mdel_apply] at h
  · rw [← h, inv_mul_cancel_left₀ (hd i)]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hT (show id k < id i from hk), zero_mul]
    · rw [hc (show id i < id k from hk), mul_zero]
  · simp

/- English proof (translation)
Introduce `n s T d v hT hd he ξ η`. Establish `h0 : ∀ᶠ y in 𝓝 v, ∀ i j, i < j → T y i j = 0` using `he.mono fun _ h => h.1`. Establish `hv : ∀ i, T v i i ≠ 0` using `fun i => by`. Rewrite using `[he.self_of_nhds.2 i]`. Conclude with `(hd i).ne'` after adjusting the coercions.

Establish `hne : ∀ᶠ y in 𝓝 v, ∀ i, T y i i ≠ 0` using `eventually_all.2 fun i => (hT i i).continuousAt.eventually_ne (hv i)`. Establish `hc : ∀ᶠ x in 𝓝 v, (∀ i j, j < i → conn T x ξ i j = 0) ∧ ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ` using `by filter_upwards [h0.eventually_nhds, hne] with x h1 h2`. Conclude with `conn_lowerTriangular h1 h2 ξ`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[curv, Matrix.neg_apply, mdbar_apply, dbar_congr (g := fun _ => (0 : ℂ)) (hc.mono fun y hy => hy.1 i j hij)]`.

Simplify using the standard rewrite rules. Set `H : V n → Matrix (Fin 1) (Fin 1) ℂ` to `fun x => Matrix.of fun _ _ => T x i i`. Establish `hH : ∀ᶠ x in 𝓝 v, conn T x ξ i i = conn H x ξ 0 0` using `by filter_upwards [hc, hne] with x h1 h2`. Rewrite using `[h1.2 i, (conn_lowerTriangular (T := H) (Eventually.of_forall fun _ a b hab => absurd (Subsingleton.elim a b) hab.ne) (fun _ => h2 i) ξ).2 0]`. Both sides reduce to the same expression.

Establish `hs : ContDiffAt ℝ 2 (d i) v`. Establish `h1 : ContDiffAt ℝ 2 (fun x => (T x i i).re) v` using `Complex.reCLM.contDiff.contDiffAt.comp v ((hT i i).of_le (by norm_cast))`. Use `h1.congr_of_eventuallyEq (he.mono fun x hx => ?_)` and prove the remaining obligations. Simplify using `[hx.2 i]`. Rewrite using `[← curv_line (H := H) hs (hd i).ne' (he.mono fun x hx => hx.2 i) ξ η 0 0, curv, curv, Matrix.neg_apply, Matrix.neg_apply, mdbar_apply, mdbar_apply, dbar_congr hH]`.
-/
theorem curv_lowerTriangular : ∀ (n s : ℕ) (T : V n → Matrix (Fin s) (Fin s) ℂ) (d : Fin s → V n → ℝ) (v : V n), MContDiffAt ∞ T v → (∀ i, 0 < d i v) → (∀ᶠ x in 𝓝 v, (∀ i j, i < j → T x i j = 0) ∧ ∀ i, T x i i = d i x) → ∀ ξ η, (∀ i j, j < i → curv T v ξ η i j = 0) ∧ ∀ i, curv T v ξ η i i = -leviForm (fun x => Real.log (d i x)) v ξ η := by
  intro n s T d v hT hd he ξ η
  have h0 : ∀ᶠ y in 𝓝 v, ∀ i j, i < j → T y i j = 0 := he.mono fun _ h => h.1
  have hv : ∀ i, T v i i ≠ 0 := fun i => by
    rw [he.self_of_nhds.2 i]; exact_mod_cast (hd i).ne'
  have hne : ∀ᶠ y in 𝓝 v, ∀ i, T y i i ≠ 0 :=
    eventually_all.2 fun i => (hT i i).continuousAt.eventually_ne (hv i)
  have hc : ∀ᶠ x in 𝓝 v, (∀ i j, j < i → conn T x ξ i j = 0) ∧
      ∀ i, conn T x ξ i i = (T x i i)⁻¹ * del (fun y => T y i i) x ξ := by
    filter_upwards [h0.eventually_nhds, hne] with x h1 h2
    exact conn_lowerTriangular h1 h2 ξ
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [curv, Matrix.neg_apply, mdbar_apply,
      dbar_congr (g := fun _ => (0 : ℂ)) (hc.mono fun y hy => hy.1 i j hij)]
    simp
  · let H : V n → Matrix (Fin 1) (Fin 1) ℂ := fun x => Matrix.of fun _ _ => T x i i
    have hH : ∀ᶠ x in 𝓝 v, conn T x ξ i i = conn H x ξ 0 0 := by
      filter_upwards [hc, hne] with x h1 h2
      rw [h1.2 i, (conn_lowerTriangular (T := H)
        (Eventually.of_forall fun _ a b hab => absurd (Subsingleton.elim a b) hab.ne)
        (fun _ => h2 i) ξ).2 0]
      rfl
    have hs : ContDiffAt ℝ 2 (d i) v := by
      have h1 : ContDiffAt ℝ 2 (fun x => (T x i i).re) v :=
        Complex.reCLM.contDiff.contDiffAt.comp v ((hT i i).of_le (by norm_cast))
      refine h1.congr_of_eventuallyEq (he.mono fun x hx => ?_)
      simp [hx.2 i]
    rw [← curv_line (H := H) hs (hd i).ne' (he.mono fun x hx => hx.2 i) ξ η 0 0, curv, curv,
      Matrix.neg_apply, Matrix.neg_apply, mdbar_apply, mdbar_apply, dbar_congr hH]

end GlobalTheory.ChernCalc
