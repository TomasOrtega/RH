import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero

namespace GlobalTheory.Dict

section General
open Filter Topology

/- English proof (translation)
Distinguish the cases in `hz : ∀ i, ∀ x ∈ U, T i x = 0`. Use `⟨(ρ : ℂ), Complex.ofReal_ne_zero.mpr hρ.ne', fun i x hx => ?_⟩` and prove the remaining obligations. Take `⟨k, -, hk⟩` from `h x hx`. Rewrite using `[hk i, hz i x hx, mul_zero, mul_zero]`. Simplify using `only [not_forall, exists_prop] at hz`.

Take `⟨j, x0, hx0, hTj⟩` from `hz`. Establish `hev : ∀ᶠ y in 𝓝 x0, y ∈ U ∧ T j y ≠ 0` using `(hU.eventually_mem hx0).and (((hT j).continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne hTj)`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff_ball.mp hev`. Establish `hsub : Metric.ball x0 ε ⊆ U` using `fun y hy => (hball y hy).1`. Establish `hqd : DifferentiableOn ℂ (fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε)` using `fun y hy => (((hR j).mono hsub) y hy).mul ((((hT j).mono hsub) y hy).inv (hball y hy).2)`.

Establish `hqk : ∀ y ∈ Metric.ball x0 ε, ∀ k : ℂ, (∀ i, R i y = k * T i y) → R j y * (T j y)⁻¹ = k`. Introduce `y hy k hk`. Rewrite using `[hk j, mul_inv_cancel_right₀ (hball y hy).2]`. Establish `hqn : ∀ y ∈ Metric.ball x0 ε, ‖R j y * (T j y)⁻¹‖ = ρ`. Introduce `y hy`.

Take `⟨k, hkn, hk⟩` from `h y (hsub hy)`. Rewrite using `[hqk y hy k hk, hkn]`. Establish `hx0b : x0 ∈ Metric.ball x0 ε` using `Metric.mem_ball_self hε`. Establish `hmax : IsMaxOn (norm ∘ fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) x0` using `isMaxOn_iff.mpr fun y hy => by`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[hqn y hy, hqn x0 hx0b]`. Establish `hqc` using `Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x0 ε).isPreconnected Metric.isOpen_ball hqd hx0b hmax`. Use `set C : ℂ := R j x0 * (T j x0)⁻¹ with hCdef`. Establish `hCn : ‖C‖ = ρ` using `hqn x0 hx0b`. Establish `hC0 : C ≠ 0`.

Introduce `h0`. Rewrite `hCn` using `[h0, norm_zero]`. Conclude with `hρ.ne' hCn.symm`. Establish `hloc : ∀ y ∈ Metric.ball x0 ε, ∀ i, R i y = C * T i y`. Introduce `y hy i`.

Take `⟨k, -, hk⟩` from `h y (hsub hy)`. Establish `hqy : R j y * (T j y)⁻¹ = C` using `hqc hy`. Rewrite using `[hk i, ← hqk y hy k hk, hqy]`. Set `S : Set V` to `{x | ∀ᶠ y in 𝓝 x, ∀ i, R i y = C * T i y}`. Establish `hSo : IsOpen S` using `isOpen_setOfPred_eventually_nhds`.

Establish `hx0S : x0 ∈ S` using `Filter.eventually_of_mem (Metric.ball_mem_nhds x0 hε) hloc`. Establish `hcl : closure S ∩ U ⊆ S`. Introduce and unpack `y ⟨hyS, hyU⟩`. Take `⟨δ, hδ, hδU⟩` from `Metric.isOpen_iff.mp hU y hyU`. Establish `hδ4 : 0 < δ / 4` using `by linarith`.

Take `⟨x1, hx1S, hdist⟩` from `Metric.mem_closure_iff.mp hyS (δ / 4) hδ4`. Use `Filter.eventually_of_mem (Metric.ball_mem_nhds y hδ4) fun z hz i => ?_` and prove the remaining obligations. Establish `hφD : ∀ t ∈ Metric.ball (0 : ℂ) (3 / 2), x1 + t • (z - x1) ∈ Metric.ball y δ`. Introduce `t ht`. Establish `ht' : ‖t‖ < 3 / 2` using `by simpa using ht`.

Establish `hx1' : ‖x1 - y‖ < δ / 4` using `by rw [← dist_eq_norm, dist_comm]; exact hdist`. Establish `hz' : ‖z - y‖ < δ / 4` using `by rw [← dist_eq_norm]; exact hz`. Establish `hw : ‖z - x1‖ ≤ ‖z - y‖ + ‖x1 - y‖`. Combine the equalities or inequalities in the displayed calculation. Establish `htw : ‖t • (z - x1)‖ ≤ 3 / 2 * ‖z - x1‖`.

Rewrite using `[norm_smul]`. Conclude with `mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)`. Rewrite using `[Metric.mem_ball, dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation. Establish `hφc : Continuous fun t : ℂ => x1 + t • (z - x1)` using `by fun_prop`.

Establish `hgd : DifferentiableOn ℂ (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1))) (Metric.ball (0 : ℂ) (3 / 2))`. Introduce `t ht`. Establish `hmem : x1 + t • (z - x1) ∈ U` using `hδU (hφD t ht)`. Establish `hlin : DifferentiableAt ℂ (fun t : ℂ => x1 + t • (z - x1)) t` using `by fun_prop`. Establish `h1 : DifferentiableAt ℂ (R i) (x1 + t • (z - x1))` using `(hR i).differentiableAt (hU.mem_nhds hmem)`.

Establish `h2 : DifferentiableAt ℂ (T i) (x1 + t • (z - x1))` using `(hT i).differentiableAt (hU.mem_nhds hmem)`. Conclude with `((h1.comp t hlin).sub ((h2.comp t hlin).const_mul C)).differentiableWithinAt`. Establish `htend : Filter.Tendsto (fun t : ℂ => x1 + t • (z - x1)) (𝓝 0) (𝓝 x1)` using `hφc.tendsto' 0 x1 (by simp)`. Establish `hg0 : (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1))) =ᶠ[𝓝 0] 0` using `(htend.eventually hx1S).mono fun t ht => by`. Simplify using `only [Pi.zero_apply]`.

Rewrite using `[ht i, sub_self]`. Establish `h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (3 / 2)`. Rewrite using `[Metric.mem_ball, dist_zero_right, norm_one]`. Evaluate the numerical expressions. Establish `hg1` using `(hgd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) (3 / 2)).isPreconnected (Metric.mem_ball_self (by norm_num)) hg0 h1mem`.

Establish `hz1 : x1 + (1 : ℂ) • (z - x1) = z` using `by rw [one_smul, add_sub_cancel]`. Simplify using `only [Pi.zero_apply, hz1] at hg1`. Conclude with `sub_eq_zero.mp hg1`. Establish `hUS : U ⊆ S` using `hc.subset_of_closure_inter_subset hSo ⟨x0, hx0, hx0S⟩ hcl`. Conclude with `⟨C, hC0, fun i x hx => (hUS hx).self_of_nhds i⟩`.
-/
theorem const_of_norm_factor {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {U : Set V}
    (hU : IsOpen U) (hc : IsPreconnected U) {J : Type*} (R T : J → V → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hR : ∀ i, DifferentiableOn ℂ (R i) U) (hT : ∀ i, DifferentiableOn ℂ (T i) U)
    (h : ∀ x ∈ U, ∃ k : ℂ, ‖k‖ = ρ ∧ ∀ i, R i x = k * T i x) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ U, R i x = C * T i x := by
  by_cases hz : ∀ i, ∀ x ∈ U, T i x = 0
  ·
    refine ⟨(ρ : ℂ), Complex.ofReal_ne_zero.mpr hρ.ne', fun i x hx => ?_⟩
    obtain ⟨k, -, hk⟩ := h x hx
    rw [hk i, hz i x hx, mul_zero, mul_zero]
  simp only [not_forall, exists_prop] at hz
  obtain ⟨j, x0, hx0, hTj⟩ := hz

  have hev : ∀ᶠ y in 𝓝 x0, y ∈ U ∧ T j y ≠ 0 :=
    (hU.eventually_mem hx0).and (((hT j).continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne hTj)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hsub : Metric.ball x0 ε ⊆ U := fun y hy => (hball y hy).1

  have hqd : DifferentiableOn ℂ (fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) := fun y hy =>
    (((hR j).mono hsub) y hy).mul ((((hT j).mono hsub) y hy).inv (hball y hy).2)
  have hqk : ∀ y ∈ Metric.ball x0 ε, ∀ k : ℂ, (∀ i, R i y = k * T i y) → R j y * (T j y)⁻¹ = k := by
    intro y hy k hk
    rw [hk j, mul_inv_cancel_right₀ (hball y hy).2]
  have hqn : ∀ y ∈ Metric.ball x0 ε, ‖R j y * (T j y)⁻¹‖ = ρ := by
    intro y hy
    obtain ⟨k, hkn, hk⟩ := h y (hsub hy)
    rw [hqk y hy k hk, hkn]
  have hx0b : x0 ∈ Metric.ball x0 ε := Metric.mem_ball_self hε
  have hmax : IsMaxOn (norm ∘ fun y => R j y * (T j y)⁻¹) (Metric.ball x0 ε) x0 :=
    isMaxOn_iff.mpr fun y hy => by
      simp only [Function.comp_apply]
      rw [hqn y hy, hqn x0 hx0b]

  have hqc := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball x0 ε).isPreconnected
    Metric.isOpen_ball hqd hx0b hmax
  set C : ℂ := R j x0 * (T j x0)⁻¹ with hCdef
  have hCn : ‖C‖ = ρ := hqn x0 hx0b
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hCn
    exact hρ.ne' hCn.symm
  have hloc : ∀ y ∈ Metric.ball x0 ε, ∀ i, R i y = C * T i y := by
    intro y hy i
    obtain ⟨k, -, hk⟩ := h y (hsub hy)
    have hqy : R j y * (T j y)⁻¹ = C := hqc hy
    rw [hk i, ← hqk y hy k hk, hqy]

  let S : Set V := {x | ∀ᶠ y in 𝓝 x, ∀ i, R i y = C * T i y}
  have hSo : IsOpen S := isOpen_setOfPred_eventually_nhds
  have hx0S : x0 ∈ S := Filter.eventually_of_mem (Metric.ball_mem_nhds x0 hε) hloc
  have hcl : closure S ∩ U ⊆ S := by
    rintro y ⟨hyS, hyU⟩
    obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU y hyU
    have hδ4 : 0 < δ / 4 := by linarith
    obtain ⟨x1, hx1S, hdist⟩ := Metric.mem_closure_iff.mp hyS (δ / 4) hδ4
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds y hδ4) fun z hz i => ?_

    have hφD : ∀ t ∈ Metric.ball (0 : ℂ) (3 / 2), x1 + t • (z - x1) ∈ Metric.ball y δ := by
      intro t ht
      have ht' : ‖t‖ < 3 / 2 := by simpa using ht
      have hx1' : ‖x1 - y‖ < δ / 4 := by rw [← dist_eq_norm, dist_comm]; exact hdist
      have hz' : ‖z - y‖ < δ / 4 := by rw [← dist_eq_norm]; exact hz
      have hw : ‖z - x1‖ ≤ ‖z - y‖ + ‖x1 - y‖ := by
        calc ‖z - x1‖ = ‖(z - y) - (x1 - y)‖ := by congr 1; abel
          _ ≤ ‖z - y‖ + ‖x1 - y‖ := norm_sub_le _ _
      have htw : ‖t • (z - x1)‖ ≤ 3 / 2 * ‖z - x1‖ := by
        rw [norm_smul]; exact mul_le_mul_of_nonneg_right ht'.le (norm_nonneg _)
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖x1 + t • (z - x1) - y‖ = ‖(x1 - y) + t • (z - x1)‖ := by congr 1; abel
        _ ≤ ‖x1 - y‖ + ‖t • (z - x1)‖ := norm_add_le _ _
        _ < δ := by linarith
    have hφc : Continuous fun t : ℂ => x1 + t • (z - x1) := by fun_prop

    have hgd : DifferentiableOn ℂ (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1)))
        (Metric.ball (0 : ℂ) (3 / 2)) := by
      intro t ht
      have hmem : x1 + t • (z - x1) ∈ U := hδU (hφD t ht)
      have hlin : DifferentiableAt ℂ (fun t : ℂ => x1 + t • (z - x1)) t := by fun_prop
      have h1 : DifferentiableAt ℂ (R i) (x1 + t • (z - x1)) := (hR i).differentiableAt (hU.mem_nhds hmem)
      have h2 : DifferentiableAt ℂ (T i) (x1 + t • (z - x1)) := (hT i).differentiableAt (hU.mem_nhds hmem)
      exact ((h1.comp t hlin).sub ((h2.comp t hlin).const_mul C)).differentiableWithinAt

    have htend : Filter.Tendsto (fun t : ℂ => x1 + t • (z - x1)) (𝓝 0) (𝓝 x1) :=
      hφc.tendsto' 0 x1 (by simp)
    have hg0 : (fun t : ℂ => R i (x1 + t • (z - x1)) - C * T i (x1 + t • (z - x1))) =ᶠ[𝓝 0] 0 :=
      (htend.eventually hx1S).mono fun t ht => by
        simp only [Pi.zero_apply]
        rw [ht i, sub_self]

    have h1mem : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (3 / 2) := by
      rw [Metric.mem_ball, dist_zero_right, norm_one]; norm_num
    have hg1 := (hgd.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) (3 / 2)).isPreconnected (Metric.mem_ball_self (by norm_num)) hg0 h1mem
    have hz1 : x1 + (1 : ℂ) • (z - x1) = z := by rw [one_smul, add_sub_cancel]
    simp only [Pi.zero_apply, hz1] at hg1
    exact sub_eq_zero.mp hg1
  have hUS : U ⊆ S := hc.subset_of_closure_inter_subset hSo ⟨x0, hx0, hx0S⟩ hcl
  exact ⟨C, hC0, fun i x hx => (hUS hx).self_of_nhds i⟩

end General

end GlobalTheory.Dict

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

/- English proof (translation)
Unfold `bchar`. Use `Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_` and prove the remaining obligations. Establish `htri : (mat b τ).BlockTriangular id` using `fun a c hca => (hb τ).2 a c hca`. Establish `hdet` using `(hb τ).1`. Rewrite `hdet` using `[Matrix.det_of_isUpperTriangular htri]`.

Conclude with `Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)`.
-/
theorem bchar_ne_zero_of_mem_bor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (la : Wt Ψ r)
    {b : Frame Ψ r} (hb : b ∈ Bor Ψ r) : bchar la b ≠ 0 := by
  unfold bchar
  refine Finset.prod_ne_zero_iff.mpr fun τ _ => Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ ?_

  have htri : (mat b τ).BlockTriangular id := fun a c hca => (hb τ).2 a c hca
  have hdet := (hb τ).1
  rw [Matrix.det_of_isUpperTriangular htri] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

/- English proof (translation)
Rewrite using `[psgn, Finset.abs_prod]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem abs_psgn' (p0 n : ℕ) : |psgn p0 n| = 1 := by
  rw [psgn, Finset.abs_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[dmin, lminor, hx, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn, Complex.ofReal_prod, Finset.prod_range]`. Simplify using the standard rewrite rules.
-/
private theorem dmin_eq_psgn_of_gram_diagonal {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
    {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (p0 : ℕ) (x : Frame Ψ r) (τ : Ψ)
    (hx : gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ))
    (i : Fin (r + 1)) : dmin G x τ i = ((psgn p0 i : ℝ) : ℂ) := by
  rw [dmin, lminor, hx, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, psgn,
    Complex.ofReal_prod, Finset.prod_range]
  simp

/- English proof (translation)
Take `⟨x₀, b, hb, hgram, rfl⟩` from `(GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx`. Use `⟨b, hb, fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩` and prove the remaining obligations. Use `show (mat x τ * mat b τ).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero (hx τ).1 (hb τ).1`.

Rewrite using `[dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.ofReal_re]`. Establish `h1` using `abs_psgn' X.p0 i`. Use `mul_self_pos.mpr fun h0 => ?_` and prove the remaining obligations. Rewrite `h1` using `[h0, abs_zero]`. Conclude with `zero_ne_one h1`.

Rewrite using `[dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.norm_real, Real.norm_eq_abs, abs_psgn']`.
-/
theorem exists_unitFr_rmul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ IsUnitFr X (rmul x b) := by
  obtain ⟨x₀, b, hb, hgram, rfl⟩ :=
    (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r X.p0 X.Ψ X.Gm X.Gm_herm).1 x hx
  refine ⟨b, hb, fun τ => ⟨?_, fun i => ?_⟩, fun τ i => ?_⟩
  · show (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.ofReal_re]
    have h1 := abs_psgn' X.p0 i
    refine mul_self_pos.mpr fun h0 => ?_
    rw [h0, abs_zero] at h1
    exact zero_ne_one h1
  · rw [dmin_eq_psgn_of_gram_diagonal X.Gm X.p0 _ τ (hgram τ) i, Complex.norm_real, Real.norm_eq_abs, abs_psgn']

/- English proof (translation)
Introduce `E _ _ _ r X la Jx R T ρ hρ hRT hunit`. Establish `hcd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i`. Introduce `τ i`. Unfold `dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat`. Use `fun_prop`.

Establish `hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det`. Introduce `τ`. Unfold `mat`. Use `fun_prop`. Establish `hopen : IsOpen X.dom` using `by show IsOpen {x | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}`.

Simplify using `only [Set.ofPred_forall, Set.ofPred_and]`. Conclude with `isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp (hcd τ i))))`. Establish `hconn : IsPreconnected X.dom` using `(GlobalTheory.frames_isConnected E r X).isPreconnected`. Use `const_of_norm_factor hopen hconn R T ρ hρ (fun i => (hRT i).1) (fun i => (hRT i).2.1) ?_` and prove the remaining obligations. Introduce `x hx`.

Take `⟨b, hb, hxb, hu⟩` from `exists_unitFr_rmul X hx`. Take `⟨κ, hκ, hRTκ⟩` from `hunit _ hxb hu`. Use `⟨κ, hκ, fun i => ?_⟩` and prove the remaining obligations. Establish `hne` using `bchar_ne_zero_of_mem_bor la hb`. Establish `h1` using `hRTκ i`.

Rewrite `h1` using `[((hRT i).2.2 x hx b hb).1, ((hRT i).2.2 x hx b hb).2]`. Apply `mul_left_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem const_of_norm_factor_unitFr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (Jx : Type) (R T : Jx → Frame X.Ψ r → ℂ) (ρ : ℝ), 0 < ρ → (∀ i, DifferentiableOn ℂ (R i) X.dom ∧ DifferentiableOn ℂ (T i) X.dom ∧ ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, R i (rmul x b) = bchar la b * R i x ∧ T i (rmul x b) = bchar la b * T i x) → (∀ x ∈ X.dom, IsUnitFr X x → ∃ κ : ℂ, ‖κ‖ = ρ ∧ ∀ i, R i x = κ * T i x) → ∃ C : ℂ, C ≠ 0 ∧ ∀ i, ∀ x ∈ X.dom, R i x = C * T i x := by
  intro E _ _ _ r X la Jx R T ρ hρ hRT hunit
  have hcd : ∀ (τ : X.Ψ) (i : Fin (r + 1)), Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
    intro τ i
    unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
    fun_prop
  have hdet : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => (mat x τ).det := by
    intro τ
    unfold mat
    fun_prop
  have hopen : IsOpen X.dom := by
    show IsOpen {x | ∀ τ : X.Ψ, (mat x τ).det ≠ 0 ∧ ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}
    simp only [Set.ofPred_forall, Set.ofPred_and]
    exact isOpen_iInter_of_finite fun τ => (isOpen_ne_fun (hdet τ) continuous_const).inter
      (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
        (continuous_const.mul (Complex.continuous_re.comp (hcd τ i))))
  have hconn : IsPreconnected X.dom := (GlobalTheory.frames_isConnected E r X).isPreconnected
  refine const_of_norm_factor hopen hconn R T ρ hρ (fun i => (hRT i).1) (fun i => (hRT i).2.1) ?_

  intro x hx
  obtain ⟨b, hb, hxb, hu⟩ := exists_unitFr_rmul X hx
  obtain ⟨κ, hκ, hRTκ⟩ := hunit _ hxb hu
  refine ⟨κ, hκ, fun i => ?_⟩
  have hne := bchar_ne_zero_of_mem_bor la hb
  have h1 := hRTκ i
  rw [((hRT i).2.2 x hx b hb).1, ((hRT i).2.2 x hx b hb).2] at h1
  apply mul_left_cancel₀ hne
  rw [h1]
  ring

end GlobalTheory.Dict
