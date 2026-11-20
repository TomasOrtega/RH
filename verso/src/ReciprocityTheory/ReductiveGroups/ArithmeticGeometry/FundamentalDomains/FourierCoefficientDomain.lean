import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientMatrices
import Lemmata.GeneralBFactBisForm.Imports

namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology

noncomputable section

section Cauchy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_bis_form.goal1 .. | (apply Bl.general_b_fact_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_form.goal1 <;> assumption)`.
-/
lemma norm_fderiv_le {U : Set F} (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U)
    {y : F} {R C : ℝ} (hR : 0 < R) (hball : closedBall y R ⊆ U)
    (hC : ∀ z ∈ closedBall y R, ‖G z‖ ≤ C) : ‖fderiv ℂ G y‖ ≤ C / R := by
  first | exact Bl.general_b_fact_bis_form.goal1 .. | (apply Bl.general_b_fact_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_form.goal1 <;> assumption)

end Cauchy

section Param

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ}

/- English proof (translation)
Introduce `x0 hx0`. Establish `hcA : ∀ x, Continuous fun t => A t x` using `fun x => hA.clm_apply continuous_const`. Use `set K0 := (fun t => A t x0) '' K with hK0def`. Establish `hK0 : IsCompact K0` using `hK.image (hcA x0)`. Establish `hK0U : K0 ⊆ U` using `by rintro _ ⟨t, ht, rfl⟩; exact hAU t ht x0 hx0`.

Take `⟨δ, hδ, hδU⟩` from `hK0.exists_cthickening_subset_open hU hK0U`. Establish `hK1 : IsCompact (cthickening δ K0)` using `hK0.cthickening`. Take `⟨C, hC⟩` from `hK1.exists_bound_of_continuousOn (hG.continuousOn.mono hδU)`. Take `⟨Am, hAm⟩` from `hK.exists_bound_of_continuousOn hA.continuousOn`. Take `⟨Me, hMe⟩` from `hK.exists_bound_of_continuousOn he.continuousOn`.

Use `set A1 := max Am 1 with hA1def`. Establish `hA1 : 0 < A1` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Use `set ε := δ / 2 / A1 with hεdef`. Establish `hε : 0 < ε` using `by positivity`. Establish `hnear : ∀ t ∈ K, ∀ x ∈ ball x0 ε, closedBall (A t x) (δ / 2) ⊆ cthickening δ K0`.

Introduce `t ht x hx z hz`. Establish `hx' : ‖x - x0‖ < ε` using `by rw [← dist_eq_norm]; exact hx`. Establish `h1 : dist (A t x) (A t x0) ≤ δ / 2`. Rewrite using `[dist_eq_norm, ← map_sub]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : dist z (A t x0) ≤ δ`. Combine the linear relations using `[dist_triangle z (A t x) (A t x0), mem_closedBall.1 hz]`. Conclude with `mem_cthickening_of_dist_le z (A t x0) δ K0 ⟨t, ht, rfl⟩ h2`. Establish `hin : ∀ t ∈ K, ∀ x ∈ ball x0 ε, A t x ∈ U` using `fun t ht x hx => hδU (hnear t ht x hx (mem_closedBall_self (by positivity)))`. Establish `hfd : ∀ t ∈ K, ∀ x ∈ ball x0 ε, ‖fderiv ℂ G (A t x)‖ ≤ C / (δ / 2)` using `fun t ht x hx => norm_fderiv_le hU hG (by positivity) ((hnear t ht x hx).trans hδU) (fun z hz => hC z (hnear t ht x hx hz))`.

Establish `hball : ball x0 ε ∈ 𝓝 x0` using `ball_mem_nhds x0 hε`. Establish `hcont : ∀ x ∈ ball x0 ε, ContinuousOn (fun t => G (A t x) * e t) K` using `fun x hx => (hG.continuousOn.comp (hcA x).continuousOn (fun t ht => hin t ht x hx)).mul he.continuousOn`. Establish `hfin : IsFiniteMeasure (volume.restrict K)` using `⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩`. Establish `m1 : Measurable fun t => fderiv ℂ G (A t x0)` using `(measurable_fderiv ℂ G).comp (hcA x0).measurable`. Establish `m2 : Measurable fun t => (fderiv ℂ G (A t x0)).comp (A t)` using `(isBoundedBilinearMap_comp.continuous.measurable).comp (m1.prodMk hA.measurable)`.

Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K) (F := fun x t => G (A t x) * e t) (F' := fun x t => e t • (fderiv ℂ G (A t x)).comp (A t)) (bound := fun _ => Me * (C / (δ / 2) * A1)) hball (by filter_upwards [hball] with x hx; exact (hcont x hx).aestrongly …`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul (hMe t ht) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hMe t ht))` and prove the remaining obligations. Conclude with `(ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hfd t ht x hx) (le_trans (hAm t ht) (le_max_left _ _)) (norm_nonneg _) (le_trans (norm_nonneg _) (hfd t ht x hx)))))`. Use the proof step `(integrable_const _)`.

Use the proof step `((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by`. Establish `h1 : HasFDerivAt G (fderiv ℂ G (A t x)) (A t x)` using `(hG.differentiableAt (hU.mem_nhds (hin t ht x hx))).hasFDerivAt`. Conclude with `(h1.comp x (A t).hasFDerivAt).mul_const (e t)))`. Conclude with `key.differentiableAt.differentiableWithinAt`.
-/
theorem diffOn_param {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKm : MeasurableSet K)
    (A : (Fin n → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t ∈ K, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (Fin n → ℝ) → ℂ) (he : Continuous e) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  have hcA : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  set K0 := (fun t => A t x0) '' K with hK0def
  have hK0 : IsCompact K0 := hK.image (hcA x0)
  have hK0U : K0 ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hAU t ht x0 hx0
  obtain ⟨δ, hδ, hδU⟩ := hK0.exists_cthickening_subset_open hU hK0U
  have hK1 : IsCompact (cthickening δ K0) := hK0.cthickening
  obtain ⟨C, hC⟩ := hK1.exists_bound_of_continuousOn (hG.continuousOn.mono hδU)
  obtain ⟨Am, hAm⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨Me, hMe⟩ := hK.exists_bound_of_continuousOn he.continuousOn
  set A1 := max Am 1 with hA1def
  have hA1 : 0 < A1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := δ / 2 / A1 with hεdef
  have hε : 0 < ε := by positivity
  have hnear : ∀ t ∈ K, ∀ x ∈ ball x0 ε, closedBall (A t x) (δ / 2) ⊆ cthickening δ K0 := by
    intro t ht x hx z hz
    have hx' : ‖x - x0‖ < ε := by rw [← dist_eq_norm]; exact hx
    have h1 : dist (A t x) (A t x0) ≤ δ / 2 := by
      rw [dist_eq_norm, ← map_sub]
      calc ‖A t (x - x0)‖ ≤ ‖A t‖ * ‖x - x0‖ := (A t).le_opNorm _
        _ ≤ A1 * ε := mul_le_mul (le_trans (hAm t ht) (le_max_left _ _)) hx'.le (norm_nonneg _) hA1.le
        _ = δ / 2 := by rw [hεdef]; field_simp
    have h2 : dist z (A t x0) ≤ δ := by
      linarith [dist_triangle z (A t x) (A t x0), mem_closedBall.1 hz]
    exact mem_cthickening_of_dist_le z (A t x0) δ K0 ⟨t, ht, rfl⟩ h2
  have hin : ∀ t ∈ K, ∀ x ∈ ball x0 ε, A t x ∈ U := fun t ht x hx =>
    hδU (hnear t ht x hx (mem_closedBall_self (by positivity)))
  have hfd : ∀ t ∈ K, ∀ x ∈ ball x0 ε, ‖fderiv ℂ G (A t x)‖ ≤ C / (δ / 2) := fun t ht x hx =>
    norm_fderiv_le hU hG (by positivity) ((hnear t ht x hx).trans hδU)
      (fun z hz => hC z (hnear t ht x hx hz))
  have hball : ball x0 ε ∈ 𝓝 x0 := ball_mem_nhds x0 hε
  have hcont : ∀ x ∈ ball x0 ε, ContinuousOn (fun t => G (A t x) * e t) K := fun x hx =>
    (hG.continuousOn.comp (hcA x).continuousOn (fun t ht => hin t ht x hx)).mul he.continuousOn
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have m1 : Measurable fun t => fderiv ℂ G (A t x0) := (measurable_fderiv ℂ G).comp (hcA x0).measurable
  have m2 : Measurable fun t => (fderiv ℂ G (A t x0)).comp (A t) :=
    (isBoundedBilinearMap_comp.continuous.measurable).comp (m1.prodMk hA.measurable)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t)
    (F' := fun x t => e t • (fderiv ℂ G (A t x)).comp (A t))
    (bound := fun _ => Me * (C / (δ / 2) * A1)) hball
    (by filter_upwards [hball] with x hx; exact (hcont x hx).aestronglyMeasurable hKm)
    ((hcont x0 (mem_ball_self hε)).integrableOn_compact hK)
    ((he.measurable.smul m2).aestronglyMeasurable)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      calc ‖e t • (fderiv ℂ G (A t x)).comp (A t)‖
          = ‖e t‖ * ‖(fderiv ℂ G (A t x)).comp (A t)‖ := norm_smul _ _
        _ ≤ Me * (C / (δ / 2) * A1) := by
          refine mul_le_mul (hMe t ht) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hMe t ht))
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hfd t ht x hx)
            (le_trans (hAm t ht) (le_max_left _ _)) (norm_nonneg _)
            (le_trans (norm_nonneg _) (hfd t ht x hx)))))
    (integrable_const _)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      have h1 : HasFDerivAt G (fderiv ℂ G (A t x)) (A t x) :=
        (hG.differentiableAt (hU.mem_nhds (hin t ht x hx))).hasFDerivAt
      exact (h1.comp x (A t).hasFDerivAt).mul_const (e t)))
  exact key.differentiableAt.differentiableWithinAt

end Param

section Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Simplify using `only [gram, hermC, col, mat, Matrix.of_apply]`. Use `fun_prop`.
-/
lemma cont_gram (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

/- English proof (translation)
Establish `h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩ ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re})`. Use extensionality with `x`. Simplify using `[Data.dom, GG]`. Rewrite using `[h]`. Use `isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)` and prove the remaining obligations.

Conclude with `isOpen_ne_fun (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det continuous_const`. Conclude with `isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp ((cont_gram X τ).matrix_submatrix _ _).matrix_det))`.
-/
lemma isOpen_dom : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x; simp [Data.dom, GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det
      continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      ((cont_gram X τ).matrix_submatrix _ _).matrix_det))

def ZbL (b : X.Ψ → Fin 2 → Fin 2 → ℂ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.Zb u b
      map_add' x y := by
        funext τ
        show X.zmat u b τ * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.zmat u b τ * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }

/- English proof (translation)
Establish `hB' : ∀ τ i k, Continuous fun t => B t τ i k` using `fun τ i k => by fun_prop`. Use `continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_` and prove the remaining obligations. Simplify using `only [Data.Zb, Data.zmat, Matrix.mul_apply, Matrix.of_apply, mat]`. Use `fun_prop`.
-/
lemma cont_Zb {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) (y : Frame X.Ψ r) : Continuous fun t => X.Zb u (B t) y := by
  have hB' : ∀ τ i k, Continuous fun t => B t τ i k := fun τ i k => by fun_prop
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  simp only [Data.Zb, Data.zmat, Matrix.mul_apply, Matrix.of_apply, mat]
  fun_prop

/- English proof (translation)
The claim follows from `continuous_clm_apply.2 fun y => cont_Zb X u hB y`.
-/
lemma cont_ZbL {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) : Continuous fun t => ZbL X u (B t) :=
  continuous_clm_apply.2 fun y => cont_Zb X u hB y

end Dom

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
