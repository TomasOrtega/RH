import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.JInvariant

open Complex UpperHalfPlane ModularForm EisensteinSeries MatrixGroups Filter Topology Set
open scoped PeriodPair Real Modular

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

/- English proof (translation)
Establish `ha` using `ModularFormClass.analyticAt_cuspFunction_zero (f := E₄) one_pos one_mem_strictPeriods_SL`. Establish `h0 : cuspFunction 1 E₄ 0 = 1`. Use `EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩` as an intermediate fact. Simplify `this` using `[qExpansion_coeff]`. Establish `hcomp : ∀ τ : ℍ, cuspFunction 1 E₄ (Function.Periodic.qParam 1 τ) = E₄ τ` using `fun τ ↦ SlashInvariantFormClass.eq_cuspFunction E₄ τ one_mem_strictPeriods_SL one_ne_zero`.

Use `ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)` as an intermediate fact. Rewrite `this` using `[h0]`. Conclude with `this.congr hcomp`.
-/
theorem tendsto_E₄_atImInfty : Tendsto (fun τ : ℍ ↦ E₄ τ) atImInfty (𝓝 1) := by
  have ha := ModularFormClass.analyticAt_cuspFunction_zero (f := E₄) one_pos
    one_mem_strictPeriods_SL
  have h0 : cuspFunction 1 E₄ 0 = 1 := by
    have := EisensteinSeries.E_qExpansion_coeff_zero (k := 4) (by norm_num) ⟨2, rfl⟩
    simpa [qExpansion_coeff] using this
  have hcomp : ∀ τ : ℍ, cuspFunction 1 E₄ (Function.Periodic.qParam 1 τ) = E₄ τ := fun τ ↦
    SlashInvariantFormClass.eq_cuspFunction E₄ τ one_mem_strictPeriods_SL one_ne_zero
  have := ha.continuousAt.tendsto.comp (qParam_tendsto_atImInfty one_pos)
  rw [h0] at this
  exact this.congr hcomp

/- English proof (translation)
The claim follows from `ModularForm.discriminant_isZeroAtImInfty`.
-/
theorem tendsto_discriminant_atImInfty :
    Tendsto (fun τ : ℍ ↦ ModularForm.discriminant τ) atImInfty (𝓝 0) :=
  ModularForm.discriminant_isZeroAtImInfty

/- English proof (translation)
Establish `h1 : ∀ᶠ τ in atImInfty, (1 / 2 : ℝ) ≤ ‖E₄ τ‖` using `tendsto_E₄_atImInfty.norm.eventually (Ici_mem_nhds (by norm_num))`. Establish `hc : (0 : ℝ) < 1 / (8 * (|R| + 1))` using `by positivity`. Establish `h2 : ∀ᶠ τ in atImInfty, ‖ModularForm.discriminant τ‖ < 1 / (8 * (|R| + 1))` using `tendsto_discriminant_atImInfty.norm.eventually (Iio_mem_nhds (by simpa using hc))`. Use `filter_upwards [h1, h2] with τ h1 h2`. Establish `hpos : 0 < ‖ModularForm.discriminant τ‖` using `norm_pos_iff.2 (ModularForm.discriminant_ne_zero τ)`.

Rewrite using `[modularJ, norm_div, norm_pow, le_div_iff₀ hpos]`. Establish `hR : R ≤ |R| + 1` using `by linarith [le_abs_self R]`. Establish `h3 : (|R| + 1) * ‖ModularForm.discriminant τ‖ ≤ 1 / 8`. Rewrite `h2` using `[lt_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : (1 / 2 : ℝ) ^ 3 ≤ ‖E₄ τ‖ ^ 3` using `pow_le_pow_left₀ (by norm_num) h1 3`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem eventually_le_norm_modularJ (R : ℝ) : ∀ᶠ τ in atImInfty, R ≤ ‖modularJ τ‖ := by
  have h1 : ∀ᶠ τ in atImInfty, (1 / 2 : ℝ) ≤ ‖E₄ τ‖ :=
    tendsto_E₄_atImInfty.norm.eventually (Ici_mem_nhds (by norm_num))
  have hc : (0 : ℝ) < 1 / (8 * (|R| + 1)) := by positivity
  have h2 : ∀ᶠ τ in atImInfty, ‖ModularForm.discriminant τ‖ < 1 / (8 * (|R| + 1)) :=
    tendsto_discriminant_atImInfty.norm.eventually (Iio_mem_nhds (by simpa using hc))
  filter_upwards [h1, h2] with τ h1 h2
  have hpos : 0 < ‖ModularForm.discriminant τ‖ :=
    norm_pos_iff.2 (ModularForm.discriminant_ne_zero τ)
  rw [modularJ, norm_div, norm_pow, le_div_iff₀ hpos]
  have hR : R ≤ |R| + 1 := by linarith [le_abs_self R]
  have h3 : (|R| + 1) * ‖ModularForm.discriminant τ‖ ≤ 1 / 8 := by
    rw [lt_div_iff₀ (by positivity)] at h2
    linarith
  have h4 : (1 / 2 : ℝ) ^ 3 ≤ ‖E₄ τ‖ ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  nlinarith

/- English proof (translation)
The claim follows from `(atImInfty_mem _).1 (eventually_le_norm_modularJ R)`.
-/
theorem exists_le_norm_modularJ (R : ℝ) : ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → R ≤ ‖modularJ τ‖ :=
  (atImInfty_mem _).1 (eventually_le_norm_modularJ R)

def modularJC (z : ℂ) : ℂ := modularJ (ofComplex z)

/- English proof (translation)
Rewrite using `[modularJC, ofComplex_apply]`.
-/
lemma modularJC_coe (τ : ℍ) : modularJC τ = modularJ τ := by
  rw [modularJC, ofComplex_apply]

/- English proof (translation)
Establish `h4 : DifferentiableOn ℂ ((fun τ : ℍ ↦ E₄ τ) ∘ ofComplex) {z : ℂ | 0 < z.im}` using `UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo E₄)`. Establish `hΔ : DifferentiableOn ℂ ((fun τ : ℍ ↦ ModularForm.discriminant τ) ∘ ofComplex) {z : ℂ | 0 < z.im}`. Use `UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo CuspForm.discriminant)` as an intermediate fact. Simplify `this` using `[CuspForm.coe_discriminant]`. Use `(h4.pow 3).div hΔ fun z _ ↦ ModularForm.discriminant_ne_zero _` and prove the remaining obligations.
-/
lemma differentiableOn_modularJC : DifferentiableOn ℂ modularJC {z : ℂ | 0 < z.im} := by
  have h4 : DifferentiableOn ℂ ((fun τ : ℍ ↦ E₄ τ) ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo E₄)
  have hΔ : DifferentiableOn ℂ ((fun τ : ℍ ↦ ModularForm.discriminant τ) ∘ ofComplex)
      {z : ℂ | 0 < z.im} := by
    have := UpperHalfPlane.mdifferentiable_iff.1 (ModularFormClass.holo CuspForm.discriminant)
    simpa [CuspForm.coe_discriminant] using this
  refine (h4.pow 3).div hΔ fun z _ ↦ ModularForm.discriminant_ne_zero _

/- English proof (translation)
The claim follows from `differentiableOn_modularJC.analyticOnNhd isOpen_upperHalfPlaneSet`.
-/
lemma analyticOnNhd_modularJC : AnalyticOnNhd ℂ modularJC {z : ℂ | 0 < z.im} :=
  differentiableOn_modularJC.analyticOnNhd isOpen_upperHalfPlaneSet

/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, rfl⟩`. Conclude with `⟨τ, τ.im_pos, modularJC_coe τ⟩`. Introduce and unpack `⟨z, hz, rfl⟩`.

Conclude with `⟨ofComplex z, rfl⟩`.
-/
lemma range_modularJ : range modularJ = modularJC '' {z : ℂ | 0 < z.im} := by
  ext w
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨τ, τ.im_pos, modularJC_coe τ⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨ofComplex z, rfl⟩

/- English proof (translation)
Introduce and unpack `⟨w, hw⟩`. Take `⟨A, hA⟩` from `exists_le_norm_modularJ (‖w‖ + 1)`. Set `τ : ℍ` to `⟨(|A| + 1) * Complex.I, by simp; positivity⟩`. Establish `hτ : A ≤ τ.im` using `by show A ≤ ((|A| + 1) * Complex.I).im`. Simplify using the standard rewrite rules.

Combine the linear relations using `[le_abs_self A]`. Establish `h1` using `hA τ hτ`. Rewrite `h1` using `[← modularJC_coe, hw _ τ.im_pos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma not_exists_modularJC_const : ¬ ∃ w, ∀ z ∈ {z : ℂ | 0 < z.im}, modularJC z = w := by
  rintro ⟨w, hw⟩
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  let τ : ℍ := ⟨(|A| + 1) * Complex.I, by simp; positivity⟩
  have hτ : A ≤ τ.im := by
    show A ≤ ((|A| + 1) * Complex.I).im
    simp
    linarith [le_abs_self A]
  have h1 := hA τ hτ
  rw [← modularJC_coe, hw _ τ.im_pos] at h1
  linarith

def fdBelow (A : ℝ) : Set ℂ :=
  {z | 1 ≤ normSq z ∧ |z.re| ≤ 1 / 2 ∧ 0 ≤ z.im ∧ z.im ≤ A}

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `hz`. Rewrite `h1` using `[normSq_apply]`. Establish `hre : z.re * z.re ≤ 1 / 4`. Use `abs_le.1 h2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Break down `h3.lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `h1` using `[← h]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma im_pos_of_mem_fdBelow {A : ℝ} {z : ℂ} (hz : z ∈ fdBelow A) : 0 < z.im := by
  obtain ⟨h1, h2, h3, -⟩ := hz
  rw [normSq_apply] at h1
  have hre : z.re * z.re ≤ 1 / 4 := by
    have := abs_le.1 h2
    nlinarith
  rcases h3.lt_or_eq with h | h
  · exact h
  · rw [← h] at h1
    nlinarith

/- English proof (translation)
Use `Metric.isCompact_of_isClosed_isBounded ?_ ?_` and prove the remaining obligations. Conclude with `(isClosed_le continuous_const continuous_normSq).inter ((isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter ((isClosed_le continuous_const Complex.continuous_im).inter (isClosed_le Complex.continuous_im continuous_const)))`. Use `(Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + |A|)).subset fun z hz ↦ ?_` and prove the remaining obligations. Take `⟨-, h2, h3, h4⟩` from `hz`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma isCompact_fdBelow (A : ℝ) : IsCompact (fdBelow A) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_normSq).inter
      ((isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 / 2 + |A|)).subset fun z hz ↦ ?_
    obtain ⟨-, h2, h3, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
      _ ≤ 1 / 2 + |A| :=
        add_le_add h2 (by rw [abs_of_nonneg h3]; exact h4.trans (le_abs_self A))

/- English proof (translation)
Rewrite using `[range_modularJ]`. Break down `analyticOnNhd_modularJC.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected with h | h` into its components or cases. Conclude with `absurd h not_exists_modularJC_const`. Conclude with `h _ subset_rfl isOpen_upperHalfPlaneSet`.
-/
lemma isOpen_range_modularJ : IsOpen (range modularJ) := by
  rw [range_modularJ]
  rcases analyticOnNhd_modularJC.is_constant_or_isOpen
      (convex_halfSpace_im_gt 0).isPreconnected with h | h
  · exact absurd h not_exists_modularJC_const
  · exact h _ subset_rfl isOpen_upperHalfPlaneSet

/- English proof (translation)
Use `closure_subset_iff_isClosed.1 fun w hw ↦ ?_` and prove the remaining obligations. Take `⟨A, hA⟩` from `exists_le_norm_modularJ (‖w‖ + 1)`. Establish `hK : IsCompact (modularJC '' fdBelow A)` using `(isCompact_fdBelow A).image_of_continuousOn (differentiableOn_modularJC.continuousOn.mono fun z hz ↦ im_pos_of_mem_fdBelow hz)`. Establish `hsub : range modularJ ⊆ modularJC '' fdBelow A ∪ {y | ‖w‖ + 1 ≤ ‖y‖}`. Introduce and unpack `_ ⟨τ, rfl⟩`.

Take `⟨g, hg⟩` from `ModularGroup.exists_smul_mem_fd τ`. Rewrite using `[← modularJ_smul g τ]`. Distinguish the cases in `him : A ≤ (g • τ).im`. Conclude with `Or.inr (hA _ him)`. Use `Or.inl ⟨(g • τ : ℍ), ⟨hg.1, hg.2, (g • τ).im_pos.le, ?_⟩, modularJC_coe _⟩` and prove the remaining obligations.

Conclude with `(not_le.1 him).le`. Establish `hclosed : IsClosed (modularJC '' fdBelow A ∪ {y : ℂ | ‖w‖ + 1 ≤ ‖y‖})` using `hK.isClosed.union (isClosed_le continuous_const continuous_norm)`. Break down `closure_minimal hsub hclosed hw with h | h` into its components or cases. Take `⟨z, hz, rfl⟩` from `h`. Conclude with `⟨ofComplex z, rfl⟩`.

Establish `h' : ‖w‖ + 1 ≤ ‖w‖` using `h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma isClosed_range_modularJ : IsClosed (range modularJ) := by
  refine closure_subset_iff_isClosed.1 fun w hw ↦ ?_
  obtain ⟨A, hA⟩ := exists_le_norm_modularJ (‖w‖ + 1)
  have hK : IsCompact (modularJC '' fdBelow A) :=
    (isCompact_fdBelow A).image_of_continuousOn
      (differentiableOn_modularJC.continuousOn.mono fun z hz ↦ im_pos_of_mem_fdBelow hz)
  have hsub : range modularJ ⊆ modularJC '' fdBelow A ∪ {y | ‖w‖ + 1 ≤ ‖y‖} := by
    rintro _ ⟨τ, rfl⟩
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    rw [← modularJ_smul g τ]
    by_cases him : A ≤ (g • τ).im
    · exact Or.inr (hA _ him)
    · refine Or.inl ⟨(g • τ : ℍ), ⟨hg.1, hg.2, (g • τ).im_pos.le, ?_⟩, modularJC_coe _⟩
      exact (not_le.1 him).le
  have hclosed : IsClosed (modularJC '' fdBelow A ∪ {y : ℂ | ‖w‖ + 1 ≤ ‖y‖}) :=
    hK.isClosed.union (isClosed_le continuous_const continuous_norm)
  rcases closure_minimal hsub hclosed hw with h | h
  · obtain ⟨z, hz, rfl⟩ := h
    exact ⟨ofComplex z, rfl⟩
  · have h' : ‖w‖ + 1 ≤ ‖w‖ := h
    linarith

/- English proof (translation)
Establish `h : range modularJ = univ` using `IsClopen.eq_univ ⟨isClosed_range_modularJ, isOpen_range_modularJ⟩ (range_nonempty _)`. Conclude with `Set.range_eq_univ.1 h`.
-/
theorem modularJ_surjective : Function.Surjective modularJ := by
  have h : range modularJ = univ :=
    IsClopen.eq_univ ⟨isClosed_range_modularJ, isOpen_range_modularJ⟩ (range_nonempty _)
  exact Set.range_eq_univ.1 h

/- English proof (translation)
Take `⟨τ, hτ⟩` from `modularJ_surjective W.j`. Use `⟨τ, W.exists_variableChange_of_j_eq _ ?_⟩` and prove the remaining obligations. Rewrite using `[weierstrassCurve_latticeOfTau_j, hτ]`.
-/
theorem exists_variableChange_eq_weierstrassCurve_latticeOfTau (W : WeierstrassCurve ℂ)
    [W.IsElliptic] :
    ∃ τ : ℍ, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve (latticeOfTau τ) := by
  obtain ⟨τ, hτ⟩ := modularJ_surjective W.j
  refine ⟨τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [weierstrassCurve_latticeOfTau_j, hτ]

/- English proof (translation)
Take `⟨τ, C, hC⟩` from `exists_variableChange_eq_weierstrassCurve_latticeOfTau W`. Conclude with `⟨latticeOfTau τ, C, hC⟩`.
-/
theorem exists_variableChange_eq_weierstrassCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ L : PeriodPair, ∃ C : WeierstrassCurve.VariableChange ℂ, C • W = weierstrassCurve L := by
  obtain ⟨τ, C, hC⟩ := exists_variableChange_eq_weierstrassCurve_latticeOfTau W
  exact ⟨latticeOfTau τ, C, hC⟩

end Elliptic
end GroundTheory.Global
