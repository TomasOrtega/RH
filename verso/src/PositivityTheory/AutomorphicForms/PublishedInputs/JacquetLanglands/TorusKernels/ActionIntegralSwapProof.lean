import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.AnnihilatorQuotientResidues

variable {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}

def actEquiv (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

/- English proof (translation)
The claim follows from `(actEquiv hP g).measurableEmbedding`.
-/
lemma embed (hP : Pres G μ) (g : G) : MeasurableEmbedding (fun y : Y => g • y) :=
  (actEquiv hP g).measurableEmbedding

/- English proof (translation)
Rewrite using `[enorm_smul, Real.enorm_eq_ofReal (hb.nonneg y)]`.
-/
lemma enorm_cut {b : Y → ℝ} (hb : IsCut G b) (y : Y) (x : ℂ) :
    ‖b y • x‖ₑ = ENNReal.ofReal (b y) * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg y)]

/- English proof (translation)
Rewrite using `[← lintegral_tsum]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb'.nonneg _) (hb'.sum y).summable, (hb'.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]`. Introduce `g`.

Conclude with `((ENNReal.measurable_ofReal.comp (hb'.meas.comp (hP g).measurable)).mul ((ENNReal.measurable_ofReal.comp hb.meas).mul hu)).aemeasurable`.
-/
lemma lint_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ
      = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ := by
  rw [← lintegral_tsum]
  · congr 1
    funext y
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb'.nonneg _)
      (hb'.sum y).summable, (hb'.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  · intro g
    exact ((ENNReal.measurable_ofReal.comp (hb'.meas.comp (hP g).measurable)).mul
      ((ENNReal.measurable_ofReal.comp hb.meas).mul hu)).aemeasurable

/- English proof (translation)
Establish `h` using `(hP g).lintegral_comp_emb (embed hP g) (fun z => ENNReal.ofReal (b (g⁻¹ • z)) * (ENNReal.ofReal (b' z) * u z))`. Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [inv_smul_smul, hinv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma lint_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℝ≥0∞)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ
      = ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ := by
  have h := (hP g).lintegral_comp_emb (embed hP g)
    (fun z => ENNReal.ofReal (b (g⁻¹ • z)) * (ENNReal.ofReal (b' z) * u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv]
  ring

/- English proof (translation)
Rewrite using `[lint_split hP hb hb' u hu, lint_split hP hb' hb u hu]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma lint_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ = ∫⁻ y, ENNReal.ofReal (b' y) * u y ∂μ := by
  rw [lint_split hP hb hb' u hu, lint_split hP hb' hb u hu]
  calc _ = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ :=
        tsum_congr (lint_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq
        (fun g => ∫⁻ y, ENNReal.ofReal (b (g • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ)

/- English proof (translation)
Use `⟨(hb'.meas.smul hu).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Establish `h` using `hi.hasFiniteIntegral`. Establish `e` using `lint_eq hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm (fun g y => by simp only [hinv])`. Simplify using `only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h ⊢`. Rewrite using `[← e]` and apply the resulting hypothesis.
-/
lemma integrable_swap [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) : Integrable (fun y => b' y • u y) μ := by
  refine ⟨(hb'.meas.smul hu).aestronglyMeasurable, ?_⟩
  have h := hi.hasFiniteIntegral
  have e := lint_eq hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm (fun g y => by simp only [hinv])
  simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h ⊢
  rwa [← e]

/- English proof (translation)
Rewrite using `[← integral_tsum]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[(hb'.sum y).summable.tsum_smul_const, (hb'.sum y).tsum_eq, one_smul]`. Introduce `g`.

Conclude with `((hb'.meas.comp (hP g).measurable).smul (hb.meas.smul hu)).aestronglyMeasurable`. Establish `h` using `hi.hasFiniteIntegral`. Establish `e` using `lint_split hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm`. Simplify using `only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h e ⊢`. Rewrite using `[← e]`.

Conclude with `h.ne`.
-/
lemma int_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hi : Integrable (fun y => b y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∑' g : G, ∫ y, b' (g • y) • (b y • u y) ∂μ := by
  rw [← integral_tsum]
  · congr 1
    funext y
    rw [(hb'.sum y).summable.tsum_smul_const, (hb'.sum y).tsum_eq, one_smul]
  · intro g
    exact ((hb'.meas.comp (hP g).measurable).smul (hb.meas.smul hu)).aestronglyMeasurable
  · have h := hi.hasFiniteIntegral
    have e := lint_split hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm
    simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h e ⊢
    rw [← e]
    exact h.ne

/- English proof (translation)
Establish `h` using `(hP g).integral_comp (embed hP g) (fun z => b (g⁻¹ • z) • (b' z • u z))`. Rewrite using `[← h]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [inv_smul_smul, hinv]`.

Rewrite using `[smul_comm]`.
-/
lemma int_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℂ)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫ y, b' (g • y) • (b y • u y) ∂μ = ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := by
  have h := (hP g).integral_comp (embed hP g) (fun z => b (g⁻¹ • z) • (b' z • u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv]
  rw [smul_comm]

/- English proof (translation)
Rewrite using `[int_split hP hb hb' u hu hi, int_split hP hb' hb u hu hi']`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma int_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) (hi' : Integrable (fun y => b' y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∫ y, b' y • u y ∂μ := by
  rw [int_split hP hb hb' u hu hi, int_split hP hb' hb u hu hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr (int_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq (fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ)

end UpperTheory.Esk.AnnihilatorQuotientResidues

/- English proof (translation)
Introduce `G Y _ _ _ _ μ hP b b' hb hb'`. Use `⟨fun u hu hinv => UpperTheory.Esk.AnnihilatorQuotientResidues.lint_eq hP hb hb' u hu hinv, fun u hu hinv hi => ?_⟩` and prove the remaining obligations. Establish `hi'` using `UpperTheory.Esk.AnnihilatorQuotientResidues.integrable_swap hP hb hb' u hu hinv hi`. Conclude with `⟨hi', UpperTheory.Esk.AnnihilatorQuotientResidues.int_eq hP hb hb' u hu hinv hi hi'⟩`.
-/
theorem UpperTheory.Esk.action_integral_swap_proof : UpperTheory.Esk.C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  refine ⟨fun u hu hinv => UpperTheory.Esk.AnnihilatorQuotientResidues.lint_eq hP hb hb' u hu hinv, fun u hu hinv hi => ?_⟩
  have hi' := UpperTheory.Esk.AnnihilatorQuotientResidues.integrable_swap hP hb hb' u hu hinv hi
  exact ⟨hi', UpperTheory.Esk.AnnihilatorQuotientResidues.int_eq hP hb hb' u hu hinv hi hi'⟩
