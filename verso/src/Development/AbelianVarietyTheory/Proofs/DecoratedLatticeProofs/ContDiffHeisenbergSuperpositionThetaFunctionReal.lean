import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SmoothIffRealCoordinatesAndRealLines
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsInfFamFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergTranslateThetaFunctionRealCoorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SuperposSmooth

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def dl (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (u : RW T S) (F : WO S T → ℂ) :
    WO S T → ℂ :=
  fun y => deriv (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F y) 0

def bas (S T : HSp D) : Module.Basis (Fin (Module.finrank ℝ (RW T S))) ℝ (RW T S) := Module.finBasis ℝ (RW T S)

def coordC (S T : HSp D) (i : Fin (Module.finrank ℝ (RW T S))) : RW T S →L[ℝ] ℂ :=
  (LinearMap.toContinuousLinearMap ((bas S T).coord i)).smulRight (1 : ℂ)

/- English proof (translation)
Use extensionality with `u`. Establish `e : φ u = ∑ i, (bas S T).repr u i • φ (bas S T i)` using `by conv_lhs => rw [← (bas S T).sum_repr u]`. Rewrite using `[map_sum]`. Simplify using `only [map_smul]`. Rewrite using `[e]`.

Simplify using `[coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]`.
-/
theorem clm_expand (φ : RW T S →L[ℝ] ℂ) : φ = ∑ i, φ (bas S T i) • coordC S T i := by
  ext u
  have e : φ u = ∑ i, (bas S T).repr u i • φ (bas S T i) := by
    conv_lhs => rw [← (bas S T).sum_repr u]
    rw [map_sum]
    simp only [map_smul]
  rw [e]
  simp [coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]

/- English proof (translation)
Unfold `heisO`. Rewrite using `[norm_mul, hψ.1.2.1, one_mul]`. Conclude with `hC _`.
-/
theorem norm_heisO_le (hψ : IsStdChar D ψ (-1)) (x : WO S T) {G : WO S T → ℂ} {C : ℝ} (hC : ∀ y, ‖G y‖ ≤ C)
    (w : WO S T) : ‖heisO ψ S T x G w‖ ≤ C := by
  unfold heisO
  rw [norm_mul, hψ.1.2.1, one_mul]
  exact hC _

/- English proof (translation)
Take `⟨L, hL, hLe⟩` from `(smooth_iff_sm_and_real_lines D θ σ h T S).2.2 u`. Establish `e : dl ψ σ S T u F = dLine ψ S T L F`. Use function extensionality and compare the values at `y`. Unfold `dl dLine`. Simplify using `only [hLe]`.

Rewrite using `[e]`. Conclude with `theta_dLine h.inf hψ hL hF`.
-/
theorem theta_dl (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    (u : RW T S) : IsThetaFunO ψ S T (dl ψ σ S T u F) := by
  obtain ⟨L, hL, hLe⟩ := (smooth_iff_sm_and_real_lines D θ σ h T S).2.2 u
  have e : dl ψ σ S T u F = dLine ψ S T L F := by
    funext y
    unfold dl dLine
    simp only [hLe]
  rw [e]
  exact theta_dLine h.inf hψ hL hF

def sco (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (F : WO S T → ℂ) (u z : RW T S)
    (w : WO S T) : ℂ :=
  (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * heisO ψ S T (iotaW σ T S z) F w +
    heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) w

/- English proof (translation)
Establish `hs` using `GlobalTheory.T.contDiff_heisenbergTranslate_thetaFunction_realCoords D θ σ h ψ hψ S T F hF w`. Establish `hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z) z` using `((hs.1.differentiable (by simp)) z).hasFDerivAt`. Establish `e : c • fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z = ∑ i, (c * sco ψ σ S T F (bas S T i) z w) • coordC S T i`. Rewrite using `[clm_expand (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z), Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, hs.2 z (bas S T i)]`. Both sides reduce to the same expression. Rewrite using `[← e]`. Conclude with `hd.const_mul c`.
-/
theorem hasFDerivAt_pt (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    (w : WO S T) (c : ℂ) (z : RW T S) :
    HasFDerivAt (fun z : RW T S => c * heisO ψ S T (iotaW σ T S z) F w)
      (∑ i, (c * sco ψ σ S T F (bas S T i) z w) • coordC S T i) z := by
  have hs := GlobalTheory.T.contDiff_heisenbergTranslate_thetaFunction_realCoords D θ σ h ψ hψ S T F hF w
  have hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w)
      (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z) z :=
    ((hs.1.differentiable (by simp)) z).hasFDerivAt
  have e : c • fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z =
      ∑ i, (c * sco ψ σ S T F (bas S T i) z w) • coordC S T i := by
    rw [clm_expand (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hs.2 z (bas S T i)]
    rfl
  rw [← e]
  exact hd.const_mul c

/- English proof (translation)
Use `haveI : BorelSpace (WO S T) := ⟨rfl⟩`. Conclude with `((theta_heisO_real h.inf hψ (h.real_iota T S z) hG).cont.measurable.comp hv).aestronglyMeasurable`.
-/
theorem aesm_heisO (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : WO S T → ℂ} (hG : IsThetaFunO ψ S T G)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) (z : RW T S) :
    AEStronglyMeasurable (fun x => heisO ψ S T (iotaW σ T S z) G (v x)) μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  exact ((theta_heisO_real h.inf hψ (h.real_iota T S z) hG).cont.measurable.comp hv).aestronglyMeasurable

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ G hG`. Conclude with `ha.mul_bdd (aesm_heisO h hψ hG μ hv z) (Filter.Eventually.of_forall fun x => norm_heisO_le hψ _ hC _)`.
-/
theorem integrable_heisO (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : WO S T → ℂ} (hG : IsThetaFunO ψ S T G)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (z : RW T S) :
    Integrable (fun x => a x * heisO ψ S T (iotaW σ T S z) G (v x)) μ := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ G hG
  exact ha.mul_bdd (aesm_heisO h hψ hG μ hv z) (Filter.Eventually.of_forall fun x => norm_heisO_le hψ _ hC _)

/- English proof (translation)
The claim follows from `((aesm_heisO h hψ hF μ hv z).const_mul _).add (aesm_heisO h hψ (theta_dl h hψ hF u) μ hv z)`.
-/
theorem aesm_sco (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) (u z : RW T S) :
    AEStronglyMeasurable (fun x => sco ψ σ S T F u z (v x)) μ :=
  ((aesm_heisO h hψ hF μ hv z).const_mul _).add (aesm_heisO h hψ (theta_dl h hψ hF u) μ hv z)

/- English proof (translation)
Establish `e : (fun x => a x * sco ψ σ S T F u z (v x)) = fun x => (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * (a x * heisO ψ S T (iotaW σ T S z) F (v x)) + a x * heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) (v x)`. Use function extensionality and compare the values at `x`. Unfold `sco`. Expand and normalize the polynomial expressions, which then agree. Establish `i1` using `(integrable_heisO h hψ hF μ hv ha z).const_mul ((Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ))`.

Establish `i2` using `integrable_heisO h hψ (theta_dl h hψ hF u) μ hv ha z`. Rewrite using `[e]`. Conclude with `⟨i1.add i2, by rw [integral_add i1 i2, integral_const_mul]⟩`.
-/
theorem integral_sco (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (u z : RW T S) :
    Integrable (fun x => a x * sco ψ σ S T F u z (v x)) μ ∧
      ∫ x, a x * sco ψ σ S T F u z (v x) ∂μ =
        (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * (∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ) +
          ∫ x, a x * heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) (v x) ∂μ := by
  have e : (fun x => a x * sco ψ σ S T F u z (v x)) = fun x =>
      (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * (a x * heisO ψ S T (iotaW σ T S z) F (v x)) +
        a x * heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) (v x) := by
    funext x; unfold sco; ring
  have i1 := (integrable_heisO h hψ hF μ hv ha z).const_mul ((Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ))
  have i2 := integrable_heisO h hψ (theta_dl h hψ hF u) μ hv ha z
  rw [e]
  exact ⟨i1.add i2, by rw [integral_add i1 i2, integral_const_mul]⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF`. Establish `hCd : ∀ i, ∃ C' : ℝ, ∀ y, ‖dl ψ σ S T (bas S T i) F y‖ ≤ C'` using `fun i => GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ (theta_dl h hψ hF (bas S T i))`. Use `choose Cd hCd using hCd`. Establish `hM : ∀ i, ∃ M : ℝ, ∀ z ∈ Metric.closedBall z₀ 1, ‖omO S T z (bas S T i)‖ ≤ M` using `fun i => (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn (LinearMap.continuous_of_finiteDimensional ((omO S T).flip (bas S T i))).continuousOn`. Use `choose M hM using hM`.

Establish `hsco : ∀ i, ∀ z ∈ Metric.ball z₀ 1, ∀ w, ‖sco ψ σ S T F (bas S T i) z w‖ ≤ Real.pi * M i * C + Cd i`. Introduce `i z hz w`. Unfold `sco`. Use `(norm_add_le _ _).trans (add_le_add ?_ (norm_heisO_le hψ _ (hCd i) w))` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`.

Establish `h1 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi` using `by simp [Real.pi_pos.le]`. Establish `h2 : ‖((omO S T z (bas S T i) : ℝ) : ℂ)‖ ≤ M i`. Rewrite using `[Complex.norm_real]`. Conclude with `hM i z (Metric.ball_subset_closedBall hz)`. Establish `h3` using `norm_heisO_le hψ (iotaW σ T S z) hC w`.

Rewrite using `[h1]`. Establish `hM0 : 0 ≤ M i` using `(norm_nonneg _).trans h2`. Use `gcongr`. Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (F := fun z x => a x * heisO ψ S T (iotaW σ T S z) F (v x)) (F' := fun z x => ∑ i, (a x * sco ψ σ S T F (bas S T i) z (v x)) • coordC S T i) (bound := fun x => ‖a x‖ * ∑ i, (Real.pi * M i * C + Cd i) * ‖coordC S T i‖) (Metri …`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_mul, mul_assoc]`. Use `gcongr`. Conclude with `hsco i z hz (v x))`.

Use the proof step `(ha.norm.mul_const _)`. Use the proof step `(Filter.Eventually.of_forall fun x z _ => hasFDerivAt_pt h hψ hF (v x) (a x) z)`. Use `key.congr_fderiv ?_` and prove the remaining obligations. Rewrite using `[integral_finset_sum _ fun i _ => (integral_sco h hψ hF μ hv ha (bas S T i) z₀).1.smul_const _]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_smul_const, (integral_sco h hψ hF μ hv ha (bas S T i) z₀).2]`.
-/
theorem hasFDerivAt_superpos (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (z₀ : RW T S) :
    HasFDerivAt (fun z : RW T S => ∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ)
      (∑ i, ((Real.pi * Complex.I) * ((omO S T z₀ (bas S T i) : ℝ) : ℂ) *
          (∫ x, a x * heisO ψ S T (iotaW σ T S z₀) F (v x) ∂μ) +
        ∫ x, a x * heisO ψ S T (iotaW σ T S z₀) (dl ψ σ S T (bas S T i) F) (v x) ∂μ) • coordC S T i) z₀ := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  have hCd : ∀ i, ∃ C' : ℝ, ∀ y, ‖dl ψ σ S T (bas S T i) F y‖ ≤ C' := fun i =>
    GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ (theta_dl h hψ hF (bas S T i))
  choose Cd hCd using hCd
  have hM : ∀ i, ∃ M : ℝ, ∀ z ∈ Metric.closedBall z₀ 1, ‖omO S T z (bas S T i)‖ ≤ M := fun i =>
    (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
      (LinearMap.continuous_of_finiteDimensional ((omO S T).flip (bas S T i))).continuousOn
  choose M hM using hM
  have hsco : ∀ i, ∀ z ∈ Metric.ball z₀ 1, ∀ w,
      ‖sco ψ σ S T F (bas S T i) z w‖ ≤ Real.pi * M i * C + Cd i := by
    intro i z hz w
    unfold sco
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_heisO_le hψ _ (hCd i) w))
    rw [norm_mul, norm_mul]
    have h1 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by simp [Real.pi_pos.le]
    have h2 : ‖((omO S T z (bas S T i) : ℝ) : ℂ)‖ ≤ M i := by
      rw [Complex.norm_real]; exact hM i z (Metric.ball_subset_closedBall hz)
    have h3 := norm_heisO_le hψ (iotaW σ T S z) hC w
    rw [h1]
    have hM0 : 0 ≤ M i := (norm_nonneg _).trans h2
    gcongr
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun z x => a x * heisO ψ S T (iotaW σ T S z) F (v x))
    (F' := fun z x => ∑ i, (a x * sco ψ σ S T F (bas S T i) z (v x)) • coordC S T i)
    (bound := fun x => ‖a x‖ * ∑ i, (Real.pi * M i * C + Cd i) * ‖coordC S T i‖) (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (ha.aestronglyMeasurable.mul (aesm_heisO h hψ hF μ hv z)))
    (integrable_heisO h hψ hF μ hv ha z₀)
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (ha.aestronglyMeasurable.mul (aesm_sco h hψ hF μ hv (bas S T i) z₀)).smul_const _)
    (Filter.Eventually.of_forall fun x z hz => by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, norm_mul, mul_assoc]
      gcongr
      exact hsco i z hz (v x))
    (ha.norm.mul_const _)
    (Filter.Eventually.of_forall fun x z _ => hasFDerivAt_pt h hψ hF (v x) (a x) z)
  refine key.congr_fderiv ?_
  rw [integral_finset_sum _ fun i _ => (integral_sco h hψ hF μ hv ha (bas S T i) z₀).1.smul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_const, (integral_sco h hψ hF μ hv ha (bas S T i) z₀).2]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `F hF`. Conclude with `contDiff_zero.2 (continuous_iff_continuousAt.2 fun z => (hasFDerivAt_superpos h hψ hF μ hv ha z).continuousAt)`. Consider the case `succ n ih`.

Introduce `F hF`. Rewrite using `[show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]`. Use `⟨_, ?_, fun z => hasFDerivAt_superpos h hψ hF μ hv ha z⟩` and prove the remaining obligations. Use `ContDiff.sum fun i _ => ContDiff.smul_const ?_ _` and prove the remaining obligations. Establish `hom : ContDiff ℝ n fun z : RW T S => ((omO S T z (bas S T i) : ℝ) : ℂ)` using `Complex.ofRealCLM.contDiff.comp (LinearMap.toContinuousLinearMap ((omO S T).flip (bas S T i))).contDiff`.

Conclude with `((contDiff_const.mul hom).mul (ih F hF)).add (ih _ (theta_dl h hψ hF (bas S T i)))`.
-/
theorem contDiff_superpos_nat (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ} (ha : Integrable a μ) (n : ℕ) :
    ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
      ContDiff ℝ n (fun z : RW T S => ∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ) := by
  induction n with
  | zero =>
    intro F hF
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z =>
      (hasFDerivAt_superpos h hψ hF μ hv ha z).continuousAt)
  | succ n ih =>
    intro F hF
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, fun z => hasFDerivAt_superpos h hψ hF μ hv ha z⟩
    refine ContDiff.sum fun i _ => ContDiff.smul_const ?_ _
    have hom : ContDiff ℝ n fun z : RW T S => ((omO S T z (bas S T i) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (LinearMap.toContinuousLinearMap ((omO S T).flip (bas S T i))).contDiff
    exact ((contDiff_const.mul hom).mul (ih F hF)).add (ih _ (theta_dl h hψ hF (bas S T i)))

end GlobalTheory.SuperposSmooth

/- English proof (translation)
Introduce `D θ σ h ψ hψ S T F hF Ω _ μ v a hv ha`. Conclude with `contDiff_infty.2 fun n => GlobalTheory.SuperposSmooth.contDiff_superpos_nat h hψ μ hv ha n F hF`.
-/
theorem GlobalTheory.SuperposSmooth.main : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → WO S T) (a : Ω → ℂ), Measurable v → Integrable a μ → ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F (v x) ∂μ) := by
  intro D θ σ h ψ hψ S T F hF Ω _ μ v a hv ha
  exact contDiff_infty.2 fun n => GlobalTheory.SuperposSmooth.contDiff_superpos_nat h hψ μ hv ha n F hF

end
