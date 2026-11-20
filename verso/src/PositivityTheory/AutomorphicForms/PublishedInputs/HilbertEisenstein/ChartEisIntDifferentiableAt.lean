import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ContDiffOnOfContDiffAtOne
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LibSmoothDec
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.FiniteSupportOfHyp

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap ContDiff Topology
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

set_option linter.unusedSectionVars false

namespace UpperTheory.HilbertEisensteinWeightOne.SLowLib

open UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Take `⟨d, hd0, hd⟩` from `exists_den_row c g (isCompact_singleton (x := a))`. Take `⟨k, U, hU, hdec⟩` from `exists_decay_bound_two F (isCompact_singleton (x := a)) d hd0 0`. Use `set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'`. Use `set K := ∑ i, ∑ j, ‖G' i j‖ with hKdef`. Establish `hK : 0 ≤ K` using `by positivity`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `hUs : Summable (fun ξ : Xi F => (K + 1) ^ k * |U ξ.1|)`. Establish `hi : Function.Injective (fun x : Xi F => x.1)` using `fun x y h => Subtype.ext h`. Conclude with `(hU.abs.comp_injective hi).mul_left _`. Use `Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) hUs` and prove the remaining obligations.

Take `⟨ξ, hξ⟩` from `ξ`. Distinguish the cases in `hf : finRow c (rowv g a ξ) = 0`. Simplify using `only [hf, norm_zero, zero_mul]`. Check the signs of the components of the expression. Establish `hcond : ∀ w, Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧ Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g : GA F 2) : …`.

Unfold `finRow at hf`. Use `split_ifs at hf with hc`. Conclude with `hc`. Conclude with `absurd rfl hf`. Establish `hden` using `hd a (Set.mem_singleton a) ξ hcond`.

Establish `hdecay` using `hdec a (Set.mem_singleton a) 1 le_rfl ξ hξ hden`. Rewrite `hdecay` using `[map_one, one_mul]`. Simplify using `only [pow_zero, inv_one, one_mul] at hdecay`. Use `set P : Vr F := fun i => UpperTheory.V.TR.pInf F ((a : Ad F) * algebraMap F (Ad F) (ξ i)) with hPdef`. Establish `hw1 : vInf (rowv g a ξ) = P ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F)` using `vInf_rowv g a ξ`.

Establish `hPw : ‖P‖ ≤ K * ‖vInf (rowv g a ξ)‖`. Establish `e : P = vInf (rowv g a ξ) ᵥ* G'`. Rewrite using `[hw1, Matrix.vecMul_vecMul, hG', map_pInf_mul_inv, Matrix.vecMul_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `hw'` using `inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Use `gcongr`. Conclude with `hdecay.trans (le_abs_self _)`.
-/
theorem summable_row (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) :
    ∃ k : ℕ, Summable (fun ξ : Xi F => ‖finRow c (rowv g a ξ.1)‖ * ((1 + ‖vInf (rowv g a ξ.1)‖) ^ k)⁻¹) := by
  classical
  obtain ⟨d, hd0, hd⟩ := exists_den_row c g (isCompact_singleton (x := a))
  obtain ⟨k, U, hU, hdec⟩ := exists_decay_bound_two F (isCompact_singleton (x := a)) d hd0 0
  set G' := ((g⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) with hG'
  set K := ∑ i, ∑ j, ‖G' i j‖ with hKdef
  have hK : 0 ≤ K := by positivity
  refine ⟨k, ?_⟩
  have hUs : Summable (fun ξ : Xi F => (K + 1) ^ k * |U ξ.1|) := by
    have hi : Function.Injective (fun x : Xi F => x.1) := fun x y h => Subtype.ext h
    exact (hU.abs.comp_injective hi).mul_left _
  refine Summable.of_nonneg_of_le (fun ξ => by positivity) (fun ξ => ?_) hUs
  obtain ⟨ξ, hξ⟩ := ξ
  by_cases hf : finRow c (rowv g a ξ) = 0
  · simp only [hf, norm_zero, zero_mul]
    positivity
  have hcond : ∀ w, Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2)
      a * g : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 0))) ≤ WithZero.exp (-(c w : ℤ)) ∧
      Valued.v (pLoc F w (pFin F ((rowA ξ ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g :
        GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))) 1)) - 1) ≤ WithZero.exp (-(c w : ℤ)) := by
    unfold finRow at hf
    split_ifs at hf with hc
    · exact hc
    · exact absurd rfl hf
  have hden := hd a (Set.mem_singleton a) ξ hcond
  have hdecay := hdec a (Set.mem_singleton a) 1 le_rfl ξ hξ hden
  rw [map_one, one_mul] at hdecay
  simp only [pow_zero, inv_one, one_mul] at hdecay
  set P : Vr F := fun i => UpperTheory.V.TR.pInf F ((a : Ad F) * algebraMap F (Ad F) (ξ i)) with hPdef
  have hw1 : vInf (rowv g a ξ) = P ᵥ* (g : Matrix (Fin 2) (Fin 2) (Ad F)).map (UpperTheory.V.TR.pInf F) :=
    vInf_rowv g a ξ
  have hPw : ‖P‖ ≤ K * ‖vInf (rowv g a ξ)‖ := by
    have e : P = vInf (rowv g a ξ) ᵥ* G' := by
      rw [hw1, Matrix.vecMul_vecMul, hG', map_pInf_mul_inv, Matrix.vecMul_one]
    calc ‖P‖ = ‖vInf (rowv g a ξ) ᵥ* G'‖ := by rw [← e]
      _ ≤ ‖vInf (rowv g a ξ)‖ * K := norm_vecMul_le' _ _
      _ = K * ‖vInf (rowv g a ξ)‖ := mul_comm _ _
  have hw' := inv_pow_le_of_le (norm_nonneg P) (norm_nonneg _) hK hPw k
  calc ‖finRow c (rowv g a ξ)‖ * ((1 + ‖vInf (rowv g a ξ)‖) ^ k)⁻¹
      ≤ 1 * ((K + 1) ^ k * ((1 + ‖P‖) ^ k)⁻¹) :=
        mul_le_mul (norm_finRow_le c _) hw' (by positivity) zero_le_one
    _ ≤ (K + 1) ^ k * |U ξ| := by
        rw [one_mul]
        gcongr
        exact hdecay.trans (le_abs_self _)

def Srow (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) (x : UpperTheory.V.TR.Lie F 2) : ℂ :=
  ∫ ξ, finRow c (rowv g a ξ.1) * archS F (B1 (vInf (rowv g a ξ.1)) x) ∂(Measure.count : Measure (Xi F))

/- English proof (translation)
The claim follows from `(measurable_of_countable f).aestronglyMeasurable`.
-/
theorem aesm_count {β : Type*} [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β]
    [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β] (f : Xi F → β) :
    AEStronglyMeasurable f (Measure.count : Measure (Xi F)) :=
  (measurable_of_countable f).aestronglyMeasurable

/- English proof (translation)
Take `⟨k, hk⟩` from `summable_row c g a`. Use `⟨k, (integrable_count_iff).2 ?_⟩` and prove the remaining obligations. Simplify `hk.abs` using `[Real.norm_eq_abs]`.
-/
theorem integrable_row_weight (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) :
    ∃ k : ℕ, Integrable (fun ξ : Xi F => ‖finRow c (rowv g a ξ.1)‖ * ((1 + ‖vInf (rowv g a ξ.1)‖) ^ k)⁻¹)
      (Measure.count : Measure (Xi F)) := by
  obtain ⟨k, hk⟩ := summable_row c g a
  refine ⟨k, (integrable_count_iff).2 ?_⟩
  simpa [Real.norm_eq_abs] using hk.abs

/- English proof (translation)
Take `⟨k, hk⟩` from `integrable_row_weight c g a`. Conclude with `hasFDerivAt_integral_schwartz_bilin (archS F) B1 Metric.isOpen_ball (by norm_num : (0 : ℝ) < 1 / 2) (fun x hx v => half_norm_le_norm_left_bilinear hx v) (aesm_count _) (aesm_count _) hk hx`.
-/
theorem hasFDerivAt_Srow (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) {x : UpperTheory.V.TR.Lie F 2}
    (hx : x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)) :
    HasFDerivAt (Srow c g a)
      (∫ ξ, finRow c (rowv g a ξ.1) • fderiv ℝ (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) x
        ∂(Measure.count : Measure (Xi F))) x := by
  obtain ⟨k, hk⟩ := integrable_row_weight c g a
  exact hasFDerivAt_integral_schwartz_bilin (archS F) B1 Metric.isOpen_ball (by norm_num : (0 : ℝ) < 1 / 2)
    (fun x hx v => half_norm_le_norm_left_bilinear hx v) (aesm_count _) (aesm_count _) hk hx

/- English proof (translation)
Take `⟨k, hk⟩` from `integrable_row_weight c g a`. Take `⟨C, -, hC⟩` from `exists_bound_bilD (archS F) B1 (by norm_num : (0 : ℝ) < 1 / 2) (fun x hx v => half_norm_le_norm_left_bilinear hx v) 1 k`. Use `(hk.const_mul C).mono' (aesm_count _) (ae_of_all _ fun ξ => ?_)` and prove the remaining obligations. Establish `h` using `hC x hx (vInf (rowv g a ξ.1))`. Rewrite `h` using `[bilD, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]`.

Rewrite using `[norm_smul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integrable_fderiv_row (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F) {x : UpperTheory.V.TR.Lie F 2}
    (hx : x ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)) :
    Integrable (fun ξ : Xi F => finRow c (rowv g a ξ.1) • fderiv ℝ (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) x)
      (Measure.count : Measure (Xi F)) := by
  obtain ⟨k, hk⟩ := integrable_row_weight c g a
  obtain ⟨C, -, hC⟩ := exists_bound_bilD (archS F) B1 (by norm_num : (0 : ℝ) < 1 / 2)
    (fun x hx v => half_norm_le_norm_left_bilinear hx v) 1 k
  refine (hk.const_mul C).mono' (aesm_count _) (ae_of_all _ fun ξ => ?_)
  have h := hC x hx (vInf (rowv g a ξ.1))
  rw [bilD, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero] at h
  rw [norm_smul]
  calc ‖finRow c (rowv g a ξ.1)‖ * ‖fderiv ℝ (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) x‖
      ≤ ‖finRow c (rowv g a ξ.1)‖ * (C * ((1 + ‖vInf (rowv g a ξ.1)‖) ^ k)⁻¹) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = C * (‖finRow c (rowv g a ξ.1)‖ * ((1 + ‖vInf (rowv g a ξ.1)‖) ^ k)⁻¹) := by ring

/- English proof (translation)
Unfold `thetaS Srow`. Rewrite using `[integral_count_Xi]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, row_term, mul_comm]`.
-/
theorem thetaS_eq_Srow (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F)
    (y : GL (Fin 2) (UpperTheory.V.TR.Rinf F)) :
    thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g * UpperTheory.V.TR.infGL F 2 y) =
      Srow c g a (UpperTheory.V.TR.toL y.val) := by
  unfold thetaS Srow
  rw [integral_count_Xi]
  refine tsum_congr fun ξ => ?_
  rw [mul_assoc, row_term, mul_comm]

/- English proof (translation)
Establish `h1 : UpperTheory.V.TR.toL (k 0).val = UpperTheory.V.TR.oneL F 2` using `by rw [hk0]; rfl`. Establish `hball : UpperTheory.V.TR.toL (k 0).val ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4)`. Rewrite using `[h1]; exact Metric.mem_ball_self (by norm_num)`. Establish `hI` using `integrable_fderiv_row c g a hball`. Use `set D : {ξ : Fin 2 → F // ξ ≠ 0} → ℂ := fun ξ => finRow c (rowv g a ξ.1) * fderiv ℝ (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) (UpperTheory.V.TR.toL (k 0).val) X with hD`.

Use `⟨D, fun ξ => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (fun s => Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g * UpperTheory.V.TR.infGL F 2 (k s) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)))) = fun s => archS F (B1 (vInf (rowv g a ξ.1)) (UpperTheory.V.TR.toL (k s).val)) * finRow c (rowv g a ξ.1)`. Use function extensionality and compare the values at `fun s => by rw [mul_assoc, row_term]`. Rewrite using `[e]`. Establish `hd : HasFDerivAt (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) (fderiv ℝ (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) (UpperTheory.V.TR.toL (k 0).val)) (UpperTheory.V.TR.toL (k 0).val)` using `(((contDiff_bil (archS F) B1 (vInf (rowv g a ξ.1))).differentiable infty_ne_zero) _).hasFDerivAt`.

Use `((hd.comp_hasDerivAt 0 hk).mul_const (finRow c (rowv g a ξ.1))).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [hD]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `(integrable_count_iff).1 (hI.apply_continuousLinearMap X)`. Use `Summable.of_norm (h2.congr fun ξ => ?_)` and prove the remaining obligations.

Simplify using `only [hD, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Establish `e : (fun s => thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g * UpperTheory.V.TR.infGL F 2 (k s))) = fun s => Srow c g a (UpperTheory.V.TR.toL (k s).val)`. Use function extensionality and compare the values at `fun s => thetaS_eq_Srow c g a (k s)`. Rewrite using `[e]`. Use `((hasFDerivAt_Srow c g a hball).comp_hasDerivAt 0 hk).congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[ContinuousLinearMap.integral_apply hI X, integral_count_Xi]`. Both sides reduce to the same expression.
-/
theorem thetaS_curve (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2) (a : Ideles F)
    (k : ℝ → GL (Fin 2) (UpperTheory.V.TR.Rinf F)) (X : UpperTheory.V.TR.Lie F 2) (hk0 : k 0 = 1)
    (hk : HasDerivAt (fun s => UpperTheory.V.TR.toL (k s).val) X 0) :
    ∃ D : {ξ : Fin 2 → F // ξ ≠ 0} → ℂ,
      (∀ ξ, HasDerivAt (fun s => Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g *
        UpperTheory.V.TR.infGL F 2 (k s) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)))) (D ξ) 0) ∧ Summable D ∧
      HasDerivAt (fun s => thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g *
        UpperTheory.V.TR.infGL F 2 (k s))) (∑' ξ, D ξ) 0 := by
  have h1 : UpperTheory.V.TR.toL (k 0).val = UpperTheory.V.TR.oneL F 2 := by rw [hk0]; rfl
  have hball : UpperTheory.V.TR.toL (k 0).val ∈ Metric.ball (UpperTheory.V.TR.oneL F 2) (1 / 4) := by
    rw [h1]; exact Metric.mem_ball_self (by norm_num)
  have hI := integrable_fderiv_row c g a hball
  set D : {ξ : Fin 2 → F // ξ ≠ 0} → ℂ := fun ξ => finRow c (rowv g a ξ.1) *
    fderiv ℝ (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) (UpperTheory.V.TR.toL (k 0).val) X with hD
  refine ⟨D, fun ξ => ?_, ?_, ?_⟩
  · have e : (fun s => Phi c (rowA ξ.1 ᵥ* ((Matrix.GeneralLinearGroup.scalar (Fin 2) a * g *
        UpperTheory.V.TR.infGL F 2 (k s) : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)))) =
        fun s => archS F (B1 (vInf (rowv g a ξ.1)) (UpperTheory.V.TR.toL (k s).val)) * finRow c (rowv g a ξ.1) :=
      funext fun s => by rw [mul_assoc, row_term]
    rw [e]
    have hd : HasFDerivAt (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x))
        (fderiv ℝ (fun x => archS F (B1 (vInf (rowv g a ξ.1)) x)) (UpperTheory.V.TR.toL (k 0).val))
        (UpperTheory.V.TR.toL (k 0).val) :=
      (((contDiff_bil (archS F) B1 (vInf (rowv g a ξ.1))).differentiable infty_ne_zero) _).hasFDerivAt
    refine ((hd.comp_hasDerivAt 0 hk).mul_const (finRow c (rowv g a ξ.1))).congr_deriv ?_
    simp only [hD]
    ring
  · have h2 := (integrable_count_iff).1 (hI.apply_continuousLinearMap X)
    refine Summable.of_norm (h2.congr fun ξ => ?_)
    simp only [hD, ContinuousLinearMap.smul_apply, smul_eq_mul]
  · have e : (fun s => thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) a * g *
        UpperTheory.V.TR.infGL F 2 (k s))) = fun s => Srow c g a (UpperTheory.V.TR.toL (k s).val) :=
      funext fun s => thetaS_eq_Srow c g a (k s)
    rw [e]
    refine ((hasFDerivAt_Srow c g a hball).comp_hasDerivAt 0 hk).congr_deriv ?_
    rw [ContinuousLinearMap.integral_apply hI X, integral_count_Xi]
    rfl

/- English proof (translation)
Establish `hS : DifferentiableAt ℝ (Srow c g (av (t, u))) (UpperTheory.V.TR.oneL F 2)` using `(hasFDerivAt_Srow c g _ (Metric.mem_ball_self (by norm_num))).differentiableAt`. Establish `h0 : dl g (UpperTheory.V.TR.oneL F 2) ≠ 0` using `by rw [dl_one]; exact (absD_pos g).ne'`. Establish `h1 : DifferentiableAt ℝ (fun x => dl g x ^ ((1 : ℝ) / 2)) (UpperTheory.V.TR.oneL F 2)` using `(((contDiff_dl g).differentiable infty_ne_zero) _).rpow_const (Or.inl h0)`. Establish `hD : DifferentiableAt ℝ (Dc g) (UpperTheory.V.TR.oneL F 2)` using `by show DifferentiableAt ℝ (fun x => ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) _`. Conclude with `Complex.ofRealCLM.differentiableAt.comp _ h1`.

Establish `e : Sr χ c g (t, u) = fun x => (((χ.1 (av (t, u)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)) * Srow c g (av (t, u)) x`. Use function extensionality and compare the values at `x`. Unfold `Sr Srow kap1 w1`. Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (ae_of_all _ fun ξ => ?_)` and prove the remaining obligations.

Simplify using `only`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : DifferentiableAt ℝ (fun x => Dc g x * Sr χ c g (t, u) x) (UpperTheory.V.TR.oneL F 2)`. Rewrite using `[e]`. Conclude with `hD.mul (hS.const_mul _)`.

Conclude with `hd.congr_of_eventuallyEq (chart_eisInt_row χ c g (t, u))`.
-/
theorem chart_eisInt_differentiableAt (χ : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (g : GA F 2)
    (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) :
    DifferentiableAt ℝ (UpperTheory.V.TR.chart (fun g' => eisInt χ (Phi c) g' t u) g) (UpperTheory.V.TR.oneL F 2) := by
  have hS : DifferentiableAt ℝ (Srow c g (av (t, u))) (UpperTheory.V.TR.oneL F 2) :=
    (hasFDerivAt_Srow c g _ (Metric.mem_ball_self (by norm_num))).differentiableAt
  have h0 : dl g (UpperTheory.V.TR.oneL F 2) ≠ 0 := by rw [dl_one]; exact (absD_pos g).ne'
  have h1 : DifferentiableAt ℝ (fun x => dl g x ^ ((1 : ℝ) / 2)) (UpperTheory.V.TR.oneL F 2) :=
    (((contDiff_dl g).differentiable infty_ne_zero) _).rpow_const (Or.inl h0)
  have hD : DifferentiableAt ℝ (Dc g) (UpperTheory.V.TR.oneL F 2) := by
    show DifferentiableAt ℝ (fun x => ((dl g x ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) _
    exact Complex.ofRealCLM.differentiableAt.comp _ h1
  have e : Sr χ c g (t, u) = fun x => (((χ.1 (av (t, u)) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)) * Srow c g (av (t, u)) x := by
    funext x
    unfold Sr Srow kap1 w1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only
    ring
  have hd : DifferentiableAt ℝ (fun x => Dc g x * Sr χ c g (t, u) x) (UpperTheory.V.TR.oneL F 2) := by
    rw [e]
    exact hD.mul (hS.const_mul _)
  exact hd.congr_of_eventuallyEq (chart_eisInt_row χ c g (t, u))

end UpperTheory.HilbertEisensteinWeightOne.SLowLib
