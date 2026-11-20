import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DblActId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzWeylFourier
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRealisedOnAdelicSchwartzLeviInverseTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.TowU
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix

noncomputable section

namespace GlobalTheory.TowU.FourWeyl

open GlobalTheory.AdelicSvN.Weyl GlobalTheory.AdelicSvNLevi

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
Substitute `hm` using the available equality. Use `letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F`. Use `haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`.

Use `haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace`. Establish `h` using `Measure.isAddLeftInvariant_eq_smul μ (adeleMeasurePi F (ι := κ))`. Generalize the expression as in `Measure.addHaarScalarFactor μ (adeleMeasurePi F (ι := κ)) = k at h`. Use `⟨k, fun h0 => ?_, fun f => ?_, fun g => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[h0, zero_smul]`.

Conclude with `hμ.toIsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty (by rw [h]; rfl)`. Rewrite using `[h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`. Rewrite using `[h, lintegral_smul_measure]`. Both sides reduce to the same expression.
-/
theorem adelicHaar_piSigma_eq_const_mul_selfDual (m : MeasurableSpace (κ → AdeleRing (𝓞 F) F))
    (hm : m = @MeasurableSpace.pi κ _ fun _ => measurableSpace_adeleRing F)
    (μ : @Measure (κ → AdeleRing (𝓞 F) F) m) (hμ : @Measure.IsAddHaarMeasure _ _ _ m μ) :
    ∃ k : ℝ≥0, k ≠ 0 ∧ (∀ f : (κ → AdeleRing (𝓞 F) F) → ℂ, ∫ x, f x ∂μ = (k : ℂ) * ∫ x, f x ∂(adeleMeasurePi F)) ∧
      ∀ g : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞, ∫⁻ x, g x ∂μ = k * ∫⁻ x, g x ∂(adeleMeasurePi F) := by
  subst hm
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have h := Measure.isAddLeftInvariant_eq_smul μ (adeleMeasurePi F (ι := κ))
  generalize Measure.addHaarScalarFactor μ (adeleMeasurePi F (ι := κ)) = k at h
  refine ⟨k, fun h0 => ?_, fun f => ?_, fun g => ?_⟩
  · rw [h0, zero_smul] at h
    exact hμ.toIsOpenPosMeasure.open_pos Set.univ isOpen_univ Set.univ_nonempty (by rw [h]; rfl)
  · rw [h, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  · rw [h, lintegral_smul_measure]
    rfl

/- English proof (translation)
Use `adelicHaar_piSigma_eq_const_mul_selfDual (borel _) ?_ μ hμ` and prove the remaining obligations. Use `letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F`. Use `haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Conclude with `(Pi.borelSpace (X := fun _ : κ => AdeleRing (𝓞 F) F)).measurable_eq.symm`.
-/
theorem haar_cmp (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ k : ℝ≥0, k ≠ 0 ∧ (∀ f : (κ → AF F) → ℂ, ∫ x, f x ∂μ = (k : ℂ) * ∫ x, f x ∂(adeleMeasurePi F)) ∧
      ∀ g : (κ → AF F) → ℝ≥0∞, ∫⁻ x, g x ∂μ = k * ∫⁻ x, g x ∂(adeleMeasurePi F) := by
  refine adelicHaar_piSigma_eq_const_mul_selfDual (borel _) ?_ μ hμ
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  exact (Pi.borelSpace (X := fun _ : κ => AdeleRing (𝓞 F) F)).measurable_eq.symm

/- English proof (translation)
Rewrite `hφ`, the goal using `[schA_eq]`. Conclude with `adelicFourierPi_mem_schwartzBruhatPi hφ`.
-/
theorem four_mem {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) : adelicFourierPi F φ ∈ schA F κ := by
  rw [schA_eq] at hφ ⊢
  exact adelicFourierPi_mem_schwartzBruhatPi hφ

/- English proof (translation)
Rewrite `hφ` using `[schA_eq]`. Conclude with `adelicFourierPi_adelicFourierPi hφ`.
-/
theorem four_four {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    adelicFourierPi F (adelicFourierPi F φ) = fun x => φ (-x) := by
  rw [schA_eq] at hφ
  exact adelicFourierPi_adelicFourierPi hφ

/- English proof (translation)
Rewrite using `[four_four (four_mem (four_mem hφ)), four_four hφ]`. Simplify using `only [neg_neg]`.
-/
theorem four_pow_four {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    adelicFourierPi F (adelicFourierPi F (adelicFourierPi F (adelicFourierPi F φ))) = φ := by
  rw [four_four (four_mem (four_mem hφ)), four_four hφ]
  simp only [neg_neg]

/- English proof (translation)
Rewrite `hφ` using `[schA_eq]`. Conclude with `integrable_of_mem_schwartzBruhatPi hφ`.
-/
theorem integrable_schA {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) : Integrable φ (adeleMeasurePi F) := by
  rw [schA_eq] at hφ
  exact integrable_of_mem_schwartzBruhatPi hφ

/- English proof (translation)
Use `⟨∫ x, ‖adelicFourierPi F (adelicFourierPi F (adelicFourierPi F φ)) x‖ ∂(adeleMeasurePi F), fun y => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← four_pow_four hφ]`. Use `(norm_integral_le_integral_norm _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [norm_mul, Circle.norm_coe, mul_one]`.
-/
theorem bounded_schA {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) : ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C := by
  refine ⟨∫ x, ‖adelicFourierPi F (adelicFourierPi F (adelicFourierPi F φ)) x‖ ∂(adeleMeasurePi F), fun y => ?_⟩
  conv_lhs => rw [← four_pow_four hφ]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_mul, Circle.norm_coe, mul_one]

/- English proof (translation)
Use `letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F`. Use `haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace`. Establish `hc : Continuous fun p : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) => (adelicChar F (∑ i, p.1 i * p.2 i) : ℂ)` using `continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)))`.

Establish `hi : Integrable (Function.uncurry fun x y : κ → AdeleRing (𝓞 F) F => f x * g y * (adelicChar F (∑ i, x i * y i) : ℂ)) ((adeleMeasurePi F).prod (adeleMeasurePi F))` using `(hf.mul_prod hg).mul_bdd (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => le_of_eq (Circle.norm_coe _))`. Establish `h` using `integral_integral_swap hi`. Simplify using `only [adelicFourierPi, ← integral_const_mul, ← integral_mul_const]`. Use `Eq.trans ?_ (h.symm.trans ?_)` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `y`. Use `congr 1`. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree. Use `congr 1`.

Use function extensionality and compare the values at `x`. Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [mul_comm (x _) (y _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_four_mul {f g : (κ → AdeleRing (𝓞 F) F) → ℂ} (hf : Integrable f (adeleMeasurePi F))
    (hg : Integrable g (adeleMeasurePi F)) :
    ∫ y, adelicFourierPi F f y * g y ∂(adeleMeasurePi F) = ∫ x, f x * adelicFourierPi F g x ∂(adeleMeasurePi F) := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleRing F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := Pi.borelSpace
  have hc : Continuous fun p : (κ → AdeleRing (𝓞 F) F) × (κ → AdeleRing (𝓞 F) F) =>
      (adelicChar F (∑ i, p.1 i * p.2 i) : ℂ) :=
    continuous_subtype_val.comp ((continuous_adelicChar (K := F)).comp
      (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_fst).mul
        ((continuous_apply i).comp continuous_snd)))
  have hi : Integrable (Function.uncurry fun x y : κ → AdeleRing (𝓞 F) F =>
      f x * g y * (adelicChar F (∑ i, x i * y i) : ℂ)) ((adeleMeasurePi F).prod (adeleMeasurePi F)) :=
    (hf.mul_prod hg).mul_bdd (c := 1) hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => le_of_eq (Circle.norm_coe _))
  have h := integral_integral_swap hi
  simp only [adelicFourierPi, ← integral_const_mul, ← integral_mul_const]
  refine Eq.trans ?_ (h.symm.trans ?_)
  · congr 1; funext y; congr 1; funext x; ring
  · congr 1; funext x; congr 1; funext y
    simp only [mul_comm (x _) (y _)]
    ring

/- English proof (translation)
Take `⟨C, hC⟩` from `bounded_schA hφ`. Establish `h1` using `(integrable_schA hφ).norm`. Establish `h2 : Integrable (fun x => ‖φ x‖ ^ 2) (adeleMeasurePi F)`. Use `h1.mul_bdd (c := C) h1.1 (Filter.Eventually.of_forall fun x => by rw [norm_norm]; exact hC x)` as an intermediate fact. Simplify `this` using `only [sq]`.

Rewrite using `[ofReal_integral_eq_lintegral_ofReal h2 (Filter.Eventually.of_forall fun x => sq_nonneg _)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`.
-/
theorem lintegral_sq_eq {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(adeleMeasurePi F) = ENNReal.ofReal (∫ x, ‖φ x‖ ^ 2 ∂(adeleMeasurePi F)) := by
  obtain ⟨C, hC⟩ := bounded_schA hφ
  have h1 := (integrable_schA hφ).norm
  have h2 : Integrable (fun x => ‖φ x‖ ^ 2) (adeleMeasurePi F) := by
    have := h1.mul_bdd (c := C) h1.1 (Filter.Eventually.of_forall fun x => by rw [norm_norm]; exact hC x)
    simpa only [sq] using this
  rw [ofReal_integral_eq_lintegral_ofReal h2 (Filter.Eventually.of_forall fun x => sq_nonneg _)]
  congr 1; funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/- English proof (translation)
Rewrite using `[lintegral_sq_eq hφ, lintegral_sq_eq (four_mem hφ)]`. Use `congr 1`. Use `letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F`. Establish `hg : Integrable (fun y => starRingEnd ℂ (adelicFourierPi F φ y)) (adeleMeasurePi F)` using `Complex.conjCLE.toContinuousLinearMap.integrable_comp (integrable_schA (four_mem hφ))`. Establish `h` using `integral_four_mul (integrable_schA hφ) hg`.

Establish `e : ∀ x, adelicFourierPi F (fun y => starRingEnd ℂ (adelicFourierPi F φ y)) x = starRingEnd ℂ (φ x)`. Introduce `x`. Establish `h1` using `congrFun (four_four hφ) (-x)`. Rewrite `h1` using `[neg_neg]`. Rewrite using `[← h1]`.

Use `conv_rhs => rw [adelicFourierPi]`. Rewrite using `[← integral_conj, adelicFourierPi]`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[map_mul, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]`.

Simplify using `only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg]`. Simplify using `only [e, Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_ofReal] at h`. Conclude with `h` after adjusting the coercions.
-/
theorem plancherel {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) :
    ∫⁻ x, ‖adelicFourierPi F φ x‖ₑ ^ 2 ∂(adeleMeasurePi F) = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂(adeleMeasurePi F) := by
  rw [lintegral_sq_eq hφ, lintegral_sq_eq (four_mem hφ)]
  congr 1
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := measurableSpace_adeleRing F
  have hg : Integrable (fun y => starRingEnd ℂ (adelicFourierPi F φ y)) (adeleMeasurePi F) :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp (integrable_schA (four_mem hφ))
  have h := integral_four_mul (integrable_schA hφ) hg
  have e : ∀ x, adelicFourierPi F (fun y => starRingEnd ℂ (adelicFourierPi F φ y)) x = starRingEnd ℂ (φ x) := by
    intro x
    have h1 := congrFun (four_four hφ) (-x)
    rw [neg_neg] at h1
    rw [← h1]
    conv_rhs => rw [adelicFourierPi]
    rw [← integral_conj, adelicFourierPi]
    congr 1; funext y
    rw [map_mul, ← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv]
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg]
  simp only [e, Complex.mul_conj, Complex.normSq_eq_norm_sq, integral_ofReal] at h
  exact_mod_cast h

/- English proof (translation)
Rewrite `hφ` using `[schA_eq]`. Conclude with `(poisson_of_mem_schwartzBruhatPi hφ).2.2.symm`.
-/
theorem theta_four {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) : thetaSum F (adelicFourierPi F φ) = thetaSum F φ := by
  rw [schA_eq] at hφ
  exact (poisson_of_mem_schwartzBruhatPi hφ).2.2.symm

def sgnV {R : Type} [Ring R] (ε : κ → ℤˣ) (y : κ → R) : κ → R := fun i => ((ε i : ℤ) : R) * y i

/- English proof (translation)
Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]`.
-/
theorem sgn_mul_self {R : Type} [Ring R] (e : ℤˣ) : ((e : ℤ) : R) * ((e : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

omit [Fintype κ] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [sgnV]`. Rewrite using `[← mul_assoc, sgn_mul_self, one_mul]`.
-/
theorem sgnV_sgnV {R : Type} [Ring R] (ε : κ → ℤˣ) (y : κ → R) : sgnV ε (sgnV ε y) = y := by
  funext i
  simp only [sgnV]
  rw [← mul_assoc, sgn_mul_self, one_mul]

omit [Fintype κ] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [sgnV, Pi.add_apply, mul_add]`.
-/
theorem sgnV_add {R : Type} [Ring R] (ε : κ → ℤˣ) (x y : κ → R) : sgnV ε (x + y) = sgnV ε x + sgnV ε y := by
  funext i
  simp only [sgnV, Pi.add_apply, mul_add]

/- English proof (translation)
Simplify using `only [sgnV, dotProduct]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem sgnV_dot {R : Type} [CommRing R] (ε : κ → ℤˣ) (x y : κ → R) : sgnV ε x ⬝ᵥ y = x ⬝ᵥ sgnV ε y := by
  simp only [sgnV, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

variable (F) in

def compS (ε : κ → ℤˣ) : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := LinearMap.funLeft ℂ ℂ (sgnV ε)

omit [Fintype κ] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem compS_apply (ε : κ → ℤˣ) (φ : (κ → AF F) → ℂ) (x : κ → AF F) : compS F ε φ x = φ (sgnV ε x) := rfl

omit [Fintype κ] in
/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[compS_apply, compS_apply, sgnV_sgnV]`.
-/
theorem compS_compS (ε : κ → ℤˣ) (φ : (κ → AF F) → ℂ) : compS F ε (compS F ε φ) = φ := by
  funext x
  rw [compS_apply, compS_apply, sgnV_sgnV]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [compS_apply, schr, sgnV_dot, sgnV_sgnV, sgnV_add]`.
-/
theorem compS_schr (ψ : AddChar (AF F) ℂ) (ε : κ → ℤˣ) (w : (κ → AF F) × (κ → AF F)) (φ : (κ → AF F) → ℂ) :
    compS F ε (schr ψ w φ) = schr ψ (sgnV ε w.1, sgnV ε w.2) (compS F ε φ) := by
  funext x
  simp only [compS_apply, schr, sgnV_dot, sgnV_sgnV, sgnV_add]

omit [Fintype κ] in
/- English proof (translation)
Unfold `thetaSum`. Rewrite using `[← (Function.Involutive.toPerm (sgnV (R := F) ε) (sgnV_sgnV ε)).tsum_eq]`. Use `tsum_congr fun ξ => ?_` and prove the remaining obligations. Rewrite using `[compS_apply]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `show ((ε i : ℤ) : AF F) * algebraMap F (AF F) (((ε i : ℤ) : F) * ξ i) = _`. Rewrite using `[map_mul, map_intCast, ← mul_assoc, sgn_mul_self, one_mul]`.
-/
theorem theta_compS (ε : κ → ℤˣ) (φ : (κ → AF F) → ℂ) : thetaSum F (compS F ε φ) = thetaSum F φ := by
  unfold thetaSum
  rw [← (Function.Involutive.toPerm (sgnV (R := F) ε) (sgnV_sgnV ε)).tsum_eq]
  refine tsum_congr fun ξ => ?_
  rw [compS_apply]
  congr 1
  funext i
  show ((ε i : ℤ) : AF F) * algebraMap F (AF F) (((ε i : ℤ) : F) * ξ i) = _
  rw [map_mul, map_intCast, ← mul_assoc, sgn_mul_self, one_mul]

/- English proof (translation)
Use `letI : MeasurableSpace (κ → AF F) := borel _`. Use `haveI : BorelSpace (κ → AF F) := ⟨rfl⟩`. Establish `hc : Continuous (sgnV ε : (κ → AF F) → κ → AF F)` using `continuous_pi fun i => continuous_const.mul (continuous_apply i)`. Set `e : (κ → AF F) ≃+ (κ → AF F)` to `⟨⟨sgnV ε, sgnV ε, sgnV_sgnV ε, sgnV_sgnV ε⟩, sgnV_add ε⟩`. Set `h : (κ → AF F) ≃ₜ (κ → AF F)` to `⟨e.toEquiv, hc, hc⟩`.

Conclude with `⟨μ.map e, AddEquiv.isAddHaarMeasure_map μ e hc hc, fun g => (lintegral_map_equiv g h.toMeasurableEquiv).symm⟩`.
-/
theorem haar_sgn (ε : κ → ℤˣ) (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ) :
    ∃ ν : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν ∧
      ∀ g : (κ → AF F) → ℝ≥0∞, ∫⁻ x, g (sgnV ε x) ∂μ = ∫⁻ x, g x ∂ν := by
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  have hc : Continuous (sgnV ε : (κ → AF F) → κ → AF F) :=
    continuous_pi fun i => continuous_const.mul (continuous_apply i)
  let e : (κ → AF F) ≃+ (κ → AF F) := ⟨⟨sgnV ε, sgnV ε, sgnV_sgnV ε, sgnV_sgnV ε⟩, sgnV_add ε⟩
  let h : (κ → AF F) ≃ₜ (κ → AF F) := ⟨e.toEquiv, hc, hc⟩
  exact ⟨μ.map e, AddEquiv.isAddHaarMeasure_map μ e hc hc,
    fun g => (lintegral_map_equiv g h.toMeasurableEquiv).symm⟩

variable [DecidableEq κ]

/- English proof (translation)
Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `only [sgn_mul_self, Matrix.diagonal_one]`.
-/
theorem diag_mul_self (ε : κ → ℤˣ) :
    (Matrix.diagonal fun i => ((ε i : ℤ) : F)) * (Matrix.diagonal fun i => ((ε i : ℤ) : F)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [sgn_mul_self, Matrix.diagonal_one]

/- English proof (translation)
Use `LinearMap.ext fun φ => funext fun x => ?_` and prove the remaining obligations. Rewrite using `[compS_apply, compM_apply, Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_diagonal, map_intCast]`.

Both sides reduce to the same expression.
-/
theorem compS_eq (ε : κ → ℤˣ) : compS F ε = compM (Matrix.diagonal fun i => ((ε i : ℤ) : F)) := by
  refine LinearMap.ext fun φ => funext fun x => ?_
  rw [compS_apply, compM_apply, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal, map_intCast]
  rfl

/- English proof (translation)
Rewrite using `[compS_eq]`. Conclude with `comp_mem _ _ (diag_mul_self ε) (diag_mul_self ε) φ hφ`.
-/
theorem compS_mem (ε : κ → ℤˣ) {φ : (κ → AF F) → ℂ} (hφ : φ ∈ schA F κ) : compS F ε φ ∈ schA F κ := by
  rw [compS_eq]
  exact comp_mem _ _ (diag_mul_self ε) (diag_mul_self ε) φ hφ

/- English proof (translation)
Rewrite using `[compS_eq]`. Establish `h` using `diag_mul_self (F := F) ε`. Introduce `g hg`. Take `⟨T, hT⟩` from `hl _ ⟨hg.1.comp_continuous (finHomeo _ _ h h).continuous, hg.2.comp_homeomorph (finHomeo _ _ h h)⟩`. Use `⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv _ _ h h)), fun f => ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearMap.comp_apply, comp_pureA _ _ h h, hT]`. Both sides reduce to the same expression.
-/
theorem admissibleFunctional_comp_compSignMul (ε : κ → ℤˣ) {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) :
    l ∘ₗ compS F ε ∈ (adeleClass F).adm κ := by
  rw [compS_eq]
  have h := diag_mul_self (F := F) ε
  intro g hg
  obtain ⟨T, hT⟩ := hl _ ⟨hg.1.comp_continuous (finHomeo _ _ h h).continuous, hg.2.comp_homeomorph (finHomeo _ _ h h)⟩
  refine ⟨T.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (archEquiv _ _ h h)), fun f => ?_⟩
  rw [LinearMap.comp_apply, comp_pureA _ _ h h, hT]
  rfl

omit [DecidableEq κ] in
/- English proof (translation)
Introduce `g hg`. Take `⟨T, hT⟩` from `hl g hg`. Conclude with `⟨c • T, fun f => by rw [LinearMap.smul_apply, hT]; rfl⟩`.
-/
theorem admissibleFunctional_smul (c : ℂ) {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) :
    c • l ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨c • T, fun f => by rw [LinearMap.smul_apply, hT]; rfl⟩

omit [DecidableEq κ] in
/- English proof (translation)
Introduce `g hg`. Take `⟨U, hU⟩` from `hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))`. Use `⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, hT _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU, pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]`.
-/
theorem admissibleFunctional_comp_adelicFourier {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)} (hT : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ)
    {l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ) : l ∘ₗ T ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨U, hU⟩ := hl (finiteFourierPi F g) ((mem_SB_iff _).2 (finiteFourierPi_mem ((mem_SB_iff g).1 hg)))
  refine ⟨U.comp (mixedFourierPiSchwartz F), fun f => ?_⟩
  rw [LinearMap.comp_apply, hT _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), ContinuousLinearMap.comp_apply, ← hU,
    pureA_eq, pureA_eq, adelicFourierPi_schwartzBruhatTensorPi]

end GlobalTheory.TowU.FourWeyl

namespace GlobalTheory.TowU.FourWeyl

open GlobalTheory.AdelicSvN.Weyl

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ _ μ hμ ε`. Take `⟨k, hk0, hk, -⟩` from `haar_cmp μ hμ`. Establish `hkc : ((k : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hk0`. Take `⟨T, hT0⟩` from `LinearMap.exists_extend (fourierLin (F := F) (κ := κ))`. Establish `hT : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ` using `fun φ hφ => LinearMap.congr_fun hT0 ⟨φ, hφ⟩`.

Establish `hTm : ∀ φ ∈ schA F κ, T φ ∈ schA F κ` using `fun φ hφ => by rw [hT φ hφ]; exact four_mem hφ`. Establish `hT4 : ∀ φ ∈ schA F κ, T (T (T (T φ))) = φ` using `fun φ hφ => by`. Rewrite using `[hT _ (hTm _ (hTm _ (hTm _ hφ))), hT _ (hTm _ (hTm _ hφ)), hT _ (hTm _ hφ), hT _ hφ, four_pow_four hφ]`. Use `⟨((k : ℝ) : ℂ) • (compS F ε ∘ₗ T), ((k : ℝ) : ℂ)⁻¹ • (T ∘ₗ T ∘ₗ T ∘ₗ compS F ε), ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_, fun l hl => ?_, fun l hl => ?_, fun w φ hφ => ?_, ⟨k, hkc, fun φ hφ => ?_⟩, fun μ₁ μ₂ h₁ h₂ => ?_⟩, fun φ hφ y => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (compS_mem ε (hTm φ hφ))`.

Conclude with `Submodule.smul_mem _ _ (hTm _ (hTm _ (hTm _ (compS_mem ε hφ))))`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, compS_compS, hT4 φ hφ, smul_smul, inv_mul_cancel₀ hkc, mul_inv_cancel₀ hkc, one_smul]`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, compS_compS, hT4 _ (compS_mem ε hφ), smul_smul, inv_mul_cancel₀ hkc, mul_inv_cancel₀ hkc, one_smul]`. Rewrite using `[LinearMap.comp_smul]`. Conclude with `admissibleFunctional_smul _ (admissibleFunctional_comp_adelicFourier hT (admissibleFunctional_comp_compSignMul ε hl))`.

Rewrite using `[LinearMap.comp_smul]`. Conclude with `admissibleFunctional_smul _ (admissibleFunctional_comp_compSignMul ε (admissibleFunctional_comp_adelicFourier hT (admissibleFunctional_comp_adelicFourier hT (admissibleFunctional_comp_adelicFourier hT hl))))`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply]`. Rewrite using `[hT _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w φ hφ), hT φ hφ, fourier_schr hψ, compS_schr]`. Establish `e : sgnV ε (-w.1) = fun i => -(((ε i : ℤ) : AF F) * w.1 i)`.

Use function extensionality and compare the values at `i`. Simplify using `only [sgnV, Pi.neg_apply, mul_neg]`. Rewrite using `[e]`. Use function extensionality and compare the values at `x`. Simplify using `only [schr, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[mul_left_comm]`. Both sides reduce to the same expression. Establish `e : ∀ (c : ℂ) (g : (κ → AF F) → ℂ), thetaSum F (c • g) = c * thetaSum F g` using `fun c g => tsum_mul_left`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply]`. Rewrite using `[e, theta_compS, hT φ hφ, theta_four hφ]`.

Take `⟨ν, hν, hνe⟩` from `haar_sgn ε μ₂ h₂`. Take `⟨k₁, hk₁, -, e₁⟩` from `haar_cmp μ₁ h₁`. Take `⟨k₂, hk₂, -, e₂⟩` from `haar_cmp ν hν`. Use `⟨((k ^ 2 * k₂ * k₁⁻¹ : ℝ≥0) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, fun φ hφ => ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.coe_ne_zero.2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hk0) hk₂) (inv_ne_zero hk₁))`.

Establish `hn : ‖((k : ℝ) : ℂ)‖ₑ = (k : ℝ≥0∞)` using `by simp [enorm_eq_nnnorm]`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply, smul_eq_mul, compS_apply, enorm_mul, mul_pow, hn]`. Rewrite using `[lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top), hνe (fun x => ‖T φ x‖ₑ ^ 2), e₂, e₁, hT φ hφ, plancherel hφ, ← mul_assoc, ← mul_assoc, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul, inv_mul_cancel_right₀ hk₁]`. Rewrite using `[hk]`. Simplify using `only [LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply, smul_eq_mul, compS_apply]`.

Rewrite using `[hT φ hφ, adelicFourierPi]`. Use `congr 2`. Use function extensionality and compare the values at `x`. Rewrite using `[isStd_eq hψ]`. Use `congr 3`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [sgnV]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isOp_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ], ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ ε : κ → ℤˣ, ∃ (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (S' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsOp ψ (fun w => (fun i => ((ε i : ℤ) : AF F) * w.2 i, fun i => -(((ε i : ℤ) : AF F) * w.1 i))) S S' ∧ ∀ φ ∈ schA F κ, ∀ y, S φ y = ∫ x, φ x * ψ (∑ i, ((ε i : ℤ) : AF F) * x i * y i) ∂μ := by
  intro F _ _ ψ hψ κ _ _ μ hμ ε
  obtain ⟨k, hk0, hk, -⟩ := haar_cmp μ hμ
  have hkc : ((k : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hk0
  obtain ⟨T, hT0⟩ := LinearMap.exists_extend (fourierLin (F := F) (κ := κ))
  have hT : ∀ φ ∈ schA F κ, T φ = adelicFourierPi F φ := fun φ hφ => LinearMap.congr_fun hT0 ⟨φ, hφ⟩
  have hTm : ∀ φ ∈ schA F κ, T φ ∈ schA F κ := fun φ hφ => by rw [hT φ hφ]; exact four_mem hφ
  have hT4 : ∀ φ ∈ schA F κ, T (T (T (T φ))) = φ := fun φ hφ => by
    rw [hT _ (hTm _ (hTm _ (hTm _ hφ))), hT _ (hTm _ (hTm _ hφ)), hT _ (hTm _ hφ), hT _ hφ, four_pow_four hφ]
  refine ⟨((k : ℝ) : ℂ) • (compS F ε ∘ₗ T), ((k : ℝ) : ℂ)⁻¹ • (T ∘ₗ T ∘ₗ T ∘ₗ compS F ε),
    ⟨fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_, fun φ hφ => ?_, fun l hl => ?_, fun l hl => ?_,
      fun w φ hφ => ?_, ⟨k, hkc, fun φ hφ => ?_⟩, fun μ₁ μ₂ h₁ h₂ => ?_⟩, fun φ hφ y => ?_⟩
  · exact Submodule.smul_mem _ _ (compS_mem ε (hTm φ hφ))
  · exact Submodule.smul_mem _ _ (hTm _ (hTm _ (hTm _ (compS_mem ε hφ))))
  · simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, compS_compS, hT4 φ hφ, smul_smul,
      inv_mul_cancel₀ hkc, mul_inv_cancel₀ hkc, one_smul]
  · simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, compS_compS, hT4 _ (compS_mem ε hφ), smul_smul,
      inv_mul_cancel₀ hkc, mul_inv_cancel₀ hkc, one_smul]
  · rw [LinearMap.comp_smul]
    exact admissibleFunctional_smul _ (admissibleFunctional_comp_adelicFourier hT (admissibleFunctional_comp_compSignMul ε hl))
  · rw [LinearMap.comp_smul]
    exact admissibleFunctional_smul _ (admissibleFunctional_comp_compSignMul ε (admissibleFunctional_comp_adelicFourier hT (admissibleFunctional_comp_adelicFourier hT (admissibleFunctional_comp_adelicFourier hT hl))))
  · simp only [LinearMap.smul_apply, LinearMap.comp_apply]
    rw [hT _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w φ hφ), hT φ hφ, fourier_schr hψ, compS_schr]
    have e : sgnV ε (-w.1) = fun i => -(((ε i : ℤ) : AF F) * w.1 i) := by
      funext i
      simp only [sgnV, Pi.neg_apply, mul_neg]
    rw [e]
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul]
    rw [mul_left_comm]
    rfl
  · have e : ∀ (c : ℂ) (g : (κ → AF F) → ℂ), thetaSum F (c • g) = c * thetaSum F g := fun c g => tsum_mul_left
    simp only [LinearMap.smul_apply, LinearMap.comp_apply]
    rw [e, theta_compS, hT φ hφ, theta_four hφ]
  · obtain ⟨ν, hν, hνe⟩ := haar_sgn ε μ₂ h₂
    obtain ⟨k₁, hk₁, -, e₁⟩ := haar_cmp μ₁ h₁
    obtain ⟨k₂, hk₂, -, e₂⟩ := haar_cmp ν hν
    refine ⟨((k ^ 2 * k₂ * k₁⁻¹ : ℝ≥0) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, fun φ hφ => ?_⟩
    · exact ENNReal.coe_ne_zero.2 (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hk0) hk₂) (inv_ne_zero hk₁))
    · have hn : ‖((k : ℝ) : ℂ)‖ₑ = (k : ℝ≥0∞) := by simp [enorm_eq_nnnorm]
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply, smul_eq_mul, compS_apply, enorm_mul,
        mul_pow, hn]
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top), hνe (fun x => ‖T φ x‖ₑ ^ 2), e₂, e₁,
        hT φ hφ, plancherel hφ, ← mul_assoc, ← mul_assoc, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
        inv_mul_cancel_right₀ hk₁]
  · rw [hk]
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, Pi.smul_apply, smul_eq_mul, compS_apply]
    rw [hT φ hφ, adelicFourierPi]
    congr 2
    funext x
    rw [isStd_eq hψ]
    congr 3
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [sgnV]
    ring

end GlobalTheory.TowU.FourWeyl

end
