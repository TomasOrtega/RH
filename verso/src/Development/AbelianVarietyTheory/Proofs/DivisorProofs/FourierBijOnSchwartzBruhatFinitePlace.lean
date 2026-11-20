import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.FourierLocBij

def toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) : AddChar k Circle where
  toFun t := ⟨ψ t, by simp [Submonoid.unitSphere, hn t]⟩
  map_zero_eq_one' := Circle.ext (by simp)
  map_add_eq_mul' a b := Circle.ext (AddChar.map_add_eq_mul ψ a b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_toCircle {k : Type} [AddMonoid k] (ψ : AddChar k ℂ) (hn : ∀ t, ‖ψ t‖ = 1) (t : k) :
    ((toCircle ψ hn t : Circle) : ℂ) = ψ t := rfl

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[← integral_add_right_eq_self (μ := m) (fun x => φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) (-a), ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[neg_add_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, neg_dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem translate_fourier [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) {κ : Type} [Fintype κ]
    (m : Measure (κ → k)) [m.IsAddRightInvariant] (φ : (κ → k) → ℂ) (a y : κ → k) :
    ∫ x, φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m = (ψ (-(a ⬝ᵥ y)) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
  rw [← integral_add_right_eq_self (μ := m) (fun x => φ (x + a) * (ψ (x ⬝ᵥ y) : ℂ)) (-a), ← integral_const_mul]
  congr 1
  funext x
  rw [neg_add_cancel_right, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul, neg_dotProduct]
  ring

/- English proof (translation)
Use `haveI := GlobalTheory.SplitWeil.secondCountable k`. Use `haveI := GlobalTheory.SplitWeil.t2Space k`. Take `⟨ν, hν⟩` from `(GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1`. Use `haveI := hν.1`. Use `set m : Measure (κ → k) := Measure.pi fun _ => ν with hm`.

Establish `hμ : μ = μ.addHaarScalarFactor m • m` using `Measure.isAddLeftInvariant_eq_smul μ m`. Use `set r := μ.addHaarScalarFactor m with hr_def`. Establish `hr : r ≠ 0`. Introduce `h0`. Rewrite `hμ` using `[h0, zero_smul]`.

Conclude with `NeZero.ne μ hμ`. Establish `hT : ∀ φ : (κ → k) → ℂ, (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) = fun y => ((r : ℝ) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m`. Introduce `φ`. Use function extensionality and compare the values at `y`. Rewrite using `[hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.

Establish `key` using `fun φ hφ => GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν φ hφ`. Establish `hcomp : ∀ (e : (κ → k) ≃ₜ (κ → k)), ∀ f ∈ SB (κ → k), (fun x => f (e x)) ∈ SB (κ → k)` using `fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩`. Establish `hr' : ((r : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hr`. Use `⟨fun φ hφ => ?_, fun φ₁ h₁ φ₂ h₂ he => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Use `show (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (κ → k)`.

Rewrite using `[hT]`. Conclude with `Submodule.smul_mem _ ((r : ℝ) : ℂ) (key φ hφ).1`. Establish `he' : ∀ y, ∫ x, φ₁ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m = ∫ x, φ₂ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m`. Introduce `y`. Use `congrFun he y` as an intermediate fact.

Simplify using `only at this`. Rewrite `this` using `[hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def, Complex.real_smul, Complex.real_smul]`. Conclude with `mul_left_cancel₀ hr' this`. Use function extensionality and compare the values at `a`. Establish `h1a` using `(key _ (hcomp (Homeomorph.addRight a) _ h₁)).2`.

Establish `h2a` using `(key _ (hcomp (Homeomorph.addRight a) _ h₂)).2`. Simplify using `only [Homeomorph.coe_addRight, zero_add] at h1a h2a`. Rewrite using `[← h1a, ← h2a]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Rewrite using `[translate_fourier, translate_fourier, he']`. Take `⟨Φ, hΦ⟩` from `(GlobalTheory.SplitWeil.FourierSurj.hat_surjective k κ ψ hc h1 ν hν).2 ⟨g, hg⟩`. Use `⟨((r : ℝ) : ℂ)⁻¹ • Φ.1, Submodule.smul_mem _ _ Φ.2, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hT]`.

Use function extensionality and compare the values at `y`. Establish `hΦ' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ.1 = g` using `hΦ`. Rewrite using `[← hΦ']`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc]`. Rewrite using `[integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hr', one_mul]`.

Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm y]`. Both sides reduce to the same expression.
-/
theorem bijOn_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    Set.BijOn (fun (φ : (κ → k) → ℂ) (y : κ → k) => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ)
      (SB (κ → k) : Set _) (SB (κ → k) : Set _) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hT : ∀ φ : (κ → k) → ℂ, (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) =
      fun y => ((r : ℝ) : ℂ) * ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
    intro φ
    funext y
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have key := fun φ hφ => GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν φ hφ
  have hcomp : ∀ (e : (κ → k) ≃ₜ (κ → k)), ∀ f ∈ SB (κ → k), (fun x => f (e x)) ∈ SB (κ → k) :=
    fun e f hf => ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨fun φ hφ => ?_, fun φ₁ h₁ φ₂ h₂ he => ?_, fun g hg => ?_⟩
  · show (fun y => ∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) ∈ SB (κ → k)
    rw [hT]
    exact Submodule.smul_mem _ ((r : ℝ) : ℂ) (key φ hφ).1
  · have he' : ∀ y, ∫ x, φ₁ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m = ∫ x, φ₂ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m := by
      intro y
      have := congrFun he y
      simp only at this
      rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.smul_def,
        Complex.real_smul, Complex.real_smul] at this
      exact mul_left_cancel₀ hr' this
    funext a
    have h1a := (key _ (hcomp (Homeomorph.addRight a) _ h₁)).2
    have h2a := (key _ (hcomp (Homeomorph.addRight a) _ h₂)).2
    simp only [Homeomorph.coe_addRight, zero_add] at h1a h2a
    rw [← h1a, ← h2a]
    congr 1
    funext y
    rw [translate_fourier, translate_fourier, he']
  · obtain ⟨Φ, hΦ⟩ := (GlobalTheory.SplitWeil.FourierSurj.hat_surjective k κ ψ hc h1 ν hν).2 ⟨g, hg⟩
    refine ⟨((r : ℝ) : ℂ)⁻¹ • Φ.1, Submodule.smul_mem _ _ Φ.2, ?_⟩
    simp only
    rw [hT]
    funext y
    have hΦ' : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat ψ ν Φ.1 = g := hΦ
    rw [← hΦ']
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hr', one_mul]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, dotProduct_comm y]
    rfl

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `F _ _ v ψ hc hn h1 κ _ inst _ μ _`. Use `letI : MeasurableSpace (Fv F v) := borel _`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)`. Establish `e : inst = MeasurableSpace.pi`.

Rewrite using `[BorelSpace.measurable_eq (α := κ → Fv F v)]`. Conclude with `(BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm`. Substitute `e` using the available equality. Establish `hcont : Continuous (toCircle ψ hn)` using `Continuous.subtype_mk hc _`. Establish `hne : toCircle ψ hn ≠ 1`.

Introduce `h`. Apply `h1` to reduce the goal to its premises. Use extensionality with `t`. Simplify `congrArg (fun χ : AddChar (Fv F v) Circle => ((χ t : Circle) : ℂ)) h` using `[coe_toCircle]`. Conclude with `bijOn_circle (toCircle ψ hn) hcont hne κ μ`.
-/
theorem fourier_bijOn : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 → ∀ (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure],
    Set.BijOn (fun (φ : (κ → Fv F v) → ℂ) (y : κ → Fv F v) => ∫ x, φ x * ψ (x ⬝ᵥ y) ∂μ)
      (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := by
  intro F _ _ v ψ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (toCircle ψ hn) := Continuous.subtype_mk hc _
  have hne : toCircle ψ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [coe_toCircle] using congrArg (fun χ : AddChar (Fv F v) Circle => ((χ t : Circle) : ℂ)) h
  exact bijOn_circle (toCircle ψ hn) hcont hne κ μ

end GlobalTheory.FourierLocBij
