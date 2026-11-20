import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilDilation

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [Field E] [Algebra F E]

open Classical in

/- English proof (translation)
Establish `key : (∃ s : Eˣ, Algebra.norm F (s : E) = c / Algebra.norm F (t : E)) ↔ ∃ s : Eˣ, Algebra.norm F (s : E) = c`. Establish `h1 : Algebra.norm F ((t⁻¹ : Eˣ) : E) * Algebra.norm F (t : E) = 1`. Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `hA : Algebra.norm F (t : E) ≠ 0` using `right_ne_zero_of_mul_eq_one h1`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs⟩`. Use `⟨s * t, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul, hs, div_mul_cancel₀ _ hA]`. Introduce and unpack `⟨s, hs⟩`. Use `⟨s * t⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, map_mul, hs, eq_div_iff hA, mul_assoc, h1, mul_one]`. Unfold `nsg`. Simplify using `only [key]`.
-/
theorem nsg_div_norm (c : F) (t : Eˣ) : nsg E (c / Algebra.norm F (t : E)) = nsg E c := by
  have key : (∃ s : Eˣ, Algebra.norm F (s : E) = c / Algebra.norm F (t : E)) ↔
      ∃ s : Eˣ, Algebra.norm F (s : E) = c := by
    have h1 : Algebra.norm F ((t⁻¹ : Eˣ) : E) * Algebra.norm F (t : E) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hA : Algebra.norm F (t : E) ≠ 0 := right_ne_zero_of_mul_eq_one h1
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s * t, ?_⟩
      rw [Units.val_mul, map_mul, hs, div_mul_cancel₀ _ hA]
    · rintro ⟨s, hs⟩
      refine ⟨s * t⁻¹, ?_⟩
      rw [Units.val_mul, map_mul, hs, eq_div_iff hA, mul_assoc, h1, mul_one]
  unfold nsg
  simp only [key]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχc hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη g hg t Φ hΦ`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩`. Use `haveI : Algebra.IsSeparable F E := inferInstance`. Establish `hσc : σ = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E`.

Break down `GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj σ with h | h` into its components or cases. Conclude with `absurd h hσ`. Conclude with `h`. Use `set A : F := Algebra.norm F (t : E) with hAdef`. Establish `hA : A ≠ 0` using `Algebra.norm_ne_zero_iff.2 t.ne_zero`.

Establish `hsig : σ (t : E) * (t : E) = algebraMap F E A`. Rewrite using `[hAdef, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.algebraMap_norm_eq_mul_conj, hσc, mul_comm]`. Establish `hmodE : ((modulus (t : E) : NNReal) : ℝ) = modulus A` using `GlobalTheory.CompanionTheory.NormModulus.wMod F χ hχc hχ1 E hd hc σ hσ η hη (t : E)`. Use function extensionality and compare the values at `y`. Establish `e00 : cjA A g 0 0 = g 0 0` using `by simp [cjA]`.

Establish `e01 : cjA A g 0 1 = A * g 0 1` using `by simp [cjA]`. Establish `e10 : cjA A g 1 0 = g 1 0 / A` using `by simp [cjA]`. Establish `e11 : cjA A g 1 1 = g 1 1` using `by simp [cjA]`. Simplify using `only [rWm, e00, e01, e10, e11]`. Distinguish the cases in `hc0 : g 1 0 = 0`.

Rewrite using `[rW, rW, if_pos hc0, if_pos (by rw [hc0, zero_div])]`. Establish `h1 : g 0 0 * g 0 1 * Algebra.norm F (y * (t : E)) = g 0 0 * (A * g 0 1) * Algebra.norm F y`. Rewrite using `[map_mul, ← hAdef]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, mul_assoc (algebraMap F E (g 0 0)) y (t : E)]`.

Establish `hcA : g 1 0 / A ≠ 0` using `div_ne_zero hc0 hA`. Rewrite using `[rW, rW, if_neg hc0, if_neg hcA]`. Establish `hn : nsg E (-(g 1 0 / A)) = nsg E (-(g 1 0))`. Rewrite using `[← neg_div]`. Conclude with `nsg_div_norm _ t`.

Establish `hm : (((modulus (g 1 0 / A) : ℝ)⁻¹ : ℝ) : ℂ) = (((modulus (g 1 0) : ℝ)⁻¹ : ℝ) : ℂ) * ((modulus A : ℝ) : ℂ)`. Establish `hA0 : ((modulus A : NNReal) : ℝ) ≠ 0`. Conclude with `modulus_ne_zero hA` after adjusting the coercions. Rewrite using `[div_eq_mul_inv, modulus_mul, modulus_inv]`. Use `push_cast`.

Rewrite using `[mul_inv, inv_inv]`. Use `set f : E → ℂ := fun u => (χ ((g 0 0 * Algebra.norm F (y * (t : E)) + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ (y * (t : E)) * u)) / g 1 0) : ℂ) * Φ u with hf`. Establish `hsub` using `integral_comp_mul_left (muE E χ) (t.ne_zero) f`. Establish `hint : ∫ u, f u ∂muE E χ = ((modulus A : ℝ) : ℂ) * ∫ u, f ((t : E) * u) ∂muE E χ`. Rewrite using `[hsub, ← hmodE, Complex.real_smul]`.

Establish `: ((modulus (t : E) : NNReal) : ℝ) ≠ 0`. Conclude with `modulus_ne_zero t.ne_zero` after adjusting the coercions. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hpt : ∀ u, f ((t : E) * u) = (χ ((g 0 0 * Algebra.norm F y + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ y * u)) / (g 1 0 / A)) : ℂ) * Φ (u * (t : E))`.

Introduce `u`. Establish `htr : Algebra.trace F E (σ (y * (t : E)) * ((t : E) * u)) = A * Algebra.trace F E (σ y * u)`. Establish `: σ (y * (t : E)) * ((t : E) * u) = A • (σ y * u)`. Rewrite using `[Algebra.smul_def, ← hsig, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, map_smul, smul_eq_mul]`. Establish `harg : (g 0 0 * Algebra.norm F (y * (t : E)) + g 1 1 * Algebra.norm F ((t : E) * u) - Algebra.trace F E (σ (y * (t : E)) * ((t : E) * u))) / g 1 0 = (g 0 0 * Algebra.norm F y + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ y * u)) / (g 1 0 / A)`. Rewrite using `[htr, map_mul, map_mul, ← hAdef]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [hf]`.

Rewrite using `[harg, mul_comm (t : E) u]`. Express the relevant statement in the definitionally equal form `_ * _ * _ * ∫ u, f u ∂muE E χ = _`. Rewrite using `[hint, hn, hm]`. Simplify using `only [hpt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wDiagT : Ad3.K.GL2LocalData.WDiagT := by
  intro F _ _ _ _ _ _ _ χ hχc hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη g hg t Φ hΦ
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hd
  haveI : Fact (Module.finrank F E = 2) := ⟨hd⟩
  haveI : Algebra.IsSeparable F E := inferInstance
  have hσc : σ = GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.conj F E := by
    rcases GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.eq_one_or_eq_conj σ with h | h
    · exact absurd h hσ
    · exact h
  set A : F := Algebra.norm F (t : E) with hAdef
  have hA : A ≠ 0 := Algebra.norm_ne_zero_iff.2 t.ne_zero
  have hsig : σ (t : E) * (t : E) = algebraMap F E A := by
    rw [hAdef, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.algebraMap_norm_eq_mul_conj, hσc, mul_comm]
  have hmodE : ((modulus (t : E) : NNReal) : ℝ) = modulus A :=
    GlobalTheory.CompanionTheory.NormModulus.wMod F χ hχc hχ1 E hd hc σ hσ η hη (t : E)
  funext y
  have e00 : cjA A g 0 0 = g 0 0 := by simp [cjA]
  have e01 : cjA A g 0 1 = A * g 0 1 := by simp [cjA]
  have e10 : cjA A g 1 0 = g 1 0 / A := by simp [cjA]
  have e11 : cjA A g 1 1 = g 1 1 := by simp [cjA]
  simp only [rWm, e00, e01, e10, e11]
  by_cases hc0 : g 1 0 = 0
  · rw [rW, rW, if_pos hc0, if_pos (by rw [hc0, zero_div])]
    have h1 : g 0 0 * g 0 1 * Algebra.norm F (y * (t : E)) =
        g 0 0 * (A * g 0 1) * Algebra.norm F y := by
      rw [map_mul, ← hAdef]; ring
    rw [h1, mul_assoc (algebraMap F E (g 0 0)) y (t : E)]
  · have hcA : g 1 0 / A ≠ 0 := div_ne_zero hc0 hA
    rw [rW, rW, if_neg hc0, if_neg hcA]
    have hn : nsg E (-(g 1 0 / A)) = nsg E (-(g 1 0)) := by
      rw [← neg_div]; exact nsg_div_norm _ t
    have hm : (((modulus (g 1 0 / A) : ℝ)⁻¹ : ℝ) : ℂ) =
        (((modulus (g 1 0) : ℝ)⁻¹ : ℝ) : ℂ) * ((modulus A : ℝ) : ℂ) := by
      have hA0 : ((modulus A : NNReal) : ℝ) ≠ 0 := by
        exact_mod_cast modulus_ne_zero hA
      rw [div_eq_mul_inv, modulus_mul, modulus_inv]
      push_cast
      rw [mul_inv, inv_inv]
    set f : E → ℂ := fun u => (χ ((g 0 0 * Algebra.norm F (y * (t : E)) + g 1 1 * Algebra.norm F u -
      Algebra.trace F E (σ (y * (t : E)) * u)) / g 1 0) : ℂ) * Φ u with hf
    have hsub := integral_comp_mul_left (muE E χ) (t.ne_zero) f
    have hint : ∫ u, f u ∂muE E χ = ((modulus A : ℝ) : ℂ) * ∫ u, f ((t : E) * u) ∂muE E χ := by
      rw [hsub, ← hmodE, Complex.real_smul]
      have : ((modulus (t : E) : NNReal) : ℝ) ≠ 0 := by
        exact_mod_cast modulus_ne_zero t.ne_zero
      push_cast
      field_simp
    have hpt : ∀ u, f ((t : E) * u) = (χ ((g 0 0 * Algebra.norm F y + g 1 1 * Algebra.norm F u -
        Algebra.trace F E (σ y * u)) / (g 1 0 / A)) : ℂ) * Φ (u * (t : E)) := by
      intro u
      have htr : Algebra.trace F E (σ (y * (t : E)) * ((t : E) * u)) =
          A * Algebra.trace F E (σ y * u) := by
        have : σ (y * (t : E)) * ((t : E) * u) = A • (σ y * u) := by
          rw [Algebra.smul_def, ← hsig, map_mul]; ring
        rw [this, map_smul, smul_eq_mul]
      have harg : (g 0 0 * Algebra.norm F (y * (t : E)) + g 1 1 * Algebra.norm F ((t : E) * u) -
          Algebra.trace F E (σ (y * (t : E)) * ((t : E) * u))) / g 1 0 =
          (g 0 0 * Algebra.norm F y + g 1 1 * Algebra.norm F u -
            Algebra.trace F E (σ y * u)) / (g 1 0 / A) := by
        rw [htr, map_mul, map_mul, ← hAdef]
        field_simp
      simp only [hf]
      rw [harg, mul_comm (t : E) u]
    change _ * _ * _ * ∫ u, f u ∂muE E χ = _
    rw [hint, hn, hm]
    simp only [hpt]
    ring

end GlobalTheory.CompanionTheory.WeilDilation
