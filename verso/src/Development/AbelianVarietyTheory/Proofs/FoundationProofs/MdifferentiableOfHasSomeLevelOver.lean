import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
The claim follows from `(CuspForm.discriminant).holo'`.
-/
theorem dd_mdifferentiable : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ) :=
  (CuspForm.discriminant).holo'

/- English proof (translation)
Introduce `E f ⟨N, w, hN, _, hq⟩`. Take `⟨a, ha, _⟩` from `hq 1`. Establish `hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ))` using `ha.mdifferentiable hN`. Establish `hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w)` using `fun τ => (dd_mdifferentiable τ).pow w`. Establish `hdiv` using `hg.div hD (fun τ => pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ))`.

Establish `heq : ((fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) / fun τ : ℍ => DD τ ^ w) = f`. Use function extensionality and compare the values at `τ`. Establish `h0 : DD τ ^ w ≠ 0` using `pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)`. Simplify using `only [Pi.div_apply, one_smul]`. Clear the denominators using the available nonvanishing facts.

Rewrite `hdiv` using `[heq]`. Then use the resulting hypothesis.
-/
theorem inR_mdifferentiable : ∀ (E : Subring ℂ) (f : ℍ → ℂ), InR E f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := by
  intro E f ⟨N, w, hN, _, hq⟩
  obtain ⟨a, ha, _⟩ := hq 1
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) :=
    ha.mdifferentiable hN
  have hD : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => DD τ ^ w) := fun τ => (dd_mdifferentiable τ).pow w
  have hdiv := hg.div hD (fun τ => pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ))
  have heq : ((fun τ : ℍ => DD τ ^ w * f ((1 : SL(2, ℤ)) • τ)) / fun τ : ℍ => DD τ ^ w) = f := by
    funext τ
    have h0 : DD τ ^ w ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ)
    simp only [Pi.div_apply, one_smul]
    field_simp
  rwa [heq] at hdiv

end GlobalTheory.FN
