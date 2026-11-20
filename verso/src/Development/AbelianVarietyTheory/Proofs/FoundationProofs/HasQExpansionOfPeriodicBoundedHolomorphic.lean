import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQCoeffIffHasQExpansion
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Function

namespace GlobalTheory.FN

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem periodic_comp_ofComplex_of_vadd_real {f : ℍ → ℂ} {h : ℝ}
    (hf : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) (h : ℂ) := by
  intro w
  by_cases! hw : 0 < Complex.im w
  · have : 0 < Complex.im (w + h) := by simp [hw]
    simp only [comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos this,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    convert! hf ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have : Complex.im (w + h) ≤ 0 := by simpa using hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos this,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasQ_of_periodic_bounded : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  intro N f hN hf hper hbdd
  refine ⟨fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion (N : ℝ) f), ?_⟩
  rw [GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
  exact GlobalTheory.HasQExpansion.of_periodic (by exact_mod_cast hN)
    (periodic_comp_ofComplex_of_vadd_real hper) hf hbdd

end GlobalTheory.FN
