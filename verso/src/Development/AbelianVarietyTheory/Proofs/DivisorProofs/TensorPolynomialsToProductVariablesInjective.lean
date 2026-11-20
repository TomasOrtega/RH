import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEval
open scoped TensorProduct Matrix Classical

noncomputable section

namespace GlobalTheory.CCRFock

open MvPolynomial

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem polMap_index_injective (W Λ : Type) [Fintype W] :
    Function.Injective (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
  have key : ∀ (f : W → (Λ →₀ ℕ)) (w : W) (l : Λ),
      (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) (w, l) = f w l := by
    intro f w l
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single w]
    · exact Finsupp.mapDomain_apply (Prod.mk_right_injective w) _ _
    · intro v _ hv
      apply Finsupp.mapDomain_notin_range
      rintro ⟨x, hx⟩
      exact hv (congrArg Prod.fst hx)
    · intro h
      exact absurd (Finset.mem_univ w) h
  intro f g h
  funext w
  ext l
  rw [← key f w l, ← key g w l]
  exact congrArg (fun F : (W × Λ) →₀ ℕ => F (w, l)) h

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem polMap_tprod_monomial (W Λ : Type) [Fintype W] [DecidableEq W] (f : W → (Λ →₀ ℕ)) :
    polMap W Λ (PiTensorProduct.tprod ℂ (fun w => (monomial (f w) (1 : ℂ) : MvPolynomial Λ ℂ))) =
      monomial (∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) 1 := by
  rw [monomial_sum_one]
  simp only [polMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply, rename_monomial]

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem polMap_injective (W Λ : Type) [Fintype W] [DecidableEq W] :
    Function.Injective (polMap W Λ) := by
  let B := Basis.piTensorProduct (fun _ : W => basisMonomials Λ ℂ)
  have hli : LinearIndependent ℂ (polMap W Λ ∘ B) := by
    have h := (basisMonomials (W × Λ) ℂ).linearIndependent.comp _ (polMap_index_injective W Λ)
    have e : polMap W Λ ∘ B = (basisMonomials (W × Λ) ℂ) ∘
        (fun f : W → (Λ →₀ ℕ) => ∑ w, Finsupp.mapDomain (Prod.mk w) (f w)) := by
      funext f
      simp only [Function.comp, B, Basis.piTensorProduct_apply, coe_basisMonomials]
      exact polMap_tprod_monomial W Λ f
    rw [e]
    exact h
  have h1 : polMap W Λ ∘ₗ Finsupp.linearCombination ℂ B = Finsupp.linearCombination ℂ (polMap W Λ ∘ B) := by
    ext f
    simp
  intro x y hxy
  apply B.repr.injective
  apply hli
  rw [← h1]
  simp only [LinearMap.comp_apply, Module.Basis.linearCombination_repr, hxy]

end GlobalTheory.CCRFock
