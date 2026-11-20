import Mathlib
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Treat this case separately. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem span_range_X_eq_ker_constantCoeff (k : Type) [Field k] (n : ℕ) :
    Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))
      = RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp [RingHom.mem_ker]
  · intro p hp
    rw [RingHom.mem_ker] at hp
    have key : ∀ q : MvPolynomial (Fin n) k, q - MvPolynomial.C (MvPolynomial.constantCoeff q) ∈
        Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k))) := by
      intro q
      induction q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
        have := Ideal.add_mem _ hp hq
        convert this using 1
        simp only [map_add]; ring
      | mul_X p i _ =>
        simp only [map_mul, MvPolynomial.constantCoeff_X, mul_zero, map_zero, sub_zero]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    simpa [hp] using key p

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem le_height_span_range_X_mvPolynomial : ∀ (k : Type) [Field k] (n : ℕ), ((n : ℕ∞)) ≤ (Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))).height := by
  intro k _ n
  rw [span_range_X_eq_ker_constantCoeff]
  haveI : (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨MvPolynomial.C a, by simp⟩)
  have h := ReciprocityTheory.CA.height_maximal_mvPolynomial_field k n (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin n) k →+* k))
  exact h.2.ge

end GlobalTheory
