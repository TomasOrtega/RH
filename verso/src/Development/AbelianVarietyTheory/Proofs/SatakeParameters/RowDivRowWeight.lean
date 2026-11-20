import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimePowSmulMemValueLatticeErase

noncomputable section

namespace GlobalTheory.ValCmp

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.LvT.KerLat

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem rowGen_diag_monomial_one (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (d : Fin r × Fin n →₀ ℕ) :
    rowGen R a a (monomial d 1) =
      (1 + Polynomial.X) ^ (Finsupp.weight (rowW r n) d a) * Polynomial.C (monomial d 1) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have e : (monomial (f + g) (1 : R) : MvPolynomial (Fin r × Fin n) R) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, map_add, Pi.add_apply, pow_add, map_mul]
    ring
  | single v c =>
    obtain ⟨b, s⟩ := v
    rw [← X_pow_eq_monomial, map_pow, map_pow]
    unfold rowGen
    rw [aeval_X]
    by_cases h : b = a
    · subst h
      have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) b = c := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index]
      rw [e, ← mul_pow]
      simp only [if_true]
      congr 1
      ring
    · have e : Finsupp.weight (rowW r n) (Finsupp.single (b, s) c) a = 0 := by
        simp [Finsupp.weight_apply, rowW, Finsupp.sum_single_index, Ne.symm h]
      rw [e]
      simp [h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem rowGen_diag_homog (R : Type) [CommRing R] {r n : ℕ} (μ : Fin r → ℕ) (a : Fin r)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowW r n) f μ) :
    rowGen R a a f = (1 + Polynomial.X) ^ (μ a) * Polynomial.C f := by
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : (monomial d (coeff d f) : MvPolynomial (Fin r × Fin n) R) = coeff d f • monomial d 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul, rowGen_diag_monomial_one, hf (mem_support_iff.mp hd), ← mul_smul_comm,
    Polynomial.smul_C]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem rowDiv_rowWeight : ∀ (R : Type) [CommRing R] (r n : ℕ) (μ : Fin r → ℕ)
    (f : MvPolynomial (Fin r × Fin n) R), IsWeightedHomogeneous (rowW r n) f μ →
    (∀ (a b : Fin r) (k : ℕ), ∃ μ' : Fin r → ℕ, IsWeightedHomogeneous (rowW r n) (rowDiv R a b k f) μ') ∧
      ∀ (a : Fin r) (k : ℕ), rowDiv R a a k f = ((μ a).choose k) • f := by
  intro R _ r n μ f hf
  refine ⟨fun a b k => ?_, fun a k => ?_⟩
  · have hZ : IsWeightedHomogeneous (rowZ r n) f (fun i => (μ i : ℤ)) := by
      intro d hd
      funext i
      rw [weight_rowZ, hf hd]
    have h := rowDiv_shift R _ a b k f hZ
    refine ⟨fun i => ((((fun i => (μ i : ℤ)) + k • (Pi.single a 1 - Pi.single b 1) : Fin r → ℤ)) i).toNat,
      fun d hd => ?_⟩
    funext i
    rw [← h hd, weight_rowZ, Int.toNat_natCast]
  · unfold rowDiv
    rw [rowGen_diag_homog R μ a f hf, Polynomial.coeff_mul_C, Polynomial.coeff_one_add_X_pow, nsmul_eq_mul]

end GlobalTheory.ValCmp
