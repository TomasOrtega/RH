import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem isIntegral_smul_of_charpoly_coeff_mul_int
    (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ)
    (h : ∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) :
    IsIntegral ℤ ((M : ℤ) • x) := by
  set χ := (LinearMap.mulLeft ℚ x).charpoly with hχ
  have hmon : χ.Monic := LinearMap.charpoly_monic _

  have hx : Polynomial.aeval x χ = 0 := by
    have h1 : Polynomial.aeval (LinearMap.mulLeft ℚ x) χ = 0 := LinearMap.aeval_self_charpoly _
    have h2 : Polynomial.aeval (Algebra.lmul ℚ A x) χ = Algebra.lmul ℚ A (Polynomial.aeval x χ) :=
      Polynomial.aeval_algHom_apply _ _ _
    have h3 : Algebra.lmul ℚ A x = LinearMap.mulLeft ℚ x := rfl
    rw [h3, h1] at h2
    have := congrArg (fun f : A →ₗ[ℚ] A => f 1) h2
    simpa using this.symm
  have hs : Polynomial.aeval (algebraMap ℚ A (M : ℚ) * x) (χ.scaleRoots (M : ℚ)) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero hx
  have hsmon : (χ.scaleRoots (M : ℚ)).Monic := by
    unfold Polynomial.Monic Polynomial.leadingCoeff
    rw [Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero,
      mul_one]
    exact hmon
  have hlift : χ.scaleRoots (M : ℚ) ∈ Polynomial.lifts (algebraMap ℤ ℚ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy n χ.natDegree with hn | hn | hn
    · obtain ⟨a, ha⟩ := h n
      refine ⟨a * (M : ℤ) ^ (χ.natDegree - n - 1), ?_⟩
      have he : χ.natDegree - n = (χ.natDegree - n - 1) + 1 := by omega
      rw [he, pow_succ, map_mul, map_pow, eq_intCast, eq_intCast, ← ha]
      push_cast
      ring
    · subst hn
      rw [Nat.sub_self, pow_zero, mul_one]
      exact ⟨1, by simpa using hmon.coeff_natDegree.symm⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
      exact ⟨0, by simp⟩
  obtain ⟨q, hq, -, hqmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hsmon
  refine ⟨q, hqmon, ?_⟩
  have : Polynomial.aeval ((M : ℤ) • x) q = 0 := by
    rw [← Polynomial.aeval_map_algebraMap ℚ, hq]
    convert hs using 2
    rw [Algebra.smul_def]
    simp
  simpa [Polynomial.aeval_def] using this

end GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
example : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (x : A) (M : ℕ), (∀ i, ∃ a : ℤ, (M : ℚ) * (LinearMap.mulLeft ℚ x).charpoly.coeff i = a) → IsIntegral ℤ ((M : ℤ) • x) := @GlobalTheory.isIntegral_smul_of_charpoly_coeff_mul_int
