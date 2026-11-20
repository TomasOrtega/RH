import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

A detailed English derivation is pending.
-/
theorem charpoly_eq_of_monic_aeval_linearIndependent :
    ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K),
      P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 →
      LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  intro K _ n X P hP hdeg hX hli
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  have hc : X.charpoly.Monic := Matrix.charpoly_monic X
  have hcd : X.charpoly.natDegree = n := by
    simpa using Matrix.charpoly_natDegree_eq_dim X
  have hcdeg : X.charpoly.degree = n := by
    rw [Polynomial.degree_eq_natDegree hc.ne_zero, hcd]
  have hPdeg : P.degree = n := by
    rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdeg]
  have hDdeg : (X.charpoly - P).degree < n := by
    have h := Polynomial.degree_sub_lt (p := X.charpoly) (q := P)
      (by rw [hcdeg, hPdeg]) hc.ne_zero (by rw [hc.leadingCoeff, hP.leadingCoeff])
    rwa [hcdeg] at h
  have hDaeval : Polynomial.aeval X (X.charpoly - P) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hX, sub_zero]
  rw [← sub_eq_zero]
  by_contra hD0
  have hnat : (X.charpoly - P).natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hD0).mpr hDdeg
  have hsum : ∑ i : Fin n, (X.charpoly - P).coeff (i : ℕ) • X ^ (i : ℕ) = 0 := by
    have h := Polynomial.aeval_eq_sum_range' hnat X
    rw [hDaeval, Finset.sum_range (fun i => (X.charpoly - P).coeff i • X ^ i)] at h
    exact h.symm
  have hcoeff := Fintype.linearIndependent_iff.mp hli
    (fun i : Fin n => (X.charpoly - P).coeff (i : ℕ)) hsum
  apply hD0
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < n
  · exact hcoeff ⟨k, hk⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat (not_lt.mp hk))

end GlobalTheory
