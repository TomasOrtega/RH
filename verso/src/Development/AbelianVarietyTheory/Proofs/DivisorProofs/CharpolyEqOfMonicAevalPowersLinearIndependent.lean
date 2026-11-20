import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ n X P hP hdeg hX hli`. Break down `subsingleton_or_nontrivial K with hK | hK` into its components or cases. Conclude with `Subsingleton.elim _ _`. Establish `hc : X.charpoly.Monic` using `Matrix.charpoly_monic X`. Establish `hcd : X.charpoly.natDegree = n`.

Simplify using `using Matrix.charpoly_natDegree_eq_dim X`. Establish `hcdeg : X.charpoly.degree = n`. Rewrite using `[Polynomial.degree_eq_natDegree hc.ne_zero, hcd]`. Establish `hPdeg : P.degree = n`. Rewrite using `[Polynomial.degree_eq_natDegree hP.ne_zero, hdeg]`.

Establish `hDdeg : (X.charpoly - P).degree < n`. Establish `h` using `Polynomial.degree_sub_lt (p := X.charpoly) (q := P) (by rw [hcdeg, hPdeg]) hc.ne_zero (by rw [hc.leadingCoeff, hP.leadingCoeff])`. Rewrite `h` using `[hcdeg]`. Then use the resulting hypothesis. Establish `hDaeval : Polynomial.aeval X (X.charpoly - P) = 0`. Rewrite using `[map_sub, Matrix.aeval_self_charpoly, hX, sub_zero]`.

Rewrite using `[← sub_eq_zero]`. Assume the negation of the conclusion as `hD0`. Establish `hnat : (X.charpoly - P).natDegree < n` using `(Polynomial.natDegree_lt_iff_degree_lt hD0).mpr hDdeg`. Establish `hsum : ∑ i : Fin n, (X.charpoly - P).coeff (i : ℕ) • X ^ (i : ℕ) = 0`. Establish `h` using `Polynomial.aeval_eq_sum_range' hnat X`.

Rewrite `h` using `[hDaeval, Finset.sum_range (fun i => (X.charpoly - P).coeff i • X ^ i)]`. Conclude with `h.symm`. Establish `hcoeff` using `Fintype.linearIndependent_iff.mp hli (fun i : Fin n => (X.charpoly - P).coeff (i : ℕ)) hsum`. Apply `hD0` to reduce the goal to its premises. Use extensionality with `k`.

Rewrite using `[Polynomial.coeff_zero]`. Distinguish the cases in `hk : k < n`. Conclude with `hcoeff ⟨k, hk⟩`. Conclude with `Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat (not_lt.mp hk))`.
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
