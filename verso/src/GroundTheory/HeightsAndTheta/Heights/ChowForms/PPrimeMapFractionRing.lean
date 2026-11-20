import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
Introduce `O K _ _ _ _ _ n P hP hnc`. Use `set M : Submonoid (MvPolynomial (Fin n) O) := (nonZeroDivisors O).map (C (σ := Fin n))`. Establish `: IsLocalization M (MvPolynomial (Fin n) K)` using `MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors O) K`. Establish `hprime : (Ideal.span {P}).IsPrime` using `(Ideal.span_singleton_prime hP.ne_zero).mpr hP`. Establish `hdisj : Disjoint (M : Set (MvPolynomial (Fin n) O)) ↑(Ideal.span {P})`.

Rewrite using `[Set.disjoint_left]`. Introduce and unpack `_ ⟨a, ha, rfl⟩ hmem`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Establish `hCa : (C a : MvPolynomial (Fin n) O) ≠ 0` using `by simpa using ha0`. Establish `hdvd : P ∣ C a` using `Ideal.mem_span_singleton.mp hmem`.

Establish `hdeg : P.totalDegree = 0`. Use `totalDegree_le_of_dvd_of_isDomain hdvd hCa` as an intermediate fact. Rewrite `this` using `[totalDegree_C]`. Use linear arithmetic over natural numbers and integers. Conclude with `hnc _ (totalDegree_eq_zero_iff_eq_C.mp hdeg)`.

Establish `hmap` using `IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial (Fin n) K) _ hprime hdisj`. Rewrite `hmap` using `[Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def]`. Establish `hinj : Function.Injective (map (σ` using `Fin n) (algebraMap O K)) := map_injective _ (IsFractionRing.injective O K)`. Establish `hne : map (algebraMap O K) P ≠ 0`. Introduce `h`.

Conclude with `hP.ne_zero (hinj (by rw [h, map_zero]))`. Conclude with `(Ideal.span_singleton_prime hne).mp hmap`.
-/
theorem PrimeMapFractionRing.proof : PrimeMapFractionRing.Statement := by
  intro O K _ _ _ _ _ n P hP hnc
  classical
  set M : Submonoid (MvPolynomial (Fin n) O) := (nonZeroDivisors O).map (C (σ := Fin n))
  have : IsLocalization M (MvPolynomial (Fin n) K) :=
    MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors O) K

  have hprime : (Ideal.span {P}).IsPrime := (Ideal.span_singleton_prime hP.ne_zero).mpr hP
  have hdisj : Disjoint (M : Set (MvPolynomial (Fin n) O)) ↑(Ideal.span {P}) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hCa : (C a : MvPolynomial (Fin n) O) ≠ 0 := by simpa using ha0
    have hdvd : P ∣ C a := Ideal.mem_span_singleton.mp hmem
    have hdeg : P.totalDegree = 0 := by
      have := totalDegree_le_of_dvd_of_isDomain hdvd hCa
      rw [totalDegree_C] at this
      omega
    exact hnc _ (totalDegree_eq_zero_iff_eq_C.mp hdeg)
  have hmap := IsLocalization.isPrime_of_isPrime_disjoint M (MvPolynomial (Fin n) K) _ hprime hdisj
  rw [Ideal.map_span, Set.image_singleton, MvPolynomial.algebraMap_def] at hmap

  have hinj : Function.Injective (map (σ := Fin n) (algebraMap O K)) :=
    map_injective _ (IsFractionRing.injective O K)
  have hne : map (algebraMap O K) P ≠ 0 := by
    intro h
    exact hP.ne_zero (hinj (by rw [h, map_zero]))
  exact (Ideal.span_singleton_prime hne).mp hmap

end GroundTheory.Heights₂.Heights
