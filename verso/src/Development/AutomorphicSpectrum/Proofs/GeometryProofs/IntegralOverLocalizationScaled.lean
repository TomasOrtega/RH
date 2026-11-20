import Mathlib

namespace GlobalTheory.CompanionTheory.Ggeo.ClearDenominators

open Polynomial

/- English proof (translation)
Use `revert hs`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Use `⟨1, one_mem A, one_ne_zero, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_one]`.

Conclude with `one_mem R`. Introduce `x hx`. Simplify using `at hx`. Introduce `a t _ ih hs`. Take `⟨w, hwA, hw0, hwR, hw⟩` from `ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))`.

Take `⟨u, huA, v, hvA, hv0, hvR, hav⟩` from `hfrac a (hs a (Finset.mem_insert_self a t))`. Use `⟨w * v, mul_mem hwA hvA, mul_ne_zero hw0 hv0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv]`. Conclude with `mul_mem hwR hvR`. Introduce `x hx`.

Break down `Finset.mem_insert.mp hx with hxa | hxt` into its components or cases. Establish `key : w * v * x = w * u`. Rewrite using `[hxa, hav, div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key]`.

Conclude with `mul_mem hwA huA`. Establish `key : w * v * x = v * (w * x)` using `by ring`. Rewrite using `[key]`. Conclude with `mul_mem hvA (hw x hxt)`.
-/
theorem exists_common_denominator {o K : Type} [CommRing o] [Field K] [Algebra o K]
    (A : Subalgebra o K) (R : Subring K)
    (hfrac : ∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v)
    (s : Finset K) (hs : ∀ x ∈ s, x ∈ R) :
    ∃ w ∈ A, w ≠ 0 ∧ w⁻¹ ∈ R ∧ ∀ x ∈ s, w * x ∈ A := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    refine ⟨1, one_mem A, one_ne_zero, ?_, ?_⟩
    · rw [inv_one]
      exact one_mem R
    · intro x hx
      simp at hx
  · intro a t _ ih hs
    obtain ⟨w, hwA, hw0, hwR, hw⟩ :=
      ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨u, huA, v, hvA, hv0, hvR, hav⟩ := hfrac a (hs a (Finset.mem_insert_self a t))
    refine ⟨w * v, mul_mem hwA hvA, mul_ne_zero hw0 hv0, ?_, ?_⟩
    · rw [mul_inv]
      exact mul_mem hwR hvR
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxt
      · have key : w * v * x = w * u := by
          rw [hxa, hav, div_eq_mul_inv]
          calc w * v * (u * v⁻¹) = w * u * (v * v⁻¹) := by ring
            _ = w * u := by rw [mul_inv_cancel₀ hv0, mul_one]
        rw [key]
        exact mul_mem hwA huA
      · have key : w * v * x = v * (w * x) := by ring
        rw [key]
        exact mul_mem hvA (hw x hxt)

/- English proof (translation)
Introduce `o K _ _ _ A R _ hfrac t ht`. Take `⟨p, hpm, hp⟩` from `ht`. Establish `hPm : (p.map (algebraMap R K)).Monic` using `hpm.map (algebraMap R K)`. Establish `hP : (p.map (algebraMap R K)).eval₂ (RingHom.id K) t = 0`. Rewrite using `[Polynomial.eval₂_map, RingHom.id_comp]`.

Conclude with `hp`. Establish `hPR : ∀ i, (p.map (algebraMap R K)).coeff i ∈ R`. Introduce `i`. Rewrite using `[Polynomial.coeff_map]`. Conclude with `(p.coeff i).2`.

Generalize the expression as in `p.map (algebraMap R K) = P at hPm hP hPR`. Take `⟨w, hwA, hw0, hwR, hw⟩` from `exists_common_denominator A R hfrac ((Finset.range (P.natDegree + 1)).image P.coeff) (by`. Introduce `x hx`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hx`. Conclude with `hPR i)`.

Use `⟨w, hwA, hw0, hwR, ?_⟩` and prove the remaining obligations. Establish `hcoef : ∀ i, P.coeff i * w ^ (P.natDegree - i) ∈ A`. Introduce `i`. Break down `lt_trichotomy i P.natDegree with hi | hi | hi` into its components or cases. Take `⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1` from `⟨P.natDegree - i - 1, by omega⟩`.

Establish `h1 : P.coeff i * w ^ (P.natDegree - i) = w ^ k * (w * P.coeff i)`. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Conclude with `mul_mem (pow_mem hwA k) (hw _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))`.

Rewrite using `[hi, Nat.sub_self, pow_zero, mul_one, hPm.coeff_natDegree]`. Conclude with `one_mem A`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]`. Conclude with `zero_mem A`. Establish `hQm : (P.scaleRoots w).Monic`.

Rewrite using `[Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots_natDegree]`. Conclude with `hPm`. Establish `hlift : P.scaleRoots w ∈ Polynomial.lifts (algebraMap A K)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `i`.

Rewrite using `[Polynomial.coeff_scaleRoots]`. Conclude with `⟨⟨_, hcoef i⟩, rfl⟩`. Take `⟨q, hqmap, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hlift hQm`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_eq_eval_map, hqmap]`.

Conclude with `Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id K) hP`.
-/
theorem exists_mul_isIntegral :
    ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K),
      (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) →
      ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  intro o K _ _ _ A R _ hfrac t ht
  classical
  obtain ⟨p, hpm, hp⟩ := ht
  have hPm : (p.map (algebraMap R K)).Monic := hpm.map (algebraMap R K)
  have hP : (p.map (algebraMap R K)).eval₂ (RingHom.id K) t = 0 := by
    rw [Polynomial.eval₂_map, RingHom.id_comp]
    exact hp
  have hPR : ∀ i, (p.map (algebraMap R K)).coeff i ∈ R := by
    intro i
    rw [Polynomial.coeff_map]
    exact (p.coeff i).2
  generalize p.map (algebraMap R K) = P at hPm hP hPR
  obtain ⟨w, hwA, hw0, hwR, hw⟩ := exists_common_denominator A R hfrac
    ((Finset.range (P.natDegree + 1)).image P.coeff) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hPR i)
  refine ⟨w, hwA, hw0, hwR, ?_⟩
  have hcoef : ∀ i, P.coeff i * w ^ (P.natDegree - i) ∈ A := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      have h1 : P.coeff i * w ^ (P.natDegree - i) = w ^ k * (w * P.coeff i) := by
        rw [hk]
        ring
      rw [h1]
      exact mul_mem (pow_mem hwA k)
        (hw _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))
    · rw [hi, Nat.sub_self, pow_zero, mul_one, hPm.coeff_natDegree]
      exact one_mem A
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact zero_mem A
  have hQm : (P.scaleRoots w).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots,
      Polynomial.coeff_scaleRoots_natDegree]
    exact hPm
  have hlift : P.scaleRoots w ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    exact ⟨⟨_, hcoef i⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hQm
  refine ⟨q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hqmap]
  exact Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id K) hP

end GlobalTheory.CompanionTheory.Ggeo.ClearDenominators
