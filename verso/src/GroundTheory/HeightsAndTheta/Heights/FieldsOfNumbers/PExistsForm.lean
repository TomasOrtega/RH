import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod (R := R) Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ n k) (fun k => n k • blockWeight ι ⟨k, i k⟩) (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)`. Establish `hs : (∑ k, n k • blockWeight ι ⟨k, i k⟩) = n`. Use function extensionality and compare the values at `j`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Rewrite `h` using `[hs]`.

Conclude with `h`.
-/
theorem isMultiHomog_prod_pow {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*}
    [CommRing R] (i : ∀ k, ι k) (n : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) n := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ
    (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ n k) (fun k => n k • blockWeight ι ⟨k, i k⟩)
    (w := blockWeight ι) (fun k _ => (isWeightedHomogeneous_X R _ _).pow _)
  have hs : (∑ k, n k • blockWeight ι ⟨k, i k⟩) = n := by
    funext j
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [hs] at h
  exact h

/- English proof (translation)
Introduce `h`. Take `⟨k, -, hk⟩` from `Ideal.IsPrime.prod_mem_iff.mp h`. Conclude with `hi k (hP.mem_of_pow_mem _ hk)`.
-/
theorem prod_pow_not_mem {K : Type} [Fintype K] {ι : K → Type} {R : Type*} [CommRing R]
    (P : Ideal (MRing ι R)) [hP : P.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι R) ∉ P) (n : K → ℕ) :
    (∏ k, (X ⟨k, i k⟩ : MRing ι R) ^ n k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hi k (hP.mem_of_pow_mem _ hk)

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP b`. Use `hP.isPrime` as an intermediate fact. Use `choose i hi using hP.relevant`. Use `⟨fun k => (b k).toNat, fun k => (-b k).toNat, ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (b k).toNat, ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (-b k).toNat, isMultiHomog_prod_pow i _, isMultiHomog_prod_pow i _, prod_pow_not_mem P i hi _, prod_pow_not_mem P i hi _, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`.

Simplify using `only`. Use linear arithmetic over natural numbers and integers.
-/
theorem ExistsForm.proof : ExistsForm.Statement := by
  intro F _ K _ _ ι _ P hP b
  have := hP.isPrime
  choose i hi using hP.relevant
  refine ⟨fun k => (b k).toNat, fun k => (-b k).toNat,
    ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (b k).toNat, ∏ k, (X ⟨k, i k⟩ : MRing ι F) ^ (-b k).toNat,
    isMultiHomog_prod_pow i _, isMultiHomog_prod_pow i _, prod_pow_not_mem P i hi _,
    prod_pow_not_mem P i hi _, ?_⟩
  funext k
  simp only
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
