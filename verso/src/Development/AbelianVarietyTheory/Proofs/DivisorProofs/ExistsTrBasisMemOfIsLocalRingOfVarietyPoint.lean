import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

/- English proof (translation)
Use `⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (fun p => Polynomial.coeff p 1) h0`. Simplify `h1` using `only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ, sub_zero, Polynomial.coeff_zero, if_true]`. Rewrite using `[map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C, mul_comm, e, sub_self]`.
-/
theorem isAlgebraic_of_mul_eq {S K : Type} [CommRing S] [Field K] [Algebra S K] {f : K} (a b : S)
    (hb : b ≠ 0) (e : f * algebraMap S K b = algebraMap S K a) : IsAlgebraic S f := by
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => Polynomial.coeff p 1) h0
    simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ, sub_zero,
      Polynomial.coeff_zero, if_true] using h1
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C, mul_comm, e,
      sub_self]

/- English proof (translation)
Use `letI := c.toAlgebra`. Take `⟨x, hx⟩` from `hx`. Use `haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (R : Set K)) K := by`. Use `⟨fun f => ?_⟩` and prove the remaining obligations. Take `⟨a, ha, b, hb, hb0, e⟩` from `hR.frac f`.

Conclude with `isAlgebraic_of_mul_eq (⟨a, Algebra.subset_adjoin ha⟩ : Algebra.adjoin ℂ (R : Set K)) ⟨b, Algebra.subset_adjoin hb⟩ (fun h => hb0 (congrArg Subtype.val h)) e`. Take `⟨t, hts, ht⟩` from `exists_isTranscendenceBasis_subset (R := ℂ) (R : Set K)`. Establish `h1` using `IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx`. Establish `h2` using `IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) ht`. Take `⟨e⟩` from `Cardinal.eq.1 (h1.trans h2.symm)`.

Use `⟨fun j => ⟨(e j : K), hts (e j).2⟩, ?_⟩` and prove the remaining obligations. Use `show IsTranscendenceBasis ℂ fun j => ((e j : t) : K)`. Conclude with `(isTranscendenceBasis_equiv e).2 ht`.
-/
theorem exists_trBasis_mem_of_isLocModel {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K)
    (n : ℕ) (hR : IsLocModel c R) (hx : ∃ x : Fin n → K, TrBasis c x) :
    ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) := by
  letI := c.toAlgebra
  obtain ⟨x, hx⟩ := hx
  haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (R : Set K)) K := by
    refine ⟨fun f => ?_⟩
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac f
    exact isAlgebraic_of_mul_eq (⟨a, Algebra.subset_adjoin ha⟩ : Algebra.adjoin ℂ (R : Set K))
      ⟨b, Algebra.subset_adjoin hb⟩ (fun h => hb0 (congrArg Subtype.val h)) e
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (R : Set K)
  have h1 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
  have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) ht
  obtain ⟨e⟩ := Cardinal.eq.1 (h1.trans h2.symm)
  refine ⟨fun j => ⟨(e j : K), hts (e j).2⟩, ?_⟩
  show IsTranscendenceBasis ℂ fun j => ((e j : t) : K)
  exact (isTranscendenceBasis_equiv e).2 ht

end GlobalTheory.FieldPair

/- English proof (translation)
The claim follows from `@GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel`.
-/
example : ∀ {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K) (n : ℕ), IsLocModel c R →
    (∃ x : Fin n → K, TrBasis c x) → ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) :=
  @GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel
