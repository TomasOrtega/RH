import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
open GlobalTheory.FieldPair

namespace GlobalTheory.FieldPair

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities.
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
Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
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
A detailed English derivation is pending.
-/
example : ∀ {K : Type} [Field K] (c : ℂ →+* K) (R : Subring K) (n : ℕ), IsLocModel c R →
    (∃ x : Fin n → K, TrBasis c x) → ∃ xi : Fin n → R, TrBasis c (fun j => (xi j : K)) :=
  @GlobalTheory.FieldPair.exists_trBasis_mem_of_isLocModel
