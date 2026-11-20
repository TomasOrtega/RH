import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

/- English proof (translation)
Establish `hV : IsIntegral V y` using `hy.tower_top`. Take `⟨z, hz⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hV`. Rewrite using `[← hz]`. Conclude with `z.2`.
-/
theorem isIntegral_int_mem_every_valuationSubring {F : Type} [Field F] (V : ValuationSubring F)
    {y : F} (hy : IsIntegral ℤ y) : y ∈ V := by
  have hV : IsIntegral V y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hV
  rw [← hz]
  exact z.2

/- English proof (translation)
Take `⟨a, b, hab⟩` from `hn`. Establish `hint : ∀ m : ℤ, V.valuation (m : F) ≤ 1` using `fun m => (V.valuation_le_one_iff _).2 (by simp)`. Establish `hq' : V.valuation ((q : ℕ) : F) < 1` using `V.mem_nonunits_iff.1 hq`. Use `le_antisymm (hint n) (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `hsum : ((a : F) * n + (b : F) * ((q : ℕ) : F)) = 1`.

Use `congrArg (fun t : ℤ => (t : F)) hab` as an intermediate fact. Simplify using `using this`. Establish `h1 : V.valuation ((a : F) * n) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hlt`.

Establish `h2 : V.valuation ((b : F) * ((q : ℕ) : F)) < 1`. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hq'`. Establish `h3` using `Valuation.map_add_lt _ h1 h2`. Rewrite `h3` using `[hsum, map_one]`.

Conclude with `lt_irrefl _ h3`.
-/
theorem valuationSubring_valuation_intCast_coprime_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    {q : ℕ} (hq : ((q : ℕ) : F) ∈ V.nonunits) {n : ℤ} (hn : IsCoprime n (q : ℤ)) :
    V.valuation (n : F) = 1 := by
  obtain ⟨a, b, hab⟩ := hn
  have hint : ∀ m : ℤ, V.valuation (m : F) ≤ 1 := fun m =>
    (V.valuation_le_one_iff _).2 (by simp)
  have hq' : V.valuation ((q : ℕ) : F) < 1 := V.mem_nonunits_iff.1 hq
  refine le_antisymm (hint n) (not_lt.1 fun hlt => ?_)
  have hsum : ((a : F) * n + (b : F) * ((q : ℕ) : F)) = 1 := by
    have := congrArg (fun t : ℤ => (t : F)) hab
    simpa using this
  have h1 : V.valuation ((a : F) * n) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hlt
  have h2 : V.valuation ((b : F) * ((q : ℕ) : F)) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) hq'
  have h3 := Valuation.map_add_lt _ h1 h2
  rw [hsum, map_one] at h3
  exact lt_irrefl _ h3

/- English proof (translation)
Introduce `F _ _ _ s`. Establish `: Algebra.IsAlgebraic ℤ F` using `⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)⟩`. Take `⟨d, hd0, hd⟩` from `Algebra.IsAlgebraic.exists_integral_multiples ℤ s`. Use `⟨d.natAbs.primeFactors, fun q hq hqS V hqV x hx => ?_⟩` and prove the remaining obligations. Establish `hndvd : ¬ q ∣ d.natAbs` using `fun h => hqS (Nat.mem_primeFactors.2 ⟨hq, h, Int.natAbs_ne_zero.2 hd0⟩)`.

Establish `hcop : IsCoprime d (q : ℤ)`. Rewrite using `[Int.isCoprime_iff_gcd_eq_one]`. Use `(Nat.Prime.coprime_iff_not_dvd hq).2 hndvd` as an intermediate fact. Simplify `this` using `[Int.gcd, Nat.Coprime, Nat.gcd_comm]`. Establish `hdx : (d : F) * x ∈ V`.

Use `isIntegral_int_mem_every_valuationSubring V (hd x hx)` as an intermediate fact. Simplify `this` using `[zsmul_eq_mul]`. Establish `hv1` using `valuationSubring_valuation_intCast_coprime_eq_one V hqV hcop`. Rewrite using `[← V.valuation_le_one_iff]`. Use `(V.valuation_le_one_iff _).2 hdx` as an intermediate fact.

Rewrite `this` using `[map_mul, hv1, one_mul]`. Then use the resulting hypothesis.
-/
theorem exists_finset_primes_forall_mem_valuationSubring :
    ∀ {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F] (s : Finset F),
      ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F,
        ((q : ℕ) : F) ∈ V.nonunits → ∀ x ∈ s, x ∈ V := by
  intro F _ _ _ s
  have : Algebra.IsAlgebraic ℤ F :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ F).2 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  obtain ⟨d, hd0, hd⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  refine ⟨d.natAbs.primeFactors, fun q hq hqS V hqV x hx => ?_⟩
  have hndvd : ¬ q ∣ d.natAbs := fun h =>
    hqS (Nat.mem_primeFactors.2 ⟨hq, h, Int.natAbs_ne_zero.2 hd0⟩)
  have hcop : IsCoprime d (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := (Nat.Prime.coprime_iff_not_dvd hq).2 hndvd
    simpa [Int.gcd, Nat.Coprime, Nat.gcd_comm] using this
  have hdx : (d : F) * x ∈ V := by
    have := isIntegral_int_mem_every_valuationSubring V (hd x hx)
    simpa [zsmul_eq_mul] using this
  have hv1 := valuationSubring_valuation_intCast_coprime_eq_one V hqV hcop
  rw [← V.valuation_le_one_iff]
  have := (V.valuation_le_one_iff _).2 hdx
  rwa [map_mul, hv1, one_mul] at this

end GlobalTheory
