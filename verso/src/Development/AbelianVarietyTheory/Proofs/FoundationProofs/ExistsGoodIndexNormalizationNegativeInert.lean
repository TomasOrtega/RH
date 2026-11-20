import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators Pointwise

namespace GlobalTheory.FinWeil

noncomputable def ofPrimeValues (u : ℕ → ℂ) : ℕ →* ℂ where
  toFun n := if n = 0 then 0 else n.factorization.prod fun q k => u q ^ k
  map_one' := by simp
  map_mul' a b := by
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Nat.factorization_mul ha hb,
      Finsupp.prod_add_index' (by simp) (fun q k l => pow_add _ _ _)]

/- English proof (translation)
Use `show (if q = 0 then 0 else q.factorization.prod fun q k => u q ^ k) = u q`. Rewrite using `[if_neg hq.ne_zero, hq.factorization, Finsupp.prod_single_index (by simp), pow_one]`.
-/
theorem ofPrimeValues_prime (u : ℕ → ℂ) {q : ℕ} (hq : q.Prime) : ofPrimeValues u q = u q := by
  show (if q = 0 then 0 else q.factorization.prod fun q k => u q ^ k) = u q
  rw [if_neg hq.ne_zero, hq.factorization, Finsupp.prod_single_index (by simp), pow_one]

/- English proof (translation)
Proceed by induction on `f with`. Consider the case `zero => simp`. Consider the case `succ f ih`. Rewrite using `[pow_succ, ih, pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]`.
-/
theorem sqrt_pow_nat (q f : ℕ) : ((Real.sqrt q : ℝ) : ℂ) ^ f = (Real.sqrt ((q ^ f : ℕ) : ℝ) : ℂ) := by
  induction f with
  | zero => simp
  | succ f ih =>
    rw [pow_succ, ih, pow_succ, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

/- English proof (translation)
Set `u : ℕ → ℂ` to `fun q => (Real.sqrt q : ℂ) * if S q then Complex.exp (Real.pi * Complex.I / f q) else 1`. Use `⟨ofPrimeValues u, fun n => ?_, fun q hq hf hS => ?_, fun n => ?_⟩` and prove the remaining obligations. Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => simp`. Consider the case `one => simp`.

Consider the case `prime q hq`. Introduce `_`. Rewrite using `[ofPrimeValues_prime u hq]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Conclude with `(Real.sqrt_pos.2 (by exact_mod_cast hq.pos)).ne'` after adjusting the coercions.

Use `split_ifs`. Conclude with `Complex.exp_ne_zero _`. Conclude with `one_ne_zero`. Consider the case `mul a b ha hb`. Introduce `h`.

Rewrite using `[map_mul]`. Conclude with `mul_ne_zero (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))`. Rewrite using `[map_pow, ofPrimeValues_prime u hq]`. Simplify using `only [u, if_pos hS]`. Establish `hf' : (f q : ℂ) ≠ 0` using `by exact_mod_cast hf`.

Rewrite using `[mul_pow, sqrt_pow_nat, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hf', Complex.exp_pi_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Proceed by induction on `n using Nat.recOnMul with`. Consider the case `zero => simp`. Consider the case `one => simp`.

Consider the case `prime q hq`. Introduce `_ h`. Establish `hS : ¬ S q` using `fun hS => h q hq hS dvd_rfl`. Rewrite using `[ofPrimeValues_prime u hq]`. Simplify using `only [u, if_neg hS, mul_one]`.

Consider the case `mul a b ha hb`. Introduce `h h'`. Rewrite using `[map_mul, ha (left_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_right _), hb (right_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_left _), Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]`.
-/
theorem exists_lam (S : ℕ → Prop) (f : ℕ → ℕ) :
    ∃ lam : ℕ →* ℂ, (∀ n, n ≠ 0 → lam n ≠ 0) ∧
      (∀ q, q.Prime → f q ≠ 0 → S q → lam (q ^ f q) = -(Real.sqrt ((q ^ f q : ℕ) : ℝ) : ℂ)) ∧
      ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → S q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  let u : ℕ → ℂ := fun q =>
    (Real.sqrt q : ℂ) * if S q then Complex.exp (Real.pi * Complex.I / f q) else 1
  refine ⟨ofPrimeValues u, fun n => ?_, fun q hq hf hS => ?_, fun n => ?_⟩
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _
      rw [ofPrimeValues_prime u hq]
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast hq.pos)).ne'
      · split_ifs
        · exact Complex.exp_ne_zero _
        · exact one_ne_zero
    | mul a b ha hb =>
      intro h
      rw [map_mul]
      exact mul_ne_zero (ha (left_ne_zero_of_mul h)) (hb (right_ne_zero_of_mul h))
  · rw [map_pow, ofPrimeValues_prime u hq]
    simp only [u, if_pos hS]
    have hf' : (f q : ℂ) ≠ 0 := by exact_mod_cast hf
    rw [mul_pow, sqrt_pow_nat, ← Complex.exp_nat_mul, mul_div_cancel₀ _ hf', Complex.exp_pi_mul_I]
    ring
  · induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime q hq =>
      intro _ h
      have hS : ¬ S q := fun hS => h q hq hS dvd_rfl
      rw [ofPrimeValues_prime u hq]
      simp only [u, if_neg hS, mul_one]
    | mul a b ha hb =>
      intro h h'
      rw [map_mul, ha (left_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_right _),
        hb (right_ne_zero_of_mul h) fun q hq hS hd => h' q hq hS (hd.mul_left _), Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]

/- English proof (translation)
Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)`. Take `⟨p, hp, hPp⟩` from `(Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ P)).resolve_left (Ideal.under_ne_bot ℤ hP0)`. Establish `hlo : P.LiesOver (Ideal.span {(p : ℤ)})` using `⟨hPp.symm⟩`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible`. Establish `h1` using `Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P (E ≃ₐ[ℚ] E)`.

Use `⟨p, hp, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: (p : ℤ) ∈ P.under ℤ` using `hPp ▸ Ideal.mem_span_singleton_self _`. Simplify `this` using `[Ideal.under, Ideal.mem_comap]`. Rewrite using `[h1]`. Conclude with `(Ideal.inertiaDeg_pos P ℤ).ne'`.

Rewrite using `[h1, Ideal.pow_inertiaDeg p P, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem exists_card_eq_pow {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) : ∃ q : ℕ, q.Prime ∧ (q : 𝓞 E) ∈ P ∧
      (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) ≠ 0 ∧
      Nat.card (𝓞 E ⧸ P) = q ^ (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 E) := by
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨p, hp, hPp⟩ :=
    (Ideal.isPrime_int_iff.mp (Ideal.IsPrime.under ℤ P)).resolve_left (Ideal.under_ne_bot ℤ hP0)
  have hlo : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPp.symm⟩
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
  have h1 := Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P (E ≃ₐ[ℚ] E)
  refine ⟨p, hp, ?_, ?_, ?_⟩
  · have : (p : ℤ) ∈ P.under ℤ := hPp ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.under, Ideal.mem_comap] using this
  · rw [h1]; exact (Ideal.inertiaDeg_pos P ℤ).ne'
  · rw [h1, Ideal.pow_inertiaDeg p P, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Introduce `D`. Establish `: IsGalois ℚ D.host.E` using `D.host.hostE_isGalois`. Establish `hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ` using `fun σ τ => D.host.galE_injective (by`. Rewrite using `[D.host.galE_mul, D.host.galE_mul, mul_comm])`. Take `⟨lam, h0, h1, h2⟩` from `exists_lam (InertQ D) fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 D.host.E)`.

Use `⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩` and prove the remaining obligations. Establish `hP0 : P ≠ ⊥` using `Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)`. Take `⟨q, hq, hqP, hf, hc⟩` from `exists_card_eq_pow P hP`. Establish `hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n` using `fun n => by`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]`.

Use `⟨?_, fun h => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hc]`. Distinguish the cases in `hI : InertQ D q`. Rewrite using `[h1 q hq hf hI, neg_sq, hsq]`. Rewrite using `[h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]`.

Establish `hfix : D.host.conj • P = P`. Establish `hP' : (D.host.conj • P).IsMaximal`. Break down `Ideal.map_eq_top_or_isMaximal_of_surjective (sgO D) (MulAction.surjective D.host.conj) hP with h | h` into its components or cases. Conclude with `absurd h (Ideal.IsPrime.smul (H := hP.isPrime) D.host.conj).ne_top`. Conclude with `h`.

Conclude with `hP'.eq_of_le hP.ne_top (Ideal.map_le_iff_le_comap.2 fun r hr => h r hr)`. Establish `hI : InertQ D q` using `fun Q hQ _ hqQ => GlobalTheory.SelectIdem.smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ hqP hqQ hfix`. Rewrite using `[hc]`. Conclude with `h1 q hq hf hI`. Use `D.host.der.unramEF P hP.isPrime hP0 push Not at this` as an intermediate fact.

Conclude with `this`.
-/
theorem exists_goodNorm : ∀ D : D7, ∃ lam : ℕ →* ℂ, GoodNorm (sgO D) lam ∧ ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → InertQ D q → ¬ q ∣ n) → lam n = (Real.sqrt n : ℂ) := by
  intro D
  have : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hcomm : ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, σ * τ = τ * σ := fun σ τ =>
    D.host.galE_injective (by
      rw [D.host.galE_mul,
        D.host.galE_mul, mul_comm])
  obtain ⟨lam, h0, h1, h2⟩ := exists_lam (InertQ D)
    fun q => (Ideal.span {(q : ℤ)}).inertiaDegIn (𝓞 D.host.E)
  refine ⟨lam, ⟨h0, fun P hP _ => ?_⟩, h2⟩
  have hP0 : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField _)
  obtain ⟨q, hq, hqP, hf, hc⟩ := exists_card_eq_pow P hP
  have hsq : ∀ n : ℕ, ((Real.sqrt n : ℝ) : ℂ) ^ 2 = n := fun n => by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  refine ⟨?_, fun h => ⟨?_, ?_⟩⟩
  · rw [hc]
    by_cases hI : InertQ D q
    · rw [h1 q hq hf hI, neg_sq, hsq]
    · rw [h2 _ (pow_ne_zero _ hq.ne_zero) fun p hp hIp hd => hI
        ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hd) ▸ hIp), hsq]
  · have hfix : D.host.conj • P = P := by
      have hP' : (D.host.conj • P).IsMaximal := by
        rcases Ideal.map_eq_top_or_isMaximal_of_surjective (sgO D)
          (MulAction.surjective D.host.conj) hP with h | h
        · exact absurd h (Ideal.IsPrime.smul (H := hP.isPrime) D.host.conj).ne_top
        · exact h
      exact hP'.eq_of_le hP.ne_top (Ideal.map_le_iff_le_comap.2 fun r hr => h r hr)
    have hI : InertQ D q := fun Q hQ _ hqQ =>
      GlobalTheory.SelectIdem.smul_eq_of_abelian hcomm _ hq P Q hP.isPrime hQ hqP hqQ hfix
    rw [hc]
    exact h1 q hq hf hI
  · have := D.host.der.unramEF P hP.isPrime hP0
    push Not at this
    exact this

end GlobalTheory.FinWeil
