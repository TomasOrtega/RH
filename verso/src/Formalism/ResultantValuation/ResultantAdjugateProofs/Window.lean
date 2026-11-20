import Mathlib
import Formalism.ResultantValuation.WindowValuation

open Finset

noncomputable section

namespace Formalism.ResultantValuation

section Padic

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Simplify `PadicInt.mem_span_pow_iff_le_valuation x hx n` using `[Ideal.mem_span_singleton]`.
-/
private theorem pow_dvd_iff_le_valuation_lemma {x : ℤ_[l]} (hx : x ≠ 0) (n : ℕ) :
    (l : ℤ_[l]) ^ n ∣ x ↔ n ≤ x.valuation := by
  simpa [Ideal.mem_span_singleton] using PadicInt.mem_span_pow_iff_le_valuation x hx n

/- English proof (translation)
Rewrite using `[emultiplicity_eq_coe]`. Use `⟨(pow_dvd_iff_le_valuation_lemma hx _).2 le_rfl, fun h => ?_⟩` and prove the remaining obligations. Establish `h1` using `(pow_dvd_iff_le_valuation_lemma hx _).1 h`. Use linear arithmetic over natural numbers and integers.
-/
lemma emultiplicity_eq_valuation {x : ℤ_[l]} (hx : x ≠ 0) :
    emultiplicity (l : ℤ_[l]) x = (x.valuation : ℕ∞) := by
  rw [emultiplicity_eq_coe]
  refine ⟨(pow_dvd_iff_le_valuation_lemma hx _).2 le_rfl, fun h => ?_⟩
  have h1 := (pow_dvd_iff_le_valuation_lemma hx _).1 h
  omega

/- English proof (translation)
Introduce `h`. Establish `h1` using `(pow_dvd_iff_le_valuation_lemma (one_ne_zero : (1 : ℤ_[l]) ≠ 0) 1).1 (by rwa [pow_one])`. Rewrite `h1` using `[PadicInt.valuation_one]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem not_dvd_one'_lemma_2 : ¬ (l : ℤ_[l]) ∣ 1 := by
  intro h
  have h1 := (pow_dvd_iff_le_valuation_lemma (one_ne_zero : (1 : ℤ_[l]) ≠ 0) 1).1 (by rwa [pow_one])
  rw [PadicInt.valuation_one] at h1
  omega

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Introduce `h`. Conclude with `not_dvd_one'_lemma_2 (isUnit_iff_dvd_one.mp h)`. Introduce `a b hab`.

Distinguish the cases in `ha : a = 0`. Use `left`. Rewrite using `[ha]`. Conclude with `dvd_zero _`. Distinguish the cases in `hb : b = 0`.

Use `right`. Rewrite using `[hb]`. Conclude with `dvd_zero _`. Establish `h1` using `(pow_dvd_iff_le_valuation_lemma (mul_ne_zero ha hb) 1).1 (by rwa [pow_one])`. Rewrite `h1` using `[PadicInt.valuation_mul ha hb]`.

Break down `Nat.eq_zero_or_pos a.valuation with h0 | h0` into its components or cases. Use `right`. Establish `h2` using `(pow_dvd_iff_le_valuation_lemma hb 1).2 (by omega)`. Rewrite `h2` using `[pow_one]`. Then use the resulting hypothesis. Use `left`.

Establish `h2` using `(pow_dvd_iff_le_valuation_lemma ha 1).2 (by omega)`. Rewrite `h2` using `[pow_one]`. Then use the resulting hypothesis.
-/
private theorem prime_l_lemma_3 : Prime (l : ℤ_[l]) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  · intro h
    exact not_dvd_one'_lemma_2 (isUnit_iff_dvd_one.mp h)
  · intro a b hab
    by_cases ha : a = 0
    · left; rw [ha]; exact dvd_zero _
    by_cases hb : b = 0
    · right; rw [hb]; exact dvd_zero _
    have h1 := (pow_dvd_iff_le_valuation_lemma (mul_ne_zero ha hb) 1).1 (by rwa [pow_one])
    rw [PadicInt.valuation_mul ha hb] at h1
    rcases Nat.eq_zero_or_pos a.valuation with h0 | h0
    · right
      have h2 := (pow_dvd_iff_le_valuation_lemma hb 1).2 (by omega)
      rwa [pow_one] at h2
    · left
      have h2 := (pow_dvd_iff_le_valuation_lemma ha 1).2 (by omega)
      rwa [pow_one] at h2

end Padic

/- English proof (translation)
Establish `hp : l.Prime` using `Fact.out`. Establish `hprime` using `prime_l_lemma_3 (l := l)`. Establish `hu0 : u - 1 ≠ 0`. Introduce `h`. Rewrite `hu` using `[h, PadicInt.valuation_zero]`.

Use linear arithmetic over natural numbers and integers. Establish `hdvd : (l : ℤ_[l]) ∣ u - 1`. Establish `h1` using `(pow_dvd_iff_le_valuation_lemma hu0 1).2 (by omega)`. Rewrite `h1` using `[pow_one]`. Then use the resulting hypothesis. Establish `hndvd : ¬ (l : ℤ_[l]) ∣ u`.

Introduce `h`. Apply `not_dvd_one'_lemma_2 (l := l)` to reduce the goal to its premises. Establish `h1` using `dvd_sub h hdvd`. Rewrite `h1` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Take `⟨a, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hp.one_lt.ne'`.

Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (dvd_zero l)`. Establish `hv : padicValNat l (l ^ a * m) = a`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]`.

Establish `h1` using `emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime (hp.odd_of_ne_two hl2) hdvd hndvd a`. Rewrite `h1` using `[one_pow]`. Establish `hdvd2 : (l : ℤ_[l]) ∣ u ^ l ^ a - 1`. Use `hdvd.trans ?_` and prove the remaining obligations. Simplify using `using sub_dvd_pow_sub_pow u 1 (l ^ a)`.

Establish `hndvd2 : ¬ (l : ℤ_[l]) ∣ u ^ l ^ a` using `fun h => hndvd (hprime.dvd_of_dvd_pow h)`. Establish `hm' : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l])`. Introduce `h`. Establish `hc : Nat.Coprime m l` using `((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm`. Take `⟨s, t, hst⟩` from `Nat.isCoprime_iff_coprime.2 hc`.

Establish `hst' : (s : ℤ_[l]) * (m : ℤ_[l]) + (t : ℤ_[l]) * (l : ℤ_[l]) = 1`. Establish `h3` using `congrArg (Int.cast : ℤ → ℤ_[l]) hst`. Move the coercions through the operations in `at h3`. Conclude with `h3`. Apply `not_dvd_one'_lemma_2 (l := l)` to reduce the goal to its premises.

Rewrite using `[← hst']`. Conclude with `dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)`. Establish `h2` using `emultiplicity_pow_sub_pow_of_prime hprime hdvd2 hndvd2 hm'`. Rewrite `h2` using `[one_pow, ← pow_mul]`. Establish `hE : emultiplicity (l : ℤ_[l]) (u ^ (l ^ a * m) - 1) = ((1 + a : ℕ) : ℕ∞)`.

Rewrite using `[h2, h1, emultiplicity_eq_valuation hu0, hu]`. Use `norm_cast`. Establish `hne : u ^ (l ^ a * m) - 1 ≠ 0`. Introduce `h`. Rewrite `hE` using `[h, emultiplicity_zero]`.

Conclude with `(ENat.natCast_ne_top (1 + a)) hE.symm`. Rewrite using `[hv]`. Conclude with `(emultiplicity_eq_valuation hne).symm.trans hE` after adjusting the coercions.
-/
lemma lte_unit (l : ℕ) [Fact l.Prime] (hl2 : l ≠ 2) (u : ℤ_[l]) (hu : (u - 1).valuation = 1)
    (i : ℕ) (hi : 1 ≤ i) : ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i := by
  classical
  have hp : l.Prime := Fact.out
  have hprime := prime_l_lemma_3 (l := l)
  have hu0 : u - 1 ≠ 0 := by
    intro h
    rw [h, PadicInt.valuation_zero] at hu
    omega
  have hdvd : (l : ℤ_[l]) ∣ u - 1 := by
    have h1 := (pow_dvd_iff_le_valuation_lemma hu0 1).2 (by omega)
    rwa [pow_one] at h1
  have hndvd : ¬ (l : ℤ_[l]) ∣ u := by
    intro h
    apply not_dvd_one'_lemma_2 (l := l)
    have h1 := dvd_sub h hdvd
    rwa [sub_sub_cancel] at h1
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero l)
  have hv : padicValNat l (l ^ a * m) = a := by
    rw [padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have h1 := emultiplicity_pow_prime_pow_sub_pow_prime_pow hprime (hp.odd_of_ne_two hl2) hdvd hndvd a
  rw [one_pow] at h1
  have hdvd2 : (l : ℤ_[l]) ∣ u ^ l ^ a - 1 := by
    refine hdvd.trans ?_
    simpa using sub_dvd_pow_sub_pow u 1 (l ^ a)
  have hndvd2 : ¬ (l : ℤ_[l]) ∣ u ^ l ^ a := fun h => hndvd (hprime.dvd_of_dvd_pow h)
  have hm' : ¬ (l : ℤ_[l]) ∣ (m : ℤ_[l]) := by
    intro h
    have hc : Nat.Coprime m l := ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
    obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 hc
    have hst' : (s : ℤ_[l]) * (m : ℤ_[l]) + (t : ℤ_[l]) * (l : ℤ_[l]) = 1 := by
      have h3 := congrArg (Int.cast : ℤ → ℤ_[l]) hst
      push_cast at h3
      exact h3
    apply not_dvd_one'_lemma_2 (l := l)
    rw [← hst']
    exact dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)
  have h2 := emultiplicity_pow_sub_pow_of_prime hprime hdvd2 hndvd2 hm'
  rw [one_pow, ← pow_mul] at h2
  have hE : emultiplicity (l : ℤ_[l]) (u ^ (l ^ a * m) - 1) = ((1 + a : ℕ) : ℕ∞) := by
    rw [h2, h1, emultiplicity_eq_valuation hu0, hu]
    norm_cast
  have hne : u ^ (l ^ a * m) - 1 ≠ 0 := by
    intro h
    rw [h, emultiplicity_zero] at hE
    exact (ENat.natCast_ne_top (1 + a)) hE.symm
  rw [hv]
  exact_mod_cast (emultiplicity_eq_valuation hne).symm.trans hE

/- English proof (translation)
Introduce `l _ hl2 u hu i hi`. Conclude with `lte_unit l hl2 u hu i hi`.
-/
theorem powSubOneValuation : LTEUnit := by
  intro l _ hl2 u hu i hi
  exact lte_unit l hl2 u hu i hi

end Formalism.ResultantValuation
