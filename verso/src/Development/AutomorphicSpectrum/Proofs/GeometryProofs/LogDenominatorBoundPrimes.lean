import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver

open GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ClearConstants

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, W.one_mem, by simp⟩`. Consider the case `insert a s ha ih`. Take `⟨w, hw, hs⟩` from `ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ))`. Take `⟨u, hu, hau⟩` from `h a (Finset.mem_insert_self a s)`.

Use `⟨u * w, mul_mem hu hw, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hs, hau]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem prod_one_sub_lemma {Ω : Type} [Field Ω] (W : ValuationSubring Ω) (π : Ω)
    (s : Finset Ω) (h : ∀ μ ∈ s, ∃ u ∈ W, 1 - μ = π * u) :
    ∃ w ∈ W, ∏ μ ∈ s, (1 - μ) = w * π ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, W.one_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, hs⟩ := ih (fun μ hμ => h μ (Finset.mem_insert_of_mem hμ))
    obtain ⟨u, hu, hau⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨u * w, mul_mem hu hw, ?_⟩
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, hs, hau]
    ring

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hpow : ζ ^ p = 1` using `hζ.pow_eq_one`. Establish `hζW : ζ ∈ W`. Break down `W.mem_or_inv_mem ζ with h | h` into its components or cases. Conclude with `h`.

Establish `hne : ζ ≠ 0` using `hζ.ne_zero hp.ne_zero`. Establish `h1 : (ζ⁻¹) ^ (p - 1) * ζ⁻¹ = 1`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hp.one_le, inv_pow, hpow, inv_one]`. Establish `key : (ζ⁻¹) ^ (p - 1) = ζ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, inv_mul_cancel₀ hne, mul_one]`. Use `_ = ζ := by rw [h1, one_mul]`. Rewrite using `[← key]`. Conclude with `pow_mem h _`. Establish `hprod : (p : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ)`.

Establish `h0` using `Polynomial.eval_one_cyclotomic_prime (R := Ω) (p := p)`. Rewrite `h0` using `[Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]`. Simplify using `using h0.symm`. Establish `hcard : (primitiveRoots p Ω).card = p - 1`. Rewrite using `[hζ.card_primitiveRoots, Nat.totient_prime hp]`.

Establish `hall : ∀ μ ∈ primitiveRoots p Ω, ∃ u ∈ W, 1 - μ = (ζ - 1) * u`. Introduce `μ hμ`. Establish `hμp : IsPrimitiveRoot μ p` using `(mem_primitiveRoots hp.pos).mp hμ`. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one hμp.pow_eq_one`. Use `⟨-(∑ j ∈ Finset.range i, ζ ^ j), neg_mem (sum_mem fun j _ => pow_mem hζW j), ?_⟩` and prove the remaining obligations.

Rewrite using `[← hi]`. Take the linear combination `geom_sum_mul ζ i`. Take `⟨w, hw, hw'⟩` from `prod_one_sub_lemma W (ζ - 1) _ hall`. Rewrite `hw'` using `[hcard]`. Conclude with `⟨w, hw, hprod.trans hw'⟩`.
-/
theorem prime_eq_mul_pow {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p : ℕ} (hp : p.Prime) {ζ : Ω}
    (hζ : IsPrimitiveRoot ζ p) : ∃ w ∈ W, (p : Ω) = w * (ζ - 1) ^ (p - 1) := by
  haveI := Fact.mk hp
  have hpow : ζ ^ p = 1 := hζ.pow_eq_one
  have hζW : ζ ∈ W := by
    rcases W.mem_or_inv_mem ζ with h | h
    · exact h
    · have hne : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
      have h1 : (ζ⁻¹) ^ (p - 1) * ζ⁻¹ = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hp.one_le, inv_pow, hpow, inv_one]
      have key : (ζ⁻¹) ^ (p - 1) = ζ := by
        calc (ζ⁻¹) ^ (p - 1) = (ζ⁻¹) ^ (p - 1) * ζ⁻¹ * ζ := by
              rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
          _ = ζ := by rw [h1, one_mul]
      rw [← key]
      exact pow_mem h _
  have hprod : (p : Ω) = ∏ μ ∈ primitiveRoots p Ω, (1 - μ) := by
    have h0 := Polynomial.eval_one_cyclotomic_prime (R := Ω) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h0
    simpa using h0.symm
  have hcard : (primitiveRoots p Ω).card = p - 1 := by
    rw [hζ.card_primitiveRoots, Nat.totient_prime hp]
  have hall : ∀ μ ∈ primitiveRoots p Ω, ∃ u ∈ W, 1 - μ = (ζ - 1) * u := by
    intro μ hμ
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.pos).mp hμ
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμp.pow_eq_one
    refine ⟨-(∑ j ∈ Finset.range i, ζ ^ j), neg_mem (sum_mem fun j _ => pow_mem hζW j), ?_⟩
    rw [← hi]
    linear_combination geom_sum_mul ζ i
  obtain ⟨w, hw, hw'⟩ := prod_one_sub_lemma W (ζ - 1) _ hall
  rw [hcard] at hw'
  exact ⟨w, hw, hprod.trans hw'⟩

def expo (q p : ℕ) : ℕ := if p = 2 then 2 * q else q / (p - 1)

/- English proof (translation)
Unfold `expo`. Distinguish the cases in `h : p = 2`. Substitute `h` using the available equality. Simplify using `only [if_true]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg h]`. Establish `hne : ((p - 1 : ℕ) : ℝ) ≠ 0`. Establish `h2 : 2 ≤ p` using `hp.two_le`. Establish `h3 : p - 1 ≠ 0` using `by omega`.

Conclude with `h3` after adjusting the coercions. Rewrite using `[Nat.cast_div hd hne, Nat.cast_sub hp.one_le]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expo_cast {q p : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q) :
    (expo q p : ℝ) = q * (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) := by
  unfold expo
  by_cases h : p = 2
  · subst h
    simp only [if_true]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    have hne : ((p - 1 : ℕ) : ℝ) ≠ 0 := by
      have h2 : 2 ≤ p := hp.two_le
      have h3 : p - 1 ≠ 0 := by omega
      exact_mod_cast h3
    rw [Nat.cast_div hd hne, Nat.cast_sub hp.one_le]
    push_cast
    ring

/- English proof (translation)
Unfold `HT.IsCp at hκ`. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality. Rewrite `hκ` using `[if_pos rfl]`. Use `⟨1, W.one_mem, ?_⟩` and prove the remaining obligations.

Establish `he : expo q 2 = 2 * q` using `by simp [expo]`. Rewrite using `[hκ, one_mul, he, pow_mul]`. Evaluate the numerical expressions. Rewrite `hκ` using `[if_neg h2]`. Take `⟨ζ, hζ, rfl⟩` from `hκ`.

Take `⟨r, rfl⟩` from `hd`. Take `⟨w₀, hw₀, hpw⟩` from `prime_eq_mul_pow W hp hζ`. Establish `hpos : 0 < p - 1` using `by have := hp.two_le; omega`. Use `⟨w₀ ^ r, pow_mem hw₀ r, ?_⟩` and prove the remaining obligations. Establish `he : expo ((p - 1) * r) p = r`.

Simplify using `only [expo, if_neg h2]`. Conclude with `Nat.mul_div_cancel_left r hpos`. Rewrite using `[he, Nat.cast_pow, hpw, mul_pow, ← pow_mul]`.
-/
theorem pow_expo_eq {Ω : Type} [Field Ω] (W : ValuationSubring Ω) {p q : ℕ} (hp : p.Prime) (hd : p - 1 ∣ q)
    {κ : Ω} (hκ : HT.IsCp p κ) : ∃ w ∈ W, ((p ^ expo q p : ℕ) : Ω) = w * κ ^ q := by
  unfold HT.IsCp at hκ
  by_cases h2 : p = 2
  · subst h2
    rw [if_pos rfl] at hκ
    refine ⟨1, W.one_mem, ?_⟩
    have he : expo q 2 = 2 * q := by simp [expo]
    rw [hκ, one_mul, he, pow_mul]
    norm_num
  · rw [if_neg h2] at hκ
    obtain ⟨ζ, hζ, rfl⟩ := hκ
    obtain ⟨r, rfl⟩ := hd
    obtain ⟨w₀, hw₀, hpw⟩ := prime_eq_mul_pow W hp hζ
    have hpos : 0 < p - 1 := by have := hp.two_le; omega
    refine ⟨w₀ ^ r, pow_mem hw₀ r, ?_⟩
    have he : expo ((p - 1) * r) p = r := by
      simp only [expo, if_neg h2]
      exact Nat.mul_div_cancel_left r hpos
    rw [he, Nat.cast_pow, hpw, mul_pow, ← pow_mul]

/- English proof (translation)
Introduce `S m₀ hS hm₀`. Take `⟨q, hq⟩ : ∃ q : ℕ, q = ∏ p ∈ S, (p - 1)` from `⟨_, rfl⟩`. Establish `hqpos : 0 < q`. Rewrite using `[hq]`. Conclude with `Finset.prod_pos fun p hp => by have := (hS p hp).two_le; omega`.

Establish `hdvd : ∀ p ∈ S, p - 1 ∣ q` using `fun p hp => by`. Rewrite using `[hq]`. Conclude with `Finset.dvd_prod_of_mem (fun p => p - 1) hp`. Use `⟨q, m₀ ^ q * ∏ p ∈ S, p ^ expo q p, hqpos, Nat.mul_pos (pow_pos hm₀ q) (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _), ?_, ?_⟩` and prove the remaining obligations. Apply `le_of_eq` to reduce the goal to its premises.

Use `push_cast`. Establish `hm0 : ((m₀ : ℝ) ^ q) ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hm₀.ne')`. Establish `hprod : (∏ p ∈ S, (p : ℝ) ^ expo q p) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero)`. Rewrite using `[Real.log_mul hm0 hprod, Real.log_pow, Real.log_prod fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero), mul_add, Finset.mul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite using `[Real.log_pow, expo_cast (hS p hp) (hdvd p hp)]`. Expand and normalize the polynomial expressions, which then agree. Introduce `Ω _ _ W κ hκ t ht`. Establish `hrest : ∀ T : Finset ℕ, (∏ x ∈ T, ((x : Ω) ^ expo q x)) ∈ W` using `fun T => prod_mem fun x _ => pow_mem (natCast_mem W x) _`.

Use `push_cast`. Break down `hκ with rfl | ⟨p, hpS, hp⟩` into its components or cases. Rewrite `ht` using `[mul_one]`. Establish `e : (m₀ : Ω) ^ q * (∏ x ∈ S, (x : Ω) ^ expo q x) * t ^ q = ((m₀ : Ω) * t) ^ q * ∏ x ∈ S, (x : Ω) ^ expo q x` using `by ring`. Rewrite using `[e]`.

Conclude with `mul_mem (pow_mem ht q) (hrest S)`. Take `⟨w, hw, hpw⟩` from `pow_expo_eq W (hS p hpS) (hdvd p hpS) hp`. Move the coercions through the operations in `at hpw`. Establish `hsplit : ∏ x ∈ S, (x : Ω) ^ expo q x = w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x`. Rewrite using `[← Finset.mul_prod_erase S (fun x => (x : Ω) ^ expo q x) hpS, hpw]`.

Rewrite using `[hsplit]`. Establish `e : (m₀ : Ω) ^ q * (w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x) * t ^ q = w * ((m₀ : Ω) * κ * t) ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x` using `by ring`. Rewrite using `[e]`. Conclude with `mul_mem (mul_mem hw (pow_mem ht q)) (hrest _)`.
-/
theorem clear_constants : ∀ (S : Finset ℕ) (m₀ : ℕ), (∀ p ∈ S, p.Prime) → 0 < m₀ → ∃ q m : ℕ, 0 < q ∧ 0 < m ∧
    Real.log m ≤ q * (Real.log m₀ + ∑ p ∈ S, (if p = 2 then 2 else 1 / ((p : ℝ) - 1)) * Real.log p) ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (W : ValuationSubring Ω) (κ : Ω), (κ = 1 ∨ ∃ p ∈ S, HT.IsCp p κ) →
      ∀ t : Ω, ((m₀ : Ω) * κ) * t ∈ W → (m : Ω) * t ^ q ∈ W := by
  intro S m₀ hS hm₀
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = ∏ p ∈ S, (p - 1) := ⟨_, rfl⟩
  have hqpos : 0 < q := by
    rw [hq]
    exact Finset.prod_pos fun p hp => by have := (hS p hp).two_le; omega
  have hdvd : ∀ p ∈ S, p - 1 ∣ q := fun p hp => by
    rw [hq]
    exact Finset.dvd_prod_of_mem (fun p => p - 1) hp
  refine ⟨q, m₀ ^ q * ∏ p ∈ S, p ^ expo q p, hqpos,
    Nat.mul_pos (pow_pos hm₀ q) (Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _), ?_, ?_⟩
  · apply le_of_eq
    push_cast
    have hm0 : ((m₀ : ℝ) ^ q) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hm₀.ne')
    have hprod : (∏ p ∈ S, (p : ℝ) ^ expo q p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero)
    rw [Real.log_mul hm0 hprod, Real.log_pow,
      Real.log_prod fun p hp => pow_ne_zero _ (by exact_mod_cast (hS p hp).ne_zero),
      mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Real.log_pow, expo_cast (hS p hp) (hdvd p hp)]
    ring
  · intro Ω _ _ W κ hκ t ht
    have hrest : ∀ T : Finset ℕ, (∏ x ∈ T, ((x : Ω) ^ expo q x)) ∈ W :=
      fun T => prod_mem fun x _ => pow_mem (natCast_mem W x) _
    push_cast
    rcases hκ with rfl | ⟨p, hpS, hp⟩
    · rw [mul_one] at ht
      have e : (m₀ : Ω) ^ q * (∏ x ∈ S, (x : Ω) ^ expo q x) * t ^ q
          = ((m₀ : Ω) * t) ^ q * ∏ x ∈ S, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (pow_mem ht q) (hrest S)
    · obtain ⟨w, hw, hpw⟩ := pow_expo_eq W (hS p hpS) (hdvd p hpS) hp
      push_cast at hpw
      have hsplit : ∏ x ∈ S, (x : Ω) ^ expo q x = w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by
        rw [← Finset.mul_prod_erase S (fun x => (x : Ω) ^ expo q x) hpS, hpw]
      rw [hsplit]
      have e : (m₀ : Ω) ^ q * (w * κ ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x) * t ^ q
          = w * ((m₀ : Ω) * κ * t) ^ q * ∏ x ∈ S.erase p, (x : Ω) ^ expo q x := by ring
      rw [e]
      exact mul_mem (mul_mem hw (pow_mem ht q)) (hrest _)

end GlobalTheory.CompanionTheory.Ar.ClearConstants
