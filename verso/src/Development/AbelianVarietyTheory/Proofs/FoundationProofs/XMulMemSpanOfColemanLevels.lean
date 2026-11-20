import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

noncomputable section

open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col.Interp

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `: ((1 + X : PowerSeries R) ^ n) = (((1 + Polynomial.X : Polynomial R) ^ n : Polynomial R) : PowerSeries R)`. Simplify using the standard rewrite rules. Rewrite using `[this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]`.
-/
theorem coeff_one_add_X_pow (n k : ℕ) : coeff k ((1 + X : PowerSeries R) ^ n) = (n.choose k : R) := by
  have : ((1 + X : PowerSeries R) ^ n) = (((1 + Polynomial.X : Polynomial R) ^ n : Polynomial R) : PowerSeries R) := by
    simp
  rw [this, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

/- English proof (translation)
Introduce `h`. Use `congrArg (coeff N) h` as an intermediate fact. Rewrite `this` using `[map_sub, coeff_one_add_X_pow, Nat.choose_self, coeff_one, if_neg (by omega)]`. Simplify using `at this`.
-/
theorem one_add_X_pow_sub_one_ne_zero [Nontrivial R] (N : ℕ) (hN : 1 ≤ N) :
    ((1 + X : PowerSeries R) ^ N - 1) ≠ 0 := by
  intro h
  have := congrArg (coeff N) h
  rw [map_sub, coeff_one_add_X_pow, Nat.choose_self, coeff_one, if_neg (by omega)] at this
  simp at this

/- English proof (translation)
Unfold `cyc`. Rewrite using `[Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]`. Simplify using `[Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_X]`.
-/
theorem cyc_succ (p n : ℕ) (hp : p.Prime) :
    cyc R p (n + 1) = ∑ i ∈ Finset.range p, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ i := by
  unfold cyc
  rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hp]
  simp [Polynomial.eval₂_finset_sum, Polynomial.eval₂_pow, Polynomial.eval₂_X]

/- English proof (translation)
Rewrite using `[cyc_succ p n hp, geom_sum_mul, ← pow_mul, ← pow_succ]`.
-/
theorem om_succ (p n : ℕ) (hp : p.Prime) :
    (1 + X : PowerSeries R) ^ (p ^ (n + 1)) - 1 = cyc R p (n + 1) * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  rw [cyc_succ p n hp, geom_sum_mul, ← pow_mul, ← pow_succ]

/- English proof (translation)
Use `⟨∑ i ∈ Finset.range p, ∑ l ∈ Finset.range i, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ l, ?_⟩` and prove the remaining obligations. Rewrite using `[cyc_succ p n hp, Finset.sum_mul]`. Establish `: (p : PowerSeries R) = ∑ i ∈ Finset.range p, (1 : PowerSeries R)` using `by simp`. Rewrite using `[this, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[geom_sum_mul]`.
-/
theorem cyc_sub_p (p n : ℕ) (hp : p.Prime) :
    ∃ u : PowerSeries R, cyc R p (n + 1) - (p : PowerSeries R) = u * ((1 + X : PowerSeries R) ^ (p ^ n) - 1) := by
  refine ⟨∑ i ∈ Finset.range p, ∑ l ∈ Finset.range i, ((1 + X : PowerSeries R) ^ (p ^ n)) ^ l, ?_⟩
  rw [cyc_succ p n hp, Finset.sum_mul]
  have : (p : PowerSeries R) = ∑ i ∈ Finset.range p, (1 : PowerSeries R) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [geom_sum_mul]

/- English proof (translation)
Use `haveI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq`. Establish `hCq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) (C q) = 0`. Rewrite using `[PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self q), map_zero]`. Establish `ht : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) t = 0`. Establish `h2 : f * t = C q * (B - C q ^ m * s)` using `by rw [mul_sub, ← mul_assoc, ← pow_succ', h]; ring`.

Establish `h3` using `congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q}))) h2`. Rewrite `h3` using `[map_mul, map_mul, hCq, zero_mul]`. Conclude with `(mul_eq_zero.1 h3).resolve_left hf`. Establish `hd : ∀ n, ∃ a, coeff n t = q * a`. Introduce `n`.

Use `congrArg (coeff n) ht` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `this`. Use `choose a ha using hd`. Establish `ht' : t = C q * PowerSeries.mk a`.

Use extensionality with `n`. Rewrite using `[coeff_C_mul, coeff_mk, ha]`. Use `⟨PowerSeries.mk a, ?_⟩` and prove the remaining obligations. Establish `hq0 : (C q : PowerSeries R) ≠ 0`. Introduce `h0; exact hq.ne_zero (by simpa using congrArg (constantCoeff) h0)`.

Apply `mul_left_cancel₀ hq0` to reduce the goal to its premises. Rewrite using `[h, ht']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cancel_prime [IsDomain R] {q : R} (hq : Prime q) {f : PowerSeries R}
    (hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) f ≠ 0)
    {B s t : PowerSeries R} (m : ℕ)
    (h : C q * B = C q ^ (m + 1) * s + f * t) : ∃ t', B = C q ^ m * s + f * t' := by
  haveI : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).2 hq
  have hCq : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) (C q) = 0 := by
    rw [PowerSeries.map_C, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self q), map_zero]
  have ht : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q})) t = 0 := by
    have h2 : f * t = C q * (B - C q ^ m * s) := by rw [mul_sub, ← mul_assoc, ← pow_succ', h]; ring
    have h3 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {q}))) h2
    rw [map_mul, map_mul, hCq, zero_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left hf
  have hd : ∀ n, ∃ a, coeff n t = q * a := by
    intro n
    have := congrArg (coeff n) ht
    rw [PowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose a ha using hd
  have ht' : t = C q * PowerSeries.mk a := by
    ext n; rw [coeff_C_mul, coeff_mk, ha]
  refine ⟨PowerSeries.mk a, ?_⟩
  have hq0 : (C q : PowerSeries R) ≠ 0 := by
    intro h0; exact hq.ne_zero (by simpa using congrArg (constantCoeff) h0)
  apply mul_left_cancel₀ hq0
  rw [h, ht']; ring

end GlobalTheory.Col.Interp

namespace GlobalTheory.Col

open Interp in

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ _`. Use `Ideal.mem_span_pair.2 ⟨0, h, ?_⟩` and prove the remaining obligations.

Simplify using `[mul_comm]`. Consider the case `succ n ih`. Introduce `hk hcn`. Take `⟨A, B, hAB⟩` from `Ideal.mem_span_pair.1 (ih (by omega) (by omega))`. Take `⟨y, hy⟩` from `hyp (n + 1) (by omega) hk`.

Take `⟨g, hg⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hy)`. Take `⟨u, hu⟩` from `cyc_sub_p (R := R) p n hp.out`. Take `⟨m, rfl⟩ : ∃ m, c = m + 1 + n` from `⟨c - (n + 1), by omega⟩`. Establish `e1 : m + 1 + n - n = m + 1` using `by omega`. Establish `e2 : m + 1 + n - (n + 1) = m` using `by omega`.

Rewrite `hAB` using `[e1]`. Rewrite using `[e2]`. Use `set P : PowerSeries R := (p : PowerSeries R) with hP`. Use `set om : PowerSeries R := (1 + X : PowerSeries R) ^ (p ^ n) - 1 with hom`. Establish `key : C (p : R) * B = C (p : R) ^ (m + 1) * (u * A - u * X * P ^ n * y) + cyc R p (n + 1) * (B - u * X * g)`.

Rewrite using `[map_natCast]`. Take the linear combination `(-B) * hu - u * hAB + (u * X) * hg`. Establish `hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (cyc R p (n + 1)) ≠ 0` using `by haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpR.ne_zero).2 hpR`. Introduce `h0`. Establish `h1` using `congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))) (om_succ (R := R) p n hp.out)`.

Rewrite `h1` using `[map_mul, h0, zero_mul]`. Use `one_add_X_pow_sub_one_ne_zero (R := R ⧸ Ideal.span {(p : R)}) (p ^ (n + 1)) (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_` and prove the remaining obligations. Simplify using `using h1`. Take `⟨t', ht'⟩` from `cancel_prime hpR hf m key`. Rewrite `ht'` using `[map_natCast]`.

Use `Ideal.mem_span_pair.2 ⟨A * P + (u * A - u * X * P ^ n * y) * om, t', ?_⟩` and prove the remaining obligations. Rewrite using `[om_succ (R := R) p n hp.out]`. Take the linear combination `hAB - om * ht'`.
-/
theorem X_mul_mem_span_of_levels (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (hR : IsDomain R)
    (hpR : Prime (p : R)) (_hc : IsAdicComplete (Ideal.span {(p : R)}) R)
    (h : PowerSeries R) (k c : ℕ)
    (hyp : ∀ r, 1 ≤ r → r ≤ k → ∃ y : PowerSeries R, ev R p r h = ev R p r ((p : PowerSeries R) ^ c * y)) :
    ∀ j, j ≤ k → j ≤ c → X * h ∈ Ideal.span {(p : PowerSeries R) ^ (c - j), (1 + X) ^ (p ^ j) - 1} := by
  intro j
  induction j with
  | zero =>
    intro _ _
    refine Ideal.mem_span_pair.2 ⟨0, h, ?_⟩
    simp [mul_comm]
  | succ n ih =>
    intro hk hcn
    obtain ⟨A, B, hAB⟩ := Ideal.mem_span_pair.1 (ih (by omega) (by omega))
    obtain ⟨y, hy⟩ := hyp (n + 1) (by omega) hk
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hy)
    obtain ⟨u, hu⟩ := cyc_sub_p (R := R) p n hp.out
    obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 + n := ⟨c - (n + 1), by omega⟩
    have e1 : m + 1 + n - n = m + 1 := by omega
    have e2 : m + 1 + n - (n + 1) = m := by omega
    rw [e1] at hAB
    rw [e2]
    set P : PowerSeries R := (p : PowerSeries R) with hP
    set om : PowerSeries R := (1 + X : PowerSeries R) ^ (p ^ n) - 1 with hom
    have key : C (p : R) * B = C (p : R) ^ (m + 1) * (u * A - u * X * P ^ n * y)
        + cyc R p (n + 1) * (B - u * X * g) := by
      rw [map_natCast]
      linear_combination (-B) * hu - u * hAB + (u * X) * hg
    have hf : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (cyc R p (n + 1)) ≠ 0 := by
      haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hpR.ne_zero).2 hpR
      intro h0
      have h1 := congrArg (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))) (om_succ (R := R) p n hp.out)
      rw [map_mul, h0, zero_mul] at h1
      refine one_add_X_pow_sub_one_ne_zero (R := R ⧸ Ideal.span {(p : R)}) (p ^ (n + 1))
        (Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hp.out.ne_zero)) ?_
      simpa using h1
    obtain ⟨t', ht'⟩ := cancel_prime hpR hf m key
    rw [map_natCast] at ht'
    refine Ideal.mem_span_pair.2 ⟨A * P + (u * A - u * X * P ^ n * y) * om, t', ?_⟩
    rw [om_succ (R := R) p n hp.out]
    linear_combination hAB - om * ht'

end GlobalTheory.Col
