import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

open Polynomial

variable {k L : Type} [Field k] [Field L] [Algebra k L]

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range]`. Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_pow]`. Use `mul_le_one' ?_ (pow_le_one' hx _)` and prove the remaining obligations. Distinguish the cases in `hc : p.coeff i = 0`.

Simplify using `[hc]`. Rewrite using `[u.2.2 _ hc]`.
-/
theorem place_aeval_le_one (x : L) (u : Place k L) (hx : u.1 x ≤ 1) (p : k[X]) :
    u.1 (aeval x p) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  refine mul_le_one' ?_ (pow_le_one' hx _)
  by_cases hc : p.coeff i = 0
  · simp [hc]
  · rw [u.2.2 _ hc]

/- English proof (translation)
Establish `h1 : u.1 (algebraMap k L (q.coeff 0)) = 1` using `u.2.2 _ hq`. Establish `h2 : u.1 (x * aeval x q.divX) < 1`. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_lt_of_le hx (place_aeval_le_one x u hx.le _)`. Use `conv_lhs => rw [← X_mul_divX_add q]`.

Rewrite using `[map_add, map_mul, aeval_X, aeval_C, Valuation.map_add_eq_of_lt_right u.1 (by rw [h1]; exact h2), h1]`.
-/
theorem place_aeval_eq_one (x : L) (u : Place k L) (hx : u.1 x < 1) (q : k[X]) (hq : q.coeff 0 ≠ 0) :
    u.1 (aeval x q) = 1 := by
  have h1 : u.1 (algebraMap k L (q.coeff 0)) = 1 := u.2.2 _ hq
  have h2 : u.1 (x * aeval x q.divX) < 1 := by
    rw [map_mul]
    exact mul_lt_one_of_lt_of_le hx (place_aeval_le_one x u hx.le _)
  conv_lhs => rw [← X_mul_divX_add q]
  rw [map_add, map_mul, aeval_X, aeval_C, Valuation.map_add_eq_of_lt_right u.1 (by rw [h1]; exact h2), h1]

/- English proof (translation)
Take `⟨q, hpq, hq⟩` from `exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0`. Establish `hq0 : q.coeff 0 ≠ 0`. Introduce `h`. Apply `hq` to reduce the goal to its premises. Simplify `h` using `[X_dvd_iff]`.

Use `conv_lhs => rw [hpq]`. Simplify using `[map_mul, map_pow, place_aeval_eq_one x u hx q hq0]`.
-/
theorem place_aeval_eq_pow (x : L) (u : Place k L) (hx : u.1 x < 1) (p : k[X]) (hp : p ≠ 0) :
    u.1 (aeval x p) = u.1 x ^ p.rootMultiplicity 0 := by
  obtain ⟨q, hpq, hq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp 0
  have hq0 : q.coeff 0 ≠ 0 := by
    intro h; apply hq; simpa [X_dvd_iff] using h
  conv_lhs => rw [hpq]
  simp [map_mul, map_pow, place_aeval_eq_one x u hx q hq0]

end GlobalTheory.Nef

namespace GlobalTheory.Nef

open Polynomial

/- English proof (translation)
Establish `hmem : ∀ y : L, ∃ r s : k[X], y = aeval x r / aeval x s` using `fun y => (IntermediateField.mem_adjoin_simple_iff (F := k) (α := x) y).1 (by rw [htop]; trivial)`. Establish `hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0` using `fun p hp h => hx ⟨p, hp, h⟩`. Establish `hval : ∀ u : Place k L, u.1 x < 1 → u.1 x = WithZero.exp (-1 : ℤ)`. Introduce `u hu`. Establish `hx0 : u.1 x ≠ 0`.

Rewrite using `[Valuation.ne_zero_iff]`. Introduce `h`. Apply `hne X X_ne_zero` to reduce the goal to its premises. Simplify using `using h`. Use `set b := WithZero.log (u.1 x) with hb`.

Establish `hub : u.1 x = WithZero.exp b` using `(WithZero.exp_log hx0).symm`. Establish `hb0 : b < 0`. Establish `: WithZero.exp b < WithZero.exp (0 : ℤ)` using `by rw [← hub, WithZero.exp_zero]; exact hu`. Conclude with `WithZero.exp_lt_exp.1 this`. Take `⟨y, hy⟩` from `u.2.1 (WithZero.exp (-1 : ℤ))`.

Take `⟨r, s, rfl⟩` from `hmem y`. Establish `hr : r ≠ 0` using `by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm`. Establish `hs : s ≠ 0` using `by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm`. Rewrite `hy` using `[map_div₀, place_aeval_eq_pow x u hu r hr, place_aeval_eq_pow x u hu s hs, hub, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_inj]`. Establish `hmul : b * ((r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0) = -1`.

Rewrite using `[← hy]`. Simplify using `only [nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Break down `Int.eq_one_or_neg_one_of_mul_eq_neg_one hmul with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hub, h]`. Establish `hpol : ∀ u : Place k L, u.1 x < 1 → ∀ p : k[X], p ≠ 0 → u.1 (aeval x p) = WithZero.exp (-1 : ℤ) ^ p.rootMultiplicity 0` using `fun u hu p hp => by`. Rewrite using `[place_aeval_eq_pow x u hu p hp, hval u hu]`. Set `e : RatFunc k ≃ₐ[k] L` to `((RatFunc.algEquivOfTranscendental x hx).trans (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv`. Establish `heX : e RatFunc.X = x` using `by simp [e]`.

Establish `heXs : e.symm x = RatFunc.X` using `by rw [← heX, AlgEquiv.symm_apply_apply]`. Set `V` to `(Polynomial.idealX k).valuation (RatFunc k)`. Set `v0 : Valuation L (WithZero (Multiplicative ℤ))` to `V.comap (e.symm : L →+* RatFunc k)`. Establish `hv0 : ∀ y, v0 y = V (e.symm y)` using `fun y => rfl`. Establish `hVX : V RatFunc.X = WithZero.exp (-1 : ℤ)`.

Rewrite using `[← RatFunc.algebraMap_X, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ X_ne_zero (Polynomial.idealX_span k)`. Set `v : Place k L` to `⟨v0, fun γ => by`. Take `⟨r, hr⟩` from `RatFunc.valuation_surjective (K := k) γ`. Conclude with `⟨e r, by rw [hv0, AlgEquiv.symm_apply_apply]; exact hr⟩,`.

Use `fun c hc => by`. Rewrite using `[hv0, AlgEquiv.commutes, IsScalarTower.algebraMap_apply k k[X] (RatFunc k), IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]`. Introduce `hmem'`. Rewrite `hmem'` using `[Polynomial.idealX_span, Ideal.mem_span_singleton, X_dvd_iff]`. Simplify using `[hc] at hmem'⟩`.

Establish `hvx : v.1 x = WithZero.exp (-1 : ℤ)` using `by show v0 x = _; rw [hv0, heXs, hVX]`. Use `⟨v, by simp [ord, hvx], fun w hw => ?_⟩` and prove the remaining obligations. Establish `hvl : v.1 x < 1` using `by rw [hvx]; exact WithZero.exp_lt_exp.2 (by norm_num) |>.trans_eq WithZero.exp_zero`. Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `y`.

Take `⟨r, s, rfl⟩` from `hmem y`. Rewrite using `[map_div₀, map_div₀]`. Distinguish the cases in `hr : r = 0`. Simplify using `[hr]`. Distinguish the cases in `hs : s = 0`.

Simplify using `[hs]`. Rewrite using `[hpol w hw r hr, hpol w hw s hs, hpol v hvl r hr, hpol v hvl s hs]`.
-/
theorem exists_unique_place_ord_eq_one (k L : Type) [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x) (htop : k⟮x⟯ = ⊤) :
    ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  have hmem : ∀ y : L, ∃ r s : k[X], y = aeval x r / aeval x s := fun y =>
    (IntermediateField.mem_adjoin_simple_iff (F := k) (α := x) y).1 (by rw [htop]; trivial)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h => hx ⟨p, hp, h⟩
  have hval : ∀ u : Place k L, u.1 x < 1 → u.1 x = WithZero.exp (-1 : ℤ) := by
    intro u hu
    have hx0 : u.1 x ≠ 0 := by
      rw [Valuation.ne_zero_iff]; intro h; apply hne X X_ne_zero; simpa using h
    set b := WithZero.log (u.1 x) with hb
    have hub : u.1 x = WithZero.exp b := (WithZero.exp_log hx0).symm
    have hb0 : b < 0 := by
      have : WithZero.exp b < WithZero.exp (0 : ℤ) := by rw [← hub, WithZero.exp_zero]; exact hu
      exact WithZero.exp_lt_exp.1 this
    obtain ⟨y, hy⟩ := u.2.1 (WithZero.exp (-1 : ℤ))
    obtain ⟨r, s, rfl⟩ := hmem y
    have hr : r ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    have hs : s ≠ 0 := by rintro rfl; simp at hy; exact WithZero.exp_ne_zero hy.symm
    rw [map_div₀, place_aeval_eq_pow x u hu r hr, place_aeval_eq_pow x u hu s hs, hub,
      ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_sub, WithZero.exp_inj] at hy
    have hmul : b * ((r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0) = -1 := by
      rw [← hy]; simp only [nsmul_eq_mul]; ring
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hmul with h | h
    · omega
    · rw [hub, h]
  have hpol : ∀ u : Place k L, u.1 x < 1 → ∀ p : k[X], p ≠ 0 →
      u.1 (aeval x p) = WithZero.exp (-1 : ℤ) ^ p.rootMultiplicity 0 := fun u hu p hp => by
    rw [place_aeval_eq_pow x u hu p hp, hval u hu]
  let e : RatFunc k ≃ₐ[k] L := ((RatFunc.algEquivOfTranscendental x hx).trans
    (IntermediateField.equivOfEq htop)).trans IntermediateField.topEquiv
  have heX : e RatFunc.X = x := by simp [e]
  have heXs : e.symm x = RatFunc.X := by rw [← heX, AlgEquiv.symm_apply_apply]
  let V := (Polynomial.idealX k).valuation (RatFunc k)
  let v0 : Valuation L (WithZero (Multiplicative ℤ)) := V.comap (e.symm : L →+* RatFunc k)
  have hv0 : ∀ y, v0 y = V (e.symm y) := fun y => rfl
  have hVX : V RatFunc.X = WithZero.exp (-1 : ℤ) := by
    rw [← RatFunc.algebraMap_X, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_singleton _ X_ne_zero (Polynomial.idealX_span k)
  let v : Place k L := ⟨v0, fun γ => by
      obtain ⟨r, hr⟩ := RatFunc.valuation_surjective (K := k) γ
      exact ⟨e r, by rw [hv0, AlgEquiv.symm_apply_apply]; exact hr⟩,
    fun c hc => by
      rw [hv0, AlgEquiv.commutes, IsScalarTower.algebraMap_apply k k[X] (RatFunc k),
        IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
      intro hmem'
      rw [Polynomial.idealX_span, Ideal.mem_span_singleton, X_dvd_iff] at hmem'
      simp [hc] at hmem'⟩
  have hvx : v.1 x = WithZero.exp (-1 : ℤ) := by
    show v0 x = _; rw [hv0, heXs, hVX]
  refine ⟨v, by simp [ord, hvx], fun w hw => ?_⟩
  have hvl : v.1 x < 1 := by rw [hvx]; exact WithZero.exp_lt_exp.2 (by norm_num) |>.trans_eq WithZero.exp_zero
  apply Subtype.ext
  ext y
  obtain ⟨r, s, rfl⟩ := hmem y
  rw [map_div₀, map_div₀]
  by_cases hr : r = 0
  · simp [hr]
  by_cases hs : s = 0
  · simp [hs]
  rw [hpol w hw r hr, hpol w hw s hs, hpol v hvl r hr, hpol v hvl s hs]

end GlobalTheory.Nef
