import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Integer

set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.Out.KrullAlg

variable {A : Type*} [CommRing A] [IsDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K]

def denIdeal {ι : Type*} (x : ι → K) : Ideal A where
  carrier := {r | ∀ i, algebraMap A K r * x i ∈ (algebraMap A K).range}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨u, hu⟩ := ha i
    obtain ⟨v, hv⟩ := hb i
    exact ⟨u + v, by rw [map_add, hu, hv, map_add, add_mul]⟩
  zero_mem' := fun i => ⟨0, by simp⟩
  smul_mem' := by
    intro c a ha i
    obtain ⟨u, hu⟩ := ha i
    exact ⟨c * u, by rw [map_mul, hu, smul_eq_mul, map_mul, mul_assoc]⟩

omit [IsDomain A] [IsFractionRing A K] in
/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
lemma mem_denIdeal {ι : Type*} {x : ι → K} {r : A} :
    r ∈ denIdeal (A := A) x ↔ ∀ i, algebraMap A K r * x i ∈ (algebraMap A K).range := Iff.rfl

/- English proof (translation)
Establish `hne : (Ideal.Quotient.mk (denIdeal (A` using `A) x) 1) ≠ 0 := by`. Rewrite using `[Ne, Ideal.Quotient.eq_zero_iff_mem]`. Introduce `h`. Take `⟨i, hi⟩` from `hx`. Apply `hi` to reduce the goal to its premises.

Use `h i` as an intermediate fact. Simplify using `using this`. Take `⟨P, hP, -⟩` from `exists_le_isAssociatedPrime_of_isNoetherianRing A _ hne`. Rewrite `hP` using `[isAssociatedPrime_iff]`. Take `⟨hPp, y, hy⟩` from `hP`.

Take `⟨d, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `key : ∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range`. Introduce `r`. Rewrite using `[hy, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Use `show (∀ i, algebraMap A K (r * d) * x i ∈ (algebraMap A K).range) ↔ _`.

Simplify using `only [map_mul, mul_assoc]`. Use `⟨d, P, hPp, key, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hPp.ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one, key 1]`. Introduce `i`. Simplify using `using hcon i`.
-/
lemma exists_assoc [IsNoetherianRing A] {ι : Type*} (x : ι → K)
    (hx : ∃ i, x i ∉ (algebraMap A K).range) :
    ∃ (d : A) (P : Ideal A), P.IsPrime ∧
      (∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range) ∧
      ∃ i, algebraMap A K d * x i ∉ (algebraMap A K).range := by
  classical
  have hne : (Ideal.Quotient.mk (denIdeal (A := A) x) 1) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    intro h
    obtain ⟨i, hi⟩ := hx
    apply hi
    have := h i
    simpa using this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hne
  rw [isAssociatedPrime_iff] at hP
  obtain ⟨hPp, y, hy⟩ := hP
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
  have key : ∀ r, r ∈ P ↔ ∀ i, algebraMap A K r * (algebraMap A K d * x i) ∈ (algebraMap A K).range := by
    intro r
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    show (∀ i, algebraMap A K (r * d) * x i ∈ (algebraMap A K).range) ↔ _
    simp only [map_mul, mul_assoc]
  refine ⟨d, P, hPp, key, ?_⟩
  by_contra hcon
  push_neg at hcon
  apply hPp.ne_top
  rw [Ideal.eq_top_iff_one, key 1]
  intro i
  simpa using hcon i

/- English proof (translation)
Take `⟨d, P, hP, hPmem, i0, hi0⟩` from `exists_assoc x hx`. Take `⟨b0, hb0⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) (fun i => algebraMap A K d * x i)`. Establish `hb0P : (b0 : A) ∈ P` using `(hPmem _).2 fun i => by`. Take `⟨y, hy⟩` from `hb0 i`. Conclude with `⟨y, by rw [hy, Algebra.smul_def]⟩`.

Establish `hb0ne : (b0 : A) ≠ 0` using `nonZeroDivisors.coe_ne_zero b0`. Establish `hPne : P ≠ ⊥` using `fun h => hb0ne (by rw [h] at hb0P; exact (Submodule.mem_bot A).1 hb0P)`. Establish `hex : ∃ p ∈ P, ∃ u : A, algebraMap A K u = algebraMap A K p * (algebraMap A K d * x i0) ∧ u ∉ P`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Apply `hi0` to reduce the goal to its premises. Set `N : Submodule A K` to `Submodule.map (Algebra.linearMap A K) P`. Establish `hNfg : N.FG` using `(IsNoetherian.noetherian P).map (Algebra.linearMap A K)`. Establish `hNne : N ≠ ⊥`. Introduce `h`.

Establish `hm : algebraMap A K b0 ∈ N` using `(Submodule.mem_map).2 ⟨(b0 : A), hb0P, rfl⟩`. Rewrite `hm` using `[h, Submodule.mem_bot]`. Conclude with `hb0ne ((IsFractionRing.injective A K) (hm.trans (map_zero _).symm))`. Establish `hint : IsIntegral A (algebraMap A K d * x i0)`. Use `isIntegral_of_smul_mem_submodule N hNne hNfg _ fun n hn => ?_` and prove the remaining obligations.

Take `⟨a, haP, rfl⟩` from `(Submodule.mem_map).1 hn`. Take `⟨u, hu⟩` from `(hPmem a).1 haP i0`. Establish `huP` using `hne a haP u hu`. Use `(Submodule.mem_map).2 ⟨u, huP, ?_⟩` and prove the remaining obligations. Simplify using `only [Algebra.linearMap_apply, smul_eq_mul]`.

Rewrite using `[hu]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Conclude with `⟨a, ha⟩`. Take `⟨p, hpP, u, hu, huP⟩` from `hex`.

Use `⟨P, hP, ?_, p * d, P.mul_mem_right d hpP, fun j => ?_, i0, u, huP, ?_⟩` and prove the remaining obligations. Use `haveI : Submodule.IsPrincipal (Ideal.span {p}) := ⟨⟨p, rfl⟩⟩`. Establish `hmin : P ∈ (Ideal.span {p}).minimalPrimes`. Use `⟨⟨hP, (Ideal.span_singleton_le_iff_mem P).2 hpP⟩, fun Q hQ hQP => ?_⟩` and prove the remaining obligations. Introduce `q hq`.

Take `⟨v, hv⟩` from `(hPmem q).1 hq i0`. Establish `e : q * u = p * v` using `IsFractionRing.injective A K (by rw [map_mul, map_mul, hu, hv]; ring)`. Establish `h1 : q * u ∈ Q` using `e ▸ Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem Q).1 hQ.2)`. Break down `hQ.1.mem_or_mem h1 with h2 | h2` into its components or cases. Conclude with `h2`.

Conclude with `absurd (hQP h2) huP`. Establish `h1 : P.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin`. Establish `h0 : P.height ≠ 0` using `fun h => hPne (Ideal.height_eq_zero_iff_eq_bot.1 h)`. Conclude with `le_antisymm h1 (ENat.one_le_iff_ne_zero.2 h0)`. Take `⟨v, hv⟩` from `(hPmem p).1 hpP j`.

Conclude with `⟨v, by rw [hv, map_mul]; ring⟩`. Rewrite using `[hu, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_clear [IsNoetherianRing A] [IsIntegrallyClosed A] {ι : Type*} [Finite ι]
    (x : ι → K) (hx : ∃ i, x i ∉ (algebraMap A K).range) :
    ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧ ∃ b ∈ P,
      (∀ i, algebraMap A K b * x i ∈ (algebraMap A K).range) ∧
      ∃ i, ∃ u ∉ P, algebraMap A K u = algebraMap A K b * x i := by
  classical
  obtain ⟨d, P, hP, hPmem, i0, hi0⟩ := exists_assoc x hx
  obtain ⟨b0, hb0⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A)
    (fun i => algebraMap A K d * x i)
  have hb0P : (b0 : A) ∈ P := (hPmem _).2 fun i => by
    obtain ⟨y, hy⟩ := hb0 i
    exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  have hb0ne : (b0 : A) ≠ 0 := nonZeroDivisors.coe_ne_zero b0
  have hPne : P ≠ ⊥ := fun h => hb0ne (by rw [h] at hb0P; exact (Submodule.mem_bot A).1 hb0P)
  have hex : ∃ p ∈ P, ∃ u : A, algebraMap A K u = algebraMap A K p * (algebraMap A K d * x i0) ∧
      u ∉ P := by
    by_contra hne
    push_neg at hne
    apply hi0
    let N : Submodule A K := Submodule.map (Algebra.linearMap A K) P
    have hNfg : N.FG := (IsNoetherian.noetherian P).map (Algebra.linearMap A K)
    have hNne : N ≠ ⊥ := by
      intro h
      have hm : algebraMap A K b0 ∈ N := (Submodule.mem_map).2 ⟨(b0 : A), hb0P, rfl⟩
      rw [h, Submodule.mem_bot] at hm
      exact hb0ne ((IsFractionRing.injective A K) (hm.trans (map_zero _).symm))
    have hint : IsIntegral A (algebraMap A K d * x i0) := by
      refine isIntegral_of_smul_mem_submodule N hNne hNfg _ fun n hn => ?_
      obtain ⟨a, haP, rfl⟩ := (Submodule.mem_map).1 hn
      obtain ⟨u, hu⟩ := (hPmem a).1 haP i0
      have huP := hne a haP u hu
      refine (Submodule.mem_map).2 ⟨u, huP, ?_⟩
      simp only [Algebra.linearMap_apply, smul_eq_mul]
      rw [hu]
      ring
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    exact ⟨a, ha⟩
  obtain ⟨p, hpP, u, hu, huP⟩ := hex
  refine ⟨P, hP, ?_, p * d, P.mul_mem_right d hpP, fun j => ?_, i0, u, huP, ?_⟩
  · haveI : Submodule.IsPrincipal (Ideal.span {p}) := ⟨⟨p, rfl⟩⟩
    have hmin : P ∈ (Ideal.span {p}).minimalPrimes := by
      refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem P).2 hpP⟩, fun Q hQ hQP => ?_⟩
      intro q hq
      obtain ⟨v, hv⟩ := (hPmem q).1 hq i0
      have e : q * u = p * v := IsFractionRing.injective A K (by rw [map_mul, map_mul, hu, hv]; ring)
      have h1 : q * u ∈ Q := e ▸ Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem Q).1 hQ.2)
      rcases hQ.1.mem_or_mem h1 with h2 | h2
      · exact h2
      · exact absurd (hQP h2) huP
    have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
    have h0 : P.height ≠ 0 := fun h => hPne (Ideal.height_eq_zero_iff_eq_bot.1 h)
    exact le_antisymm h1 (ENat.one_le_iff_ne_zero.2 h0)
  · obtain ⟨v, hv⟩ := (hPmem p).1 hpP j
    exact ⟨v, by rw [hv, map_mul]; ring⟩
  · rw [hu, map_mul]
    ring

/- English proof (translation)
Take `⟨P, hP, h1, b, hbP, -, ⟨i, u, huP, hu⟩⟩` from `exists_clear (A := A) (ι := Unit) (fun _ => x) ⟨(), hx⟩`. Establish `hu' : algebraMap A K u = algebraMap A K b * x` using `hu`. Use `⟨P, hP, h1, fun s hs hsx => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hsx`. Establish `e : algebraMap A K (s * u) = algebraMap A K (b * a)`.

Rewrite using `[map_mul, map_mul, hu', ha]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : s * u = b * a` using `IsFractionRing.injective A K e`. Establish `h3 : s * u ∈ P` using `e2 ▸ P.mul_mem_right a hbP`. Break down `hP.mem_or_mem h3 with h4 | h4` into its components or cases.

Conclude with `hs h4`. Conclude with `huP h4`.
-/
theorem exists_height_one_not_mem [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (hx : x ∉ (algebraMap A K).range) :
    ∃ P : Ideal A, P.IsPrime ∧ P.height = 1 ∧
      ∀ s ∉ P, algebraMap A K s * x ∉ (algebraMap A K).range := by
  obtain ⟨P, hP, h1, b, hbP, -, ⟨i, u, huP, hu⟩⟩ :=
    exists_clear (A := A) (ι := Unit) (fun _ => x) ⟨(), hx⟩
  have hu' : algebraMap A K u = algebraMap A K b * x := hu
  refine ⟨P, hP, h1, fun s hs hsx => ?_⟩
  obtain ⟨a, ha⟩ := hsx
  have e : algebraMap A K (s * u) = algebraMap A K (b * a) := by
    rw [map_mul, map_mul, hu', ha]
    ring
  have e2 : s * u = b * a := IsFractionRing.injective A K e
  have h3 : s * u ∈ P := e2 ▸ P.mul_mem_right a hbP
  rcases hP.mem_or_mem h3 with h4 | h4
  · exact hs h4
  · exact huP h4

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Take `⟨P, hP, h1, hs⟩` from `exists_height_one_not_mem x hx`. Take `⟨s, hsP, hsx⟩` from `h P hP h1`. Conclude with `hs s hsP hsx`.
-/
theorem mem_range_of_forall_height_one [IsNoetherianRing A] [IsIntegrallyClosed A] (x : K)
    (h : ∀ P : Ideal A, P.IsPrime → P.height = 1 →
      ∃ s ∉ P, algebraMap A K s * x ∈ (algebraMap A K).range) :
    x ∈ (algebraMap A K).range := by
  by_contra hx
  obtain ⟨P, hP, h1, hs⟩ := exists_height_one_not_mem x hx
  obtain ⟨s, hsP, hsx⟩ := h P hP h1
  exact hs s hsP hsx

omit [IsFractionRing A K] in

/- English proof (translation)
Use `(Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).subset ?_` and prove the remaining obligations. Introduce and unpack `P ⟨hP, h1, haP⟩`. Establish `hle : Ideal.span {a} ≤ P` using `(Ideal.span_singleton_le_iff_mem P).mpr haP`. Take `⟨Q, hQ, hQP⟩` from `Ideal.exists_minimalPrimes_le hle`. Establish `hQprime : Q.IsPrime` using `hQ.1.1`.

Distinguish the cases in `hQP' : Q = P`. Conclude with `hQP' ▸ hQ`. It suffices to derive a contradiction. Establish `hlt : Q < P` using `lt_of_le_of_ne hQP hQP'`. Establish `hQne : (⊥ : Ideal A) < Q`.

Use `lt_of_le_of_ne bot_le (fun hb => ha ?_)` and prove the remaining obligations. Establish `h3 : a ∈ Q` using `hQ.1.2 (Ideal.mem_span_singleton_self a)`. Rewrite `h3` using `[← hb]`. Conclude with `Ideal.mem_bot.mp h3`. Establish `h1' : Order.height (⟨P, hP⟩ : PrimeSpectrum A) = 1` using `by first`.

Consider the case `(rw [Ideal.IsPrime.height_eq_primeHeight] at h1; exact h1)`. Consider the case `(rw [Ideal.height_eq_primeHeight_of_isPrime] at h1; exact h1)`. Consider the case `(rw [← Ideal.primeHeight_eq_height] at h1; exact h1)`. Consider the case `(rw [Ideal.IsPrime.height] at h1; exact h1)`. Consider the case `(simp only [Ideal.height, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff, iInf_iInf_eq_left] at h1; exact h1)`.

Establish `hlt' : (⟨Q, hQprime⟩ : PrimeSpectrum A) < ⟨P, hP⟩` using `(PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hlt`. Establish `hQ1 : Order.height (⟨Q, hQprime⟩ : PrimeSpectrum A) < 1`. Rewrite using `[← h1']`. Conclude with `Order.height_strictMono hlt' (lt_of_le_of_lt (Order.height_mono (le_of_lt hlt')) (by rw [h1']; exact ENat.one_lt_top))`. Establish `hne' : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum A) < ⟨Q, hQprime⟩` using `(PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hQne`.

Establish `hQ0` using `Order.height_strictMono hne' (lt_of_le_of_lt (Order.height_mono (le_of_lt hne')) (lt_trans hQ1 ENat.one_lt_top))`. Establish `hQz : Order.height (⟨Q, hQprime⟩ : PrimeSpectrum A) = 0` using `ENat.lt_one_iff_eq_zero.mp hQ1`. Rewrite `hQ0` using `[hQz]`. Conclude with `absurd hQ0 (not_lt_zero')`.
-/
theorem finite_height_one [IsNoetherianRing A] {a : A} (ha : a ≠ 0) :
    {P : Ideal A | P.IsPrime ∧ P.height = 1 ∧ a ∈ P}.Finite := by
  classical
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing A (Ideal.span {a})).subset ?_
  rintro P ⟨hP, h1, haP⟩
  have hle : Ideal.span {a} ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr haP
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hle
  have hQprime : Q.IsPrime := hQ.1.1
  by_cases hQP' : Q = P
  · exact hQP' ▸ hQ
  · exfalso
    have hlt : Q < P := lt_of_le_of_ne hQP hQP'
    have hQne : (⊥ : Ideal A) < Q := by
      refine lt_of_le_of_ne bot_le (fun hb => ha ?_)
      have h3 : a ∈ Q := hQ.1.2 (Ideal.mem_span_singleton_self a)
      rw [← hb] at h3
      exact Ideal.mem_bot.mp h3
    have h1' : Order.height (⟨P, hP⟩ : PrimeSpectrum A) = 1 := by
      first
      | (rw [Ideal.IsPrime.height_eq_primeHeight] at h1; exact h1)
      | (rw [Ideal.height_eq_primeHeight_of_isPrime] at h1; exact h1)
      | (rw [← Ideal.primeHeight_eq_height] at h1; exact h1)
      | (rw [Ideal.IsPrime.height] at h1; exact h1)
      | (simp only [Ideal.height, Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff,
          iInf_iInf_eq_left] at h1; exact h1)
    have hlt' : (⟨Q, hQprime⟩ : PrimeSpectrum A) < ⟨P, hP⟩ := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hlt
    have hQ1 : Order.height (⟨Q, hQprime⟩ : PrimeSpectrum A) < 1 := by
      rw [← h1']
      exact Order.height_strictMono hlt'
        (lt_of_le_of_lt (Order.height_mono (le_of_lt hlt')) (by rw [h1']; exact ENat.one_lt_top))
    have hne' : (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum A) < ⟨Q, hQprime⟩ :=
      (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp hQne
    have hQ0 := Order.height_strictMono hne'
      (lt_of_le_of_lt (Order.height_mono (le_of_lt hne')) (lt_trans hQ1 ENat.one_lt_top))
    have hQz : Order.height (⟨Q, hQprime⟩ : PrimeSpectrum A) = 0 := ENat.lt_one_iff_eq_zero.mp hQ1
    rw [hQz] at hQ0
    exact absurd hQ0 (not_lt_zero')

end ReciprocityTheory.ChartRestriction.G.Out.KrullAlg
