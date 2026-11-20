import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Use `hc.toIsHausdorff.haus' s fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `h n`.
-/
private theorem eq_zero_of_forall_mem_pow_of_isAdicComplete {S : Type} [CommRing S] (I : Ideal S)
    (hc : IsAdicComplete I S) (s : S) (h : ∀ n : ℕ, s ∈ I ^ n) : s = 0 := by
  refine hc.toIsHausdorff.haus' s fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact h n

/- English proof (translation)
Take `⟨L, hL⟩` from `hc.toIsPrecomplete.prec' f fun {a b} hab => by`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Conclude with `h hab`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Use `hL n` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Then use the resulting hypothesis.
-/
private theorem exists_limit_of_isAdicComplete {S : Type} [CommRing S] (I : Ideal S)
    (hc : IsAdicComplete I S) (f : ℕ → S) (h : ∀ {a b : ℕ}, a ≤ b → f a - f b ∈ I ^ a) :
    ∃ L : S, ∀ n, f n - L ∈ I ^ n := by
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec' f fun {a b} hab => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    exact h hab
  refine ⟨L, fun n => ?_⟩
  have := hL n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

/- English proof (translation)
Establish `hu : IsUnit (a : S)`. Assume the negation of the conclusion as `h`. Conclude with `ha ((IsLocalRing.mem_maximalIdeal _).2 h)`. Take `⟨t, ht⟩ : ∃ t : S, (a : S) * t = 1` from `⟨((hu.unit⁻¹ : Sˣ) : S), hu.mul_val_inv⟩`. Take `⟨b, hbΛ, hb⟩` from `hres t`.

Establish `h1 : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) ∈ maximalIdeal S`. Establish `e : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) = (a : S) * (t - b)`. Use `push_cast`. Rewrite using `[mul_sub, ht]`. Rewrite using `[e]`.

Conclude with `Ideal.mul_mem_left _ _ hb`. Take `⟨c, hcd⟩` from `hdiv _ h1`. Establish `hab : (a : S) * b = 1 - (π : S) * c`. Establish `e` using `congrArg Subtype.val hcd`. Move the coercions through the operations in `at e`.

Take the linear combination `-e`. Establish `htΛ : t ∈ Λ`. Apply `hcl` to reduce the goal to its premises. Introduce `n`. Use `⟨(b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i, Λ.mul_mem hbΛ (Λ.sum_mem fun i _ => Λ.pow_mem (Λ.mul_mem π.2 c.2) i), ?_⟩` and prove the remaining obligations.

Establish `g` using `mul_neg_geom_sum ((π : S) * c) n`. Establish `e : t - (b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i = t * ((π : S) * c) ^ n`. Take the linear combination `((b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * ht - t * (∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * hab - t * g`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ hπm) n)`.

Conclude with `isUnit_iff_exists_inv.2 ⟨⟨t, htΛ⟩, Subtype.ext ht⟩`.
-/
private theorem isUnit_of_not_mem_maximalIdeal_of_closed {S : Type} [CommRing S] [IsLocalRing S]
    (Λ : Subring S) (π : Λ) (hπm : (π : S) ∈ maximalIdeal S)
    (hres : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S)
    (hdiv : ∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a)
    (hcl : ∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ)
    (a : Λ) (ha : (a : S) ∉ maximalIdeal S) : IsUnit a := by
  have hu : IsUnit (a : S) := by
    by_contra h
    exact ha ((IsLocalRing.mem_maximalIdeal _).2 h)
  obtain ⟨t, ht⟩ : ∃ t : S, (a : S) * t = 1 := ⟨((hu.unit⁻¹ : Sˣ) : S), hu.mul_val_inv⟩
  obtain ⟨b, hbΛ, hb⟩ := hres t
  have h1 : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) ∈ maximalIdeal S := by
    have e : ((1 - a * ⟨b, hbΛ⟩ : Λ) : S) = (a : S) * (t - b) := by
      push_cast
      rw [mul_sub, ht]
    rw [e]
    exact Ideal.mul_mem_left _ _ hb
  obtain ⟨c, hcd⟩ := hdiv _ h1
  have hab : (a : S) * b = 1 - (π : S) * c := by
    have e := congrArg Subtype.val hcd
    push_cast at e
    linear_combination -e
  have htΛ : t ∈ Λ := by
    apply hcl
    intro n
    refine ⟨(b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i,
      Λ.mul_mem hbΛ (Λ.sum_mem fun i _ => Λ.pow_mem (Λ.mul_mem π.2 c.2) i), ?_⟩
    have g := mul_neg_geom_sum ((π : S) * c) n
    have e : t - (b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i = t * ((π : S) * c) ^ n := by
      linear_combination ((b : S) * ∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * ht
        - t * (∑ i ∈ Finset.range n, ((π : S) * c) ^ i) * hab - t * g
    rw [e]
    exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow (Ideal.mul_mem_right _ _ hπm) n)
  exact isUnit_iff_exists_inv.2 ⟨⟨t, htΛ⟩, Subtype.ext ht⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, fun a _ => by simp⟩`. Consider the case `succ k ih`. Take `⟨N, hN⟩` from `ih`. Establish `hne : ((π ^ k : Λ) : S) ≠ 0`.

Use `push_cast`. Conclude with `pow_ne_zero _ hπ0`. Choose the witnesses or unpack the hypotheses as in `⟨M, hM⟩ : ∃ M, ((π ^ k : Λ) : S) ∉ maximalIdeal S ^ M := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hne (eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ h)`. Use `⟨max N M, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `hN a (Ideal.pow_le_pow_right (le_max_left _ _) ha)`. Rewrite using `[pow_succ]`. Use `mul_dvd_mul_left _ ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hu`. Establish `hunit : IsUnit u` using `isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl u fun h => hu (hdiv u h)`. Apply `hM` to reduce the goal to its premises. Establish `e : π ^ k = (π ^ k * u) * ↑hunit.unit⁻¹`. Rewrite using `[mul_assoc, hunit.mul_val_inv, mul_one]`.

Rewrite using `[e, Subring.coe_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (le_max_right _ _) ha)`.
-/
private theorem exists_pow_dvd_of_mem_maximalIdeal_pow {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    (Λ : Subring S) (π : Λ) (hπ0 : (π : S) ≠ 0) (hπm : (π : S) ∈ maximalIdeal S)
    (hc : IsAdicComplete (maximalIdeal S) S)
    (hres : ∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S)
    (hdiv : ∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a)
    (hcl : ∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ)
    (k : ℕ) : ∃ N : ℕ, ∀ a : Λ, (a : S) ∈ maximalIdeal S ^ N → π ^ k ∣ a := by
  induction k with
  | zero => exact ⟨0, fun a _ => by simp⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    have hne : ((π ^ k : Λ) : S) ≠ 0 := by
      push_cast
      exact pow_ne_zero _ hπ0
    obtain ⟨M, hM⟩ : ∃ M, ((π ^ k : Λ) : S) ∉ maximalIdeal S ^ M := by
      by_contra h
      push_neg at h
      exact hne (eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ h)
    refine ⟨max N M, fun a ha => ?_⟩
    obtain ⟨u, rfl⟩ := hN a (Ideal.pow_le_pow_right (le_max_left _ _) ha)
    rw [pow_succ]
    refine mul_dvd_mul_left _ ?_
    by_contra hu
    have hunit : IsUnit u := isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl u fun h => hu (hdiv u h)
    apply hM
    have e : π ^ k = (π ^ k * u) * ↑hunit.unit⁻¹ := by
      rw [mul_assoc, hunit.mul_val_inv, mul_one]
    rw [e, Subring.coe_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (le_max_right _ _) ha)

/- English proof (translation)
Introduce `S _ _ _ Λ π hπ0 hπm hc hres hdiv hcl`. Establish `hunit : ∀ a : Λ, IsUnit a ↔ (a : S) ∉ maximalIdeal S` using `fun a => ⟨fun h hm => (IsLocalRing.mem_maximalIdeal _).1 hm (h.map Λ.subtype), isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl a⟩`. Establish `hsep : ∀ x : Λ, (∀ n : ℕ, π ^ n ∣ x) → x = 0`. Introduce `x hx`. Establish `: (x : S) = 0`.

Use `eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ fun n => ?_` and prove the remaining obligations. Take `⟨c, hc'⟩` from `hx n`. Rewrite using `[hc', Subring.coe_mul, Subring.coe_pow]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm n)`. Conclude with `this` after adjusting the coercions.

Establish `hirr : Irreducible π`. Use `⟨fun h => (hunit π).1 h hπm, fun ⦃a b⦄ hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨ha, hb⟩` from `hne`.

Rewrite `ha`, `hb` using `[hunit, not_not]`. Take `⟨x, rfl⟩` from `hdiv a ha`. Take `⟨y, rfl⟩` from `hdiv b hb`. Establish `h0 : π * (1 - π * (x * y)) = 0` using `by linear_combination hab`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases.

Conclude with `hπ0 (by rw [h]; rfl)`. Conclude with `(hunit π).1 (isUnit_iff_exists_inv.2 ⟨x * y, by linear_combination -h⟩) hπm`. Establish `hfac : ∀ {x : Λ}, x ≠ 0 → ∃ n : ℕ, Associated (π ^ n) x`. Introduce `x hx`. Establish `hex : ∃ n, ¬ π ^ n ∣ x`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx (hsep x h)`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk, hk1⟩ : ∃ k, π ^ k ∣ x ∧ ¬ π ^ (k + 1) ∣ x := by`. Establish `h0 : Nat.find hex ≠ 0`.

Introduce `h`. Use `Nat.find_spec hex` as an intermediate fact. Rewrite `this` using `[h, pow_zero]`. Conclude with `this (one_dvd x)`. Take `⟨k, hk⟩` from `Nat.exists_eq_succ_of_ne_zero h0`.

Use `⟨k, not_not.1 (Nat.find_min hex (by omega)), ?_⟩` and prove the remaining obligations. Rewrite using `[← Nat.succ_eq_add_one, ← hk]`. Conclude with `Nat.find_spec hex`. Take `⟨u, rfl⟩` from `hk`. Establish `hu : IsUnit u` using `(hunit u).2 fun hm => hk1 (by`.

Rewrite using `[pow_succ]`. Conclude with `mul_dvd_mul_left _ (hdiv u hm))`. Conclude with `⟨k, hu.unit, by rw [hu.unit_spec]⟩`. Establish `hdvr : IsDiscreteValuationRing Λ` using `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, hfac⟩`. Establish `hmax : maximalIdeal Λ = Ideal.span {π}`.

Use extensionality with `x`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not, Ideal.mem_span_singleton]`. Use `⟨hdiv x, fun ⟨c, hc'⟩ => ?_⟩` and prove the remaining obligations. Rewrite using `[hc', Subring.coe_mul]`. Conclude with `Ideal.mul_mem_right _ _ hπm`.

Use `⟨hdvr, hmax, ?_⟩` and prove the remaining obligations. Rewrite using `[hmax]`. Establish `hmem : ∀ (n : ℕ) (y : Λ), y ∈ (Ideal.span {π}) ^ n • (⊤ : Submodule Λ Λ) ↔ π ^ n ∣ y`. Introduce `n y`. Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Use `{ haus' := ?_, prec' := ?_ }` and prove the remaining obligations. Introduce `x hx`. Use `hsep x fun n => ?_` and prove the remaining obligations. Use `hx n` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, sub_zero, hmem]`. Then use the resulting hypothesis.

Introduce `f hf`. Establish `hfS : ∀ {a b : ℕ}, a ≤ b → (f a : S) - f b ∈ maximalIdeal S ^ a`. Introduce `a b hab`. Use `hf hab` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, hmem]`.

Take `⟨c, hc'⟩` from `this`. Establish `e` using `congrArg Subtype.val hc'`. Move the coercions through the operations in `at e`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm a)`.

Take `⟨L, hL⟩` from `exists_limit_of_isAdicComplete _ hc (fun n => (f n : S)) hfS`. Establish `hLΛ : L ∈ Λ` using `hcl L fun n => ⟨f n, (f n).2, by`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem (hL n)⟩`. Use `⟨⟨L, hLΛ⟩, fun n => ?_⟩` and prove the remaining obligations.

Rewrite using `[SModEq.sub_mem, hmem]`. Take `⟨N, hN⟩` from `exists_pow_dvd_of_mem_maximalIdeal_pow Λ π hπ0 hπm hc hres hdiv hcl n`. Establish `h1 : π ^ n ∣ f n - f (max n N)`. Use `hf (le_max_left n N)` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, hmem]`. Then use the resulting hypothesis.

Establish `h2 : π ^ n ∣ f (max n N) - ⟨L, hLΛ⟩` using `hN _ (by`. Use `push_cast`. Conclude with `Ideal.pow_le_pow_right (le_max_right n N) (hL _))`. Use `dvd_add h1 h2` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem isDVR_of_closed_subring_principal :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (Λ : Subring S) (π : Λ), (π : S) ≠ 0 → (π : S) ∈ maximalIdeal S → IsAdicComplete (maximalIdeal S) S → (∀ s : S, ∃ a ∈ Λ, s - a ∈ maximalIdeal S) → (∀ a : Λ, (a : S) ∈ maximalIdeal S → π ∣ a) → (∀ s : S, (∀ n : ℕ, ∃ a ∈ Λ, s - a ∈ maximalIdeal S ^ n) → s ∈ Λ) → ∃ _ : IsDiscreteValuationRing Λ, maximalIdeal Λ = Ideal.span {π} ∧ IsAdicComplete (maximalIdeal Λ) Λ := by
  intro S _ _ _ Λ π hπ0 hπm hc hres hdiv hcl
  have hunit : ∀ a : Λ, IsUnit a ↔ (a : S) ∉ maximalIdeal S := fun a =>
    ⟨fun h hm => (IsLocalRing.mem_maximalIdeal _).1 hm (h.map Λ.subtype),
      isUnit_of_not_mem_maximalIdeal_of_closed Λ π hπm hres hdiv hcl a⟩
  have hsep : ∀ x : Λ, (∀ n : ℕ, π ^ n ∣ x) → x = 0 := by
    intro x hx
    have : (x : S) = 0 := by
      refine eq_zero_of_forall_mem_pow_of_isAdicComplete _ hc _ fun n => ?_
      obtain ⟨c, hc'⟩ := hx n
      rw [hc', Subring.coe_mul, Subring.coe_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm n)
    exact_mod_cast this
  have hirr : Irreducible π := by
    refine ⟨fun h => (hunit π).1 h hπm, fun ⦃a b⦄ hab => ?_⟩
    by_contra hne
    push_neg at hne
    obtain ⟨ha, hb⟩ := hne
    rw [hunit, not_not] at ha hb
    obtain ⟨x, rfl⟩ := hdiv a ha
    obtain ⟨y, rfl⟩ := hdiv b hb
    have h0 : π * (1 - π * (x * y)) = 0 := by linear_combination hab
    rcases mul_eq_zero.1 h0 with h | h
    · exact hπ0 (by rw [h]; rfl)
    · exact (hunit π).1 (isUnit_iff_exists_inv.2 ⟨x * y, by linear_combination -h⟩) hπm
  have hfac : ∀ {x : Λ}, x ≠ 0 → ∃ n : ℕ, Associated (π ^ n) x := by
    intro x hx
    have hex : ∃ n, ¬ π ^ n ∣ x := by
      by_contra h
      push_neg at h
      exact hx (hsep x h)
    classical
    obtain ⟨k, hk, hk1⟩ : ∃ k, π ^ k ∣ x ∧ ¬ π ^ (k + 1) ∣ x := by
      have h0 : Nat.find hex ≠ 0 := by
        intro h
        have := Nat.find_spec hex
        rw [h, pow_zero] at this
        exact this (one_dvd x)
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero h0
      refine ⟨k, not_not.1 (Nat.find_min hex (by omega)), ?_⟩
      rw [← Nat.succ_eq_add_one, ← hk]
      exact Nat.find_spec hex
    obtain ⟨u, rfl⟩ := hk
    have hu : IsUnit u := (hunit u).2 fun hm => hk1 (by
      rw [pow_succ]
      exact mul_dvd_mul_left _ (hdiv u hm))
    exact ⟨k, hu.unit, by rw [hu.unit_spec]⟩
  have hdvr : IsDiscreteValuationRing Λ :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization ⟨π, hirr, hfac⟩
  have hmax : maximalIdeal Λ = Ideal.span {π} := by
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit, not_not, Ideal.mem_span_singleton]
    refine ⟨hdiv x, fun ⟨c, hc'⟩ => ?_⟩
    rw [hc', Subring.coe_mul]
    exact Ideal.mul_mem_right _ _ hπm
  refine ⟨hdvr, hmax, ?_⟩
  rw [hmax]
  have hmem : ∀ (n : ℕ) (y : Λ), y ∈ (Ideal.span {π}) ^ n • (⊤ : Submodule Λ Λ) ↔ π ^ n ∣ y := by
    intro n y
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    refine hsep x fun n => ?_
    have := hx n
    rwa [SModEq.sub_mem, sub_zero, hmem] at this
  · intro f hf
    have hfS : ∀ {a b : ℕ}, a ≤ b → (f a : S) - f b ∈ maximalIdeal S ^ a := by
      intro a b hab
      have := hf hab
      rw [SModEq.sub_mem, hmem] at this
      obtain ⟨c, hc'⟩ := this
      have e := congrArg Subtype.val hc'
      push_cast at e
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπm a)
    obtain ⟨L, hL⟩ := exists_limit_of_isAdicComplete _ hc (fun n => (f n : S)) hfS
    have hLΛ : L ∈ Λ := hcl L fun n => ⟨f n, (f n).2, by
      rw [← neg_sub]
      exact neg_mem (hL n)⟩
    refine ⟨⟨L, hLΛ⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, hmem]
    obtain ⟨N, hN⟩ := exists_pow_dvd_of_mem_maximalIdeal_pow Λ π hπ0 hπm hc hres hdiv hcl n
    have h1 : π ^ n ∣ f n - f (max n N) := by
      have := hf (le_max_left n N)
      rwa [SModEq.sub_mem, hmem] at this
    have h2 : π ^ n ∣ f (max n N) - ⟨L, hLΛ⟩ := hN _ (by
      push_cast
      exact Ideal.pow_le_pow_right (le_max_right n N) (hL _))
    have := dvd_add h1 h2
    rwa [sub_add_sub_cancel] at this

end GlobalTheory
