import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplFlat

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Use `⟨fun f hf => ?_⟩` and prove the remaining obligations. Simplify using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢`. Establish `h1 : ∀ n, ∃ d ∈ I ^ n, g d = f (n + 1) - f n`. Introduce `n`. Use `(((I.map g) ^ n).neg_mem (hf (Nat.le_succ n)))` as an intermediate fact.

Rewrite `this` using `[neg_sub, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective g hg]`. Conclude with `this`. Use `choose d hd hgd using h1`. Take `⟨b0, hb0⟩` from `hg (f 0)`. Set `u : ℕ → B` to `fun n => b0 + ∑ i ∈ Finset.range n, d i`.

Establish `hu : ∀ n, g (u n) = f n`. Introduce `n`. Simplify using `only [u, map_add, map_sum, hgd, hb0, Finset.sum_range_sub]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : ∀ {m n}, m ≤ n → u m ≡ u n [SMOD (I ^ m • ⊤ : Submodule B B)]`.

Introduce `m n hmn`. Simplify using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ k hk ih`.

Establish `e : u m - u (k + 1) = (u m - u k) - d k`. Simplify using `only [u, Finset.sum_range_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hk (hd k))`.

Take `⟨L, hL⟩` from `hB.prec hc`. Use `⟨g L, fun n => ?_⟩` and prove the remaining obligations. Use `hL n` as an intermediate fact. Simplify using `only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this`. Rewrite using `[← hu, ← map_sub, ← Ideal.map_pow]`.

Conclude with `Ideal.mem_map_of_mem _ this`.
-/
private theorem prec_of_surj {B C : Type} [CommRing B] [CommRing C] (g : B →+* C)
    (I : Ideal B) [hB : IsPrecomplete I B] (hg : Function.Surjective g) :
    IsPrecomplete (I.map g) C := by
  refine ⟨fun f hf => ?_⟩
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hf ⊢
  have h1 : ∀ n, ∃ d ∈ I ^ n, g d = f (n + 1) - f n := by
    intro n
    have := (((I.map g) ^ n).neg_mem (hf (Nat.le_succ n)))
    rw [neg_sub, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective g hg] at this
    exact this
  choose d hd hgd using h1
  obtain ⟨b0, hb0⟩ := hg (f 0)
  let u : ℕ → B := fun n => b0 + ∑ i ∈ Finset.range n, d i
  have hu : ∀ n, g (u n) = f n := by
    intro n
    simp only [u, map_add, map_sum, hgd, hb0, Finset.sum_range_sub]
    ring
  have hc : ∀ {m n}, m ≤ n → u m ≡ u n [SMOD (I ^ m • ⊤ : Submodule B B)] := by
    intro m n hmn
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      have e : u m - u (k + 1) = (u m - u k) - d k := by
        simp only [u, Finset.sum_range_succ]; ring
      rw [e]
      exact Ideal.sub_mem _ ih (Ideal.pow_le_pow_right hk (hd k))
  obtain ⟨L, hL⟩ := hB.prec hc
  refine ⟨g L, fun n => ?_⟩
  have := hL n
  simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← hu, ← map_sub, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ this

/- English proof (translation)
Establish `hp` using `h.isPrime`. Establish `h1 : (1 : R) ∉ p` using `(Ideal.ne_top_iff_one _).1 hp.ne_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`.

Conclude with `⟨i, hi, 1, h1, by simp⟩`. Consider the case `zero => exact ⟨0, I.zero_mem, 1, h1, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨i, hi, s, hs, hx⟩` from `hx`. Take `⟨j, hj, t, ht, hy⟩` from `hy`.

Use `⟨t * i + s * j, I.add_mem (I.mul_mem_left _ hi) (I.mul_mem_left _ hj), s * t, fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩` and prove the remaining obligations. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t) hx) (Ideal.mul_mem_left _ (algebraMap R B s) hy)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `smul b x _ hx`. Take `⟨i, hi, s, hs, hx⟩` from `hx`. Take `⟨a, t, ht, hb⟩` from `h.dense n b`. Use `⟨a * i, I.mul_mem_left _ hi, s * t, fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩` and prove the remaining obligations. Use `Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t * b) hx) (Ideal.mul_mem_left _ (algebraMap R B i) hb)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem approx_map {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) (I : Ideal R) (n : ℕ) (x : B)
    (hx : x ∈ I.map (algebraMap R B)) :
    ∃ i ∈ I, ∃ s : R, s ∉ p ∧ algebraMap R B s * x - algebraMap R B i ∈ maximalIdeal B ^ n := by
  have hp := h.isPrime
  have h1 : (1 : R) ∉ p := (Ideal.ne_top_iff_one _).1 hp.ne_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, hi, 1, h1, by simp⟩
  | zero => exact ⟨0, I.zero_mem, 1, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨j, hj, t, ht, hy⟩ := hy
    refine ⟨t * i + s * j, I.add_mem (I.mul_mem_left _ hi) (I.mul_mem_left _ hj), s * t,
      fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t) hx)
      (Ideal.mul_mem_left _ (algebraMap R B s) hy)
    convert this using 1
    simp only [map_add, map_mul]; ring
  | smul b x _ hx =>
    obtain ⟨i, hi, s, hs, hx⟩ := hx
    obtain ⟨a, t, ht, hb⟩ := h.dense n b
    refine ⟨a * i, I.mul_mem_left _ hi, s * t, fun hst => (hp.mem_or_mem hst).elim hs ht, ?_⟩
    have := Ideal.add_mem _ (Ideal.mul_mem_left _ (algebraMap R B t * b) hx)
      (Ideal.mul_mem_left _ (algebraMap R B i) hb)
    convert this using 1
    simp only [map_mul, smul_eq_mul]; ring

/- English proof (translation)
Introduce `R _ _ p B _ _ _ S _ _ q C _ _ _ _ _ _ _ h hRS hq hBC hker`. Use `haveI := h.noeth`. Use `haveI := h.complete`. Establish `hp` using `h.isPrime`. Establish `hN : IsNoetherianRing C` using `isNoetherianRing_of_surjective B C (algebraMap B C) hBC`.

Use `haveI hloc : IsLocalHom (algebraMap B C) := IsLocalHom.of_surjective _ hBC`. Establish `hm : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C` using `IsLocalRing.map_maximalIdeal_of_surjective _ hBC`. Establish `hsq : ∀ r : R, algebraMap S C (algebraMap R S r) = algebraMap B C (algebraMap R B r)`. Introduce `r`. Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Establish `hqp : ∀ r : R, algebraMap R S r ∈ q ↔ r ∈ p`. Introduce `r`. Rewrite using `[← hq, Ideal.mem_comap]`. Establish `hpre : IsPrecomplete (maximalIdeal C) C` using `hm ▸ prec_of_surj (algebraMap B C) _ hBC`. Use `⟨hN, {}, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Take `⟨r, rfl⟩` from `hRS x`. Rewrite using `[hqp, ← h.comap_eq, Ideal.mem_comap, Ideal.mem_comap, hsq, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]`. Introduce `n c`. Take `⟨b, rfl⟩` from `hBC c`.

Take `⟨a, s, hs, hab⟩` from `h.dense n b`. Use `⟨algebraMap R S a, algebraMap R S s, fun hh => hs ((hqp s).1 hh), ?_⟩` and prove the remaining obligations. Rewrite using `[hsq, hsq, ← map_mul, ← map_sub, ← hm, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hab`. Introduce `n x hx`.

Take `⟨a, rfl⟩` from `hRS x`. Rewrite `hx` using `[hsq, ← hm, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hBC]`. Take `⟨y, hy, hya⟩` from `hx`. Establish `hk : algebraMap R B a - y ∈ RingHom.ker (algebraMap B C)`. Rewrite using `[RingHom.mem_ker, map_sub, hya, sub_self]`.

Rewrite `hk` using `[hker]`. Take `⟨i, hi, s, hs, hsi⟩` from `approx_map h _ n _ hk`. Establish `h2 : algebraMap R B (s * a - i) ∈ maximalIdeal B ^ n`. Use `Ideal.add_mem _ hsi (Ideal.mul_mem_left _ (algebraMap R B s) hy)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [map_sub, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht, hta⟩` from `h.strict n _ h2`. Use `⟨algebraMap R S (t * s), fun hh => (hp.mem_or_mem ((hqp _).1 hh)).elim ht hs, ?_⟩` and prove the remaining obligations. Establish `h3 : algebraMap R S (t * (s * a - i)) ∈ q ^ n`.

Use `Ideal.mem_map_of_mem (algebraMap R S) hta` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ n this` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap, hq]`. Rewrite `hi` using `[RingHom.mem_ker]`.

Use `h3 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_sub, map_mul, hi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.AlgebraTools.IsCplAt.quotient :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (S : Type) [CommRing S] [Algebra R S] (q : Ideal S) (C : Type) [CommRing C] [IsLocalRing C]
      [Algebra S C] [Algebra B C] [Algebra R C] [IsScalarTower R S C] [IsScalarTower R B C],
      IsCplAt R p B → Function.Surjective (algebraMap R S) → q.comap (algebraMap R S) = p →
      Function.Surjective (algebraMap B C) →
      RingHom.ker (algebraMap B C) = (RingHom.ker (algebraMap R S)).map (algebraMap R B) → IsCplAt S q C := by
  intro R _ _ p B _ _ _ S _ _ q C _ _ _ _ _ _ _ h hRS hq hBC hker
  haveI := h.noeth
  haveI := h.complete
  have hp := h.isPrime
  have hN : IsNoetherianRing C := isNoetherianRing_of_surjective B C (algebraMap B C) hBC
  haveI hloc : IsLocalHom (algebraMap B C) := IsLocalHom.of_surjective _ hBC
  have hm : (maximalIdeal B).map (algebraMap B C) = maximalIdeal C :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hBC
  have hsq : ∀ r : R, algebraMap S C (algebraMap R S r) = algebraMap B C (algebraMap R B r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hqp : ∀ r : R, algebraMap R S r ∈ q ↔ r ∈ p := by
    intro r; rw [← hq, Ideal.mem_comap]
  have hpre : IsPrecomplete (maximalIdeal C) C := hm ▸ prec_of_surj (algebraMap B C) _ hBC
  refine ⟨hN, {}, ?_, ?_, ?_⟩
  · ext x
    obtain ⟨r, rfl⟩ := hRS x
    rw [hqp, ← h.comap_eq, Ideal.mem_comap, Ideal.mem_comap, hsq, mem_maximalIdeal,
      mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]
  · intro n c
    obtain ⟨b, rfl⟩ := hBC c
    obtain ⟨a, s, hs, hab⟩ := h.dense n b
    refine ⟨algebraMap R S a, algebraMap R S s, fun hh => hs ((hqp s).1 hh), ?_⟩
    rw [hsq, hsq, ← map_mul, ← map_sub, ← hm, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hab
  · intro n x hx
    obtain ⟨a, rfl⟩ := hRS x
    rw [hsq, ← hm, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ hBC] at hx
    obtain ⟨y, hy, hya⟩ := hx
    have hk : algebraMap R B a - y ∈ RingHom.ker (algebraMap B C) := by
      rw [RingHom.mem_ker, map_sub, hya, sub_self]
    rw [hker] at hk
    obtain ⟨i, hi, s, hs, hsi⟩ := approx_map h _ n _ hk
    have h2 : algebraMap R B (s * a - i) ∈ maximalIdeal B ^ n := by
      have := Ideal.add_mem _ hsi (Ideal.mul_mem_left _ (algebraMap R B s) hy)
      convert this using 1
      simp only [map_sub, map_mul]; ring
    obtain ⟨t, ht, hta⟩ := h.strict n _ h2
    refine ⟨algebraMap R S (t * s), fun hh => (hp.mem_or_mem ((hqp _).1 hh)).elim ht hs, ?_⟩
    have h3 : algebraMap R S (t * (s * a - i)) ∈ q ^ n := by
      have := Ideal.mem_map_of_mem (algebraMap R S) hta
      rw [Ideal.map_pow] at this
      refine Ideal.pow_right_mono ?_ n this
      rw [Ideal.map_le_iff_le_comap, hq]
    rw [RingHom.mem_ker] at hi
    convert h3 using 1
    simp only [map_sub, map_mul, hi]; ring
