import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem deep_smod_iff {O : Type} [CommRing O] (π a b : O) (n : ℕ) :
    a ≡ b [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule O O)] ↔ π ^ n ∣ a - b := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]

/- English proof (translation)
Set `T : O → O` to `fun x => y - π * h.eval x`. Establish `hT : ∀ (n : ℕ) (a b : O), π ^ n ∣ a - b → π ^ (n + 1) ∣ T a - T b`. Introduce `n a b hab`. Establish `h1 : π ^ n ∣ h.eval a - h.eval b` using `hab.trans (Polynomial.sub_dvd_eval_sub a b h)`. Take `⟨c, hc⟩` from `h1`.

Use `⟨-c, ?_⟩` and prove the remaining obligations. Simplify using `only [T]`. Take the linear combination `(-π) * hc`. Set `s : ℕ → O` to `fun n => T^[n] 0`. Establish `hs : ∀ n, s (n + 1) = T (s n)` using `fun n => Function.iterate_succ_apply' T n 0`.

Establish `h1 : ∀ n, π ^ n ∣ s n - s (n + 1)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use `hT n _ _ ih` as an intermediate fact. Rewrite `this` using `[← hs, ← hs]`. Then use the resulting hypothesis. Establish `h2 : ∀ m n, m ≤ n → π ^ m ∣ s m - s n`. Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `dvd_add ih ((pow_dvd_pow π hmn).trans (h1 n))` as an intermediate fact. Simplify using `using this`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := Ideal.span {π}) (M := O) inferInstance (f := s) (fun {m n} hmn => (deep_smod_iff π _ _ m).2 (h2 m n hmn))`.

Establish `hL' : ∀ n, π ^ n ∣ s n - L` using `fun n => (deep_smod_iff π _ _ n).1 (hL n)`. Establish `h0 : L - T L = 0`. Use `IsHausdorff.haus (I := Ideal.span {π}) (M := O) inferInstance _ (fun n => ?_)` and prove the remaining obligations. Rewrite using `[deep_smod_iff]`. Establish `a1` using `hT n _ _ (hL' n)`.

Rewrite `a1` using `[← hs]`. Establish `a2` using `dvd_sub a1 (hL' (n + 1))`. Establish `a3` using `(pow_dvd_pow π (Nat.le_succ n)).trans a2`. Use `a3 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.

Use `⟨L, ?_⟩` and prove the remaining obligations. Simplify using `only [T] at h0`. Take the linear combination `h0`.
-/
theorem deep_exists_solution {O : Type} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (h : O[X]) (y : O) :
    ∃ x : O, x + π * h.eval x = y := by
  let T : O → O := fun x => y - π * h.eval x
  have hT : ∀ (n : ℕ) (a b : O), π ^ n ∣ a - b → π ^ (n + 1) ∣ T a - T b := by
    intro n a b hab
    have h1 : π ^ n ∣ h.eval a - h.eval b := hab.trans (Polynomial.sub_dvd_eval_sub a b h)
    obtain ⟨c, hc⟩ := h1
    refine ⟨-c, ?_⟩
    simp only [T]
    linear_combination (-π) * hc
  let s : ℕ → O := fun n => T^[n] 0
  have hs : ∀ n, s (n + 1) = T (s n) := fun n => Function.iterate_succ_apply' T n 0
  have h1 : ∀ n, π ^ n ∣ s n - s (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hT n _ _ ih
      rwa [← hs, ← hs] at this
  have h2 : ∀ m n, m ≤ n → π ^ m ∣ s m - s n := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := dvd_add ih ((pow_dvd_pow π hmn).trans (h1 n))
      simpa using this
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {π}) (M := O) inferInstance (f := s)
    (fun {m n} hmn => (deep_smod_iff π _ _ m).2 (h2 m n hmn))
  have hL' : ∀ n, π ^ n ∣ s n - L := fun n => (deep_smod_iff π _ _ n).1 (hL n)
  have h0 : L - T L = 0 := by
    refine IsHausdorff.haus (I := Ideal.span {π}) (M := O) inferInstance _ (fun n => ?_)
    rw [deep_smod_iff]
    have a1 := hT n _ _ (hL' n)
    rw [← hs] at a1
    have a2 := dvd_sub a1 (hL' (n + 1))
    have a3 := (pow_dvd_pow π (Nat.le_succ n)).trans a2
    convert a3 using 1
    ring
  refine ⟨L, ?_⟩
  simp only [T] at h0
  linear_combination h0

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ n ih`. Take `⟨g, hg⟩` from `ih`. Use `⟨g * (1 + C t * X) + C (n : O), fun x => ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ, hg]`. Simplify using `only [eval_add, eval_mul, eval_one, eval_C, eval_X, Nat.cast_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deep_binomial {O : Type} [CommRing O] (t : O) (n : ℕ) :
    ∃ g : O[X], ∀ x : O, (1 + t * x) ^ n = 1 + n * t * x + t ^ 2 * x ^ 2 * g.eval x := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨g * (1 + C t * X) + C (n : O), fun x => ?_⟩
    rw [pow_succ, hg]
    simp only [eval_add, eval_mul, eval_one, eval_C, eval_X, Nat.cast_succ]
    ring

/- English proof (translation)
Rewrite using `[oneUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]`. Establish `: ((Ideal.Quotient.mk (Ideal.span {t}) : O →* O ⧸ Ideal.span {t}) (u : O) = 1) ↔ Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1` using `Iff.rfl`. Rewrite using `[this, Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx⟩`.

Conclude with `⟨x, by linear_combination hx⟩`. Introduce and unpack `⟨x, hx⟩`. Conclude with `⟨x, by linear_combination hx⟩`.
-/
theorem deep_mem_oneUnits {O : Type} [CommRing O] (t : O) (u : Oˣ) :
    u ∈ oneUnits t ↔ ∃ x : O, (u : O) = 1 + t * x := by
  rw [oneUnits, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
  have : ((Ideal.Quotient.mk (Ideal.span {t}) : O →* O ⧸ Ideal.span {t}) (u : O) = 1) ↔
      Ideal.Quotient.mk (Ideal.span {t}) (u : O) = Ideal.Quotient.mk (Ideal.span {t}) 1 := Iff.rfl
  rw [this, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by linear_combination hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by linear_combination hx⟩

/- English proof (translation)
Establish `h : π ∈ (⊥ : Ideal O).jacobson` using `IsAdicComplete.le_jacobson_bot (Ideal.span {π}) (Ideal.mem_span_singleton_self π)`. Use `Ideal.mem_jacobson_bot.1 h x` as an intermediate fact. Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis.
-/
theorem deep_isUnit {O : Type} [CommRing O] (π : O)
    [IsAdicComplete (Ideal.span {π}) O] (x : O) : IsUnit (1 + π * x) := by
  have h : π ∈ (⊥ : Ideal O).jacobson :=
    IsAdicComplete.le_jacobson_bot (Ideal.span {π}) (Ideal.mem_span_singleton_self π)
  have := Ideal.mem_jacobson_bot.1 h x
  rwa [add_comm] at this

/- English proof (translation)
Introduce `p O _ _ _ π hp hπ hc`. Take `⟨g, hg⟩` from `deep_binomial ((p : O) * π) p`. Establish `key : ∀ x : O, (1 + (p : O) * π * x) ^ p = 1 + (p : O) ^ 2 * π * (x + π * (X ^ 2 * g).eval x)`. Introduce `x`. Rewrite using `[hg]`.

Simplify using `only [eval_mul, eval_pow, eval_X]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp0 : (p : O) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne'`. Prove the components needed by the constructor for the conclusion. Use extensionality with `u`.

Rewrite using `[pows, Subgroup.mem_map, deep_mem_oneUnits]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, rfl⟩`. Take `⟨x, hx⟩` from `(deep_mem_oneUnits _ _).1 hv`. Conclude with `⟨_, by rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hx, key]⟩`.

Introduce and unpack `⟨y, hy⟩`. Take `⟨x, hx⟩` from `deep_exists_solution π (X ^ 2 * g) y`. Take `⟨v, hv⟩` from `deep_isUnit π ((p : O) * x)`. Establish `hv' : (v : O) = 1 + (p : O) * π * x` using `by rw [hv]; ring`. Use `⟨v, (deep_mem_oneUnits _ _).2 ⟨x, hv'⟩, Units.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[powMonoidHom_apply, Units.val_pow_eq_pow_val, hv', key, hx, hy]`. Rewrite using `[pTor, Nat.card_eq_one_iff_exists]`. Use `⟨⟨1, one_mem _, one_pow _⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨u, hu, hu1⟩`. Take `⟨x, hx⟩` from `(deep_mem_oneUnits _ _).1 hu`.

Establish `h1 : (u : O) ^ p = 1` using `by rw [← Units.val_pow_eq_pow_val, hu1, Units.val_one]`. Rewrite `h1` using `[hx, key]`. Establish `h2 : (p : O) ^ 2 * π * (x * (1 + π * (x * g.eval x))) = 0`. Simplify using `only [eval_mul, eval_pow, eval_X] at h1`. Take the linear combination `h1`.

Establish `h3 : x = 0`. Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `absurd h (mul_ne_zero (pow_ne_zero _ hp0) hπ)`. Conclude with `(mul_eq_zero.1 h).resolve_right (deep_isUnit π _).ne_zero`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations.

Simplify using `[hx, h3]`.
-/
theorem deep_units_pows :
    ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [CharZero O] (π : O), 0 < p → π ≠ 0 →
      IsAdicComplete (Ideal.span {π}) O →
      pows p (oneUnits ((p : O) * π)) = oneUnits ((p : O) ^ 2 * π) ∧
        pTor p (oneUnits ((p : O) * π)) = 1 := by
  intro p O _ _ _ π hp hπ hc
  obtain ⟨g, hg⟩ := deep_binomial ((p : O) * π) p
  have key : ∀ x : O, (1 + (p : O) * π * x) ^ p =
      1 + (p : O) ^ 2 * π * (x + π * (X ^ 2 * g).eval x) := by
    intro x
    rw [hg]
    simp only [eval_mul, eval_pow, eval_X]
    ring
  have hp0 : (p : O) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  constructor
  · ext u
    rw [pows, Subgroup.mem_map, deep_mem_oneUnits]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨x, hx⟩ := (deep_mem_oneUnits _ _).1 hv
      exact ⟨_, by rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hx, key]⟩
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := deep_exists_solution π (X ^ 2 * g) y
      obtain ⟨v, hv⟩ := deep_isUnit π ((p : O) * x)
      have hv' : (v : O) = 1 + (p : O) * π * x := by rw [hv]; ring
      refine ⟨v, (deep_mem_oneUnits _ _).2 ⟨x, hv'⟩, Units.ext ?_⟩
      rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, hv', key, hx, hy]
  · rw [pTor, Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, one_mem _, one_pow _⟩, ?_⟩
    rintro ⟨u, hu, hu1⟩
    obtain ⟨x, hx⟩ := (deep_mem_oneUnits _ _).1 hu
    have h1 : (u : O) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hu1, Units.val_one]
    rw [hx, key] at h1
    have h2 : (p : O) ^ 2 * π * (x * (1 + π * (x * g.eval x))) = 0 := by
      simp only [eval_mul, eval_pow, eval_X] at h1
      linear_combination h1
    have h3 : x = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h (mul_ne_zero (pow_ne_zero _ hp0) hπ)
      · exact (mul_eq_zero.1 h).resolve_right (deep_isUnit π _).ne_zero
    refine Subtype.ext (Units.ext ?_)
    simp [hx, h3]

end GlobalTheory.CNorm
