import Mathlib

noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up.U3

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap R C) n]`. Conclude with `hv.map_le_one _`.
-/
theorem v_natCast_le_one (hv : v.Integers R) (n : ℕ) : v (n : C) ≤ 1 := by
  rw [← map_natCast (algebraMap R C) n]
  exact hv.map_le_one _

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap R C) n]`. Conclude with `hv.map_le_one _`.
-/
theorem v_intCast_le_one (hv : v.Integers R) (n : ℤ) : v (n : C) ≤ 1 := by
  rw [← map_intCast (algebraMap R C) n]
  exact hv.map_le_one _

/- English proof (translation)
Take `⟨m, rfl⟩` from `h`. Use `push_cast`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem v_intCast_lt_one_of_dvd (hv : v.Integers R) (hpv : v (p : C) < 1) {n : ℤ}
    (h : (p : ℤ) ∣ n) : v (n : C) < 1 := by
  obtain ⟨m, rfl⟩ := h
  push_cast
  rw [map_mul]
  calc v (p : C) * v (m : C) ≤ v (p : C) * 1 :=
        mul_le_mul_of_nonneg_left (v_intCast_le_one hv m) zero_le'
    _ < 1 := by rw [mul_one]; exact hpv

/- English proof (translation)
Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp.out`. Take `⟨a, b, hab⟩` from `(Prime.coprime_iff_not_dvd hpz).mpr h`. Establish `h1 : (a : C) * (p : C) + (b : C) * (n : C) = 1`. Use `congrArg (Int.cast : ℤ → C) hab` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `ha : v ((a : C) * (p : C)) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hb : 1 ≤ v ((b : C) * (n : C))`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use `v.map_add_lt ha hlt` as an intermediate fact. Rewrite `this` using `[h1, map_one]`. Conclude with `lt_irrefl _ this`.

Use `le_antisymm (v_intCast_le_one hv n) ?_` and prove the remaining obligations. Rewrite `hb` using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem v_intCast_eq_one (hv : v.Integers R) (hpv : v (p : C) < 1) {n : ℤ}
    (h : ¬ (p : ℤ) ∣ n) : v (n : C) = 1 := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpz).mpr h
  have h1 : (a : C) * (p : C) + (b : C) * (n : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    exact this
  have ha : v ((a : C) * (p : C)) < 1 := by
    rw [map_mul]
    calc v (a : C) * v (p : C) ≤ 1 * v (p : C) :=
          mul_le_mul_of_nonneg_right (v_intCast_le_one hv a) zero_le'
      _ < 1 := by rw [one_mul]; exact hpv
  have hb : 1 ≤ v ((b : C) * (n : C)) := by
    by_contra hlt
    push_neg at hlt
    have := v.map_add_lt ha hlt
    rw [h1, map_one] at this
    exact lt_irrefl _ this
  refine le_antisymm (v_intCast_le_one hv n) ?_
  rw [map_mul] at hb
  calc 1 ≤ v (b : C) * v (n : C) := hb
    _ ≤ 1 * v (n : C) := mul_le_mul_of_nonneg_right (v_intCast_le_one hv b) zero_le'
    _ = v (n : C) := one_mul _

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h2 : 2 ≤ p` using `hp.out.two_le`. Establish `key : v r ^ 1 < v r ^ p` using `pow_lt_pow_right₀ h (by omega)`. Rewrite `key` using `[pow_one, ← map_pow, hr]`.

Conclude with `lt_irrefl _ key`.
-/
theorem v_le_one_of_pow_eq {r : C} (hr : r ^ p = r) : v r ≤ 1 := by
  by_contra h
  push_neg at h
  have h2 : 2 ≤ p := hp.out.two_le
  have key : v r ^ 1 < v r ^ p := pow_lt_pow_right₀ h (by omega)
  rw [pow_one, ← map_pow, hr] at key
  exact lt_irrefl _ key

/- English proof (translation)
Rewrite using `[← geom_sum₂_mul, map_mul]`. Establish `hS : v (∑ j ∈ range i, r ^ j * s ^ (i - 1 - j)) ≤ 1`. Apply `v.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul, map_pow, map_pow]`.

Conclude with `mul_le_one₀ (pow_le_one₀ zero_le' hr) zero_le' (pow_le_one₀ zero_le' hs)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem v_pow_sub_le {r s : C} (hr : v r ≤ 1) (hs : v s ≤ 1) (i : ℕ) :
    v (r ^ i - s ^ i) ≤ v (r - s) := by
  rw [← geom_sum₂_mul, map_mul]
  have hS : v (∑ j ∈ range i, r ^ j * s ^ (i - 1 - j)) ≤ 1 := by
    apply v.map_sum_le
    intro j _
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one₀ (pow_le_one₀ zero_le' hr) zero_le' (pow_le_one₀ zero_le' hs)
  calc _ ≤ 1 * v (r - s) := mul_le_mul_of_nonneg_right hS zero_le'
    _ = _ := one_mul _

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hd : r - s ≠ 0` using `sub_ne_zero.mpr hne`. Establish `hr1 : v r ≤ 1` using `v_le_one_of_pow_eq hr`. Establish `hs1 : v s ≤ 1` using `v_le_one_of_pow_eq hs`. Take `⟨S, hS⟩ : ∃ S, S = ∑ k ∈ range p, r ^ k * s ^ (p - 1 - k)` from `⟨_, rfl⟩`.

Establish `hSd : S * (r - s) = r - s` using `by rw [hS, geom_sum₂_mul, hr, hs]`. Establish `hS1 : S = 1` using `mul_right_cancel₀ hd (by rw [hSd, one_mul])`. Establish `hconst : ∑ k ∈ range p, s ^ k * s ^ (p - 1 - k) = (p : C) * s ^ (p - 1)`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => s ^ (p - 1)) (fun k hk => by`. Rewrite using `[← pow_add]`.

Use `congr 1`. Use `Finset.mem_range.mp hk` as an intermediate fact. Use the proof step `omega)]`. Simplify using the standard rewrite rules. Establish `hdiff : S - (p : C) * s ^ (p - 1) = ∑ k ∈ range p, (r ^ k - s ^ k) * s ^ (p - 1 - k)`.

Rewrite using `[← hconst, hS, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Establish `hlt1 : v (S - (p : C) * s ^ (p - 1)) < 1`. Rewrite using `[hdiff]`. Apply `v.map_sum_lt one_ne_zero` to reduce the goal to its premises.

Introduce `k _`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hlt2 : v ((p : C) * s ^ (p - 1)) < 1`. Rewrite using `[map_mul, map_pow]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hv : v S < 1`. Use `v.map_add_lt hlt1 hlt2` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Rewrite `hv` using `[hS1, map_one]`.

Conclude with `lt_irrefl _ hv`.
-/
theorem teich_unique (hv : v.Integers R) (hpv : v (p : C) < 1) {r s : C} (hr : r ^ p = r)
    (hs : s ^ p = s) (h : v (r - s) < 1) : r = s := by
  by_contra hne
  have hd : r - s ≠ 0 := sub_ne_zero.mpr hne
  have hr1 : v r ≤ 1 := v_le_one_of_pow_eq hr
  have hs1 : v s ≤ 1 := v_le_one_of_pow_eq hs
  obtain ⟨S, hS⟩ : ∃ S, S = ∑ k ∈ range p, r ^ k * s ^ (p - 1 - k) := ⟨_, rfl⟩
  have hSd : S * (r - s) = r - s := by rw [hS, geom_sum₂_mul, hr, hs]
  have hS1 : S = 1 := mul_right_cancel₀ hd (by rw [hSd, one_mul])
  have hconst : ∑ k ∈ range p, s ^ k * s ^ (p - 1 - k) = (p : C) * s ^ (p - 1) := by
    rw [Finset.sum_congr rfl (g := fun _ => s ^ (p - 1)) (fun k hk => by
      rw [← pow_add]
      congr 1
      have := Finset.mem_range.mp hk
      omega)]
    simp
  have hdiff : S - (p : C) * s ^ (p - 1) = ∑ k ∈ range p, (r ^ k - s ^ k) * s ^ (p - 1 - k) := by
    rw [← hconst, hS, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hlt1 : v (S - (p : C) * s ^ (p - 1)) < 1 := by
    rw [hdiff]
    apply v.map_sum_lt one_ne_zero
    intro k _
    rw [map_mul]
    calc v (r ^ k - s ^ k) * v (s ^ (p - 1 - k)) ≤ v (r ^ k - s ^ k) * 1 :=
          mul_le_mul_of_nonneg_left (by rw [map_pow]; exact pow_le_one₀ zero_le' hs1) zero_le'
      _ ≤ v (r - s) := by rw [mul_one]; exact v_pow_sub_le hr1 hs1 k
      _ < 1 := h
  have hlt2 : v ((p : C) * s ^ (p - 1)) < 1 := by
    rw [map_mul, map_pow]
    calc v (p : C) * v s ^ (p - 1) ≤ v (p : C) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ zero_le' hs1) zero_le'
      _ < 1 := by rw [mul_one]; exact hpv
  have hv : v S < 1 := by
    have := v.map_add_lt hlt1 hlt2
    rwa [sub_add_cancel] at this
  rw [hS1, map_one] at hv
  exact lt_irrefl _ hv

/- English proof (translation)
Establish `hdvd : (p : ℤ) ∣ ((n : ℤ) ^ p - n)`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[ZMod.pow_card, sub_self]`. Establish `hv1 : v ((n : C) ^ p - n) < 1`.

Use `v_intCast_lt_one_of_dvd hv hpv hdvd` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `hmon : (Polynomial.X ^ p - Polynomial.X : Polynomial C).Monic` using `Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp.out.one_lt)`. Establish `heq : (Polynomial.X ^ p - Polynomial.X : Polynomial C) = ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => Polynomial.X - Polynomial.C a)).prod` using `by first`.

Consider the case `exact Polynomial.eq_prod_roots_of_monic_of_splits_id hmon (IsAlgClosed.splits _)`. Consider the case `exact (Polynomial.Monic.eq_prod_roots_of_splits_id hmon (IsAlgClosed.splits _))`. Consider the case `(have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (Polynomial.X ^ p - Polynomial.X : Polynomial C)))`. Rewrite `hc` using `[hmon.leadingCoeff, map_one, one_mul]`. Conclude with `hc.symm)`.

Consider the case `(have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (k := C) (p := Polynomial.X ^ p - Polynomial.X))`. Rewrite `hc` using `[hmon.leadingCoeff, map_one, one_mul]`. Conclude with `hc.symm)`. Establish `heval : (n : C) ^ p - n = ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => (n : C) - a)).prod`. Use `congrArg (Polynomial.eval (n : C)) heq` as an intermediate fact.

Rewrite `this` using `[Polynomial.eval_multiset_prod, Multiset.map_map]`. Simplify `this` using `[Function.comp_def]`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hge : 1 ≤ v ((n : C) ^ p - n)`.

Rewrite using `[heval, map_multiset_prod, Multiset.map_map]`. Apply `Multiset.one_le_prod_of_one_le` to reduce the goal to its premises. Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hx`. Establish `h2` using `(Polynomial.mem_roots hmon.ne_zero).mp ha`.

Rewrite `h2` using `[Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]`. Establish `h3` using `hno a (sub_eq_zero.mp h2)`. Simplify using `only [Function.comp_apply]`. Rewrite using `[Valuation.map_sub_swap]` and apply the resulting hypothesis. Conclude with `absurd hv1 (not_lt.mpr hge)`.
-/
theorem exists_teich [IsAlgClosed C] (hv : v.Integers R) (hpv : v (p : C) < 1) (n : ℕ) :
    ∃ r : C, r ^ p = r ∧ v (r - n) < 1 := by
  have hdvd : (p : ℤ) ∣ ((n : ℤ) ^ p - n) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  have hv1 : v ((n : C) ^ p - n) < 1 := by
    have := v_intCast_lt_one_of_dvd hv hpv hdvd
    push_cast at this
    exact this
  have hmon : (Polynomial.X ^ p - Polynomial.X : Polynomial C).Monic :=
    Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hp.out.one_lt)
  have heq : (Polynomial.X ^ p - Polynomial.X : Polynomial C) =
      ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
    first
    | exact Polynomial.eq_prod_roots_of_monic_of_splits_id hmon (IsAlgClosed.splits _)
    | exact (Polynomial.Monic.eq_prod_roots_of_splits_id hmon (IsAlgClosed.splits _))
    | (have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits (Polynomial.X ^ p - Polynomial.X : Polynomial C)))
       rw [hmon.leadingCoeff, map_one, one_mul] at hc
       exact hc.symm)
    | (have hc := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
          (IsAlgClosed.card_roots_eq_natDegree (k := C) (p := Polynomial.X ^ p - Polynomial.X))
       rw [hmon.leadingCoeff, map_one, one_mul] at hc
       exact hc.symm)
  have heval : (n : C) ^ p - n =
      ((Polynomial.X ^ p - Polynomial.X : Polynomial C).roots.map (fun a => (n : C) - a)).prod := by
    have := congrArg (Polynomial.eval (n : C)) heq
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at this
    simpa [Function.comp_def] using this
  by_contra hno
  push_neg at hno
  have hge : 1 ≤ v ((n : C) ^ p - n) := by
    rw [heval, map_multiset_prod, Multiset.map_map]
    apply Multiset.one_le_prod_of_one_le
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
    have h2 := (Polynomial.mem_roots hmon.ne_zero).mp ha
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h2
    have h3 := hno a (sub_eq_zero.mp h2)
    simp only [Function.comp_apply]
    rwa [Valuation.map_sub_swap]
  exact absurd hv1 (not_lt.mpr hge)

/- English proof (translation)
Use `haveI : NeZero p := ⟨hp.out.ne_zero⟩`. Use `choose ω hω1 hω2 using fun a : ZMod p => exists_teich hv hpv (p := p) a.val`. Establish `hω1' : ∀ a, v (ω a) ≤ 1` using `fun a => v_le_one_of_pow_eq (hω1 a)`. Use `⟨ω, hω1, hω2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `teich_unique hv hpv (hω1 0) (zero_pow hp.out.ne_zero) ?_` and prove the remaining obligations.

Simplify using `using hω2 0`. Use `teich_unique hv hpv (hω1 1) (one_pow _) ?_` and prove the remaining obligations. Use `hω2 1` as an intermediate fact. Rewrite `this` using `[ZMod.val_one, Nat.cast_one]`. Then use the resulting hypothesis. Introduce `a b`.

Use `teich_unique hv hpv (hω1 (a * b)) (by rw [mul_pow, hω1, hω1]) ?_` and prove the remaining obligations. Establish `e4 : v (((a * b).val : C) - (a.val : C) * (b.val : C)) < 1`. Establish `hd : (p : ℤ) ∣ (((a * b).val : ℤ) - (a.val : ℤ) * (b.val : ℤ))`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`.

Simplify using `[ZMod.natCast_zmod_val]`. Use `v_intCast_lt_one_of_dvd hv hpv hd` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`. Establish `e5 : v ((a.val : C) * (b.val : C) - ω a * ω b) < 1`.

Establish `hx : (a.val : C) * b.val - ω a * ω b = -((ω a - a.val) * b.val + ω a * (ω b - b.val))` using `by ring`. Rewrite using `[hx, Valuation.map_neg]`. Apply `v.map_add_lt` to reduce the goal to its premises. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hx : ω (a * b) - ω a * ω b = (ω (a * b) - ((a * b).val : C)) + ((((a * b).val : C) - (a.val : C) * (b.val : C)) + ((a.val : C) * (b.val : C) - ω a * ω b))` using `by ring`. Rewrite using `[hx]`. Conclude with `v.map_add_lt (hω2 (a * b)) (v.map_add_lt e4 e5)`.

Introduce `a b hab`. Use `le_antisymm ((v.map_sub (ω a) (ω b)).trans (max_le (hω1' a) (hω1' b))) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h1 : v ((a.val : C) - (b.val : C)) < 1`.

Establish `hx : (a.val : C) - b.val = -(ω a - a.val) + (ω a - ω b) + (ω b - b.val)` using `by ring`. Rewrite using `[hx]`. Conclude with `v.map_add_lt (v.map_add_lt (by rw [Valuation.map_neg]; exact hω2 a) hlt) (hω2 b)`. Establish `hnd : ¬ (p : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ))`. Introduce `hd`.

Apply `hab` to reduce the goal to its premises. Rewrite `hd` using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hd`. Simplify `hd` using `[sub_eq_zero, ZMod.natCast_zmod_val]`. Use `v_intCast_eq_one hv hpv hnd` as an intermediate fact.

Move the coercions through the operations in `at this`. Rewrite `h1` using `[this]`. Conclude with `lt_irrefl _ h1`.
-/
theorem exists_teichChar [IsAlgClosed C] (hv : v.Integers R) (hpv : v (p : C) < 1) :
    ∃ ω : ZMod p → C, (∀ a, ω a ^ p = ω a) ∧ (∀ a, v (ω a - (a.val : C)) < 1) ∧
      ω 0 = 0 ∧ ω 1 = 1 ∧ (∀ a b, ω (a * b) = ω a * ω b) ∧
      (∀ a b, a ≠ b → v (ω a - ω b) = 1) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  choose ω hω1 hω2 using fun a : ZMod p => exists_teich hv hpv (p := p) a.val
  have hω1' : ∀ a, v (ω a) ≤ 1 := fun a => v_le_one_of_pow_eq (hω1 a)
  refine ⟨ω, hω1, hω2, ?_, ?_, ?_, ?_⟩
  · refine teich_unique hv hpv (hω1 0) (zero_pow hp.out.ne_zero) ?_
    simpa using hω2 0
  · refine teich_unique hv hpv (hω1 1) (one_pow _) ?_
    have := hω2 1
    rwa [ZMod.val_one, Nat.cast_one] at this
  · intro a b
    refine teich_unique hv hpv (hω1 (a * b)) (by rw [mul_pow, hω1, hω1]) ?_
    have e4 : v (((a * b).val : C) - (a.val : C) * (b.val : C)) < 1 := by
      have hd : (p : ℤ) ∣ (((a * b).val : ℤ) - (a.val : ℤ) * (b.val : ℤ)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        simp [ZMod.natCast_zmod_val]
      have := v_intCast_lt_one_of_dvd hv hpv hd
      push_cast at this
      exact this
    have e5 : v ((a.val : C) * (b.val : C) - ω a * ω b) < 1 := by
      have hx : (a.val : C) * b.val - ω a * ω b = -((ω a - a.val) * b.val + ω a * (ω b - b.val)) := by ring
      rw [hx, Valuation.map_neg]
      apply v.map_add_lt
      · rw [map_mul]
        calc _ ≤ v (ω a - a.val) * 1 := mul_le_mul_of_nonneg_left (v_natCast_le_one hv _) zero_le'
          _ < 1 := by rw [mul_one]; exact hω2 a
      · rw [map_mul]
        calc _ ≤ 1 * v (ω b - b.val) := mul_le_mul_of_nonneg_right (hω1' a) zero_le'
          _ < 1 := by rw [one_mul]; exact hω2 b
    have hx : ω (a * b) - ω a * ω b = (ω (a * b) - ((a * b).val : C)) +
        ((((a * b).val : C) - (a.val : C) * (b.val : C)) + ((a.val : C) * (b.val : C) - ω a * ω b)) := by ring
    rw [hx]
    exact v.map_add_lt (hω2 (a * b)) (v.map_add_lt e4 e5)
  · intro a b hab
    refine le_antisymm ((v.map_sub (ω a) (ω b)).trans (max_le (hω1' a) (hω1' b))) ?_
    by_contra hlt
    push_neg at hlt
    have h1 : v ((a.val : C) - (b.val : C)) < 1 := by
      have hx : (a.val : C) - b.val = -(ω a - a.val) + (ω a - ω b) + (ω b - b.val) := by ring
      rw [hx]
      exact v.map_add_lt (v.map_add_lt (by rw [Valuation.map_neg]; exact hω2 a) hlt) (hω2 b)
    have hnd : ¬ (p : ℤ) ∣ ((a.val : ℤ) - (b.val : ℤ)) := by
      intro hd
      apply hab
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
      push_cast at hd
      simpa [sub_eq_zero, ZMod.natCast_zmod_val] using hd
    have := v_intCast_eq_one hv hpv hnd
    push_cast at this
    rw [this] at h1
    exact lt_irrefl _ h1

/- English proof (translation)
Use `haveI : NeZero (p : C) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩`. Take `⟨ζ, hζ⟩` from `IsAlgClosed.exists_root (Polynomial.cyclotomic p C) (by`. Rewrite using `[Polynomial.degree_cyclotomic, Nat.totient_prime hp.out]`. Use `hp.out.two_le` as an intermediate fact. Use `norm_cast`.

Use the proof step `omega)`. Conclude with `⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩`.
-/
theorem exists_primRoot [IsAlgClosed C] [CharZero C] : ∃ ζ : C, IsPrimitiveRoot ζ p := by
  haveI : NeZero (p : C) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p C) (by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime hp.out]
    have := hp.out.two_le
    norm_cast
    omega)
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

/- English proof (translation)
Take `⟨i, -, hi⟩` from `hβ.eq_pow_of_pow_eq_one hα.pow_eq_one`. Establish `hβ1 : v β = 1` using `(pow_eq_one_iff_of_nonneg zero_le' hp.out.ne_zero).mp (by rw [← map_pow, hβ.pow_eq_one, map_one])`. Rewrite using `[← hi]`. Use `v_pow_sub_le (v := v) (r := β) (s := 1) hβ1.le (by rw [map_one]) i` as an intermediate fact. Rewrite `this` using `[one_pow]`. Then use the resulting hypothesis.
-/
theorem val_sub_one_le {α β : C} (hα : IsPrimitiveRoot α p) (hβ : IsPrimitiveRoot β p) :
    v (α - 1) ≤ v (β - 1) := by
  obtain ⟨i, -, hi⟩ := hβ.eq_pow_of_pow_eq_one hα.pow_eq_one
  have hβ1 : v β = 1 :=
    (pow_eq_one_iff_of_nonneg zero_le' hp.out.ne_zero).mp (by rw [← map_pow, hβ.pow_eq_one, map_one])
  rw [← hi]
  have := v_pow_sub_le (v := v) (r := β) (s := 1) hβ1.le (by rw [map_one]) i
  rwa [one_pow] at this

/- English proof (translation)
Establish `hcyc` using `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz`. Establish `h1 : (p : C) = ∏ μ ∈ primitiveRoots p C, (1 - μ)`. Use `congrArg (Polynomial.eval 1) hcyc` as an intermediate fact. Rewrite `this` using `[Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod]`. Simplify using `using this`.

Establish `hc : ∀ μ ∈ primitiveRoots p C, v (1 - μ) = v (z - 1)`. Introduce `μ hμ`. Establish `hμ' : IsPrimitiveRoot μ p` using `(mem_primitiveRoots hp.out.pos).mp hμ`. Rewrite using `[Valuation.map_sub_swap]`. Conclude with `le_antisymm (val_sub_one_le hμ' hz) (val_sub_one_le hz hμ')`.

Rewrite using `[h1, map_prod, Finset.prod_congr rfl hc, Finset.prod_const, hz.card_primitiveRoots, Nat.totient_prime hp.out]`.
-/
theorem val_prim_root {z : C} (hz : IsPrimitiveRoot z p) : v (z - 1) ^ (p - 1) = v (p : C) := by
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 : (p : C) = ∏ μ ∈ primitiveRoots p C, (1 - μ) := by
    have := congrArg (Polynomial.eval 1) hcyc
    rw [Polynomial.eval_one_cyclotomic_prime, Polynomial.eval_prod] at this
    simpa using this
  have hc : ∀ μ ∈ primitiveRoots p C, v (1 - μ) = v (z - 1) := by
    intro μ hμ
    have hμ' : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.out.pos).mp hμ
    rw [Valuation.map_sub_swap]
    exact le_antisymm (val_sub_one_le hμ' hz) (val_sub_one_le hz hμ')
  rw [h1, map_prod, Finset.prod_congr rfl hc, Finset.prod_const, hz.card_primitiveRoots,
    Nat.totient_prime hp.out]

end ReciprocityTheory.PGsh.Up.U3
