import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Establish `hj` using `(Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I h)) (↑hx.unit⁻¹ : A)`. Establish `e : z = x * ((z - x) * ↑hx.unit⁻¹ + 1)`. Take the linear combination `(-(z - x)) * hx.mul_val_inv`. Rewrite using `[e]`. Conclude with `hx.mul hj`.
-/
private theorem unit_of_sub_mem {A : Type} [CommRing A] (I : Ideal A) [IsAdicComplete I A]
    {x z : A} (hx : IsUnit x) (h : z - x ∈ I) : IsUnit z := by
  have hj := (Ideal.mem_jacobson_bot.mp (IsAdicComplete.le_jacobson_bot I h)) (↑hx.unit⁻¹ : A)
  have e : z = x * ((z - x) * ↑hx.unit⁻¹ + 1) := by
    linear_combination (-(z - x)) * hx.mul_val_inv
  rw [e]
  exact hx.mul hj

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ d ih`. Take `⟨c, hc⟩` from `ih`. Use `⟨c + (∑ i ∈ Finset.range d, b i) * b d + r * c * b d, ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.prod_range_succ, Finset.sum_range_succ, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem prod_one_add {A : Type} [CommRing A] (b : ℕ → A) (r : A) (d : ℕ) :
    ∃ c, ∏ i ∈ Finset.range d, (1 + b i * r) =
      1 + (∑ i ∈ Finset.range d, b i) * r + r ^ 2 * c := by
  induction d with
  | zero => exact ⟨0, by simp⟩
  | succ d ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + (∑ i ∈ Finset.range d, b i) * b d + r * c * b d, ?_⟩
    rw [Finset.prod_range_succ, Finset.sum_range_succ, hc]
    ring

/- English proof (translation)
Establish `key : ∀ i, (⇑τ)^[i] (y * w) = (⇑τ)^[i] y * (⇑τ)^[i] w`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ i ih`.

Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]`. Simplify using `only [itN, key, Finset.prod_mul_distrib]`.
-/
private theorem itN_mul {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ) (y w : A) :
    itN τ d (y * w) = itN τ d y * itN τ d w := by
  have key : ∀ i, (⇑τ)^[i] (y * w) = (⇑τ)^[i] y * (⇑τ)^[i] w := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul]
  simp only [itN, key, Finset.prod_mul_distrib]

/- English proof (translation)
Unfold `itN`. Rewrite using `[map_prod]`. Simplify using `only [← Function.iterate_succ_apply' (⇑τ)]`. Consider the cases of `d with`. Consider the case `zero => simp`.

Consider the case `succ m`. Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] y), hd y]`. Both sides reduce to the same expression.
-/
private theorem itN_fixed {A : Type} [CommRing A] (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (y : A) : τ (itN τ d y) = itN τ d y := by
  unfold itN
  rw [map_prod]
  simp only [← Function.iterate_succ_apply' (⇑τ)]
  cases d with
  | zero => simp
  | succ m =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun i => (⇑τ)^[i] y), hd y]
    rfl

/- English proof (translation)
Use `set N := itN τ d y with hN`. Use `set v : A := ↑hu.unit⁻¹ with hv`. Establish `hNv : N * v = 1` using `hu.mul_val_inv`. Establish `hNfix : τ N = N` using `itN_fixed τ d hd y`. Establish `hvfix : τ v = v`.

Establish `h1 : τ N * τ v = 1` using `by rw [← map_mul, hNv, map_one]`. Rewrite `h1` using `[hNfix]`. Combine the equalities or inequalities in the displayed calculation. Establish `hwfix : τ ((x - N) * v) = (x - N) * v` using `by rw [map_mul, map_sub, hτx, hNfix, hvfix]`. Establish `hit : ∀ i (z : A), (⇑τ)^[i] z = ((τ : A →+* A) ^ i) z`.

Introduce `i z`. Rewrite using `[RingHom.coe_pow]`. Both sides reduce to the same expression. Establish `hwit : ∀ i, (⇑τ)^[i] ((x - N) * v) = (x - N) * v`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ i ih => rw [Function.iterate_succ_apply', ih, hwfix]`. Establish `hwI : (x - N) * v ∈ I ^ n`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises.

Rewrite using `[← neg_sub]`. Conclude with `neg_mem h`. Take `⟨c, hc⟩` from `prod_one_add (fun i => (⇑τ)^[i] a) ((x - N) * v) d`. Use `beta_reduce at hc`. Use `⟨y * (1 + a * ((x - N) * v)), ?_, ?_⟩` and prove the remaining obligations.

Establish `e : y * (1 + a * ((x - N) * v)) - y = (y * a) * ((x - N) * v)` using `by ring`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ hwI`. Establish `e1 : itN τ d (1 + a * ((x - N) * v)) = ∏ i ∈ Finset.range d, (1 + (⇑τ)^[i] a * ((x - N) * v))`. Unfold `itN`.

Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[hit, map_add, map_one, map_mul, ← hit, ← hit, hwit]`. Rewrite using `[itN_mul, ← hN, e1, hc, ha]`. Establish `e2 : N * (1 + 1 * ((x - N) * v) + ((x - N) * v) ^ 2 * c) - x = N * c * ((x - N) * v) ^ 2`.

Take the linear combination `(x - N) * hNv`. Rewrite using `[e2]`. Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Establish `h2 : ((x - N) * v) ^ 2 ∈ I ^ (n * 2)`. Rewrite using `[pow_mul]`.

Conclude with `Ideal.pow_mem_pow hwI 2`. Conclude with `Ideal.pow_le_pow_right (by omega) h2`.
-/
private theorem step {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A) (d : ℕ)
    (hd : ∀ x, τ^[d] x = x) (a : A) (ha : ∑ i ∈ Finset.range d, τ^[i] a = 1)
    (x : A) (hτx : τ x = x) (n : ℕ) (hn : n ≠ 0) (y : A) (hu : IsUnit (itN τ d y))
    (h : itN τ d y - x ∈ I ^ n) :
    ∃ y', y' - y ∈ I ^ n ∧ itN τ d y' - x ∈ I ^ (n + 1) := by
  set N := itN τ d y with hN
  set v : A := ↑hu.unit⁻¹ with hv
  have hNv : N * v = 1 := hu.mul_val_inv
  have hNfix : τ N = N := itN_fixed τ d hd y
  have hvfix : τ v = v := by
    have h1 : τ N * τ v = 1 := by rw [← map_mul, hNv, map_one]
    rw [hNfix] at h1
    calc τ v = (N * v) * τ v := by rw [hNv, one_mul]
      _ = v * (N * τ v) := by ring
      _ = v := by rw [h1, mul_one]
  have hwfix : τ ((x - N) * v) = (x - N) * v := by rw [map_mul, map_sub, hτx, hNfix, hvfix]
  have hit : ∀ i (z : A), (⇑τ)^[i] z = ((τ : A →+* A) ^ i) z := by
    intro i z
    rw [RingHom.coe_pow]
    rfl
  have hwit : ∀ i, (⇑τ)^[i] ((x - N) * v) = (x - N) * v := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', ih, hwfix]
  have hwI : (x - N) * v ∈ I ^ n := by
    apply Ideal.mul_mem_right
    rw [← neg_sub]
    exact neg_mem h
  obtain ⟨c, hc⟩ := prod_one_add (fun i => (⇑τ)^[i] a) ((x - N) * v) d
  beta_reduce at hc
  refine ⟨y * (1 + a * ((x - N) * v)), ?_, ?_⟩
  · have e : y * (1 + a * ((x - N) * v)) - y = (y * a) * ((x - N) * v) := by ring
    rw [e]
    exact Ideal.mul_mem_left _ _ hwI
  · have e1 : itN τ d (1 + a * ((x - N) * v)) = ∏ i ∈ Finset.range d, (1 + (⇑τ)^[i] a * ((x - N) * v)) := by
      unfold itN
      apply Finset.prod_congr rfl
      intro i _
      rw [hit, map_add, map_one, map_mul, ← hit, ← hit, hwit]
    rw [itN_mul, ← hN, e1, hc, ha]
    have e2 : N * (1 + 1 * ((x - N) * v) + ((x - N) * v) ^ 2 * c) - x = N * c * ((x - N) * v) ^ 2 := by
      linear_combination (x - N) * hNv
    rw [e2]
    apply Ideal.mul_mem_left
    have h2 : ((x - N) * v) ^ 2 ∈ I ^ (n * 2) := by
      rw [pow_mul]
      exact Ideal.pow_mem_pow hwI 2
    exact Ideal.pow_le_pow_right (by omega) h2

/- English proof (translation)
Establish `h1 : Ideal.map τ I ≤ I` using `Ideal.map_le_iff_le_comap.mpr (fun x hx => hI x hx)`. Establish `h2 : τ z ∈ Ideal.map τ (I ^ n)` using `Ideal.mem_map_of_mem τ h`. Rewrite `h2` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h1 n h2`.
-/
private theorem tau_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n : ℕ) {z : A} (h : z ∈ I ^ n) : τ z ∈ I ^ n := by
  have h1 : Ideal.map τ I ≤ I := Ideal.map_le_iff_le_comap.mpr (fun x hx => hI x hx)
  have h2 : τ z ∈ Ideal.map τ (I ^ n) := Ideal.mem_map_of_mem τ h
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => exact h`. Consider the case `succ i ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `tau_pow_mem I τ hI n ih`.
-/
private theorem iter_pow_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (n i : ℕ) {z : A} (h : z ∈ I ^ n) : τ^[i] z ∈ I ^ n := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact tau_pow_mem I τ hI n ih

/- English proof (translation)
Establish `hs : ∀ i, (⇑τ)^[i] u - (⇑τ)^[i] v ∈ I ^ n`. Introduce `i`. Establish `e : ∀ j, (⇑τ)^[j] u - (⇑τ)^[j] v = (⇑τ)^[j] (u - v)`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => rfl`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub, ih]`. Rewrite using `[e]`. Conclude with `iter_pow_mem I τ hI n i h`.

Unfold `itN`. Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih`. Rewrite using `[Finset.prod_range_succ, Finset.prod_range_succ]`.

Establish `e2 : (∏ i ∈ Finset.range d, (⇑τ)^[i] u) * (⇑τ)^[d] u - (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] v = (∏ i ∈ Finset.range d, (⇑τ)^[i] u - ∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] u + (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * ((⇑τ)^[d] u - (⇑τ)^[d] v)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ ih) (Ideal.mul_mem_left _ _ (hs d))`.
-/
private theorem itN_sub_mem {A : Type} [CommRing A] (I : Ideal A) (τ : A ≃+* A)
    (hI : ∀ x ∈ I, τ x ∈ I) (d n : ℕ) {u v : A} (h : u - v ∈ I ^ n) :
    itN τ d u - itN τ d v ∈ I ^ n := by
  have hs : ∀ i, (⇑τ)^[i] u - (⇑τ)^[i] v ∈ I ^ n := by
    intro i
    have e : ∀ j, (⇑τ)^[j] u - (⇑τ)^[j] v = (⇑τ)^[j] (u - v) := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ← map_sub, ih]
    rw [e]
    exact iter_pow_mem I τ hI n i h
  unfold itN
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    have e2 : (∏ i ∈ Finset.range d, (⇑τ)^[i] u) * (⇑τ)^[d] u - (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] v
        = (∏ i ∈ Finset.range d, (⇑τ)^[i] u - ∏ i ∈ Finset.range d, (⇑τ)^[i] v) * (⇑τ)^[d] u
          + (∏ i ∈ Finset.range d, (⇑τ)^[i] v) * ((⇑τ)^[d] u - (⇑τ)^[d] v) := by
      ring
    rw [e2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ ih) (Ideal.mul_mem_left _ _ (hs d))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem mem_smul_top {A : Type} [CommRing A] (I : Ideal A) (n : ℕ) (z : A) :
    z ∈ (I ^ n • ⊤ : Submodule A A) ↔ z ∈ I ^ n := by
  simp

/- English proof (translation)
Introduce `A _ I _ τ d hd hI a ha x y hx hτx hy`. Establish `hunit : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) → IsUnit (itN τ d z)`. Introduce `n z hz`. Conclude with `unit_of_sub_mem I hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hz)`. Establish `hstep : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) → ∃ z', z' - z ∈ I ^ (n + 1) ∧ itN τ d z' - x ∈ I ^ (n + 1 + 1)`.

Introduce `n z hz`. Conclude with `step I τ d hd a ha x hτx (n + 1) (Nat.succ_ne_zero n) z (hunit n z hz) hz`. Use `choose! g hg1 hg2 using hstep`. Set `f : ℕ → A` to `fun k => Nat.rec (motive := fun _ => A) y (fun k z => g k z) k`. Establish `hf0 : f 0 = y` using `rfl`.

Establish `hfs : ∀ k, f (k + 1) = g k (f k)` using `fun k => rfl`. Establish `hfN : ∀ k, itN τ d (f k) - x ∈ I ^ (k + 1)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa [hf0] using hy`.

Consider the case `succ k ih`. Rewrite using `[hfs]`. Conclude with `hg2 k (f k) ih`. Establish `hfd : ∀ k, f (k + 1) - f k ∈ I ^ (k + 1)`. Introduce `k`.

Rewrite using `[hfs]`. Conclude with `hg1 k (f k) (hfN k)`. Establish `hcauchy : ∀ m k, f m - f (m + k) ∈ I ^ m`. Introduce `m k`. Proceed by induction on `k with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : f m - f (m + (k + 1)) = (f m - f (m + k)) - (f (m + k + 1) - f (m + k))`. Rewrite using `[← add_assoc]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `Ideal.sub_mem _ ih ?_` and prove the remaining obligations. Conclude with `Ideal.pow_le_pow_right (by omega) (hfd (m + k))`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := I) (M := A) inferInstance (f := f) (by`. Introduce `m n hmn`.

Rewrite using `[SModEq.sub_mem, mem_smul_top]`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Conclude with `hcauchy m k)`. Use `⟨L, ?_⟩` and prove the remaining obligations. Establish `hzero` using `IsHausdorff.haus (I := I) (M := A) inferInstance (itN τ d L - x) (by`.

Introduce `n`. Rewrite using `[SModEq.sub_mem, sub_zero, mem_smul_top]`. Establish `h1 : itN τ d L - itN τ d (f n) ∈ I ^ n`. Apply `itN_sub_mem I τ hI d n` to reduce the goal to its premises. Establish `h0` using `SModEq.sub_mem.mp (hL n)`.

Rewrite `h0` using `[mem_smul_top]`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem h0`. Establish `h2 : itN τ d (f n) - x ∈ I ^ n` using `Ideal.pow_le_pow_right (by omega) (hfN n)`. Establish `e : itN τ d L - x = (itN τ d L - itN τ d (f n)) + (itN τ d (f n) - x)` using `by ring`.

Rewrite using `[e]`. Conclude with `Ideal.add_mem _ h1 h2)`. Conclude with `sub_eq_zero.mp hzero`.
-/
theorem normAdic : NormAdic := by
  intro A _ I _ τ d hd hI a ha x y hx hτx hy
  have hunit : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) → IsUnit (itN τ d z) := by
    intro n z hz
    exact unit_of_sub_mem I hx (Ideal.pow_le_self (Nat.succ_ne_zero n) hz)
  have hstep : ∀ n : ℕ, ∀ z : A, itN τ d z - x ∈ I ^ (n + 1) →
      ∃ z', z' - z ∈ I ^ (n + 1) ∧ itN τ d z' - x ∈ I ^ (n + 1 + 1) := by
    intro n z hz
    exact step I τ d hd a ha x hτx (n + 1) (Nat.succ_ne_zero n) z (hunit n z hz) hz
  choose! g hg1 hg2 using hstep
  let f : ℕ → A := fun k => Nat.rec (motive := fun _ => A) y (fun k z => g k z) k
  have hf0 : f 0 = y := rfl
  have hfs : ∀ k, f (k + 1) = g k (f k) := fun k => rfl
  have hfN : ∀ k, itN τ d (f k) - x ∈ I ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa [hf0] using hy
    | succ k ih =>
      rw [hfs]
      exact hg2 k (f k) ih
  have hfd : ∀ k, f (k + 1) - f k ∈ I ^ (k + 1) := by
    intro k
    rw [hfs]
    exact hg1 k (f k) (hfN k)
  have hcauchy : ∀ m k, f m - f (m + k) ∈ I ^ m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : f m - f (m + (k + 1)) = (f m - f (m + k)) - (f (m + k + 1) - f (m + k)) := by
        rw [← add_assoc]
        ring
      rw [e]
      refine Ideal.sub_mem _ ih ?_
      exact Ideal.pow_le_pow_right (by omega) (hfd (m + k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := A) inferInstance (f := f) (by
    intro m n hmn
    rw [SModEq.sub_mem, mem_smul_top]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    exact hcauchy m k)
  refine ⟨L, ?_⟩
  have hzero := IsHausdorff.haus (I := I) (M := A) inferInstance (itN τ d L - x) (by
    intro n
    rw [SModEq.sub_mem, sub_zero, mem_smul_top]
    have h1 : itN τ d L - itN τ d (f n) ∈ I ^ n := by
      apply itN_sub_mem I τ hI d n
      have h0 := SModEq.sub_mem.mp (hL n)
      rw [mem_smul_top] at h0
      rw [← neg_sub]
      exact neg_mem h0
    have h2 : itN τ d (f n) - x ∈ I ^ n := Ideal.pow_le_pow_right (by omega) (hfN n)
    have e : itN τ d L - x = (itN τ d L - itN τ d (f n)) + (itN τ d (f n) - x) := by ring
    rw [e]
    exact Ideal.add_mem _ h1 h2)
  exact sub_eq_zero.mp hzero

end UpperTheory.Gal.InertialTypesAlt.L
