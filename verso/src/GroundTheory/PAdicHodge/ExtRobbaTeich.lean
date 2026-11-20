import Mathlib
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GroundTheory.PAdicHodge

open Ideal

structure TeichLift (p : ℕ) (L : Type*) [NormedField L] (Γ : Type*) [CommRing Γ] where

  π : Γ

  red : Γ →+* L
  red_surjective : Function.Surjective red
  ker_red : RingHom.ker red = Ideal.span {π}
  π_mem_nonZeroDivisors : π ∈ nonZeroDivisors Γ
  isAdicComplete : IsAdicComplete (Ideal.span {π}) Γ

  int : Subring Γ
  π_mem_int : π ∈ int
  norm_red_le_one : ∀ x ∈ int, ‖red x‖ ≤ 1
  exists_mem_int : ∀ a : L, ‖a‖ ≤ 1 → ∃ x ∈ int, red x = a
  exists_eq_π_mul : ∀ x ∈ int, red x = 0 → ∃ y ∈ int, x = π * y
  mem_int_of_approx : ∀ x, (∀ N : ℕ, ∃ y ∈ int, x - y ∈ Ideal.span {π ^ N}) → x ∈ int

namespace TeichLift

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L] [CharP L p]
  [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)

abbrev I : Ideal Γ := Ideal.span {T.π}

/- English proof (translation)
Rewrite using `[Ideal.mem_span_singleton']`. Conclude with `⟨fun ⟨a, h⟩ => ⟨a, by rw [← h, mul_comm]⟩, fun ⟨a, h⟩ => ⟨a, by rw [h, mul_comm]⟩⟩`.
-/
theorem mem_span_pow {x : Γ} {n : ℕ} : x ∈ Ideal.span {T.π ^ n} ↔ ∃ y, x = T.π ^ n * y := by
  rw [Ideal.mem_span_singleton']
  exact ⟨fun ⟨a, h⟩ => ⟨a, by rw [← h, mul_comm]⟩, fun ⟨a, h⟩ => ⟨a, by rw [h, mul_comm]⟩⟩

/- English proof (translation)
The claim follows from `Ideal.span_singleton_pow _ _`.
-/
theorem I_pow (n : ℕ) : T.I ^ n = Ideal.span {T.π ^ n} := Ideal.span_singleton_pow _ _

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, T.ker_red, ← pow_one T.π, T.mem_span_pow]`.
-/
theorem red_eq_zero_iff {x : Γ} : T.red x = 0 ↔ ∃ y, x = T.π * y := by
  rw [← RingHom.mem_ker, T.ker_red, ← pow_one T.π, T.mem_span_pow]

/- English proof (translation)
The claim follows from `T.red_eq_zero_iff.2 ⟨1, (mul_one _).symm⟩`.
-/
theorem red_π : T.red T.π = 0 := T.red_eq_zero_iff.2 ⟨1, (mul_one _).symm⟩

/- English proof (translation)
Establish `hπ` using `pow_mem T.π_mem_nonZeroDivisors n`. Establish `: T.π ^ n * (x - y) = 0` using `by rw [mul_sub, h, sub_self]`. Conclude with `sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hπ).1 _ this)`.
-/
theorem π_pow_mul_cancel {n : ℕ} {x y : Γ} (h : T.π ^ n * x = T.π ^ n * y) : x = y := by
  have hπ := pow_mem T.π_mem_nonZeroDivisors n
  have : T.π ^ n * (x - y) = 0 := by rw [mul_sub, h, sub_self]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hπ).1 _ this)

/- English proof (translation)
The claim follows from `T.π_pow_mul_cancel (n := 1) (by simpa using h)`.
-/
theorem π_mul_cancel {x y : Γ} (h : T.π * x = T.π * y) : x = y :=
  T.π_pow_mul_cancel (n := 1) (by simpa using h)

/- English proof (translation)
Take `⟨y, hy⟩` from `T.mem_span_pow.1 h`. Use `T.mem_span_pow.2 ⟨y, T.π_mul_cancel ?_⟩` and prove the remaining obligations. Rewrite using `[hy, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_span_pow_of_π_mul {n : ℕ} {x : Γ} (h : T.π * x ∈ Ideal.span {T.π ^ (n + 1)}) :
    x ∈ Ideal.span {T.π ^ n} := by
  obtain ⟨y, hy⟩ := T.mem_span_pow.1 h
  refine T.mem_span_pow.2 ⟨y, T.π_mul_cancel ?_⟩
  rw [hy, pow_succ]; ring

/- English proof (translation)
The claim follows from `T.mem_span_pow.2 ⟨T.π ^ (m - n) * x, by rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]⟩`.
-/
theorem π_pow_mul_mem {m n : ℕ} (h : n ≤ m) (x : Γ) : T.π ^ m * x ∈ Ideal.span {T.π ^ n} :=
  T.mem_span_pow.2 ⟨T.π ^ (m - n) * x, by rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨y, rfl⟩` from `T.mem_span_pow.1 hx`. Conclude with `T.π_pow_mul_mem h y`.
-/
theorem span_pow_anti {m n : ℕ} (h : n ≤ m) : Ideal.span {T.π ^ m} ≤ Ideal.span {T.π ^ n} := by
  intro x hx
  obtain ⟨y, rfl⟩ := T.mem_span_pow.1 hx
  exact T.π_pow_mul_mem h y

def quotEquiv : (Γ ⧸ T.I) ≃+* L :=
  (Ideal.quotEquivOfEq T.ker_red.symm).trans (RingHom.quotientKerEquivOfSurjective T.red_surjective)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotEquiv_mk (x : Γ) : T.quotEquiv (Ideal.Quotient.mk T.I x) = T.red x := rfl

instance charP_quot : CharP (Γ ⧸ T.I) p :=
  charP_of_injective_ringHom (f := T.quotEquiv.symm.toRingHom) T.quotEquiv.symm.injective p

/- English proof (translation)
Rewrite using `[RingEquiv.symm_apply_eq, quotEquiv_mk, h]`.
-/
theorem quotEquiv_symm (a : L) (x : Γ) (h : T.red x = a) :
    T.quotEquiv.symm a = Ideal.Quotient.mk T.I x := by
  rw [RingEquiv.symm_apply_eq, quotEquiv_mk, h]

variable (p) in

def toPerfection : L →+* Perfection (Γ ⧸ T.I) p :=
  Perfection.lift p L (Γ ⧸ T.I) T.quotEquiv.symm.toRingHom

def teich : L →*₀ Γ :=
  haveI := T.isAdicComplete
  (Perfection.teichmuller₀ p T.I).comp (T.toPerfection p).toMonoidWithZeroHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_toPerfection (a : L) (n : ℕ) :
    Perfection.coeff (Γ ⧸ T.I) p n (T.toPerfection p a) =
      T.quotEquiv.symm ((((frobeniusEquiv L p).symm : L →+* L))^[n] a) := rfl

/- English proof (translation)
Use `haveI := T.isAdicComplete`. Rewrite using `[← quotEquiv_mk]`. Use `show T.quotEquiv (Ideal.Quotient.mk T.I (Perfection.teichmuller₀ p T.I (T.toPerfection p a))) = a`. Rewrite using `[Perfection.mk_teichmuller₀, coeff_toPerfection]`. Simplify using the standard rewrite rules.
-/
theorem red_teich (a : L) : T.red (T.teich a) = a := by
  haveI := T.isAdicComplete
  rw [← quotEquiv_mk]
  show T.quotEquiv (Ideal.Quotient.mk T.I (Perfection.teichmuller₀ p T.I (T.toPerfection p a))) = a
  rw [Perfection.mk_teichmuller₀, coeff_toPerfection]
  simp

/- English proof (translation)
The claim follows from `map_mul _ _ _`.
-/
theorem teich_mul (a b : L) : T.teich (a * b) = T.teich a * T.teich b := map_mul _ _ _

/- English proof (translation)
The claim follows from `map_zero _`.
-/
@[simp] theorem teich_zero : T.teich 0 = 0 := map_zero _

/- English proof (translation)
The claim follows from `map_one _`.
-/
@[simp] theorem teich_one : T.teich 1 = 1 := map_one _

/- English proof (translation)
The claim follows from `map_pow _ _ _`.
-/
theorem teich_pow (a : L) (n : ℕ) : T.teich (a ^ n) = T.teich a ^ n := map_pow _ _ _

/- English proof (translation)
Use `haveI := T.isAdicComplete`. Establish `h : Ideal.Quotient.mk T.I z = Perfection.coeff (Γ ⧸ T.I) p n (T.toPerfection p a)`. Rewrite using `[coeff_toPerfection]`. Conclude with `(T.quotEquiv_symm _ z hz).symm`. Use `Perfection.teichmuller₀_sModEq (p := p) (I := T.I) h` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, T.I_pow]`. Conclude with `this`.
-/
theorem teich_sub_pow_mem (a : L) (n : ℕ) (z : Γ)
    (hz : T.red z = (((frobeniusEquiv L p).symm : L →+* L))^[n] a) :
    T.teich a - z ^ p ^ n ∈ Ideal.span {T.π ^ (n + 1)} := by
  haveI := T.isAdicComplete
  have h : Ideal.Quotient.mk T.I z = Perfection.coeff (Γ ⧸ T.I) p n (T.toPerfection p a) := by
    rw [coeff_toPerfection]
    exact (T.quotEquiv_symm _ z hz).symm
  have := Perfection.teichmuller₀_sModEq (p := p) (I := T.I) h
  rw [SModEq.sub_mem, T.I_pow] at this
  exact this

/- English proof (translation)
Rewrite using `[map_sub, red_teich, sub_self]`.
-/
theorem red_sub_teich_red (x : Γ) : T.red (x - T.teich (T.red x)) = 0 := by
  rw [map_sub, red_teich, sub_self]

def tail (x : Γ) : Γ := (T.red_eq_zero_iff.1 (T.red_sub_teich_red x)).choose

/- English proof (translation)
The claim follows from `(T.red_eq_zero_iff.1 (T.red_sub_teich_red x)).choose_spec`.
-/
theorem sub_teich_eq_π_mul_tail (x : Γ) : x - T.teich (T.red x) = T.π * T.tail x :=
  (T.red_eq_zero_iff.1 (T.red_sub_teich_red x)).choose_spec

/- English proof (translation)
Rewrite using `[← T.sub_teich_eq_π_mul_tail]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eq_teich_add_π_mul_tail (x : Γ) : x = T.teich (T.red x) + T.π * T.tail x := by
  rw [← T.sub_teich_eq_π_mul_tail]; ring

/- English proof (translation)
Establish `ha : T.red x = a` using `by rw [h, map_add, map_mul, red_π, zero_mul, add_zero, red_teich]`. Use `T.π_mul_cancel ?_` and prove the remaining obligations. Rewrite using `[← T.sub_teich_eq_π_mul_tail, ha, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tail_eq {x y : Γ} {a : L} (h : x = T.teich a + T.π * y) : T.tail x = y := by
  have ha : T.red x = a := by rw [h, map_add, map_mul, red_π, zero_mul, add_zero, red_teich]
  refine T.π_mul_cancel ?_
  rw [← T.sub_teich_eq_π_mul_tail, ha, h]; ring

def coeff (x : Γ) (n : ℕ) : L := T.red (T.tail^[n] x)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coeff_zero (x : Γ) : T.coeff x 0 = T.red x := rfl

/- English proof (translation)
Simplify using `[coeff, Function.iterate_succ_apply]`.
-/
theorem coeff_succ (x : Γ) (n : ℕ) : T.coeff x (n + 1) = T.coeff (T.tail x) n := by
  simp [coeff, Function.iterate_succ_apply]

def finSum (a : ℕ → L) (n : ℕ) : Γ := ∑ i ∈ Finset.range n, T.π ^ i * T.teich (a i)

/- English proof (translation)
Simplify using `[finSum]`.
-/
@[simp] theorem finSum_zero (a : ℕ → L) : T.finSum a 0 = 0 := by simp [finSum]

/- English proof (translation)
Simplify using `[finSum, Finset.sum_range_succ]`.
-/
theorem finSum_succ (a : ℕ → L) (n : ℕ) :
    T.finSum a (n + 1) = T.finSum a n + T.π ^ n * T.teich (a n) := by
  simp [finSum, Finset.sum_range_succ]

/- English proof (translation)
Simplify using `only [finSum, Finset.sum_range_succ', pow_zero, one_mul, Finset.mul_sum]`. Rewrite using `[add_comm]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finSum_succ' (a : ℕ → L) (n : ℕ) :
    T.finSum a (n + 1) = T.teich (a 0) + T.π * T.finSum (fun i => a (i + 1)) n := by
  simp only [finSum, Finset.sum_range_succ', pow_zero, one_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/- English proof (translation)
Proceed by induction on `n, h using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`. Rewrite using `[finSum_succ, add_sub_right_comm]`. Conclude with `add_mem ih (T.π_pow_mul_mem hmn _)`.
-/
theorem finSum_sub_finSum_mem (a : ℕ → L) {m n : ℕ} (h : m ≤ n) :
    T.finSum a n - T.finSum a m ∈ Ideal.span {T.π ^ m} := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [finSum_succ, add_sub_right_comm]
    exact add_mem ih (T.π_pow_mul_mem hmn _)

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]`.
-/
theorem finSum_congr {a b : ℕ → L} {n : ℕ} (h : ∀ i < n, a i = b i) :
    T.finSum a n = T.finSum b n :=
  Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.1 hi)]

/- English proof (translation)
Establish `h0 : T.finSum a m = 0`. Rewrite using `[T.finSum_congr (b := 0) h]`. Simplify using `[finSum]`. Simplify `T.finSum_sub_finSum_mem a hmn` using `[h0]`.
-/
theorem finSum_mem_span_of_eq_zero {a : ℕ → L} {n m : ℕ} (h : ∀ i < m, a i = 0) (hmn : m ≤ n) :
    T.finSum a n ∈ Ideal.span {T.π ^ m} := by
  have h0 : T.finSum a m = 0 := by
    rw [T.finSum_congr (b := 0) h]; simp [finSum]
  simpa [h0] using T.finSum_sub_finSum_mem a hmn

def partialSum (x : Γ) (n : ℕ) : Γ := T.finSum (T.coeff x) n

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simp [partialSum]`. Consider the case `succ n ih`. Establish `h1 : T.partialSum x (n + 1) = T.teich (T.red x) + T.π * T.partialSum (T.tail x) n`. Simplify using `only [partialSum, finSum_succ', coeff_zero, coeff_succ]`.

Rewrite using `[h1, Function.iterate_succ_apply, pow_succ', mul_assoc, ← ih]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sub_partialSum (x : Γ) (n : ℕ) : x - T.partialSum x n = T.π ^ n * T.tail^[n] x := by
  induction n generalizing x with
  | zero => simp [partialSum]
  | succ n ih =>
    have h1 : T.partialSum x (n + 1) = T.teich (T.red x) + T.π * T.partialSum (T.tail x) n := by
      simp only [partialSum, finSum_succ', coeff_zero, coeff_succ]
    rw [h1, Function.iterate_succ_apply, pow_succ', mul_assoc, ← ih]
    calc x - (T.teich (T.red x) + T.π * T.partialSum (T.tail x) n)
        = (x - T.teich (T.red x)) - T.π * T.partialSum (T.tail x) n := by ring
      _ = T.π * T.tail x - T.π * T.partialSum (T.tail x) n := by rw [T.sub_teich_eq_π_mul_tail]
      _ = T.π * (T.tail x - T.partialSum (T.tail x) n) := by ring

/- English proof (translation)
The claim follows from `T.mem_span_pow.2 ⟨_, T.sub_partialSum x n⟩`.
-/
theorem sub_partialSum_mem (x : Γ) (n : ℕ) : x - T.partialSum x n ∈ Ideal.span {T.π ^ n} :=
  T.mem_span_pow.2 ⟨_, T.sub_partialSum x n⟩

/- English proof (translation)
Rewrite using `[finSum_succ', map_add, map_mul, red_π, zero_mul, add_zero, red_teich]`.
-/
theorem red_finSum (a : ℕ → L) (n : ℕ) : T.red (T.finSum a (n + 1)) = a 0 := by
  rw [finSum_succ', map_add, map_mul, red_π, zero_mul, add_zero, red_teich]

/- English proof (translation)
Proceed by induction on `n generalizing x a with`. Consider the case `zero`. Introduce `m hm`. Take `rfl : m = 0` from `by omega`. Take `⟨y, hy⟩` from `T.mem_span_pow.1 h`.

Use `congrArg T.red hy` as an intermediate fact. Rewrite `this` using `[map_sub, red_finSum, map_mul, map_pow, red_π, zero_pow (by norm_num), zero_mul, sub_eq_zero]`. Simplify using `using this`. Consider the case `succ n ih`. Establish `h0 : T.red x = a 0`.

Take `⟨y, hy⟩` from `T.mem_span_pow.1 h`. Use `congrArg T.red hy` as an intermediate fact. Rewrite `this` using `[map_sub, red_finSum, map_mul, map_pow, red_π, zero_pow (by norm_num), zero_mul, sub_eq_zero]`. Conclude with `this`. Establish `h1 : T.tail x - T.finSum (fun i => a (i + 1)) (n + 1) ∈ Ideal.span {T.π ^ (n + 1)}`.

Use `T.mem_span_pow_of_π_mul ?_` and prove the remaining obligations. Establish `: x - T.finSum a (n + 1 + 1) = T.π * (T.tail x - T.finSum (fun i => a (i + 1)) (n + 1))`. Rewrite using `[T.finSum_succ' a (n + 1), ← h0]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[T.sub_teich_eq_π_mul_tail]`.

Use `_ = _ := by ring`. Rewrite using `[← this]`. Conclude with `h`. Introduce `m hm`. Break down `m with _ | m` into its components or cases.

Simplify using `using h0`. Rewrite using `[coeff_succ]; exact ih h1 m (by omega)`.
-/
theorem coeff_eq_of_mem {n : ℕ} {x : Γ} {a : ℕ → L}
    (h : x - T.finSum a (n + 1) ∈ Ideal.span {T.π ^ (n + 1)}) : ∀ m ≤ n, T.coeff x m = a m := by
  induction n generalizing x a with
  | zero =>
    intro m hm
    obtain rfl : m = 0 := by omega
    obtain ⟨y, hy⟩ := T.mem_span_pow.1 h
    have := congrArg T.red hy
    rw [map_sub, red_finSum, map_mul, map_pow, red_π, zero_pow (by norm_num), zero_mul,
      sub_eq_zero] at this
    simpa using this
  | succ n ih =>
    have h0 : T.red x = a 0 := by
      obtain ⟨y, hy⟩ := T.mem_span_pow.1 h
      have := congrArg T.red hy
      rw [map_sub, red_finSum, map_mul, map_pow, red_π, zero_pow (by norm_num), zero_mul,
        sub_eq_zero] at this
      exact this
    have h1 : T.tail x - T.finSum (fun i => a (i + 1)) (n + 1) ∈ Ideal.span {T.π ^ (n + 1)} := by
      refine T.mem_span_pow_of_π_mul ?_
      have : x - T.finSum a (n + 1 + 1) = T.π * (T.tail x - T.finSum (fun i => a (i + 1)) (n + 1)) := by
        rw [T.finSum_succ' a (n + 1), ← h0]
        calc x - (T.teich (T.red x) + T.π * T.finSum (fun i => a (i + 1)) (n + 1))
            = (x - T.teich (T.red x)) - T.π * T.finSum (fun i => a (i + 1)) (n + 1) := by ring
          _ = T.π * T.tail x - T.π * T.finSum (fun i => a (i + 1)) (n + 1) := by
            rw [T.sub_teich_eq_π_mul_tail]
          _ = _ := by ring
      rw [← this]; exact h
    intro m hm
    rcases m with _ | m
    · simpa using h0
    · rw [coeff_succ]; exact ih h1 m (by omega)

/- English proof (translation)
Use `haveI := T.isAdicComplete`. Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus' (I := T.I) (x - y) fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]`. Establish `h1` using `T.sub_partialSum_mem x n`.

Establish `h2` using `T.sub_partialSum_mem y n`. Establish `: x - y = (x - T.partialSum x n) - (y - T.partialSum y n)`. Simplify using `only [partialSum, h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `sub_mem h1 h2`.
-/
theorem eq_of_coeff_eq {x y : Γ} (h : T.coeff x = T.coeff y) : x = y := by
  haveI := T.isAdicComplete
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := T.I) (x - y) fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow]
  have h1 := T.sub_partialSum_mem x n
  have h2 := T.sub_partialSum_mem y n
  have : x - y = (x - T.partialSum x n) - (y - T.partialSum y n) := by
    simp only [partialSum, h]; ring
  rw [this]; exact sub_mem h1 h2

def ofCoeff (a : ℕ → L) : Γ :=
  haveI := T.isAdicComplete
  (IsPrecomplete.prec' (I := T.I) (T.finSum a) fun {m n} hmn => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub]
    exact neg_mem (T.finSum_sub_finSum_mem a hmn)).choose

/- English proof (translation)
Use `haveI := T.isAdicComplete`. Use `(IsPrecomplete.prec' (I := T.I) (T.finSum a) fun {m n} hmn => by` as an intermediate fact. Rewrite using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub]`. Conclude with `neg_mem (T.finSum_sub_finSum_mem a hmn)).choose_spec n`. Rewrite `this` using `[SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub]`.

Simplify `neg_mem this` using `[ofCoeff]`.
-/
theorem mk_sub_finSum_mem (a : ℕ → L) (n : ℕ) : T.ofCoeff a - T.finSum a n ∈ Ideal.span {T.π ^ n} := by
  haveI := T.isAdicComplete
  have := (IsPrecomplete.prec' (I := T.I) (T.finSum a) fun {m n} hmn => by
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub]
    exact neg_mem (T.finSum_sub_finSum_mem a hmn)).choose_spec n
  rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, T.I_pow, ← neg_sub] at this
  simpa [ofCoeff] using neg_mem this

/- English proof (translation)
The claim follows from `funext fun n => T.coeff_eq_of_mem (T.mk_sub_finSum_mem a (n + 1)) n le_rfl`.
-/
@[simp] theorem coeff_ofCoeff (a : ℕ → L) : T.coeff (T.ofCoeff a) = a :=
  funext fun n => T.coeff_eq_of_mem (T.mk_sub_finSum_mem a (n + 1)) n le_rfl

/- English proof (translation)
The claim follows from `T.eq_of_coeff_eq (by simp)`.
-/
theorem ofCoeff_coeff (x : Γ) : T.ofCoeff (T.coeff x) = x := T.eq_of_coeff_eq (by simp)

/- English proof (translation)
Use `T.coeff_eq_of_mem ?_` and prove the remaining obligations. Use `add_mem h (T.sub_partialSum_mem y (n + 1))` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem coeff_eq_coeff_of_sub_mem {x y : Γ} {n : ℕ} (h : x - y ∈ Ideal.span {T.π ^ (n + 1)}) :
    ∀ m ≤ n, T.coeff x m = T.coeff y m := by
  refine T.coeff_eq_of_mem ?_
  have := add_mem h (T.sub_partialSum_mem y (n + 1))
  rwa [sub_add_sub_cancel] at this

/- English proof (translation)
Rewrite using `[coeff_succ, T.tail_eq (a := 0) (y := x) (by simp)]`.
-/
theorem coeff_π_mul_succ (x : Γ) (n : ℕ) : T.coeff (T.π * x) (n + 1) = T.coeff x n := by
  rw [coeff_succ, T.tail_eq (a := 0) (y := x) (by simp)]

/- English proof (translation)
Simplify using `[red_π]`.
-/
@[simp] theorem coeff_π_mul_zero (x : Γ) : T.coeff (T.π * x) 0 = 0 := by
  simp [red_π]

/- English proof (translation)
Proceed by induction on `k generalizing n with`. Consider the case `zero => simp`. Consider the case `succ k ih => rw [pow_succ', mul_assoc, ← add_assoc, coeff_π_mul_succ, ih]`.
-/
theorem coeff_π_pow_mul_add (k : ℕ) (x : Γ) (n : ℕ) :
    T.coeff (T.π ^ k * x) (n + k) = T.coeff x n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, ← add_assoc, coeff_π_mul_succ, ih]

/- English proof (translation)
Proceed by induction on `k generalizing n with`. Consider the case `zero => omega`. Consider the case `succ k ih`. Rewrite using `[pow_succ', mul_assoc]`. Break down `n with _ | n` into its components or cases.

Conclude with `T.coeff_π_mul_zero _`. Rewrite using `[coeff_π_mul_succ, ih (by omega)]`.
-/
theorem coeff_π_pow_mul_of_lt {k : ℕ} (x : Γ) {n : ℕ} (h : n < k) : T.coeff (T.π ^ k * x) n = 0 := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [pow_succ', mul_assoc]
    rcases n with _ | n
    · exact T.coeff_π_mul_zero _
    · rw [coeff_π_mul_succ, ih (by omega)]

/- English proof (translation)
Introduce `m hm`. Take `⟨y, rfl⟩` from `T.mem_span_pow.1 h`. Conclude with `T.coeff_π_pow_mul_of_lt y (by omega)`.
-/
theorem coeff_of_mem_span {x : Γ} {n : ℕ} (h : x ∈ Ideal.span {T.π ^ (n + 1)}) :
    ∀ m ≤ n, T.coeff x m = 0 := by
  intro m hm
  obtain ⟨y, rfl⟩ := T.mem_span_pow.1 h
  exact T.coeff_π_pow_mul_of_lt y (by omega)

/- English proof (translation)
Use `T.coeff_of_mem_span (x := (0 : Γ)) (n := n) (zero_mem _) n le_rfl` as an intermediate fact. Conclude with `this`.
-/
@[simp] theorem coeff_zero_elem (n : ℕ) : T.coeff (0 : Γ) n = 0 := by
  have := T.coeff_of_mem_span (x := (0 : Γ)) (n := n) (zero_mem _) n le_rfl
  exact this

/- English proof (translation)
Use `T.coeff_eq_of_mem (a := fun i => c * T.coeff x i) ?_ n le_rfl` and prove the remaining obligations. Establish `: T.finSum (fun i => c * T.coeff x i) (n + 1) = T.teich c * T.partialSum x (n + 1)`. Simplify using `only [finSum, partialSum, Finset.mul_sum, T.teich_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[this, ← mul_sub]`.

Conclude with `Ideal.mul_mem_left _ _ (T.sub_partialSum_mem x (n + 1))`.
-/
theorem coeff_teich_mul (c : L) (x : Γ) (n : ℕ) : T.coeff (T.teich c * x) n = c * T.coeff x n := by
  refine T.coeff_eq_of_mem (a := fun i => c * T.coeff x i) ?_ n le_rfl
  have : T.finSum (fun i => c * T.coeff x i) (n + 1) = T.teich c * T.partialSum x (n + 1) := by
    simp only [finSum, partialSum, Finset.mul_sum, T.teich_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, ← mul_sub]
  exact Ideal.mul_mem_left _ _ (T.sub_partialSum_mem x (n + 1))

/- English proof (translation)
Use `T.coeff_teich_mul c 1 n` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this]`. Establish `h1 : T.coeff (1 : Γ) n = if n = 0 then 1 else 0`. Rewrite using `[← T.teich_one]`.

Use `T.coeff_eq_of_mem (a := fun i => if i = 0 then 1 else 0) ?_ n le_rfl` and prove the remaining obligations. Establish `: T.finSum (fun i => if i = 0 then (1 : L) else 0) (n + 1) = T.teich 1`. Rewrite using `[finSum_succ']`. Simplify using `[finSum]`. Simplify using `[this]`.

Apply the tactic sequence `rw [h1]; split_ifs <;> simp`.
-/
theorem coeff_teich (c : L) (n : ℕ) : T.coeff (T.teich c) n = if n = 0 then c else 0 := by
  have := T.coeff_teich_mul c 1 n
  rw [mul_one] at this
  rw [this]
  have h1 : T.coeff (1 : Γ) n = if n = 0 then 1 else 0 := by
    rw [← T.teich_one]
    refine T.coeff_eq_of_mem (a := fun i => if i = 0 then 1 else 0) ?_ n le_rfl
    have : T.finSum (fun i => if i = 0 then (1 : L) else 0) (n + 1) = T.teich 1 := by
      rw [finSum_succ']
      simp [finSum]
    simp [this]
  rw [h1]; split_ifs <;> simp

/- English proof (translation)
Break down `lt_or_ge n k with h | h` into its components or cases. Rewrite using `[T.coeff_π_pow_mul_of_lt _ h, if_neg (by omega)]`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le' h`. Rewrite using `[T.coeff_π_pow_mul_add, coeff_teich]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem coeff_π_pow_mul_teich (k : ℕ) (c : L) (n : ℕ) :
    T.coeff (T.π ^ k * T.teich c) n = if n = k then c else 0 := by
  rcases lt_or_ge n k with h | h
  · rw [T.coeff_π_pow_mul_of_lt _ h, if_neg (by omega)]
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
    rw [T.coeff_π_pow_mul_add, coeff_teich]
    split_ifs <;> first | rfl | omega

/- English proof (translation)
Proceed by induction on `n generalizing a with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply, pow_succ, pow_mul, ih]`. Conclude with `frobeniusEquiv_symm_pow_p L p a`.
-/
theorem iterate_frobeniusEquiv_symm_pow (a : L) (n : ℕ) :
    ((((frobeniusEquiv L p).symm : L →+* L))^[n] a) ^ p ^ n = a := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih]
    exact frobeniusEquiv_symm_pow_p L p a

/- English proof (translation)
Rewrite using `[← norm_pow, iterate_frobeniusEquiv_symm_pow]`.
-/
theorem norm_iterate_frobeniusEquiv_symm_pow (a : L) (n : ℕ) :
    ‖((((frobeniusEquiv L p).symm : L →+* L))^[n] a)‖ ^ p ^ n = ‖a‖ := by
  rw [← norm_pow, iterate_frobeniusEquiv_symm_pow]

/- English proof (translation)
Establish `h` using `norm_iterate_frobeniusEquiv_symm_pow a n`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).1 (h ▸ ha)`.
-/
theorem norm_iterate_frobeniusEquiv_symm_le_one {a : L} (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖((((frobeniusEquiv L p).symm : L →+* L))^[n] a)‖ ≤ 1 := by
  have h := norm_iterate_frobeniusEquiv_symm_pow a n
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).1 (h ▸ ha)

/- English proof (translation)
Use `T.mem_int_of_approx _ fun N => ?_` and prove the remaining obligations. Take `⟨z, hz, hzb⟩` from `T.exists_mem_int _ (norm_iterate_frobeniusEquiv_symm_le_one ha N)`. Conclude with `⟨z ^ p ^ N, pow_mem hz _, T.span_pow_anti (Nat.le_succ N) (T.teich_sub_pow_mem a N z hzb)⟩`.
-/
theorem teich_mem_int {a : L} (ha : ‖a‖ ≤ 1) : T.teich a ∈ T.int := by
  refine T.mem_int_of_approx _ fun N => ?_
  obtain ⟨z, hz, hzb⟩ := T.exists_mem_int _ (norm_iterate_frobeniusEquiv_symm_le_one ha N)
  exact ⟨z ^ p ^ N, pow_mem hz _, T.span_pow_anti (Nat.le_succ N) (T.teich_sub_pow_mem a N z hzb)⟩

/- English proof (translation)
Establish `h1 : x - T.teich (T.red x) ∈ T.int` using `sub_mem hx (T.teich_mem_int (T.norm_red_le_one x hx))`. Take `⟨y, hy, hxy⟩` from `T.exists_eq_π_mul _ h1 (T.red_sub_teich_red x)`. Rewrite `hxy` using `[T.sub_teich_eq_π_mul_tail]`. Rewrite using `[T.π_mul_cancel hxy]` and apply the resulting hypothesis.
-/
theorem tail_mem_int {x : Γ} (hx : x ∈ T.int) : T.tail x ∈ T.int := by
  have h1 : x - T.teich (T.red x) ∈ T.int :=
    sub_mem hx (T.teich_mem_int (T.norm_red_le_one x hx))
  obtain ⟨y, hy, hxy⟩ := T.exists_eq_π_mul _ h1 (T.red_sub_teich_red x)
  rw [T.sub_teich_eq_π_mul_tail] at hxy
  rwa [T.π_mul_cancel hxy]

/- English proof (translation)
The claim follows from `Subring.sum_mem _ fun i hi => mul_mem (pow_mem T.π_mem_int _) (T.teich_mem_int (h i (Finset.mem_range.1 hi)))`.
-/
theorem finSum_mem_int {a : ℕ → L} {n : ℕ} (h : ∀ i < n, ‖a i‖ ≤ 1) : T.finSum a n ∈ T.int :=
  Subring.sum_mem _ fun i hi =>
    mul_mem (pow_mem T.π_mem_int _) (T.teich_mem_int (h i (Finset.mem_range.1 hi)))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx n`. Establish `: T.tail^[n] x ∈ T.int`. Proceed by induction on `n with`. Consider the case `zero => exact hx`.

Consider the case `succ n ih => rw [Function.iterate_succ_apply']`. Conclude with `T.tail_mem_int ih`. Conclude with `T.norm_red_le_one _ this`. Introduce `h`. Conclude with `T.mem_int_of_approx x fun N => ⟨T.partialSum x N, T.finSum_mem_int fun i _ => h i, T.sub_partialSum_mem x N⟩`.
-/
theorem mem_int_iff {x : Γ} : x ∈ T.int ↔ ∀ n, ‖T.coeff x n‖ ≤ 1 := by
  constructor
  · intro hx n
    have : T.tail^[n] x ∈ T.int := by
      induction n with
      | zero => exact hx
      | succ n ih => rw [Function.iterate_succ_apply']; exact T.tail_mem_int ih
    exact T.norm_red_le_one _ this
  · intro h
    exact T.mem_int_of_approx x fun N =>
      ⟨T.partialSum x N, T.finSum_mem_int fun i _ => h i, T.sub_partialSum_mem x N⟩

/- English proof (translation)
The claim follows from `map_natCast _ n`.
-/
theorem red_natCast (n : ℕ) : T.red (n : Γ) = (n : L) := map_natCast _ n

/- English proof (translation)
The claim follows from `T.exists_eq_π_mul _ (natCast_mem _ p) (by rw [red_natCast, CharP.cast_eq_zero])`.
-/
theorem exists_natCast_p_eq : ∃ w ∈ T.int, (p : Γ) = T.π * w :=
  T.exists_eq_π_mul _ (natCast_mem _ p) (by rw [red_natCast, CharP.cast_eq_zero])

def PrefixLe (x : Γ) (n : ℕ) (b : ℝ) : Prop := ∀ m ≤ n, ‖T.coeff x m‖ ≤ b

variable {T} in
/- English proof (translation)
Introduce `m hm` and use `(h m hm).trans hb`.
-/
theorem PrefixLe.mono {x : Γ} {n : ℕ} {b b' : ℝ} (h : T.PrefixLe x n b) (hb : b ≤ b') :
    T.PrefixLe x n b' := fun m hm => (h m hm).trans hb

variable {T} in
/- English proof (translation)
The claim follows from `(norm_nonneg _).trans (h 0 (Nat.zero_le _))`.
-/
theorem PrefixLe.nonneg {x : Γ} {n : ℕ} {b : ℝ} (h : T.PrefixLe x n b) : 0 ≤ b :=
  (norm_nonneg _).trans (h 0 (Nat.zero_le _))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨T.finSum (fun i => T.coeff x i / c) (n + 1), T.finSum_mem_int fun i hi => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div, div_le_one (norm_pos_iff.2 hc)]`. Conclude with `h i (by omega)`.

Establish `: T.teich c * T.finSum (fun i => T.coeff x i / c) (n + 1) = T.partialSum x (n + 1)`. Simplify using `only [finSum, partialSum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, ← T.teich_mul, mul_div_cancel₀ _ hc]`. Rewrite using `[this]`.

Conclude with `T.sub_partialSum_mem x (n + 1)`. Introduce and unpack `⟨u, hu, h⟩ m hm`. Rewrite using `[T.coeff_eq_coeff_of_sub_mem h m hm, coeff_teich_mul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) ((T.mem_int_iff.1 hu) m)`.
-/
theorem prefixLe_iff_exists {x : Γ} {n : ℕ} {c : L} (hc : c ≠ 0) :
    T.PrefixLe x n ‖c‖ ↔ ∃ u ∈ T.int, x - T.teich c * u ∈ Ideal.span {T.π ^ (n + 1)} := by
  constructor
  · intro h
    refine ⟨T.finSum (fun i => T.coeff x i / c) (n + 1), T.finSum_mem_int fun i hi => ?_, ?_⟩
    · rw [norm_div, div_le_one (norm_pos_iff.2 hc)]
      exact h i (by omega)
    · have : T.teich c * T.finSum (fun i => T.coeff x i / c) (n + 1) = T.partialSum x (n + 1) := by
        simp only [finSum, partialSum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_left_comm, ← T.teich_mul, mul_div_cancel₀ _ hc]
      rw [this]; exact T.sub_partialSum_mem x (n + 1)
  · rintro ⟨u, hu, h⟩ m hm
    rw [T.coeff_eq_coeff_of_sub_mem h m hm, coeff_teich_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((T.mem_int_iff.1 hu) m)

/- English proof (translation)
Take `⟨m, hm, hmax⟩` from `(Finset.range (n + 1)).exists_max_image (fun i => ‖T.coeff x i‖) ⟨0, by simp⟩`. Conclude with `⟨T.coeff x m, fun i hi => hmax i (Finset.mem_range.2 (by omega)), fun b hb => hb m (by simpa [Nat.lt_succ_iff] using hm)⟩`.
-/
theorem exists_prefix_max (x : Γ) (n : ℕ) :
    ∃ c : L, T.PrefixLe x n ‖c‖ ∧ ∀ b, T.PrefixLe x n b → ‖c‖ ≤ b := by
  obtain ⟨m, hm, hmax⟩ := (Finset.range (n + 1)).exists_max_image (fun i => ‖T.coeff x i‖)
    ⟨0, by simp⟩
  exact ⟨T.coeff x m, fun i hi => hmax i (Finset.mem_range.2 (by omega)),
    fun b hb => hb m (by simpa [Nat.lt_succ_iff] using hm)⟩

/- English proof (translation)
Establish `h0 : T.partialSum x (n + 1) = 0`. Simplify using `only [partialSum, finSum]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Use `h i (by simpa [Nat.lt_succ_iff] using hi)` as an intermediate fact. Rewrite using `[norm_le_zero_iff.1 this, T.teich_zero, mul_zero]`.

Simplify `T.sub_partialSum_mem x (n + 1)` using `[h0]`.
-/
theorem mem_span_of_prefixLe_zero {x : Γ} {n : ℕ} (h : T.PrefixLe x n 0) :
    x ∈ Ideal.span {T.π ^ (n + 1)} := by
  have h0 : T.partialSum x (n + 1) = 0 := by
    simp only [partialSum, finSum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have := h i (by simpa [Nat.lt_succ_iff] using hi)
    rw [norm_le_zero_iff.1 this, T.teich_zero, mul_zero]
  simpa [h0] using T.sub_partialSum_mem x (n + 1)

/- English proof (translation)
Introduce `m hm` and use `by rw [T.coeff_of_mem_span h m hm, norm_zero]; exact hb`.
-/
theorem prefixLe_of_mem_span {x : Γ} {n : ℕ} (h : x ∈ Ideal.span {T.π ^ (n + 1)}) {b : ℝ}
    (hb : 0 ≤ b) : T.PrefixLe x n b := fun m hm => by
  rw [T.coeff_of_mem_span h m hm, norm_zero]; exact hb

/- English proof (translation)
The claim follows from `T.prefixLe_of_mem_span (zero_mem _) hb`.
-/
theorem prefixLe_zero (n : ℕ) {b : ℝ} (hb : 0 ≤ b) : T.PrefixLe 0 n b :=
  T.prefixLe_of_mem_span (zero_mem _) hb

/- English proof (translation)
Take `⟨c₁, h₁, h₁'⟩` from `T.exists_prefix_max x n`. Take `⟨c₂, h₂, h₂'⟩` from `T.exists_prefix_max y n`. Choose the witnesses or unpack the hypotheses as in `⟨c, hcx, hcy, hcb⟩ : ∃ c : L, T.PrefixLe x n ‖c‖ ∧ T.PrefixLe y n ‖c‖ ∧ ‖c‖ ≤ b := by`. Break down `le_total ‖c₁‖ ‖c₂‖ with h | h` into its components or cases. Conclude with `⟨c₂, h₁.mono h, h₂, h₂' b hy⟩`.

Conclude with `⟨c₁, h₁, h₂.mono h, h₁' b hx⟩`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Rewrite `hcx`, `hcy` using `[norm_zero]`. Conclude with `T.prefixLe_of_mem_span (add_mem (T.mem_span_of_prefixLe_zero hcx) (T.mem_span_of_prefixLe_zero hcy)) hx.nonneg`.

Take `⟨u, hu, hxu⟩` from `(T.prefixLe_iff_exists hc).1 hcx`. Take `⟨v, hv, hyv⟩` from `(T.prefixLe_iff_exists hc).1 hcy`. Use `((T.prefixLe_iff_exists hc).2 ⟨u + v, add_mem hu hv, ?_⟩).mono hcb` and prove the remaining obligations. Use `add_mem hxu hyv` as an intermediate fact. Rewrite `this` using `[show x - T.teich c * u + (y - T.teich c * v) = x + y - T.teich c * (u + v) by ring]`. Then use the resulting hypothesis.
-/
theorem prefixLe_add {x y : Γ} {n : ℕ} {b : ℝ} (hx : T.PrefixLe x n b) (hy : T.PrefixLe y n b) :
    T.PrefixLe (x + y) n b := by
  obtain ⟨c₁, h₁, h₁'⟩ := T.exists_prefix_max x n
  obtain ⟨c₂, h₂, h₂'⟩ := T.exists_prefix_max y n
  obtain ⟨c, hcx, hcy, hcb⟩ : ∃ c : L, T.PrefixLe x n ‖c‖ ∧ T.PrefixLe y n ‖c‖ ∧ ‖c‖ ≤ b := by
    rcases le_total ‖c₁‖ ‖c₂‖ with h | h
    · exact ⟨c₂, h₁.mono h, h₂, h₂' b hy⟩
    · exact ⟨c₁, h₁, h₂.mono h, h₁' b hx⟩
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero] at hcx hcy
    exact T.prefixLe_of_mem_span (add_mem (T.mem_span_of_prefixLe_zero hcx)
      (T.mem_span_of_prefixLe_zero hcy)) hx.nonneg
  · obtain ⟨u, hu, hxu⟩ := (T.prefixLe_iff_exists hc).1 hcx
    obtain ⟨v, hv, hyv⟩ := (T.prefixLe_iff_exists hc).1 hcy
    refine ((T.prefixLe_iff_exists hc).2 ⟨u + v, add_mem hu hv, ?_⟩).mono hcb
    have := add_mem hxu hyv
    rwa [show x - T.teich c * u + (y - T.teich c * v) = x + y - T.teich c * (u + v) by ring] at this

/- English proof (translation)
Take `⟨c, hc₁, hc₂⟩` from `T.exists_prefix_max x n`. Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Rewrite `hc₁` using `[norm_zero]`. Conclude with `T.prefixLe_of_mem_span (neg_mem (T.mem_span_of_prefixLe_zero hc₁)) hx.nonneg`.

Take `⟨u, hu, hxu⟩` from `(T.prefixLe_iff_exists hc).1 hc₁`. Use `((T.prefixLe_iff_exists hc).2 ⟨-u, neg_mem hu, ?_⟩).mono (hc₂ b hx)` and prove the remaining obligations. Use `neg_mem hxu` as an intermediate fact. Rewrite `this` using `[show -(x - T.teich c * u) = -x - T.teich c * (-u) by ring]`. Then use the resulting hypothesis.
-/
theorem prefixLe_neg {x : Γ} {n : ℕ} {b : ℝ} (hx : T.PrefixLe x n b) : T.PrefixLe (-x) n b := by
  obtain ⟨c, hc₁, hc₂⟩ := T.exists_prefix_max x n
  by_cases hc : c = 0
  · subst hc
    rw [norm_zero] at hc₁
    exact T.prefixLe_of_mem_span (neg_mem (T.mem_span_of_prefixLe_zero hc₁)) hx.nonneg
  · obtain ⟨u, hu, hxu⟩ := (T.prefixLe_iff_exists hc).1 hc₁
    refine ((T.prefixLe_iff_exists hc).2 ⟨-u, neg_mem hu, ?_⟩).mono (hc₂ b hx)
    have := neg_mem hxu
    rwa [show -(x - T.teich c * u) = -x - T.teich c * (-u) by ring] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using T.prefixLe_neg h, T.prefixLe_neg⟩`.
-/
theorem prefixLe_neg_iff {x : Γ} {n : ℕ} {b : ℝ} : T.PrefixLe (-x) n b ↔ T.PrefixLe x n b :=
  ⟨fun h => by simpa using T.prefixLe_neg h, T.prefixLe_neg⟩

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `T.prefixLe_add hx (T.prefixLe_neg hy)`.
-/
theorem prefixLe_sub {x y : Γ} {n : ℕ} {b : ℝ} (hx : T.PrefixLe x n b) (hy : T.PrefixLe y n b) :
    T.PrefixLe (x - y) n b := by
  rw [sub_eq_add_neg]; exact T.prefixLe_add hx (T.prefixLe_neg hy)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using T.prefixLe_zero n hb`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `T.prefixLe_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem prefixLe_sum {ι : Type*} (s : Finset ι) (f : ι → Γ) {n : ℕ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i ∈ s, T.PrefixLe (f i) n b) : T.PrefixLe (∑ i ∈ s, f i) n b := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T.prefixLe_zero n hb
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact T.prefixLe_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `m hm`. Rewrite using `[coeff_π_pow_mul_teich]`. Use `split_ifs with h'`. Substitute `h'` using the available equality. Conclude with `h hm`.

Simplify using `using hb`.
-/
theorem prefixLe_π_pow_mul_teich (k : ℕ) (c : L) (n : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (h : k ≤ n → ‖c‖ ≤ b) : T.PrefixLe (T.π ^ k * T.teich c) n b := by
  intro m hm
  rw [coeff_π_pow_mul_teich]
  split_ifs with h'
  · subst h'; exact h hm
  · simpa using hb

/- English proof (translation)
Establish `h1 : x * y - T.partialSum x (n + 1) * T.partialSum y (n + 1) ∈ Ideal.span {T.π ^ (n + 1)}`. Establish `: x * y - T.partialSum x (n + 1) * T.partialSum y (n + 1) = (x - T.partialSum x (n + 1)) * y + T.partialSum x (n + 1) * (y - T.partialSum y (n + 1))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ (T.sub_partialSum_mem x _)) (Ideal.mul_mem_left _ _ (T.sub_partialSum_mem y _))`.

Establish `h2 : T.PrefixLe (T.partialSum x (n + 1) * T.partialSum y (n + 1)) n B`. Simplify using `only [partialSum, finSum, Finset.sum_mul_sum]`. Use `T.prefixLe_sum _ _ hB fun i _ => T.prefixLe_sum _ _ hB fun j _ => ?_` and prove the remaining obligations. Establish `: T.π ^ i * T.teich (T.coeff x i) * (T.π ^ j * T.teich (T.coeff y j)) = T.π ^ (i + j) * T.teich (T.coeff x i * T.coeff y j)`. Rewrite using `[T.teich_mul, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `T.prefixLe_π_pow_mul_teich _ _ _ hB fun hij => by rw [norm_mul]; exact h i j hij`. Use `T.prefixLe_add h2 (T.prefixLe_of_mem_span h1 hB)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem prefixLe_mul {x y : Γ} {n : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i j, i + j ≤ n → ‖T.coeff x i‖ * ‖T.coeff y j‖ ≤ B) : T.PrefixLe (x * y) n B := by
  have h1 : x * y - T.partialSum x (n + 1) * T.partialSum y (n + 1) ∈
      Ideal.span {T.π ^ (n + 1)} := by
    have : x * y - T.partialSum x (n + 1) * T.partialSum y (n + 1) =
        (x - T.partialSum x (n + 1)) * y + T.partialSum x (n + 1) * (y - T.partialSum y (n + 1)) := by
      ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ (T.sub_partialSum_mem x _))
      (Ideal.mul_mem_left _ _ (T.sub_partialSum_mem y _))
  have h2 : T.PrefixLe (T.partialSum x (n + 1) * T.partialSum y (n + 1)) n B := by
    simp only [partialSum, finSum, Finset.sum_mul_sum]
    refine T.prefixLe_sum _ _ hB fun i _ => T.prefixLe_sum _ _ hB fun j _ => ?_
    have : T.π ^ i * T.teich (T.coeff x i) * (T.π ^ j * T.teich (T.coeff y j)) =
        T.π ^ (i + j) * T.teich (T.coeff x i * T.coeff y j) := by
      rw [T.teich_mul, pow_add]; ring
    rw [this]
    exact T.prefixLe_π_pow_mul_teich _ _ _ hB fun hij => by rw [norm_mul]; exact h i j hij
  have := T.prefixLe_add h2 (T.prefixLe_of_mem_span h1 hB)
  rwa [add_sub_cancel] at this

/- English proof (translation)
Establish `hXY : T.red X = T.red Y`. Use `congrArg T.red h` as an intermediate fact. Rewrite `this` using `[map_sub, map_mul, map_pow, red_π, zero_pow (by omega), zero_mul, sub_eq_zero]`. Conclude with `this`. Establish `hG : (∑ i ∈ Finset.range p, X ^ i * Y ^ (p - 1 - i)) ∈ T.int` using `Subring.sum_mem _ fun i _ => mul_mem (pow_mem hX _) (pow_mem hY _)`.

Establish `hGred : T.red (∑ i ∈ Finset.range p, X ^ i * Y ^ (p - 1 - i)) = 0`. Establish `: ∀ i ∈ Finset.range p, T.red (X ^ i * Y ^ (p - 1 - i)) = T.red Y ^ (p - 1)`. Introduce `i hi`. Rewrite using `[map_mul, map_pow, map_pow, hXY, ← pow_add]`. Use `congr 1`.

Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[map_sum, Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]`. Take `⟨g, hg, hGg⟩` from `T.exists_eq_π_mul _ hG hGred`. Use `⟨g * v, mul_mem hg hv, ?_⟩` and prove the remaining obligations.

Rewrite using `[← geom_sum₂_mul, hGg, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pow_sub_pow {X Y v : Γ} (hX : X ∈ T.int) (hY : Y ∈ T.int) (hv : v ∈ T.int)
    {j : ℕ} (hj : 1 ≤ j) (h : X - Y = T.π ^ j * v) :
    ∃ w ∈ T.int, X ^ p - Y ^ p = T.π ^ (j + 1) * w := by
  have hXY : T.red X = T.red Y := by
    have := congrArg T.red h
    rw [map_sub, map_mul, map_pow, red_π, zero_pow (by omega), zero_mul, sub_eq_zero] at this
    exact this
  have hG : (∑ i ∈ Finset.range p, X ^ i * Y ^ (p - 1 - i)) ∈ T.int :=
    Subring.sum_mem _ fun i _ => mul_mem (pow_mem hX _) (pow_mem hY _)
  have hGred : T.red (∑ i ∈ Finset.range p, X ^ i * Y ^ (p - 1 - i)) = 0 := by
    have : ∀ i ∈ Finset.range p, T.red (X ^ i * Y ^ (p - 1 - i)) = T.red Y ^ (p - 1) := by
      intro i hi
      rw [map_mul, map_pow, map_pow, hXY, ← pow_add]
      congr 1; have := Finset.mem_range.1 hi; omega
    rw [map_sum, Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      CharP.cast_eq_zero, zero_mul]
  obtain ⟨g, hg, hGg⟩ := T.exists_eq_π_mul _ hG hGred
  refine ⟨g * v, mul_mem hg hv, ?_⟩
  rw [← geom_sum₂_mul, hGg, h]; ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨z, hz, by simp⟩`. Consider the case `succ k ih`. Take `⟨w, hw, h⟩` from `ih`. Rewrite using `[pow_succ, pow_mul, pow_mul]`.

Conclude with `T.exists_pow_sub_pow (pow_mem (add_mem hA (mul_mem T.π_mem_int hz)) _) (pow_mem hA _) hw (by omega) h`.
-/
theorem exists_add_π_mul_pow_sub (A z : Γ) (hA : A ∈ T.int) (hz : z ∈ T.int) (k : ℕ) :
    ∃ w ∈ T.int, (A + T.π * z) ^ p ^ k - A ^ p ^ k = T.π ^ (k + 1) * w := by
  induction k with
  | zero => exact ⟨z, hz, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw, h⟩ := ih
    rw [pow_succ, pow_mul, pow_mul]
    exact T.exists_pow_sub_pow (pow_mem (add_mem hA (mul_mem T.π_mem_int hz)) _) (pow_mem hA _) hw
      (by omega) h

/- English proof (translation)
Take `⟨wp, hwp, hpw⟩` from `T.exists_natCast_p_eq`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Conclude with `⟨0, zero_mem _, by simp⟩`. Take `⟨N, hN⟩ : ∃ N, p ^ k = N + 1` from `⟨p ^ k - 1, by have := Nat.one_le_pow k p hp.out.pos; omega⟩`. Establish `hlt : N + 1 ≠ 1`.

Rewrite using `[← hN]`. Conclude with `(Nat.one_lt_pow hk.ne' hp.out.one_lt).ne'`. Establish `hdvd : ∀ m < N, p ∣ (N + 1).choose (m + 1)` using `fun m hm => hN ▸ hp.out.dvd_choose_pow (by omega) (by omega)`. Use `⟨wp * ∑ m ∈ Finset.range N, T.teich b ^ m * (((N + 1).choose (m + 1) / p : ℕ) : Γ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem hwp (Subring.sum_mem _ fun m _ => mul_mem (pow_mem (T.teich_mem_int hb) _) (natCast_mem _ _))`.

Establish `hsum : ∑ m ∈ Finset.range N, T.teich b ^ (m + 1) * 1 ^ (N + 1 - (m + 1)) * ((N + 1).choose (m + 1) : Γ) = T.π * T.teich b * (wp * ∑ m ∈ Finset.range N, T.teich b ^ m * (((N + 1).choose (m + 1) / p : ℕ) : Γ))`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hc : ((N + 1).choose (m + 1) : Γ) = (p : Γ) * (((N + 1).choose (m + 1) / p : ℕ) : Γ)`. Rewrite using `[← Nat.cast_mul, Nat.mul_div_cancel' (hdvd m (Finset.mem_range.1 hm))]`.

Rewrite using `[hc, hpw, one_pow, mul_one, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[add_comm (1 : Γ), add_pow, T.teich_pow, hN, Finset.sum_range_succ, Finset.sum_range_succ', hsum]`. Simplify using `only [pow_zero, one_pow, mul_one, one_mul, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, Nat.sub_self, Nat.sub_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_one_add_teich_pow {b : L} (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ∃ U ∈ T.int, (1 + T.teich b) ^ p ^ k = 1 + T.teich (b ^ p ^ k) + T.π * T.teich b * U := by
  obtain ⟨wp, hwp, hpw⟩ := T.exists_natCast_p_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨0, zero_mem _, by simp⟩
  obtain ⟨N, hN⟩ : ∃ N, p ^ k = N + 1 :=
    ⟨p ^ k - 1, by have := Nat.one_le_pow k p hp.out.pos; omega⟩
  have hlt : N + 1 ≠ 1 := by
    rw [← hN]; exact (Nat.one_lt_pow hk.ne' hp.out.one_lt).ne'
  have hdvd : ∀ m < N, p ∣ (N + 1).choose (m + 1) := fun m hm =>
    hN ▸ hp.out.dvd_choose_pow (by omega) (by omega)
  refine ⟨wp * ∑ m ∈ Finset.range N, T.teich b ^ m * (((N + 1).choose (m + 1) / p : ℕ) : Γ), ?_, ?_⟩
  · exact mul_mem hwp (Subring.sum_mem _ fun m _ =>
      mul_mem (pow_mem (T.teich_mem_int hb) _) (natCast_mem _ _))
  · have hsum : ∑ m ∈ Finset.range N, T.teich b ^ (m + 1) * 1 ^ (N + 1 - (m + 1)) *
        ((N + 1).choose (m + 1) : Γ) = T.π * T.teich b *
          (wp * ∑ m ∈ Finset.range N, T.teich b ^ m * (((N + 1).choose (m + 1) / p : ℕ) : Γ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hc : ((N + 1).choose (m + 1) : Γ) = (p : Γ) * (((N + 1).choose (m + 1) / p : ℕ) : Γ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' (hdvd m (Finset.mem_range.1 hm))]
      rw [hc, hpw, one_pow, mul_one, pow_succ]; ring
    rw [add_comm (1 : Γ), add_pow, T.teich_pow, hN, Finset.sum_range_succ, Finset.sum_range_succ',
      hsum]
    simp only [pow_zero, one_pow, mul_one, one_mul, Nat.choose_zero_right, Nat.choose_self,
      Nat.cast_one, Nat.sub_self, Nat.sub_zero]
    ring

/- English proof (translation)
Use `set b' := ((((frobeniusEquiv L p).symm : L →+* L))^[k] b) with hb'def`. Establish `hb' : ‖b'‖ ≤ 1` using `norm_iterate_frobeniusEquiv_symm_le_one hb k`. Establish `hpow : b' ^ p ^ k = b` using `iterate_frobeniusEquiv_symm_pow b k`. Distinguish the cases in `hb0 : b' = 0`. Establish `: b = 0` using `by rw [← hpow, hb0, zero_pow (pow_ne_zero _ hp.out.ne_zero)]`.

Substitute `this` using the available equality. Rewrite using `[hb0, norm_zero]`. Conclude with `T.prefixLe_of_mem_span (by simp) le_rfl`. Establish `h1b' : ‖1 + b'‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hb')`. Take `⟨u0, hu0, hu0'⟩` from `T.exists_eq_π_mul (T.teich (1 + b') - (1 + T.teich b')) (sub_mem (T.teich_mem_int h1b') (add_mem (one_mem _) (T.teich_mem_int hb'))) (by simp [red_teich])`.

Take `⟨w, hw, hw'⟩` from `T.exists_add_π_mul_pow_sub (1 + T.teich b') u0 (add_mem (one_mem _) (T.teich_mem_int hb')) hu0 k`. Take `⟨U, hU, hU'⟩` from `T.exists_one_add_teich_pow hb' k`. Use `(T.prefixLe_iff_exists hb0).2 ⟨T.π * U, mul_mem T.π_mem_int hU, ?_⟩` and prove the remaining obligations. Establish `hfr : (1 + b') ^ p ^ k = 1 + b` using `by rw [add_pow_char_pow, one_pow, hpow]`. Establish `e1 : T.teich (1 + b) = (1 + T.teich b' + T.π * u0) ^ p ^ k`.

Rewrite using `[← hfr, T.teich_pow]`. Use `congr 1`. Rewrite using `[← hu0']`. Expand and normalize the polynomial expressions, which then agree. Establish `: T.teich (1 + b) - 1 - T.teich b - T.teich b' * (T.π * U) = T.π ^ (k + 1) * w`.

Rewrite using `[e1, ← hw', hU', hpow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `T.π_pow_mul_mem le_rfl w`.
-/
theorem prefixLe_teich_one_add_sub {b : L} (hb : ‖b‖ ≤ 1) (k : ℕ) :
    T.PrefixLe (T.teich (1 + b) - 1 - T.teich b) k
      ‖((((frobeniusEquiv L p).symm : L →+* L))^[k] b)‖ := by
  set b' := ((((frobeniusEquiv L p).symm : L →+* L))^[k] b) with hb'def
  have hb' : ‖b'‖ ≤ 1 := norm_iterate_frobeniusEquiv_symm_le_one hb k
  have hpow : b' ^ p ^ k = b := iterate_frobeniusEquiv_symm_pow b k
  by_cases hb0 : b' = 0
  · have : b = 0 := by rw [← hpow, hb0, zero_pow (pow_ne_zero _ hp.out.ne_zero)]
    subst this
    rw [hb0, norm_zero]
    exact T.prefixLe_of_mem_span (by simp) le_rfl
  have h1b' : ‖1 + b'‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by simp) hb')
  obtain ⟨u0, hu0, hu0'⟩ := T.exists_eq_π_mul (T.teich (1 + b') - (1 + T.teich b'))
    (sub_mem (T.teich_mem_int h1b') (add_mem (one_mem _) (T.teich_mem_int hb')))
    (by simp [red_teich])
  obtain ⟨w, hw, hw'⟩ := T.exists_add_π_mul_pow_sub (1 + T.teich b') u0
    (add_mem (one_mem _) (T.teich_mem_int hb')) hu0 k
  obtain ⟨U, hU, hU'⟩ := T.exists_one_add_teich_pow hb' k
  refine (T.prefixLe_iff_exists hb0).2 ⟨T.π * U, mul_mem T.π_mem_int hU, ?_⟩
  have hfr : (1 + b') ^ p ^ k = 1 + b := by rw [add_pow_char_pow, one_pow, hpow]
  have e1 : T.teich (1 + b) = (1 + T.teich b' + T.π * u0) ^ p ^ k := by
    rw [← hfr, T.teich_pow]
    congr 1; rw [← hu0']; ring
  have : T.teich (1 + b) - 1 - T.teich b - T.teich b' * (T.π * U) = T.π ^ (k + 1) * w := by
    rw [e1, ← hw', hU', hpow]; ring
  rw [this]; exact T.π_pow_mul_mem le_rfl w

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_add' hδ (by simp), sub_add_cancel, Real.rpow_one]`. Use `_ ≤ B ^ (1 - t) * δ ^ t := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hδ hδB (by linarith)) (Real.rpow_nonneg hδ _)`.
-/
theorem le_rpow_mix {δ B t : ℝ} (hδ : 0 ≤ δ) (hδB : δ ≤ B) (ht : t ≤ 1) :
    δ ≤ B ^ (1 - t) * δ ^ t := by
  calc δ = δ ^ (1 - t) * δ ^ t := by
        rw [← Real.rpow_add' hδ (by simp), sub_add_cancel, Real.rpow_one]
    _ ≤ B ^ (1 - t) * δ ^ t :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hδ hδB (by linarith)) (Real.rpow_nonneg hδ _)

/- English proof (translation)
Establish `hB : 0 ≤ B` using `hδ.trans hδB`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem rpow_mix_le {δ B t : ℝ} (hδ : 0 ≤ δ) (hδB : δ ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    B ^ (1 - t) * δ ^ t ≤ B := by
  have hB : 0 ≤ B := hδ.trans hδB
  calc B ^ (1 - t) * δ ^ t ≤ B ^ (1 - t) * B ^ t :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ hδB ht) (Real.rpow_nonneg hB _)
    _ = B := by rw [← Real.rpow_add' hB (by simp), sub_add_cancel, Real.rpow_one]

/- English proof (translation)
Establish `h1 : (1 : ℝ) ≤ ((p ^ k : ℕ) : ℝ)` using `by exact_mod_cast Nat.one_le_pow k p hp.out.pos`. Conclude with `⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ h1⟩`.
-/
theorem inv_pow_pos_le_one (k : ℕ) : 0 < ((p ^ k : ℕ) : ℝ)⁻¹ ∧ ((p ^ k : ℕ) : ℝ)⁻¹ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ ((p ^ k : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow k p hp.out.pos
  exact ⟨inv_pos.2 (by linarith), inv_le_one_of_one_le₀ h1⟩

/- English proof (translation)
Establish `hN : (p ^ k : ℕ) ≠ 0` using `pow_ne_zero _ hp.out.ne_zero`. Distinguish the cases in `ha : a = 0`. Establish `he : e = 0` using `by rw [ha, norm_zero] at h; exact norm_le_zero_iff.1 h`. Substitute `ha` using the available equality. Substitute `he` using the available equality.

Conclude with `T.prefixLe_of_mem_span (by simp) (by positivity)`. Establish `hb : ‖e / a‖ ≤ 1` using `by rw [norm_div, div_le_one (norm_pos_iff.2 ha)]; exact h`. Establish `hae : T.teich (a + e) - T.teich a - T.teich e = T.teich a * (T.teich (1 + e / a) - 1 - T.teich (e / a))`. Establish `h1 : a * (1 + e / a) = a + e` using `by field_simp`. Establish `h2 : a * (e / a) = e` using `by field_simp`.

Combine the equalities or inequalities in the displayed calculation. Introduce `m hm`. Rewrite using `[hae, coeff_teich_mul, norm_mul]`. Establish `hD` using `T.prefixLe_teich_one_add_sub hb k m hm`. Establish `hnb' : ‖((((frobeniusEquiv L p).symm : L →+* L))^[k] (e / a))‖ = ‖e / a‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹`.

Rewrite using `[← norm_iterate_frobeniusEquiv_symm_pow (e / a) k, Real.pow_rpow_inv_natCast (norm_nonneg _) hN]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hnb', norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _), Real.rpow_sub (norm_pos_iff.2 ha), Real.rpow_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prefixLe_teich_add_sub {a e : L} (h : ‖e‖ ≤ ‖a‖) (k : ℕ) :
    T.PrefixLe (T.teich (a + e) - T.teich a - T.teich e) k
      (‖a‖ ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * ‖e‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹) := by
  have hN : (p ^ k : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  by_cases ha : a = 0
  · have he : e = 0 := by rw [ha, norm_zero] at h; exact norm_le_zero_iff.1 h
    subst ha; subst he
    exact T.prefixLe_of_mem_span (by simp) (by positivity)
  have hb : ‖e / a‖ ≤ 1 := by rw [norm_div, div_le_one (norm_pos_iff.2 ha)]; exact h
  have hae : T.teich (a + e) - T.teich a - T.teich e =
      T.teich a * (T.teich (1 + e / a) - 1 - T.teich (e / a)) := by
    have h1 : a * (1 + e / a) = a + e := by field_simp
    have h2 : a * (e / a) = e := by field_simp
    calc T.teich (a + e) - T.teich a - T.teich e
        = T.teich (a * (1 + e / a)) - T.teich a - T.teich (a * (e / a)) := by rw [h1, h2]
      _ = _ := by rw [T.teich_mul, T.teich_mul]; ring
  intro m hm
  rw [hae, coeff_teich_mul, norm_mul]
  have hD := T.prefixLe_teich_one_add_sub hb k m hm
  have hnb' : ‖((((frobeniusEquiv L p).symm : L →+* L))^[k] (e / a))‖ =
      ‖e / a‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹ := by
    rw [← norm_iterate_frobeniusEquiv_symm_pow (e / a) k,
      Real.pow_rpow_inv_natCast (norm_nonneg _) hN]
  calc ‖a‖ * ‖T.coeff (T.teich (1 + e / a) - 1 - T.teich (e / a)) m‖
      ≤ ‖a‖ * ‖((((frobeniusEquiv L p).symm : L →+* L))^[k] (e / a))‖ :=
        mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = ‖a‖ ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * ‖e‖ ^ ((p ^ k : ℕ) : ℝ)⁻¹ := by
        rw [hnb', norm_div, Real.div_rpow (norm_nonneg _) (norm_nonneg _),
          Real.rpow_sub (norm_pos_iff.2 ha), Real.rpow_one]
        ring

/- English proof (translation)
Take `⟨ht0, ht1⟩` from `inv_pow_pos_le_one (p := p) k`. Use `set t := ((p ^ k : ℕ) : ℝ)⁻¹`. Break down `le_total ‖e‖ ‖a‖ with h | h` into its components or cases. Use `(T.prefixLe_teich_add_sub h k).mono ?_` and prove the remaining obligations. Conclude with `mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha (by linarith)) (Real.rpow_le_rpow (norm_nonneg _) he ht0.le) (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (hδ.trans hδB) _)`.

Use `T.prefixLe_teich_add_sub h k` as an intermediate fact. Rewrite using `[show T.teich (e + a) - T.teich e - T.teich a = T.teich (a + e) - T.teich a - T.teich e by`. Rewrite using `[add_comm]`. Use the proof step `ring] at this`. Use `this.mono ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem prefixLe_teich_add_sub_of_le {a e : L} {B δ : ℝ} (ha : ‖a‖ ≤ B) (he : ‖e‖ ≤ δ) (hδ : 0 ≤ δ)
    (hδB : δ ≤ B) (k : ℕ) :
    T.PrefixLe (T.teich (a + e) - T.teich a - T.teich e) k
      (B ^ (1 - ((p ^ k : ℕ) : ℝ)⁻¹) * δ ^ ((p ^ k : ℕ) : ℝ)⁻¹) := by
  obtain ⟨ht0, ht1⟩ := inv_pow_pos_le_one (p := p) k
  set t := ((p ^ k : ℕ) : ℝ)⁻¹
  rcases le_total ‖e‖ ‖a‖ with h | h
  · refine (T.prefixLe_teich_add_sub h k).mono ?_
    exact mul_le_mul (Real.rpow_le_rpow (norm_nonneg _) ha (by linarith))
      (Real.rpow_le_rpow (norm_nonneg _) he ht0.le) (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (hδ.trans hδB) _)
  · have := T.prefixLe_teich_add_sub h k
    rw [show T.teich (e + a) - T.teich e - T.teich a = T.teich (a + e) - T.teich a - T.teich e by
      rw [add_comm]; ring] at this
    refine this.mono ?_
    calc ‖e‖ ^ (1 - t) * ‖a‖ ^ t ≤ ‖e‖ := rpow_mix_le (norm_nonneg _) h ht0.le ht1
      _ ≤ δ := he
      _ ≤ B ^ (1 - t) * δ ^ t := le_rpow_mix hδ hδB ht1

def coeffHolderExp (p n : ℕ) : ℝ := ((p ^ (∑ i ∈ Finset.range (n + 1), i) : ℕ) : ℝ)⁻¹

/- English proof (translation)
The claim follows from `inv_pow_pos_le_one _`.
-/
theorem coeffHolderExp_pos_le_one (n : ℕ) : 0 < coeffHolderExp p n ∧ coeffHolderExp p n ≤ 1 :=
  inv_pow_pos_le_one _

/- English proof (translation)
Simplify using `only [coeffHolderExp, Finset.sum_range_succ _ (n + 1), pow_add, Nat.cast_mul, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeffHolderExp_succ (n : ℕ) :
    coeffHolderExp p (n + 1) = ((p ^ (n + 1) : ℕ) : ℝ)⁻¹ * coeffHolderExp p n := by
  simp only [coeffHolderExp, Finset.sum_range_succ _ (n + 1), pow_add, Nat.cast_mul, mul_inv]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `x y B δ hδ hδB hx hy m hm`. Take `rfl : m = 0` from `by omega`. Rewrite using `[coeff_zero, coeff_zero, map_add, add_sub_cancel_left]`.

Conclude with `(hy 0 le_rfl).trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one 0).2)`. Consider the case `succ n ih`. Introduce `x y B δ hδ hδB hx hy m hm`. Break down `m with _ | m` into its components or cases. Rewrite using `[coeff_zero, coeff_zero, map_add, add_sub_cancel_left]`.

Conclude with `(hy 0 (Nat.zero_le _)).trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one _).2)`. Take `⟨hs0, hs1⟩` from `inv_pow_pos_le_one (p := p) (n + 1)`. Use `set s := ((p ^ (n + 1) : ℕ) : ℝ)⁻¹ with hsdef`. Establish `hB0 : 0 ≤ B` using `hδ.trans hδB`. Use `set H := T.teich (T.red x) + T.teich (T.red y) - T.teich (T.red x + T.red y) with hHdef`.

Establish `hH : T.red H = 0` using `by rw [hHdef]; simp [red_teich]`. Take `⟨h', hh'⟩` from `T.red_eq_zero_iff.1 hH`. Establish `htail : T.tail (x + y) = T.tail x + (T.tail y + h')`. Use `T.tail_eq (a := T.red x + T.red y) ?_` and prove the remaining obligations. Establish `ex` using `T.eq_teich_add_π_mul_tail x`.

Establish `ey` using `T.eq_teich_add_π_mul_tail y`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ex, ← ey]`. Use `_ = T.teich (T.red x + T.red y) + H + T.π * T.tail x + T.π * T.tail y := by`. Rewrite using `[hHdef]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hh']; ring`. Establish `hδ' : 0 ≤ B ^ (1 - s) * δ ^ s` using `mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _)`. Establish `hδδ' : δ ≤ B ^ (1 - s) * δ ^ s` using `le_rpow_mix hδ hδB hs1`. Establish `hδ'B : B ^ (1 - s) * δ ^ s ≤ B` using `rpow_mix_le hδ hδB hs0.le hs1`.

Establish `hxt : T.PrefixLe (T.tail x) n B` using `fun i hi => by`. Rewrite using `[← coeff_succ]; exact hx (i + 1) (by omega)`. Establish `hyt : T.PrefixLe (T.tail y) n (B ^ (1 - s) * δ ^ s)` using `fun i hi => by`. Rewrite using `[← coeff_succ]; exact (hy (i + 1) (by omega)).trans hδδ'`. Establish `hHb : T.PrefixLe H (n + 1) (B ^ (1 - s) * δ ^ s)`.

Use `T.prefixLe_teich_add_sub_of_le (hx 0 (Nat.zero_le _)) (hy 0 (Nat.zero_le _)) hδ hδB (n + 1)` as an intermediate fact. Establish `e : H = -(T.teich (T.red x + T.red y) - T.teich (T.red x) - T.teich (T.red y))`. Rewrite using `[hHdef]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `T.prefixLe_neg this`. Establish `hh'b : T.PrefixLe h' n (B ^ (1 - s) * δ ^ s)` using `fun i hi => by`. Rewrite using `[← T.coeff_π_mul_succ, ← hh']; exact hHb (i + 1) (by omega)`. Use `ih hδ' hδ'B hxt (T.prefixLe_add hyt hh'b) m (by omega)` as an intermediate fact. Rewrite using `[coeff_succ, coeff_succ, htail]`.

Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Take `⟨ht0, ht1⟩` from `coeffHolderExp_pos_le_one (p := p) n`. Establish `hne : 1 - coeffHolderExp p n + (1 - s) * coeffHolderExp p n ≠ 0`. Establish `: s * coeffHolderExp p n ≤ s` using `mul_le_of_le_one_right hs0.le ht1`. Establish `hs2 : s < 1`.

Rewrite using `[hsdef]`. Establish `h2 : (1 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ)`. Conclude with `Nat.one_lt_pow (by omega) hp.out.one_lt` after adjusting the coercions. Conclude with `inv_lt_one_of_one_lt₀ h2`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _), ← Real.rpow_mul hB0, ← Real.rpow_mul hδ, ← mul_assoc, ← Real.rpow_add' hB0 hne, coeffHolderExp_succ]`. Apply the tactic sequence `congr 2 <;> ring`.
-/
theorem norm_coeff_add_sub_le (n : ℕ) : ∀ {x y : Γ} {B δ : ℝ}, 0 ≤ δ → δ ≤ B →
    T.PrefixLe x n B → T.PrefixLe y n δ → ∀ m ≤ n,
      ‖T.coeff (x + y) m - T.coeff x m‖ ≤ B ^ (1 - coeffHolderExp p n) * δ ^ coeffHolderExp p n := by
  induction n with
  | zero =>
    intro x y B δ hδ hδB hx hy m hm
    obtain rfl : m = 0 := by omega
    rw [coeff_zero, coeff_zero, map_add, add_sub_cancel_left]
    exact (hy 0 le_rfl).trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one 0).2)
  | succ n ih =>
    intro x y B δ hδ hδB hx hy m hm
    rcases m with _ | m
    · rw [coeff_zero, coeff_zero, map_add, add_sub_cancel_left]
      exact (hy 0 (Nat.zero_le _)).trans (le_rpow_mix hδ hδB (coeffHolderExp_pos_le_one _).2)
    obtain ⟨hs0, hs1⟩ := inv_pow_pos_le_one (p := p) (n + 1)
    set s := ((p ^ (n + 1) : ℕ) : ℝ)⁻¹ with hsdef
    have hB0 : 0 ≤ B := hδ.trans hδB
    set H := T.teich (T.red x) + T.teich (T.red y) - T.teich (T.red x + T.red y) with hHdef
    have hH : T.red H = 0 := by rw [hHdef]; simp [red_teich]
    obtain ⟨h', hh'⟩ := T.red_eq_zero_iff.1 hH
    have htail : T.tail (x + y) = T.tail x + (T.tail y + h') := by
      refine T.tail_eq (a := T.red x + T.red y) ?_
      have ex := T.eq_teich_add_π_mul_tail x
      have ey := T.eq_teich_add_π_mul_tail y
      calc x + y = T.teich (T.red x) + T.π * T.tail x + (T.teich (T.red y) + T.π * T.tail y) := by
            rw [← ex, ← ey]
        _ = T.teich (T.red x + T.red y) + H + T.π * T.tail x + T.π * T.tail y := by
            rw [hHdef]; ring
        _ = _ := by rw [hh']; ring
    have hδ' : 0 ≤ B ^ (1 - s) * δ ^ s :=
      mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _)
    have hδδ' : δ ≤ B ^ (1 - s) * δ ^ s := le_rpow_mix hδ hδB hs1
    have hδ'B : B ^ (1 - s) * δ ^ s ≤ B := rpow_mix_le hδ hδB hs0.le hs1
    have hxt : T.PrefixLe (T.tail x) n B := fun i hi => by
      rw [← coeff_succ]; exact hx (i + 1) (by omega)
    have hyt : T.PrefixLe (T.tail y) n (B ^ (1 - s) * δ ^ s) := fun i hi => by
      rw [← coeff_succ]; exact (hy (i + 1) (by omega)).trans hδδ'
    have hHb : T.PrefixLe H (n + 1) (B ^ (1 - s) * δ ^ s) := by
      have := T.prefixLe_teich_add_sub_of_le (hx 0 (Nat.zero_le _)) (hy 0 (Nat.zero_le _)) hδ hδB
        (n + 1)
      have e : H = -(T.teich (T.red x + T.red y) - T.teich (T.red x) - T.teich (T.red y)) := by
        rw [hHdef]; ring
      rw [e]; exact T.prefixLe_neg this
    have hh'b : T.PrefixLe h' n (B ^ (1 - s) * δ ^ s) := fun i hi => by
      rw [← T.coeff_π_mul_succ, ← hh']; exact hHb (i + 1) (by omega)
    have := ih hδ' hδ'B hxt (T.prefixLe_add hyt hh'b) m (by omega)
    rw [coeff_succ, coeff_succ, htail]
    refine this.trans (le_of_eq ?_)
    obtain ⟨ht0, ht1⟩ := coeffHolderExp_pos_le_one (p := p) n
    have hne : 1 - coeffHolderExp p n + (1 - s) * coeffHolderExp p n ≠ 0 := by
      have : s * coeffHolderExp p n ≤ s := mul_le_of_le_one_right hs0.le ht1
      have hs2 : s < 1 := by
        rw [hsdef]
        have h2 : (1 : ℝ) < ((p ^ (n + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.one_lt_pow (by omega) hp.out.one_lt
        exact inv_lt_one_of_one_lt₀ h2
      nlinarith
    rw [Real.mul_rpow (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hδ _), ← Real.rpow_mul hB0,
      ← Real.rpow_mul hδ, ← mul_assoc, ← Real.rpow_add' hB0 hne, coeffHolderExp_succ]
    congr 2 <;> ring

end TeichLift

end GroundTheory.PAdicHodge
