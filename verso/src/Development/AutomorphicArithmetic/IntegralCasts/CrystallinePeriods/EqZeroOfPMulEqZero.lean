import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.TruncLogEqOfPowEqZero

noncomputable section

open Ideal
open scoped Nat

namespace Reformulated.AutPerF

universe u v w

section Adic

variable {A : Type u} [CommRing A]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : AdicCompletion.eval (span {a}) A n x = 0`. Rewrite using `[← AdicCompletion.factor_evalₐ_eq_eval (span {a}) x (by simp), h, map_zero]`. Establish `h2 : x ∈ (span {a} ^ n • ⊤ : Submodule A (AdicCompletion (span {a}) A))`.

Rewrite using `[AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton a)]`. Conclude with `h1`. Rewrite `h2` using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨y, -, rfl⟩` from `h2`. Conclude with `⟨y, by rw [Algebra.smul_def, map_pow]⟩`.

Introduce and unpack `⟨y, rfl⟩`. Rewrite using `[map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (mem_span_singleton_self _) _), zero_mul]`.
-/
theorem evalₐ_eq_zero_iff_dvd (a : A) (n : ℕ) (x : AdicCompletion (span {a}) A) :
    AdicCompletion.evalₐ (span {a}) n x = 0 ↔
      algebraMap A (AdicCompletion (span {a}) A) a ^ n ∣ x := by
  constructor
  · intro h
    have h1 : AdicCompletion.eval (span {a}) A n x = 0 := by
      rw [← AdicCompletion.factor_evalₐ_eq_eval (span {a}) x (by simp), h, map_zero]
    have h2 : x ∈ (span {a} ^ n • ⊤ : Submodule A (AdicCompletion (span {a}) A)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (Submodule.fg_span_singleton a)]
      exact h1
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨y, -, rfl⟩ := h2
    exact ⟨y, by rw [Algebra.smul_def, map_pow]⟩
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_pow, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, ← map_pow,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (mem_span_singleton_self _) _), zero_mul]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨c, hc⟩` from `ih (by omega)`. Establish `h : ((m - 1 - k : ℕ) : ℤ) = m - (k + 1)` using `by omega`.

Use `⟨(-1) ^ k * (k ! : ℤ) + (m - (k + 1)) * c, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.descFactorial_succ, Nat.cast_mul, h, hc, Nat.factorial_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem descFactorial_pred_modEq {m k : ℕ} (hk : k < m) :
    ∃ c : ℤ, ((m - 1).descFactorial k : ℤ) = (-1) ^ k * (k ! : ℤ) + m * c := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih (by omega)
    have h : ((m - 1 - k : ℕ) : ℤ) = m - (k + 1) := by omega
    refine ⟨(-1) ^ k * (k ! : ℤ) + (m - (k + 1)) * c, ?_⟩
    rw [Nat.descFactorial_succ, Nat.cast_mul, h, hc, Nat.factorial_succ]
    push_cast
    ring

/- English proof (translation)
Rewrite using `[add_pow, Finset.sum_range_succ', Finset.mul_sum]`. Simplify using `only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Take `⟨m, rfl⟩ : ∃ m', m = m' + 1` from `⟨m - 1, by have := Finset.mem_range.1 hk; omega⟩`. Rewrite using `[← mul_assoc, ← Nat.cast_mul, Nat.add_sub_cancel, ← Nat.succ_descFactorial_succ, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Algebra.smul_def, ← map_natCast (algebraMap ℚ B) (k + 1)!]`.

Establish `: algebraMap ℚ B ((k + 1)! : ℕ) * algebraMap ℚ B (((k + 1)! : ℕ) : ℚ)⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one]`. Take the linear combination `(((m + 1).choose (k + 1) : ℕ) : B) * x ^ (k + 1) * this`.
-/
theorem mul_sum_descFactorial {B : Type*} [CommRing B] [Algebra ℚ B] (m : ℕ) (x : B) :
    (m : B) * ∑ k ∈ Finset.range m,
      ((m - 1).descFactorial k : B) * ((((k + 1) ! : ℕ) : ℚ)⁻¹ • x ^ (k + 1)) = (x + 1) ^ m - 1 := by
  rw [add_pow, Finset.sum_range_succ', Finset.mul_sum]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := Finset.mem_range.1 hk; omega⟩
  rw [← mul_assoc, ← Nat.cast_mul, Nat.add_sub_cancel, ← Nat.succ_descFactorial_succ,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Algebra.smul_def,
    ← map_natCast (algebraMap ℚ B) (k + 1)!]
  have : algebraMap ℚ B ((k + 1)! : ℕ) * algebraMap ℚ B (((k + 1)! : ℕ) : ℚ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one]
  linear_combination (((m + 1).choose (k + 1) : ℕ) : B) * x ^ (k + 1) * this

end Adic

variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]

namespace AcrisZero

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (gamma n x hx : AinfInv p R) = AinfInv.gamma n (algebraMap _ _ x) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Establish `h'` using `congrArg (Subtype.val) h`. Simplify using `only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h'`. Conclude with `((AinfInv.isUnit_p p).pow n).mul_left_cancel h'`.
-/
theorem p_pow_mul_cancel (n : ℕ) {x y : AcrisZero p R} (h : (p : AcrisZero p R) ^ n * x = p ^ n * y) :
    x = y := by
  apply Subtype.ext
  have h' := congrArg (Subtype.val) h
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast] at h'
  exact ((AinfInv.isUnit_p p).pow n).mul_left_cancel h'

/- English proof (translation)
The claim follows from `p_pow_mul_cancel 1 (by simpa using h)`.
-/
theorem p_mul_cancel {x y : AcrisZero p R} (h : (p : AcrisZero p R) * x = p * y) : x = y :=
  p_pow_mul_cancel 1 (by simpa using h)

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem mem_span_pow_iff (n : ℕ) (x : AcrisZero p R) :
    x ∈ span {(p : AcrisZero p R)} ^ n ↔ (p : AcrisZero p R) ^ n ∣ x := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, coe_gamma, AinfInv.gamma, Subalgebra.coe_algebraMap]`. Rewrite using `[Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]`.
-/
theorem factorial_mul_gamma (n : ℕ) (x : Ainf p R) (hx : Ainf.theta p R x = 0) :
    (n ! : AcrisZero p R) * gamma n x hx = algebraMap (Ainf p R) _ x ^ n := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, coe_gamma,
    AinfInv.gamma, Subalgebra.coe_algebraMap]
  rw [Algebra.smul_def, ← map_natCast (algebraMap ℚ (AinfInv p R)), ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero _), map_one, one_mul]

end AcrisZero

namespace Acris

/- English proof (translation)
The claim follows from `AdicCompletion.surjective_evalₐ _ n`.
-/
theorem eval_surjective (n : ℕ) : Function.Surjective (eval p R n) :=
  AdicCompletion.surjective_evalₐ _ n

/- English proof (translation)
The claim follows from `factorPow_evalₐ _ hle x`.
-/
theorem factorPow_eval {m n : ℕ} (hle : m ≤ n) (x : Acris p R) :
    Ideal.Quotient.factorPow _ hle (eval p R n x) = eval p R m x :=
  factorPow_evalₐ _ hle x

/- English proof (translation)
Use `evalₐ_eq_zero_iff_dvd (p : AcrisZero p R) n x` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Conclude with `this`.
-/
theorem eval_eq_zero_iff (n : ℕ) (x : Acris p R) : eval p R n x = 0 ↔ (p : Acris p R) ^ n ∣ x := by
  have := evalₐ_eq_zero_iff_dvd (p : AcrisZero p R) n x
  rw [map_natCast] at this
  exact this

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[RingHom.mem_ker, eval_eq_zero_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.
-/
theorem ker_eval (n : ℕ) : RingHom.ker (eval p R n) = span {(p : Acris p R)} ^ n := by
  ext x
  rw [RingHom.mem_ker, eval_eq_zero_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/- English proof (translation)
Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (eval p R n x)`. Take `⟨y, hy⟩` from `(eval_eq_zero_iff n (x - algebraMap _ _ a)).1 (by rw [map_sub, eval_algebraMap, ha, sub_self])`. Conclude with `⟨a, y, by rw [← hy]; ring⟩`.
-/
theorem exists_eq_add (n : ℕ) (x : Acris p R) :
    ∃ (a : AcrisZero p R) (y : Acris p R), x = algebraMap _ _ a + (p : Acris p R) ^ n * y := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R n x)
  obtain ⟨y, hy⟩ := (eval_eq_zero_iff n (x - algebraMap _ _ a)).1
    (by rw [map_sub, eval_algebraMap, ha, sub_self])
  exact ⟨a, y, by rw [← hy]; ring⟩

/- English proof (translation)
The claim follows from `ext_eval fun n => by rw [(eval_eq_zero_iff n x).2 (h n), map_zero]`.
-/
theorem eq_zero_of_forall_dvd {x : Acris p R} (h : ∀ n, (p : Acris p R) ^ n ∣ x) : x = 0 :=
  ext_eval fun n => by rw [(eval_eq_zero_iff n x).2 (h n), map_zero]

instance isAdicComplete : IsAdicComplete (span {(p : Acris p R)}) (Acris p R) := by
  have := AdicCompletion.isAdicComplete_self (span {(p : AcrisZero p R)})
    (Submodule.fg_span_singleton _)
  rw [Ideal.map_span, Set.image_singleton, map_natCast] at this
  exact this

/- English proof (translation)
Use `ext_eval fun n => ?_` and prove the remaining obligations. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (eval p R (n + 1) x)`. Establish `h1` using `congrArg (eval p R (n + 1)) h`. Rewrite `h1` using `[map_mul, map_zero, map_natCast, ← ha, ← map_natCast (Ideal.Quotient.mk (span {(p : AcrisZero p R)} ^ (n + 1))), ← map_mul, Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff]`. Take `⟨b, hb⟩` from `h1`.

Establish `hab : a = p ^ n * b` using `AcrisZero.p_mul_cancel (by rw [hb]; ring)`. Rewrite using `[← factorPow_eval (Nat.le_succ n), ← ha, map_zero]`. Simplify using `only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff]`. Conclude with `⟨b, hab⟩`.
-/
theorem eq_zero_of_p_mul_eq_zero {x : Acris p R} (h : (p : Acris p R) * x = 0) : x = 0 := by
  refine ext_eval fun n => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R (n + 1) x)
  have h1 := congrArg (eval p R (n + 1)) h
  rw [map_mul, map_zero, map_natCast, ← ha,
    ← map_natCast (Ideal.Quotient.mk (span {(p : AcrisZero p R)} ^ (n + 1))), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff] at h1
  obtain ⟨b, hb⟩ := h1
  have hab : a = p ^ n * b := AcrisZero.p_mul_cancel (by rw [hb]; ring)
  rw [← factorPow_eval (Nat.le_succ n), ← ha, map_zero]
  simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq_zero_iff_mem, AcrisZero.mem_span_pow_iff]
  exact ⟨b, hab⟩

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (eq_zero_of_p_mul_eq_zero (by rw [mul_sub, h, sub_self]))`.
-/
theorem p_mul_cancel {x y : Acris p R} (h : (p : Acris p R) * x = p * y) : x = y :=
  sub_eq_zero.1 (eq_zero_of_p_mul_eq_zero (by rw [mul_sub, h, sub_self]))

/- English proof (translation)
The claim follows from `mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_p_mul_eq_zero h`.
-/
theorem p_mem_nonZeroDivisors : (p : Acris p R) ∈ nonZeroDivisors (Acris p R) :=
  mem_nonZeroDivisors_iff_left.2 fun _ h => eq_zero_of_p_mul_eq_zero h

/- English proof (translation)
The claim follows from `sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 (pow_mem p_mem_nonZeroDivisors n) _ (by rw [mul_sub, h, sub_self]))`.
-/
theorem p_pow_mul_cancel (n : ℕ) {x y : Acris p R} (h : (p : Acris p R) ^ n * x = p ^ n * y) :
    x = y :=
  sub_eq_zero.1 (mem_nonZeroDivisors_iff_left.1 (pow_mem p_mem_nonZeroDivisors n) _
    (by rw [mul_sub, h, sub_self]))

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[IsHausdorff.eq_iff_smodEq (I := span {(p : B)})]`. Introduce `n`. Take `⟨a, y, rfl⟩` from `exists_eq_add n x`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Use `⟨f y - g y, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, map_natCast, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hom_ext {B : Type*} [CommRing B] [IsHausdorff (span {(p : B)}) B] {f g : Acris p R →+* B}
    (h : ∀ a : AcrisZero p R, f (algebraMap _ _ a) = g (algebraMap _ _ a)) : f = g := by
  ext x
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : B)})]
  intro n
  obtain ⟨a, y, rfl⟩ := exists_eq_add n x
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  refine ⟨f y - g y, ?_⟩
  simp only [map_add, map_mul, map_pow, map_natCast, h]
  ring

/- English proof (translation)
Use `⟨∑ k ∈ Finset.range (p ^ n), ((p ^ n - 1).descFactorial k : AcrisZero p R) * AcrisZero.gamma (k + 1) (u - 1) (by simp [hu]), ?_, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Use `mul_sum_descFactorial (p ^ n) (algebraMap (Ainf p R) (AinfInv p R) (u - 1))` as an intermediate fact. Rewrite `this` using `[← map_one (algebraMap (Ainf p R) (AinfInv p R)), ← map_add, sub_add_cancel, map_one, Nat.cast_pow]`. Simplify using `only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast, AddSubmonoidClass.coe_finset_sum, AcrisZero.coe_gamma, AinfInv.gamma, AddSubgroupClass.coe_sub, OneMemClass.coe_one, Subalgebra.coe_algebraMap]`.

Conclude with `this`. Rewrite using `[eval_log u hu le_rfl, Ideal.Quotient.eq, logPartial, ← Finset.sum_sub_distrib]`. Use `Ideal.sum_mem _ fun k hk => ?_` and prove the remaining obligations. Rewrite using `[← sub_mul]`. Use `Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations.

Take `⟨c, hc⟩` from `descFactorial_pred_modEq (Finset.mem_range.1 hk)`. Establish `hc'` using `congrArg (Int.cast : ℤ → AcrisZero p R) hc`. Move the coercions through the operations in `at hc'`. Rewrite using `[AcrisZero.mem_span_pow_iff, hc']`. Conclude with `⟨-c, by ring⟩`.
-/
theorem exists_quot (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) :
    ∃ l : AcrisZero p R, (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1 ∧
      eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  refine ⟨∑ k ∈ Finset.range (p ^ n), ((p ^ n - 1).descFactorial k : AcrisZero p R) *
    AcrisZero.gamma (k + 1) (u - 1) (by simp [hu]), ?_, ?_⟩
  · apply Subtype.ext
    have := mul_sum_descFactorial (p ^ n) (algebraMap (Ainf p R) (AinfInv p R) (u - 1))
    rw [← map_one (algebraMap (Ainf p R) (AinfInv p R)), ← map_add, sub_add_cancel, map_one,
      Nat.cast_pow] at this
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubringClass.coe_natCast,
      AddSubmonoidClass.coe_finset_sum, AcrisZero.coe_gamma, AinfInv.gamma,
      AddSubgroupClass.coe_sub, OneMemClass.coe_one, Subalgebra.coe_algebraMap]
    exact this
  · rw [eval_log u hu le_rfl, Ideal.Quotient.eq, logPartial, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun k hk => ?_
    rw [← sub_mul]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨c, hc⟩ := descFactorial_pred_modEq (Finset.mem_range.1 hk)
    have hc' := congrArg (Int.cast : ℤ → AcrisZero p R) hc
    push_cast at hc'
    rw [AcrisZero.mem_span_pow_iff, hc']
    exact ⟨-c, by ring⟩

/- English proof (translation)
Take `⟨l', h1, h2⟩` from `exists_quot u hu n`. Rewrite using `[h2, AcrisZero.p_pow_mul_cancel n (h1.trans hl.symm)]`.
-/
theorem eval_log_of_mul_eq (u : Ainf p R) (hu : Ainf.theta p R u = 1) (n : ℕ) (l : AcrisZero p R)
    (hl : (p : AcrisZero p R) ^ n * l = algebraMap (Ainf p R) _ u ^ p ^ n - 1) :
    eval p R n (log u hu) = Ideal.Quotient.mk _ l := by
  obtain ⟨l', h1, h2⟩ := exists_quot u hu n
  rw [h2, AcrisZero.p_pow_mul_cancel n (h1.trans hl.symm)]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem log_congr {u v : Ainf p R} (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (h : u = v) : log u hu = log v hv := by subst h; rfl

/- English proof (translation)
Use `ext_eval fun n => ?_` and prove the remaining obligations. Take `⟨a, ha, ha'⟩` from `exists_quot u hu n`. Take `⟨b, hb, hb'⟩` from `exists_quot v hv n`. Rewrite using `[map_add, ha', hb', eval_log_of_mul_eq _ huv n (a + b + p ^ n * a * b), ← map_add, Ideal.Quotient.eq, AcrisZero.mem_span_pow_iff]`. Conclude with `⟨a * b, by ring⟩`.

Rewrite using `[map_mul, mul_pow, eq_add_of_sub_eq ha.symm, eq_add_of_sub_eq hb.symm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_mul (u v : Ainf p R) (hu : Ainf.theta p R u = 1) (hv : Ainf.theta p R v = 1)
    (huv : Ainf.theta p R (u * v) = 1) : log (u * v) huv = log u hu + log v hv := by
  refine ext_eval fun n => ?_
  obtain ⟨a, ha, ha'⟩ := exists_quot u hu n
  obtain ⟨b, hb, hb'⟩ := exists_quot v hv n
  rw [map_add, ha', hb', eval_log_of_mul_eq _ huv n (a + b + p ^ n * a * b), ← map_add,
    Ideal.Quotient.eq, AcrisZero.mem_span_pow_iff]
  · exact ⟨a * b, by ring⟩
  · rw [map_mul, mul_pow, eq_add_of_sub_eq ha.symm, eq_add_of_sub_eq hb.symm]
    ring

/- English proof (translation)
The claim follows from `ext_eval fun n => by rw [eval_log_of_mul_eq _ h n 0 (by simp), map_zero, map_zero]`.
-/
@[simp] theorem log_one (h : Ainf.theta p R 1 = 1) : log (1 : Ainf p R) h = 0 :=
  ext_eval fun n => by rw [eval_log_of_mul_eq _ h n 0 (by simp), map_zero, map_zero]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp only [pow_zero, Nat.cast_zero, zero_mul]`. Conclude with `log_one _`. Consider the case `succ m ih`. Establish `h : Ainf.theta p R (u ^ m) = 1` using `by rw [map_pow, hu, one_pow]`.

Rewrite using `[log_congr hm (by rw [map_mul, h, hu, one_mul]) (pow_succ u m), log_mul _ _ h hu, ih h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_pow (u : Ainf p R) (hu : Ainf.theta p R u = 1) (m : ℕ)
    (hm : Ainf.theta p R (u ^ m) = 1) : log (u ^ m) hm = m * log u hu := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul]; exact log_one _
  | succ m ih =>
    have h : Ainf.theta p R (u ^ m) = 1 := by rw [map_pow, hu, one_pow]
    rw [log_congr hm (by rw [map_mul, h, hu, one_mul]) (pow_succ u m), log_mul _ _ h hu, ih h]
    push_cast
    ring

/- English proof (translation)
Unfold `logTeich`. Rewrite using `[← log_mul _ _ _ _ (by`. Rewrite using `[map_mul, Ainf.theta_teich, Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2, show PreTilt.untilt η'.1 = 1 from η'.2, one_mul])]`. Conclude with `log_congr _ _ (map_mul _ _ _)`.
-/
theorem logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by
  unfold logTeich
  rw [← log_mul _ _ _ _ (by
    rw [map_mul, Ainf.theta_teich, Ainf.theta_teich, show PreTilt.untilt η.1 = 1 from η.2,
      show PreTilt.untilt η'.1 = 1 from η'.2, one_mul])]
  exact log_congr _ _ (map_mul _ _ _)

/- English proof (translation)
The claim follows from `(log_congr _ (map_one _) (map_one _)).trans (log_one _)`.
-/
@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 :=
  (log_congr _ (map_one _) (map_one _)).trans (log_one _)

variable (p R) in

def logTeichHom : tateModule p R →* Multiplicative (Acris p R) where
  toFun η := Multiplicative.ofAdd (logTeich η)
  map_one' := by simp
  map_mul' η η' := by rw [logTeich_mul]; rfl

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ, logTeich_mul, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, logTeich_mul, ih]; push_cast; ring

end Acris

namespace BcrisPlus

/- English proof (translation)
The claim follows from `IsLocalization.injective (M := Submonoid.powers (p : Acris p R)) _ (Submonoid.powers_le.2 Acris.p_mem_nonZeroDivisors)`.
-/
theorem algebraMap_injective : Function.Injective (algebraMap (Acris p R) (BcrisPlus p R)) :=
  IsLocalization.injective (M := Submonoid.powers (p : Acris p R)) _
    (Submonoid.powers_le.2 Acris.p_mem_nonZeroDivisors)

end BcrisPlus

namespace Bcris

/- English proof (translation)
Simplify using `[logTeich, Acris.logTeich_mul]`.
-/
theorem logTeich_mul (η η' : tateModule p R) : logTeich (η * η') = logTeich η + logTeich η' := by
  simp [logTeich, Acris.logTeich_mul]

/- English proof (translation)
Simplify using `[logTeich]`.
-/
@[simp] theorem logTeich_one : logTeich (1 : tateModule p R) = 0 := by simp [logTeich]

/- English proof (translation)
Simplify using `[logTeich, Acris.logTeich_pow]`.
-/
theorem logTeich_pow (η : tateModule p R) (m : ℕ) : logTeich (η ^ m) = m * logTeich η := by
  simp [logTeich, Acris.logTeich_pow]

/- English proof (translation)
The claim follows from `IsLocalization.map_units (M := BcrisPlus.periods p R) (Bcris p R) ⟨_, Submonoid.subset_closure ⟨ε, h, rfl⟩⟩`.
-/
theorem isUnit_logTeich {ε : tateModule p R} (h : IsPrimitive ε) : IsUnit (logTeich ε) :=
  IsLocalization.map_units (M := BcrisPlus.periods p R) (Bcris p R)
    ⟨_, Submonoid.subset_closure ⟨ε, h, rfl⟩⟩

/- English proof (translation)
Simplify using `using (BcrisPlus.isUnit_p p R).map (algebraMap _ (Bcris p R))`.
-/
theorem isUnit_p : IsUnit (p : Bcris p R) := by
  simpa using (BcrisPlus.isUnit_p p R).map (algebraMap _ (Bcris p R))

end Bcris

end Reformulated.AutPerF
