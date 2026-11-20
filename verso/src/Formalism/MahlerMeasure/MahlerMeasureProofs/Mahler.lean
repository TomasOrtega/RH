import Formalism.MahlerMeasure.StatementB

namespace Formalism.GM

open Polynomial

def zpS (p : ℕ) [Fact p.Prime] : Subring ℚ where
  carrier := {x | padicNorm p x ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, padicNorm.mul] at *
    exact mul_le_one₀ ha (padicNorm.nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact le_trans padicNorm.nonarchimedean (max_le ha hb)
  zero_mem' := by simp [padicNorm.zero]
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, padicNorm.neg] at *
    exact ha

def zpT (p : ℕ) [Fact p.Prime] : Subring ℚ[X] where
  carrier := {P | ∀ n, P.coeff n ∈ zpS p}
  mul_mem' {a b} ha hb := by
    intro n
    rw [coeff_mul]
    exact Subring.sum_mem _ (fun x _ => Subring.mul_mem _ (ha _) (hb _))
  one_mem' := by
    intro n
    rw [coeff_one]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  add_mem' {a b} ha hb := by
    intro n
    rw [coeff_add]
    exact Subring.add_mem _ (ha n) (hb n)
  zero_mem' := by intro n; simp
  neg_mem' {a} ha := by
    intro n
    rw [coeff_neg]
    exact Subring.neg_mem _ (ha n)

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_C]`. Use `split_ifs`. Conclude with `ha`. Conclude with `Subring.zero_mem _`.
-/
lemma C_mem_zpT (p : ℕ) [Fact p.Prime] {a : ℚ} (ha : a ∈ zpS p) : C a ∈ zpT p := by
  intro n
  rw [coeff_C]
  split_ifs
  · exact ha
  · exact Subring.zero_mem _

/- English proof (translation)
Introduce `n`. Rewrite using `[coeff_X]`. Use `split_ifs`. Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`.
-/
lemma X_mem_zpT (p : ℕ) [Fact p.Prime] : (X : ℚ[X]) ∈ zpT p := by
  intro n
  rw [coeff_X]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

/- English proof (translation)
Use `show padicNorm p ((p : ℚ) ^ k / m) ≤ 1`. Establish `hp1 : 1 < p` using `hp.out.one_lt`. Establish `hm0 : (m : ℚ) ≠ 0` using `by exact_mod_cast (show m ≠ 0 by omega)`. Establish `hpk0 : (p : ℚ) ^ k ≠ 0` using `pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)`. Establish `hv : padicValNat p m ≤ k`.

Establish `h1 : p ^ padicValNat p m ≤ m` using `Nat.le_of_dvd (by omega) pow_padicValNat_dvd`. Conclude with `(Nat.pow_le_pow_iff_right hp1).1 (h1.trans hm)`. Establish `hval : padicValRat p ((p : ℚ) ^ k / m) = (k : ℤ) - padicValNat p m`. Rewrite using `[padicValRat.div hpk0 hm0, show ((p : ℚ) ^ k) = ((p ^ k : ℕ) : ℚ) by push_cast; rfl, padicValRat.of_nat, padicValRat.of_nat, padicValNat.prime_pow]`. Rewrite using `[padicNorm.eq_zpow_of_nonzero (div_ne_zero hpk0 hm0), hval]`.

Apply `zpow_le_one_of_nonpos₀ (by exact_mod_cast hp1.le)` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
lemma div_mem_zpS (p k m : ℕ) [hp : Fact p.Prime] (hm1 : 1 ≤ m) (hm : m ≤ p ^ k) :
    ((p : ℚ) ^ k / m) ∈ zpS p := by
  show padicNorm p ((p : ℚ) ^ k / m) ≤ 1
  have hp1 : 1 < p := hp.out.one_lt
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hpk0 : (p : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)

  have hv : padicValNat p m ≤ k := by
    have h1 : p ^ padicValNat p m ≤ m := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
    exact (Nat.pow_le_pow_iff_right hp1).1 (h1.trans hm)
  have hval : padicValRat p ((p : ℚ) ^ k / m) = (k : ℤ) - padicValNat p m := by
    rw [padicValRat.div hpk0 hm0, show ((p : ℚ) ^ k) = ((p ^ k : ℕ) : ℚ) by push_cast; rfl,
      padicValRat.of_nat, padicValRat.of_nat, padicValNat.prime_pow]
  rw [padicNorm.eq_zpow_of_nonzero (div_ne_zero hpk0 hm0), hval]
  apply zpow_le_one_of_nonpos₀ (by exact_mod_cast hp1.le)
  omega

noncomputable def bB (c : ℚ) (i : ℕ) (t : ℤ) : ℚ[X] :=
  C ((i.factorial : ℚ)⁻¹) * (descPochhammer ℚ i).comp (C c * X + C (t : ℚ))

/- English proof (translation)
Simplify using `[bB]`.
-/
lemma bB_zero (c : ℚ) (t : ℤ) : bB c 0 t = 1 := by
  simp [bB]

/- English proof (translation)
Establish `h1 : (descPochhammer ℚ (i + 1)).comp (Q + 1) = (Q + 1) * (descPochhammer ℚ i).comp Q`. Rewrite using `[descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp, add_sub_cancel_right]`. Establish `h2 : (descPochhammer ℚ (i + 1)).comp Q = (descPochhammer ℚ i).comp Q * (Q - (i : ℚ[X]))`. Rewrite using `[descPochhammer_succ_right, mul_comp, sub_comp, X_comp, natCast_comp]`. Rewrite using `[h1, h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma descPochhammer_comp_add_one (Q : ℚ[X]) (i : ℕ) :
    (descPochhammer ℚ (i + 1)).comp (Q + 1) =
      (descPochhammer ℚ (i + 1)).comp Q + ((i : ℚ[X]) + 1) * (descPochhammer ℚ i).comp Q := by

  have h1 : (descPochhammer ℚ (i + 1)).comp (Q + 1) = (Q + 1) * (descPochhammer ℚ i).comp Q := by
    rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp,
      add_sub_cancel_right]
  have h2 : (descPochhammer ℚ (i + 1)).comp Q = (descPochhammer ℚ i).comp Q * (Q - (i : ℚ[X])) := by
    rw [descPochhammer_succ_right, mul_comp, sub_comp, X_comp, natCast_comp]
  rw [h1, h2]
  ring

/- English proof (translation)
Establish `hQ : C c * X + C (((t + 1 : ℤ)) : ℚ) = (C c * X + C (t : ℚ)) + 1`. Use `push_cast`. Rewrite using `[C_add, C_1]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [bB]`.

Rewrite using `[hQ, descPochhammer_comp_add_one, Nat.factorial_succ]`. Establish `hf : ((i.factorial : ℚ)) ≠ 0` using `by exact_mod_cast i.factorial_ne_zero`. Establish `hi : ((i : ℚ) + 1) ≠ 0` using `by positivity`. Establish `hC : (C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹) * ((i : ℚ[X]) + 1) = C ((i.factorial : ℚ)⁻¹)`. Rewrite using `[← C_1, ← C_eq_natCast, ← C_add, ← C_mul]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_add, ← mul_assoc, hC]`.
-/
lemma bB_pascal (c : ℚ) (i : ℕ) (t : ℤ) : bB c (i + 1) (t + 1) = bB c (i + 1) t + bB c i t := by
  have hQ : C c * X + C (((t + 1 : ℤ)) : ℚ) = (C c * X + C (t : ℚ)) + 1 := by
    push_cast
    rw [C_add, C_1]
    ring
  simp only [bB]
  rw [hQ, descPochhammer_comp_add_one, Nat.factorial_succ]
  have hf : ((i.factorial : ℚ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hC : (C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹) * ((i : ℚ[X]) + 1) = C ((i.factorial : ℚ)⁻¹) := by
    rw [← C_1, ← C_eq_natCast, ← C_add, ← C_mul]
    congr 1
    push_cast
    field_simp
  rw [mul_add, ← mul_assoc, hC]

/- English proof (translation)
Simplify using `only [bB]`. Rewrite using `[descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp, Nat.factorial_succ]`. Establish `hf : ((i.factorial : ℚ)) ≠ 0` using `by exact_mod_cast i.factorial_ne_zero`. Establish `hi : ((i : ℚ) + 1) ≠ 0` using `by positivity`. Establish `e1 : C c * X + C (((0 : ℤ)) : ℚ) - 1 = C c * X + C (((-1 : ℤ)) : ℚ)`.

Simplify using `only [Int.cast_zero, C_0, add_zero, Int.cast_neg, Int.cast_one, C_neg, C_1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Establish `hC : C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * C c = C (c / ((i + 1 : ℕ) : ℚ)) * C ((i.factorial : ℚ)⁻¹)`. Rewrite using `[← C_mul, ← C_mul]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Int.cast_zero, C_0, add_zero]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma bB_succ_zero (c : ℚ) (i : ℕ) : bB c (i + 1) 0 = C (c / (i + 1 : ℕ)) * X * bB c i (-1) := by
  simp only [bB]
  rw [descPochhammer_succ_left, mul_comp, X_comp, comp_assoc, sub_comp, X_comp, one_comp,
    Nat.factorial_succ]
  have hf : ((i.factorial : ℚ)) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
  have e1 : C c * X + C (((0 : ℤ)) : ℚ) - 1 = C c * X + C (((-1 : ℤ)) : ℚ) := by
    simp only [Int.cast_zero, C_0, add_zero, Int.cast_neg, Int.cast_one, C_neg, C_1]
    ring
  rw [e1]
  have hC : C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * C c = C (c / ((i + 1 : ℕ) : ℚ)) * C ((i.factorial : ℚ)⁻¹) := by
    rw [← C_mul, ← C_mul]
    congr 1
    push_cast
    field_simp
  simp only [Int.cast_zero, C_0, add_zero]
  calc C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * (C c * X * (descPochhammer ℚ i).comp (C c * X + C (((-1 : ℤ)) : ℚ)))
      = (C ((((i + 1) * i.factorial : ℕ) : ℚ))⁻¹ * C c) * X * (descPochhammer ℚ i).comp (C c * X + C (((-1 : ℤ)) : ℚ)) := by ring
    _ = _ := by rw [hC]; ring

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _ t`. Rewrite using `[bB_zero]`. Conclude with `Subring.one_mem _`.

Consider the case `succ i ih`. Introduce `hi t`. Establish `ih'` using `ih (by omega)`. Establish `h0 : bB ((p : ℚ) ^ k) (i + 1) 0 ∈ zpT p`. Rewrite using `[bB_succ_zero]`.

Use `Subring.mul_mem _ (Subring.mul_mem _ (C_mem_zpT p ?_) (X_mem_zpT p)) (ih' _)` and prove the remaining obligations. Conclude with `div_mem_zpS p k (i + 1) (by omega) hi`. Proceed by induction on `t using Int.induction_on with`. Consider the case `zero => exact h0`. Consider the case `succ n hn => rw [bB_pascal]`.

Conclude with `Subring.add_mem _ hn (ih' _)`. Consider the case `pred n hn`. Establish `e` using `bB_pascal ((p : ℚ) ^ k) i (-(n : ℤ) - 1)`. Rewrite `e` using `[sub_add_cancel]`. Rewrite using `[show bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ) - 1) = bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ)) - bB ((p : ℚ) ^ k) i (-(n : ℤ) - 1) by`.

Rewrite using `[e]`. Use the proof step `ring]`. Conclude with `Subring.sub_mem _ hn (ih' _)`.
-/
theorem bB_mem (p k : ℕ) [Fact p.Prime] : ∀ i, i ≤ p ^ k → ∀ t : ℤ, bB ((p : ℚ) ^ k) i t ∈ zpT p := by
  intro i
  induction i with
  | zero => intro _ t; rw [bB_zero]; exact Subring.one_mem _
  | succ i ih =>
    intro hi t
    have ih' := ih (by omega)
    have h0 : bB ((p : ℚ) ^ k) (i + 1) 0 ∈ zpT p := by
      rw [bB_succ_zero]
      refine Subring.mul_mem _ (Subring.mul_mem _ (C_mem_zpT p ?_) (X_mem_zpT p)) (ih' _)
      exact div_mem_zpS p k (i + 1) (by omega) hi
    induction t using Int.induction_on with
    | zero => exact h0
    | succ n hn => rw [bB_pascal]; exact Subring.add_mem _ hn (ih' _)
    | pred n hn =>
      have e := bB_pascal ((p : ℚ) ^ k) i (-(n : ℤ) - 1)
      rw [sub_add_cancel] at e
      rw [show bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ) - 1) = bB ((p : ℚ) ^ k) (i + 1) (-(n : ℤ)) - bB ((p : ℚ) ^ k) i (-(n : ℤ) - 1) by
        rw [e]; ring]
      exact Subring.sub_mem _ hn (ih' _)

/- English proof (translation)
Introduce `p k i t₀ hp hi n`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Conclude with `bB_mem p k i hi t₀ n`.
-/
theorem mahler_disc_bound : MahlerDisc := by
  intro p k i t₀ hp hi n
  haveI : Fact p.Prime := ⟨hp⟩
  exact bB_mem p k i hi t₀ n

end Formalism.GM
