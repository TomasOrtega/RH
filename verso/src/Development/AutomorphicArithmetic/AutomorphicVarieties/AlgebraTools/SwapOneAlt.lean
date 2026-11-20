import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Establish `hu : b.T (swap a c * u) = b.T (swap a c) * b.T u` using `b.T_mul a c h u hu`. Establish `hsq` using `b.T_sq a c h`. Rewrite using `[hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]`. Use `module`.
-/
private theorem pair_lt {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) (hu : u⁻¹ a < u⁻¹ c) :
    (b.T (swap a c) * b.T u - q • b.T u) + (b.T (swap a c) * b.T (swap a c * u) - q • b.T (swap a c * u)) = 0 := by
  have hu : b.T (swap a c * u) = b.T (swap a c) * b.T u := b.T_mul a c h u hu
  have hsq := b.T_sq a c h
  rw [hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  module

/- English proof (translation)
Establish `hac : a ≠ c`. Introduce `e`. Rewrite `h` using `[e]`. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w) + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0`.

Introduce `w`. Break down `lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw` into its components or cases. Conclude with `pair_lt b h w hw`. Establish `hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c`. Simplify `hw` using `[Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right]`.

Use `pair_lt b h (swap a c * w) hu` as an intermediate fact. Rewrite `this` using `[← mul_assoc, swap_mul_self, one_mul]`. Rewrite using `[add_comm]`. Conclude with `this`. Establish `hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0`.

Use `Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_` and prove the remaining obligations. Introduce `w _ e`. Apply `hac` to reduce the goal to its premises. Use `congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e` as an intermediate fact. Simplify using `[mul_assoc] at this`.

Conclude with `this.symm`. Introduce `w`. Rewrite using `[← mul_assoc, swap_mul_self, one_mul]`. Unfold `Bern.one`. Rewrite using `[Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]`.

Conclude with `hsum`.
-/
private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := by
    intro e
    rw [e] at h
    omega
  have key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w)
      + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0 := by
    intro w
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact pair_lt b h w hw
    · have hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
        simpa [Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have := pair_lt b h (swap a c * w) hu
      rw [← mul_assoc, swap_mul_self, one_mul] at this
      rw [add_comm]
      exact this
  have hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0 := by
    refine Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simp [mul_assoc] at this
      exact this.symm
    · intro w
      rw [← mul_assoc, swap_mul_self, one_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

/- English proof (translation)
Introduce `R _ n q H _ _ b`. Establish `hinv` using `UpperTheory.V.AlgebraTools.hkInv n`. Establish `p1 : ∀ w, b.T w * b.one = q ^ invN w • b.one`. Use `UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_` and prove the remaining obligations. Rewrite using `[b.T_one, one_mul]`.

Simplify using `[invN, hinv.2.2.1]`. Introduce `a c h w hw ih`. Rewrite using `[b.T_mul a c h w hw, mul_assoc, ih, mul_smul_comm, swap_one b h, smul_smul, (hinv.1 a c h w hw).2.2, pow_succ]`. Use `⟨p1, ?_⟩` and prove the remaining obligations. Use `show (∑ w, b.T w) * b.one = _`.

Rewrite using `[Finset.sum_mul]`. Repeatedly rewrite using `[p1]`. Rewrite using `[← Finset.sum_smul]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.AlgebraTools.hkOne :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ w, b.T w * b.one = q ^ invN w • b.one) ∧ b.one * b.one = poin n q • b.one := by
  intro R _ n q H _ _ b
  have hinv := UpperTheory.V.AlgebraTools.hkInv n
  have p1 : ∀ w, b.T w * b.one = q ^ invN w • b.one := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · rw [b.T_one, one_mul]
      simp [invN, hinv.2.2.1]
    · intro a c h w hw ih
      rw [b.T_mul a c h w hw, mul_assoc, ih, mul_smul_comm, swap_one b h, smul_smul,
        (hinv.1 a c h w hw).2.2, pow_succ]
  refine ⟨p1, ?_⟩
  show (∑ w, b.T w) * b.one = _
  rw [Finset.sum_mul]
  simp_rw [p1]
  rw [← Finset.sum_smul]
  rfl
