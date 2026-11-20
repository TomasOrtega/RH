import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R E ι _ _ _ _ _ a P ha hm`. Establish `hc : ∀ i, IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j))` using `fun i => IsUnit.prod_iff.2 (fun j hj => ha i j (Ne.symm (Finset.ne_of_mem_erase hj)))`. Set `L : ι → R[X]` to `fun i => C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))`. Establish `hL : ∀ i, lag a P i = aeval P (L i)`. Introduce `i`.

Simplify using `only [L, lag, map_mul, aeval_C, Algebra.smul_def]`. Establish `hLe : ∀ i k, (L i).eval (a k) = if i = k then 1 else 0`. Introduce `i k`. Simplify using `only [L, eval_mul, eval_C, eval_prod, eval_sub, eval_X]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Conclude with `Ring.inverse_mul_cancel _ (hc i)`. Rewrite using `[Finset.prod_eq_zero (f := fun j => a k - a j) (Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ k⟩) (sub_self (a k)), mul_zero]`. Establish `hroot : ∀ i, aeval P (X - C (a i)) * lag a P i = 0`. Introduce `i`.

Rewrite using `[hL, ← map_mul]`. Establish `: (X - C (a i)) * L i = C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j, (X - C (a j))`. Simplify using `only [L]`. Rewrite using `[mul_left_comm, Finset.mul_prod_erase Finset.univ (fun j => X - C (a j)) (Finset.mem_univ i)]`. Rewrite using `[this, map_mul, hm, mul_zero]`.

Establish `hq : ∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i`. Introduce `q i`. Take `⟨g, hg⟩` from `(X_sub_C_dvd_sub_C_eval : X - C (a i) ∣ q - C (q.eval (a i)))`. Establish `hq' : q = g * (X - C (a i)) + C (q.eval (a i))`. Rewrite using `[mul_comm, ← hg]`.

Expand and normalize the polynomial expressions, which then agree. Use `conv_lhs => rw [hq']`. Rewrite using `[map_add, map_mul, add_mul, mul_assoc, hroot, mul_zero, zero_add, aeval_C, Algebra.smul_def]`. Establish `hP : ∀ i, P * lag a P i = a i • lag a P i`. Introduce `i`.

Use `hq X i` as an intermediate fact. Rewrite `this` using `[aeval_X, eval_X]`. Then use the resulting hypothesis. Establish `hcomm : ∀ y i, Commute y P → Commute y (lag a P i)`. Introduce `y i hy`. Rewrite using `[hL]`.

Generalize the expression as in `L i = f`. Proceed by induction on `f using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_right hq`. Consider the case `monomial n c`.

Rewrite using `[aeval_monomial]`. Conclude with `Commute.mul_right (show Commute y (algebraMap R E c) from (Algebra.commutes c y).symm) (hy.pow_right n)`. Establish `hsum : ∑ i, lag a P i = 1`. Establish `h1 : ∏ i, (X - C (a i)) ∣ 1 - ∑ i, L i`. Apply `Finset.prod_dvd_of_coprime` to reduce the goal to its premises.

Introduce `i _ j _ hij`. Conclude with `isCoprime_X_sub_C_of_isUnit_sub (ha i j hij)`. Introduce `k _`. Rewrite using `[dvd_iff_isRoot, IsRoot, eval_sub, eval_one, eval_finset_sum]`. Simplify using `only [hLe, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]`.

Take `⟨g, hg⟩` from `h1`. Establish `h2` using `congrArg (aeval P) hg`. Rewrite `h2` using `[map_mul, hm, zero_mul, map_sub, map_one, map_sum, sub_eq_zero]`. Simplify using `only [hL]`. Conclude with `h2.symm`.

Use `⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, hsum⟩, hP, hq, hcomm⟩` and prove the remaining obligations. Use `show lag a P i * lag a P i = lag a P i`. Use `hq (L i) i` as an intermediate fact. Rewrite `this` using `[← hL, hLe, if_pos rfl, one_smul]`. Conclude with `this`.

Use `hq (L i) j` as an intermediate fact. Rewrite `this` using `[← hL, hLe, if_neg hij, zero_smul]`. Conclude with `this`.
-/
theorem UpperTheory.V.AlgebraTools.lag_coi :
    ∀ {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] (a : ι → R) (P : E), (∀ i j, i ≠ j → IsUnit (a i - a j)) → aeval P (∏ i, (X - C (a i))) = 0 → CompleteOrthogonalIdempotents (lag a P) ∧ (∀ i, P * lag a P i = a i • lag a P i) ∧ (∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i) ∧ ∀ y i, Commute y P → Commute y (lag a P i) := by
  intro R E ι _ _ _ _ _ a P ha hm
  have hc : ∀ i, IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := fun i =>
    IsUnit.prod_iff.2 (fun j hj => ha i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  let L : ι → R[X] := fun i =>
    C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))
  have hL : ∀ i, lag a P i = aeval P (L i) := by
    intro i
    simp only [L, lag, map_mul, aeval_C, Algebra.smul_def]
  have hLe : ∀ i k, (L i).eval (a k) = if i = k then 1 else 0 := by
    intro i k
    simp only [L, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with h
    · subst h
      exact Ring.inverse_mul_cancel _ (hc i)
    · rw [Finset.prod_eq_zero (f := fun j => a k - a j)
        (Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ k⟩) (sub_self (a k)), mul_zero]
  have hroot : ∀ i, aeval P (X - C (a i)) * lag a P i = 0 := by
    intro i
    rw [hL, ← map_mul]
    have : (X - C (a i)) * L i =
        C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j, (X - C (a j)) := by
      simp only [L]
      rw [mul_left_comm, Finset.mul_prod_erase Finset.univ (fun j => X - C (a j)) (Finset.mem_univ i)]
    rw [this, map_mul, hm, mul_zero]
  have hq : ∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i := by
    intro q i
    obtain ⟨g, hg⟩ := (X_sub_C_dvd_sub_C_eval : X - C (a i) ∣ q - C (q.eval (a i)))
    have hq' : q = g * (X - C (a i)) + C (q.eval (a i)) := by
      rw [mul_comm, ← hg]
      ring
    conv_lhs => rw [hq']
    rw [map_add, map_mul, add_mul, mul_assoc, hroot, mul_zero, zero_add, aeval_C, Algebra.smul_def]
  have hP : ∀ i, P * lag a P i = a i • lag a P i := by
    intro i
    have := hq X i
    rwa [aeval_X, eval_X] at this
  have hcomm : ∀ y i, Commute y P → Commute y (lag a P i) := by
    intro y i hy
    rw [hL]
    generalize L i = f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact hp.add_right hq
    | monomial n c =>
      rw [aeval_monomial]
      exact Commute.mul_right (show Commute y (algebraMap R E c) from (Algebra.commutes c y).symm)
        (hy.pow_right n)
  have hsum : ∑ i, lag a P i = 1 := by
    have h1 : ∏ i, (X - C (a i)) ∣ 1 - ∑ i, L i := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        exact isCoprime_X_sub_C_of_isUnit_sub (ha i j hij)
      · intro k _
        rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_one, eval_finset_sum]
        simp only [hLe, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    obtain ⟨g, hg⟩ := h1
    have h2 := congrArg (aeval P) hg
    rw [map_mul, hm, zero_mul, map_sub, map_one, map_sum, sub_eq_zero] at h2
    simp only [hL]
    exact h2.symm
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, hsum⟩, hP, hq, hcomm⟩
  · show lag a P i * lag a P i = lag a P i
    have := hq (L i) i
    rw [← hL, hLe, if_pos rfl, one_smul] at this
    exact this
  · have := hq (L i) j
    rw [← hL, hLe, if_neg hij, zero_smul] at this
    exact this
