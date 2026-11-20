import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.Integral

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

/- English proof (translation)
Introduce `O _ _ _ _ _ K _ _ _ _ v hv y hy hy0`. Establish `v1 : v 1 = 0`. Establish `h` using `hv.mul 1 1 one_ne_zero one_ne_zero`. Rewrite `h` using `[one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `vneg : ∀ z : K, z ≠ 0 → v (-z) = v z`. Introduce `z hz`. Establish `h1` using `hv.mul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)`. Rewrite `h1` using `[neg_one_mul, neg_neg, v1]`. Establish `h2` using `hv.mul (-1) z (neg_ne_zero.mpr one_ne_zero) hz`.

Rewrite `h2` using `[neg_one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `vpow : ∀ k : ℕ, v (y ^ k) = k * v y`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simp [v1]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, hv.mul _ _ (pow_ne_zero _ hy0) hy0, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `vsum : ∀ (s : Finset ℕ) (f : ℕ → K) (c : ℝ), (∀ i ∈ s, f i ≠ 0 → c ≤ v (f i)) → (∑ i ∈ s, f i) ≠ 0 → c ≤ v (∑ i ∈ s, f i)`. Introduce `s f c`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro _ h`. Simplify using `at h`.

Consider the case `insert a s ha ih`. Introduce `hf hs`. Rewrite `hs`, the goal using `[Finset.sum_insert ha]`. Distinguish the cases in `hfa : f a = 0`. Rewrite `hs`, the goal using `[hfa, zero_add]`.

Conclude with `ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs`. Distinguish the cases in `hS : (∑ i ∈ s, f i) = 0`. Rewrite using `[hS, add_zero]`. Conclude with `hf a (Finset.mem_insert_self a s) hfa`. Establish `h1` using `hv.add _ _ hfa hS hs`.

Establish `h2` using `hf a (Finset.mem_insert_self a s) hfa`. Establish `h3` using `ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hS`. Conclude with `le_trans (le_min h2 h3) h1`. Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`.

Take `⟨p, hpm, hp⟩` from `hy`. Establish `hsum` using `hp`. Rewrite `hsum` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul]`. Establish `hS : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) = -(y ^ p.natDegree)` using `eq_neg_of_add_eq_zero_left hsum`. Establish `hyn : y ^ p.natDegree ≠ 0` using `pow_ne_zero _ hy0`.

Establish `hS0 : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) ≠ 0`. Rewrite using `[hS]`. Conclude with `neg_ne_zero.mpr hyn`. Establish `hnpos : 0 < p.natDegree`. Break down `Nat.eq_zero_or_pos p.natDegree with h | h` into its components or cases.

It suffices to derive a contradiction. Rewrite `hS` using `[h, Finset.sum_range_zero, pow_zero]`. Conclude with `one_ne_zero (neg_eq_zero.mp hS.symm)`. Conclude with `h`. Establish `hterm : ∀ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i ≠ 0 → ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (algebraMap O K (p.coeff i) * y ^ i)`.

Introduce `i hi hne`. Establish `hc : p.coeff i ≠ 0`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Simplify using `[h]`.

Establish `hmc : algebraMap O K (p.coeff i) ≠ 0`. Introduce `h`. Apply `hc` to reduce the goal to its premises. Conclude with `(FaithfulSMul.algebraMap_injective O K) (by rw [h, map_zero])`. Rewrite using `[hv.mul _ _ hmc (pow_ne_zero _ hy0), hv.base _ hc, vpow]`.

Establish `hi' : i ≤ p.natDegree - 1`. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hle : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ (i : ℝ) * v y`. Apply `mul_le_mul_of_nonpos_right _ hneg.le` to reduce the goal to its premises.

Conclude with `hi'` after adjusting the coercions. Establish `h0 : (0 : ℝ) ≤ ((IsDiscreteValuationRing.addVal O (p.coeff i)).toNat : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbound : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i)` using `vsum (Finset.range p.natDegree) (fun i => algebraMap O K (p.coeff i) * y ^ i) _ hterm hS0`. Rewrite `hbound` using `[hS, vneg _ hyn, vpow, Nat.cast_pred hnpos]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Alg.M.int_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] (v : K → ℝ), IsNVal O K v → ∀ y : K, IsIntegral O y → y ≠ 0 → 0 ≤ v y := by
  intro O _ _ _ _ _ K _ _ _ _ v hv y hy hy0
  have v1 : v 1 = 0 := by
    have h := hv.mul 1 1 one_ne_zero one_ne_zero
    rw [one_mul] at h
    linarith
  have vneg : ∀ z : K, z ≠ 0 → v (-z) = v z := by
    intro z hz
    have h1 := hv.mul (-1) (-1) (neg_ne_zero.mpr one_ne_zero) (neg_ne_zero.mpr one_ne_zero)
    rw [neg_one_mul, neg_neg, v1] at h1
    have h2 := hv.mul (-1) z (neg_ne_zero.mpr one_ne_zero) hz
    rw [neg_one_mul] at h2
    linarith
  have vpow : ∀ k : ℕ, v (y ^ k) = k * v y := by
    intro k
    induction k with
    | zero => simp [v1]
    | succ k ih =>
      rw [pow_succ, hv.mul _ _ (pow_ne_zero _ hy0) hy0, ih]
      push_cast
      ring
  have vsum : ∀ (s : Finset ℕ) (f : ℕ → K) (c : ℝ), (∀ i ∈ s, f i ≠ 0 → c ≤ v (f i)) →
      (∑ i ∈ s, f i) ≠ 0 → c ≤ v (∑ i ∈ s, f i) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => intro _ h; simp at h
    | insert a s ha ih =>
      intro hf hs
      rw [Finset.sum_insert ha] at hs ⊢
      by_cases hfa : f a = 0
      · rw [hfa, zero_add] at hs ⊢
        exact ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hs
      by_cases hS : (∑ i ∈ s, f i) = 0
      · rw [hS, add_zero]
        exact hf a (Finset.mem_insert_self a s) hfa
      have h1 := hv.add _ _ hfa hS hs
      have h2 := hf a (Finset.mem_insert_self a s) hfa
      have h3 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) hS
      exact le_trans (le_min h2 h3) h1
  by_contra hneg
  push_neg at hneg
  obtain ⟨p, hpm, hp⟩ := hy
  have hsum := hp
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hpm.coeff_natDegree, map_one, one_mul] at hsum
  have hS : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) = -(y ^ p.natDegree) :=
    eq_neg_of_add_eq_zero_left hsum
  have hyn : y ^ p.natDegree ≠ 0 := pow_ne_zero _ hy0
  have hS0 : (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) ≠ 0 := by
    rw [hS]
    exact neg_ne_zero.mpr hyn
  have hnpos : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with h | h
    · exfalso
      rw [h, Finset.sum_range_zero, pow_zero] at hS
      exact one_ne_zero (neg_eq_zero.mp hS.symm)
    · exact h
  have hterm : ∀ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i ≠ 0 →
      ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ v (algebraMap O K (p.coeff i) * y ^ i) := by
    intro i hi hne
    have hc : p.coeff i ≠ 0 := by
      intro h
      apply hne
      simp [h]
    have hmc : algebraMap O K (p.coeff i) ≠ 0 := by
      intro h
      apply hc
      exact (FaithfulSMul.algebraMap_injective O K) (by rw [h, map_zero])
    rw [hv.mul _ _ hmc (pow_ne_zero _ hy0), hv.base _ hc, vpow]
    have hi' : i ≤ p.natDegree - 1 := by
      have := Finset.mem_range.mp hi
      omega
    have hle : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤ (i : ℝ) * v y := by
      apply mul_le_mul_of_nonpos_right _ hneg.le
      exact_mod_cast hi'
    have h0 : (0 : ℝ) ≤ ((IsDiscreteValuationRing.addVal O (p.coeff i)).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hbound : ((p.natDegree - 1 : ℕ) : ℝ) * v y ≤
      v (∑ i ∈ Finset.range p.natDegree, algebraMap O K (p.coeff i) * y ^ i) :=
    vsum (Finset.range p.natDegree) (fun i => algebraMap O K (p.coeff i) * y ^ i) _ hterm hS0
  rw [hS, vneg _ hyn, vpow, Nat.cast_pred hnpos] at hbound
  linarith
