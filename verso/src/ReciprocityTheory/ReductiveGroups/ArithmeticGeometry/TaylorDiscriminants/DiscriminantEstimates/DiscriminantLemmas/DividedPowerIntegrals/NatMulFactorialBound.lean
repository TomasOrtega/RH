import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DivPowInteg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.DividedPowerIntegrals.GenDefs

open MvPolynomial

namespace PI.DivPowInteg.Top

open PI.DivPowInteg.Gen

section

variable {A K I J : Type} [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
  [Fintype I] [Fintype J]

noncomputable def dpow (κ : I → J → K) (n : ℕ) (R : MvPolynomial (I ⊕ J) K) :
    MvPolynomial (I ⊕ J) K :=
  ((n.factorial : ℚ)⁻¹) • (gdelta κ ^ n) R

/- English proof (translation)
Simplify using `[dpow]`.
-/
theorem dpow_zero (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) : dpow κ 0 R = R := by
  simp [dpow]

/- English proof (translation)
Simplify using `[dpow, map_add, smul_add]`.
-/
theorem dpow_add (κ : I → J → K) (n : ℕ) (p q : MvPolynomial (I ⊕ J) K) :
    dpow κ n (p + q) = dpow κ n p + dpow κ n q := by
  simp [dpow, map_add, smul_add]

/- English proof (translation)
Simplify using `[gdelta]`.
-/
theorem gdelta_C (κ : I → J → K) (c : K) : gdelta κ (C c) = 0 := by
  simp [gdelta]

/- English proof (translation)
Rewrite using `[dpow, pow_succ, Module.End.mul_apply, gdelta_C, map_zero, smul_zero]`.
-/
theorem dpow_C_succ (κ : I → J → K) (k : ℕ) (c : K) : dpow κ (k + 1) (C c) = 0 := by
  rw [dpow, pow_succ, Module.End.mul_apply, gdelta_C, map_zero, smul_zero]

/- English proof (translation)
Rewrite using `[Nat.factorial_succ]`. Use `push_cast`. Establish `h1 : (k.factorial : ℚ) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero k`. Establish `h2 : ((k : ℚ) + 1) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.
-/
theorem nat_mul_factorial_bound (k : ℕ) :
    ((k + 1).factorial : ℚ)⁻¹ * ((k + 1 : ℕ) : ℚ) = (k.factorial : ℚ)⁻¹ := by
  rw [Nat.factorial_succ]
  push_cast
  have h1 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h2 : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/- English proof (translation)
Unfold `dpow`. Rewrite using `[h, smul_add, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, nat_mul_factorial_bound, LinearMap.map_smul_of_tower]`.
-/
theorem dpow_X_mul (κ : I → J → K) (s : I ⊕ J)
    (D : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K) (R : MvPolynomial (I ⊕ J) K)
    (k : ℕ)
    (h : (gdelta κ ^ (k + 1)) (X s * R) =
      X s * (gdelta κ ^ (k + 1)) R + (k + 1) • D ((gdelta κ ^ k) R)) :
    dpow κ (k + 1) (X s * R) = X s * dpow κ (k + 1) R + D (dpow κ k R) := by
  unfold dpow
  rw [h, smul_add, mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, nat_mul_factorial_bound,
    LinearMap.map_smul_of_tower]

def Good (L : Submodule A K) (n : ℕ) (Q : MvPolynomial (I ⊕ J) K) : Prop :=
  ∀ m, Q.coeff m ∈ L ^ n

/- English proof (translation)
Introduce `m`. Rewrite using `[MvPolynomial.coeff_X_mul']`. Use `split_ifs`. Conclude with `hQ _`. Conclude with `Submodule.zero_mem _`.
-/
theorem good_X_mul (L : Submodule A K) (n : ℕ) (s : I ⊕ J) (Q : MvPolynomial (I ⊕ J) K)
    (hQ : Good L n Q) : Good L n (X s * Q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X_mul']
  split_ifs
  · exact hQ _
  · exact Submodule.zero_mem _

/- English proof (translation)
Establish `hy : coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1) ∈ L ^ k`. Establish `e : coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1) = (m s + 1) • coeff (m + Finsupp.single s 1) Q`. Rewrite using `[nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `nsmul_mem (hQ _) _`. Rewrite using `[pow_succ']`. Conclude with `Submodule.mul_mem_mul hc hy`.
-/
theorem good_smul_pderiv (L : Submodule A K) (k : ℕ) (c : K) (hc : c ∈ L) (s : I ⊕ J)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) (m : (I ⊕ J) →₀ ℕ) :
    c * (coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1)) ∈ L ^ (k + 1) := by
  have hy : coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1) ∈ L ^ k := by
    have e : coeff (m + Finsupp.single s 1) Q * ((m s : K) + 1) =
        (m s + 1) • coeff (m + Finsupp.single s 1) Q := by
      rw [nsmul_eq_mul]
      push_cast
      ring
    rw [e]
    exact nsmul_mem (hQ _) _
  rw [pow_succ']
  exact Submodule.mul_mem_mul hc hy

/- English proof (translation)
Introduce `m`. Establish `e : (dL κ i Q).coeff m = ∑ j, κ i j * coeff m (pderiv (Sum.inr j) Q)`. Simplify using `[dL, MvPolynomial.coeff_sum]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_pderiv]`. Conclude with `good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m`.
-/
theorem good_dL (L : Submodule A K) (κ : I → J → K) (hκ : ∀ i j, κ i j ∈ L) (k : ℕ) (i : I)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) : Good L (k + 1) (dL κ i Q) := by
  intro m
  have e : (dL κ i Q).coeff m = ∑ j, κ i j * coeff m (pderiv (Sum.inr j) Q) := by
    simp [dL, MvPolynomial.coeff_sum]
  rw [e]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [MvPolynomial.coeff_pderiv]
  exact good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m

/- English proof (translation)
Introduce `m`. Establish `e : (dR κ j Q).coeff m = ∑ i, κ i j * coeff m (pderiv (Sum.inl i) Q)`. Simplify using `[dR, MvPolynomial.coeff_sum]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[MvPolynomial.coeff_pderiv]`. Conclude with `good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m`.
-/
theorem good_dR (L : Submodule A K) (κ : I → J → K) (hκ : ∀ i j, κ i j ∈ L) (k : ℕ) (j : J)
    (Q : MvPolynomial (I ⊕ J) K) (hQ : Good L k Q) : Good L (k + 1) (dR κ j Q) := by
  intro m
  have e : (dR κ j Q).coeff m = ∑ i, κ i j * coeff m (pderiv (Sum.inl i) Q) := by
    simp [dR, MvPolynomial.coeff_sum]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [MvPolynomial.coeff_pderiv]
  exact good_smul_pderiv L k (κ i j) (hκ i j) _ Q hQ m

/- English proof (translation)
Establish `h0 : ∀ P : MvPolynomial (I ⊕ J) A, Good L 0 (map (algebraMap A K) P)`. Introduce `P m`. Rewrite using `[MvPolynomial.coeff_map, pow_zero]`. Conclude with `Submodule.algebraMap_mem _`. Use `MvPolynomial.induction_on (motive := fun P => ∀ n, Good L n (dpow κ n (map (algebraMap A K) P))) P ?_ ?_ ?_` and prove the remaining obligations.

Introduce `a n`. Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[dpow_zero]`. Conclude with `h0 (C a)`.

Consider the case `succ k`. Rewrite using `[MvPolynomial.map_C, dpow_C_succ]`. Introduce `m`. Rewrite using `[MvPolynomial.coeff_zero]`. Conclude with `Submodule.zero_mem _`.

Introduce `p q hp hq n m`. Rewrite using `[map_add, dpow_add, MvPolynomial.coeff_add]`. Conclude with `Submodule.add_mem _ (hp n m) (hq n m)`. Introduce `p s hp n`. Consider the cases of `n with`.

Consider the case `zero`. Rewrite using `[dpow_zero]`. Conclude with `h0 (p * X s)`. Consider the case `succ k`. Rewrite using `[map_mul, MvPolynomial.map_X, mul_comm]`.

Consider the cases of `s with`. Consider the case `inl i`. Rewrite using `[dpow_X_mul κ (Sum.inl i) (dL κ i) (map (algebraMap A K) p) k (h1 K I J κ i (map (algebraMap A K) p) k)]`. Introduce `m`. Rewrite using `[MvPolynomial.coeff_add]`.

Conclude with `Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m) (good_dL L κ hκ k i _ (hp k) m)`. Consider the case `inr j`. Rewrite using `[dpow_X_mul κ (Sum.inr j) (dR κ j) (map (algebraMap A K) p) k (h2 K I J κ j (map (algebraMap A K) p) k)]`. Introduce `m`. Rewrite using `[MvPolynomial.coeff_add]`.

Conclude with `Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m) (good_dR L κ hκ k j _ (hp k) m)`.
-/
theorem integ (h1 : PowXL) (h2 : PowXR) (L : Submodule A K) (κ : I → J → K)
    (hκ : ∀ i j, κ i j ∈ L) (P : MvPolynomial (I ⊕ J) A) :
    ∀ n, Good L n (dpow κ n (map (algebraMap A K) P)) := by
  classical
  have h0 : ∀ P : MvPolynomial (I ⊕ J) A, Good L 0 (map (algebraMap A K) P) := by
    intro P m
    rw [MvPolynomial.coeff_map, pow_zero]
    exact Submodule.algebraMap_mem _
  refine MvPolynomial.induction_on
    (motive := fun P => ∀ n, Good L n (dpow κ n (map (algebraMap A K) P))) P ?_ ?_ ?_
  · intro a n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (C a)
    | succ k =>
      rw [MvPolynomial.map_C, dpow_C_succ]
      intro m
      rw [MvPolynomial.coeff_zero]
      exact Submodule.zero_mem _
  · intro p q hp hq n m
    rw [map_add, dpow_add, MvPolynomial.coeff_add]
    exact Submodule.add_mem _ (hp n m) (hq n m)
  · intro p s hp n
    cases n with
    | zero =>
      rw [dpow_zero]
      exact h0 (p * X s)
    | succ k =>
      rw [map_mul, MvPolynomial.map_X, mul_comm]
      cases s with
      | inl i =>
        rw [dpow_X_mul κ (Sum.inl i) (dL κ i) (map (algebraMap A K) p) k
          (h1 K I J κ i (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dL L κ hκ k i _ (hp k) m)
      | inr j =>
        rw [dpow_X_mul κ (Sum.inr j) (dR κ j) (map (algebraMap A K) p) k
          (h2 K I J κ j (map (algebraMap A K) p) k)]
        intro m
        rw [MvPolynomial.coeff_add]
        exact Submodule.add_mem _ (good_X_mul L _ _ _ (hp (k + 1)) m)
          (good_dR L κ hκ k j _ (hp k) m)

end

/- English proof (translation)
Introduce `A K I J _ _ _ _ _ _ L κ hκ P n`. Establish `hd : PI.DivPowInteg.delta κ = gdelta κ` using `rfl`. Rewrite using `[hd]`. Use `⟨fun m => integ h1 h2 L κ hκ P n m, fun hv => ?_⟩` and prove the remaining obligations. Break down `hv with hv | hv` into its components or cases.

Conclude with `h3 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)`. Conclude with `h4 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)`.
-/
theorem divPowInteg_of (h1 : PowXL) (h2 : PowXR) (h3 : VanL) (h4 : VanR) : PI.DivPowInteg := by
  intro A K I J _ _ _ _ _ _ L κ hκ P n
  have hd : PI.DivPowInteg.delta κ = gdelta κ := rfl
  rw [hd]
  refine ⟨fun m => integ h1 h2 L κ hκ P n m, fun hv => ?_⟩
  rcases hv with hv | hv
  · exact h3 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)
  · exact h4 K I J κ _ n fun m hm => hv m (MvPolynomial.support_map_subset _ _ hm)

end PI.DivPowInteg.Top
