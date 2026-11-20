import Mathlib

open MvPolynomial in
/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma UpperTheory.rational_polynomial_vanishing_naturals {K : Type} [Field K] [CharZero K] {m : ℕ}
    (P : MvPolynomial (Fin m) K) (hP : P ≠ 0) :
    ∃ Q : MvPolynomial (Fin m) ℚ, Q ≠ 0 ∧ ∀ a : Fin m → ℕ,
      eval (fun i => (a i : K)) P = 0 → eval (fun i => (a i : ℚ)) Q = 0 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp hP
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℚ K, φ (coeff d P) ≠ 0 := by
    by_contra h
    push Not at h
    exact hd ((Module.forall_dual_apply_eq_zero_iff ℚ _).mp h)
  refine ⟨∑ e ∈ P.support, monomial e (φ (coeff e P)), ?_, ?_⟩
  · apply MvPolynomial.ne_zero_iff.mpr
    refine ⟨d, ?_⟩
    rw [coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    simpa [mem_support_iff, hd] using hφ
  · intro a ha
    have h1 := congrArg φ ha
    rw [eval_eq', map_sum, map_zero] at h1
    rw [map_sum, ← h1]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp)]
    have : coeff e P * ∏ i, (a i : K) ^ e i = (∏ i, (a i : ℚ) ^ e i) • coeff e P := by
      rw [Rat.smul_def, mul_comm]
      push_cast
      rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]

open MvPolynomial in
/- English proof (translation)
Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private lemma UpperTheory.exists_nat_point_avoiding_polynomials {W : Type} [Finite W] {K : W → Type} [∀ w, Field (K w)]
    [∀ w, CharZero (K w)] {m : ℕ}
    (P : ∀ w, MvPolynomial (Fin m) (K w)) (hP : ∀ w, P w ≠ 0) :
    ∃ a : Fin m → ℕ, ∀ w, eval (fun i => (a i : K w)) (P w) ≠ 0 := by
  classical
  haveI := Fintype.ofFinite W
  choose Q hQ hQ' using fun w => UpperTheory.rational_polynomial_vanishing_naturals (P w) (hP w)
  have hprod : ∏ w, Q w ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ => hQ w
  by_contra h
  push Not at h
  apply hprod
  apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℚ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  choose a ha using fun i => hx i (Set.mem_univ i)
  obtain rfl : x = fun i => (a i : ℚ) := funext fun i => (ha i).symm
  obtain ⟨w, hw⟩ := h a
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ w) (hQ' w a hw)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem UpperTheory.exists_nat_combination_isUnit_of_isUnit_combination :
    ∀ (W : Type) [Finite W] (K : W → Type) [∀ w, Field (K w)] [∀ w, CharZero (K w)] (n m : ℕ) (z : Fin m → Matrix (Fin n) (Fin n) (∀ w, K w)) (x : Fin m → ∀ w, K w), IsUnit (∑ i, x i • z i) → ∃ a : Fin m → ℕ, IsUnit (∑ i, ((a i : ℕ) : ∀ w, K w) • z i) := by
  intro W _ K _ _ n m z x hx
  let P : ∀ w, MvPolynomial (Fin m) (K w) := fun w =>
    (Matrix.of fun j k => ∑ i, MvPolynomial.X i * MvPolynomial.C (z i j k w)).det
  have key : ∀ (y : Fin m → ∀ w, K w) (w : W),
      (∑ i, y i • z i).det w = MvPolynomial.eval (fun i => y i w) (P w) := by
    intro y w
    have h1 := RingHom.map_det (Pi.evalRingHom K w) (∑ i, y i • z i)
    simp only [Pi.evalRingHom_apply] at h1
    rw [h1, RingHom.map_det]
    congr 1
    ext j k
    simp [Matrix.sum_apply, Finset.sum_apply]
  have hiff : ∀ y : Fin m → ∀ w, K w, IsUnit (∑ i, y i • z i) ↔
      ∀ w, MvPolynomial.eval (fun i => y i w) (P w) ≠ 0 := by
    intro y
    rw [Matrix.isUnit_iff_isUnit_det, Pi.isUnit_iff]
    simp only [key, isUnit_iff_ne_zero]
  obtain ⟨a, ha⟩ := UpperTheory.exists_nat_point_avoiding_polynomials P (fun w h => (hiff x).mp hx w (by simp [h]))
  exact ⟨a, (hiff fun i => (a i : ∀ w, K w)).mpr (by simpa using ha)⟩
