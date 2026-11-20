import Mathlib
import Formalism.SatakeDualWeyl.Statement

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Matrix

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cT_conj_eq {m p : Type} (M : Matrix m p ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT]

/- English proof (translation)
Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem form_Jpq (p q : ℕ) (y : Fin p ⊕ Fin q → ℂ) :
    star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) =
      (∑ i, star (y (Sum.inl i)) * y (Sum.inl i)) - ∑ j, star (y (Sum.inr j)) * y (Sum.inr j) := by
  unfold Formalism.UG.Jpq
  simp [dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec,
    Function.comp_def, sub_eq_add_neg] <;> ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Split into cases according to the possible forms of the given data. Treat this case separately.

Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
-/
theorem sylvester_le {n k : Type} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (J : Matrix n n ℂ) {p q : ℕ} (hJ : Formalism.UG.HasSignature J p q) (B : Matrix n k ℂ)
    (hB : Function.Injective B.mulVec)
    (hneg : ∀ v : k → ℂ, (star (B *ᵥ v) ⬝ᵥ (J *ᵥ (B *ᵥ v))).re ≤ 0) : Fintype.card k ≤ q := by
  classical
  obtain ⟨e, P, hP⟩ := hJ
  rw [cT_conj_eq] at hP
  by_contra hcon
  push_neg at hcon
  let T : (k → ℂ) →ₗ[ℂ] (Fin q → ℂ) := (LinearMap.funLeft ℂ ℂ Sum.inr) ∘ₗ
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) ∘ₗ
    (LinearMap.funLeft ℂ ℂ e.symm) ∘ₗ (Matrix.mulVecLin B)
  have hker : LinearMap.ker T ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]
    exact hcon
  obtain ⟨v, hvK, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hTv : T v = 0 := LinearMap.mem_ker.1 hvK
  have hyr : ∀ j, (((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ
      ((B *ᵥ v) ∘ e.symm)) (Sum.inr j) = 0 := fun j => congrFun hTv j
  set w : n → ℂ := B *ᵥ v with hwdef
  set y : Fin p ⊕ Fin q → ℂ :=
    ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ (w ∘ e.symm) with hydef
  have hw : w ∘ e.symm = (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) *ᵥ y := by
    rw [hydef, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hwne : w ≠ 0 := by
    intro h
    apply hv0
    apply hB
    show B *ᵥ v = B *ᵥ 0
    rw [Matrix.mulVec_zero]
    exact h
  have hyne : y ≠ 0 := by
    intro h
    apply hwne
    funext i
    have h3 := congrFun hw (e i)
    rw [h, Matrix.mulVec_zero] at h3
    simpa using h3
  obtain ⟨i, hi⟩ : ∃ i, y (Sum.inl i) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hyne
    funext s
    cases s with
    | inl i => exact hall i
    | inr j => exact hyr j
  have h1 : star w ⬝ᵥ (J *ᵥ w) = star (w ∘ e.symm) ⬝ᵥ (J.reindex e e *ᵥ (w ∘ e.symm)) := by
    simp only [dotProduct, mulVec, Matrix.reindex_apply, Matrix.submatrix_apply, Function.comp_apply,
      Pi.star_apply]
    refine Fintype.sum_equiv e _ _ (fun a => ?_)
    simp only [Equiv.symm_apply_apply]
    congr 1
    exact Fintype.sum_equiv e _ _ (fun b => by simp only [Equiv.symm_apply_apply])
  have hform : star w ⬝ᵥ (J *ᵥ w) = star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) := by
    rw [h1, hw, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hP]
  have hre : ∀ z : ℂ, (star z * z).re = Complex.normSq z := fun z => by
    rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
    ring
  have hpos : 0 < (star w ⬝ᵥ (J *ᵥ w)).re := by
    rw [hform, form_Jpq]
    simp only [hyr, mul_zero, Finset.sum_const_zero, sub_zero, Complex.re_sum, hre]
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩
  have := hneg v
  linarith

end PI.AutLzFinite.SlopeTestRemainingChoices
