import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.EvalBindTorusSubst

open Matrix MvPolynomial
open scoped ComplexOrder

namespace PI.UD

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem vanish_invertible (hs : SVDStep) {ι : Type} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * y τ = 1) →
      eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0)
    (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, (g τ).det ≠ 0) :
    eval (fun x : ι × Fin n × Fin n => g x.1 x.2.1 x.2.2) P = 0 := by
  choose w v d hw hv hgd using fun τ => hs n (g τ) (hg τ)
  have hR : bind₁ (torusSubst w v) P = 0 := by
    apply eq_zero_of_torus
    intro t ht
    rw [eval_bind_torusSubst]
    exact hP (fun τ => w τ * diagonal (fun k => t (τ, k)) * v τ) (fun τ => unitary_of_torus (w τ) (v τ) (hw τ) (hv τ) _ (fun k => ht (τ, k)))
  have h2 := eval_bind_torusSubst w v P (fun p => d p.1 p.2)
  rw [hR, map_zero] at h2
  have e : (fun x : ι × Fin n × Fin n => g x.1 x.2.1 x.2.2) =
      (fun x : ι × Fin n × Fin n =>
        (w x.1 * diagonal (fun k => d x.1 k) * v x.1) x.2.1 x.2.2) := by
    funext x
    rw [hgd x.1]
  rw [e]
  exact h2.symm

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem famUnitDense (hs : SVDStep) {ι : Type} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * y τ = 1) →
      eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) : P = 0 := by
  classical
  let D : MvPolynomial (ι × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hD : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
    have e : (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ)) =
        (rename (fun p : Fin n × Fin n => (τ, p.1, p.2))).toRingHom.mapMatrix
          (mvPolynomialX (Fin n) (Fin n) ℂ) := by
      ext i j
      simp [mvPolynomialX]
    rw [e, ← RingHom.map_det]
    intro h0
    apply det_mvPolynomialX_ne_zero (Fin n) ℂ
    have hinj : Function.Injective (fun p : Fin n × Fin n => (τ, p.1, p.2)) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2.1 h.2.2
    apply rename_injective _ hinj
    simpa using h0
  have hPD : P * D = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : ∀ τ, (Matrix.of fun i j : Fin n => x (τ, i, j)).det ≠ 0
    · have h1 := vanish_invertible hs P hP (fun τ => Matrix.of fun i j => x (τ, i, j)) hx
      simp only [Matrix.of_apply] at h1
      have e : (fun p : ι × Fin n × Fin n => x (p.1, p.2.1, p.2.2)) = x := rfl
      rw [e] at h1
      rw [h1, zero_mul]
    · push Not at hx
      obtain ⟨τ, hτ⟩ := hx
      have h3 : eval x D = 0 := by
        simp only [D, map_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ τ)
        rw [RingHom.map_det]
        convert hτ using 2
        ext i j
        simp
      rw [h3, mul_zero]
  exact (mul_eq_zero.mp hPD).resolve_right hD

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem framesDense_of (hs : SVDStep) (hg : GramStep) : PI.FramesDense := by
  intro ι _ n G hG P hP
  choose C hC hCd using fun τ => hg n (G τ) (hG τ)
  have hCi : ∀ τ, C τ * (C τ)⁻¹ = 1 := fun τ =>
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hCd τ))
  have hiC : ∀ τ, (C τ)⁻¹ * C τ = 1 := fun τ =>
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hCd τ))
  have h0 : bind₁ (leftSubst (fun τ => (C τ)⁻¹)) P = 0 := by
    apply famUnitDense hs
    intro u hu
    rw [eval_bind_leftSubst]
    refine hP (fun τ => (C τ)⁻¹ * u τ) ?_
    intro τ
    rw [← hC τ]
    calc ((C τ)⁻¹ * u τ)ᴴ * ((C τ)ᴴ * C τ) * ((C τ)⁻¹ * u τ)
        = (u τ)ᴴ * ((C τ * (C τ)⁻¹)ᴴ * (C τ * (C τ)⁻¹ * u τ)) := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hCi τ, conjTranspose_one, Matrix.one_mul, Matrix.one_mul, hu τ]
  apply MvPolynomial.funext
  intro x
  rw [map_zero]
  have h4 := eval_bind_leftSubst (fun τ => (C τ)⁻¹) P
    (fun τ => C τ * Matrix.of fun i j => x (τ, i, j))
  rw [h0, map_zero] at h4
  simp only [← Matrix.mul_assoc, hiC, Matrix.one_mul, Matrix.of_apply] at h4
  exact h4.symm

end PI.UD
