import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryDensity.EvalBindTorusSubst

open Matrix MvPolynomial
open scoped ComplexOrder

namespace PI.UD

/- English proof (translation)
Use `choose w v d hw hv hgd using fun τ => hs n (g τ) (hg τ)`. Establish `hR : bind₁ (torusSubst w v) P = 0`. Apply `eq_zero_of_torus` to reduce the goal to its premises. Introduce `t ht`. Rewrite using `[eval_bind_torusSubst]`.

Conclude with `hP (fun τ => w τ * diagonal (fun k => t (τ, k)) * v τ) (fun τ => unitary_of_torus (w τ) (v τ) (hw τ) (hv τ) _ (fun k => ht (τ, k)))`. Establish `h2` using `eval_bind_torusSubst w v P (fun p => d p.1 p.2)`. Rewrite `h2` using `[hR, map_zero]`. Establish `e : (fun x : ι × Fin n × Fin n => g x.1 x.2.1 x.2.2) = (fun x : ι × Fin n × Fin n => (w x.1 * diagonal (fun k => d x.1 k) * v x.1) x.2.1 x.2.2)`. Use function extensionality and compare the values at `x`.

Rewrite using `[hgd x.1]`. Rewrite using `[e]`. Conclude with `h2.symm`.
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
Set `D : MvPolynomial (ι × Fin n × Fin n) ℂ` to `∏ τ, (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det`. Establish `hD : D ≠ 0`. Use `Finset.prod_ne_zero_iff.mpr fun τ _ => ?_` and prove the remaining obligations. Establish `e : (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ)) = (rename (fun p : Fin n × Fin n => (τ, p.1, p.2))).toRingHom.mapMatrix (mvPolynomialX (Fin n) (Fin n) ℂ)`. Use extensionality with `i j`.

Simplify using `[mvPolynomialX]`. Rewrite using `[e, ← RingHom.map_det]`. Introduce `h0`. Apply `det_mvPolynomialX_ne_zero (Fin n) ℂ` to reduce the goal to its premises. Establish `hinj : Function.Injective (fun p : Fin n × Fin n => (τ, p.1, p.2))`.

Introduce `a b h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext h.2.1 h.2.2`. Apply `rename_injective _ hinj` to reduce the goal to its premises. Simplify using `using h0`.

Establish `hPD : P * D = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[map_mul, map_zero]`. Distinguish the cases in `hx : ∀ τ, (Matrix.of fun i j : Fin n => x (τ, i, j)).det ≠ 0`.

Establish `h1` using `vanish_invertible hs P hP (fun τ => Matrix.of fun i j => x (τ, i, j)) hx`. Simplify using `only [Matrix.of_apply] at h1`. Establish `e : (fun p : ι × Fin n × Fin n => x (p.1, p.2.1, p.2.2)) = x` using `rfl`. Rewrite `h1` using `[e]`. Rewrite using `[h1, zero_mul]`.

Use `push Not at hx`. Take `⟨τ, hτ⟩` from `hx`. Establish `h3 : eval x D = 0`. Simplify using `only [D, map_prod]`. Apply `Finset.prod_eq_zero (Finset.mem_univ τ)` to reduce the goal to its premises.

Rewrite using `[RingHom.map_det]`. Use `hτ using 2` and compare the differences between its conclusion and the goal. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[h3, mul_zero]`.

Conclude with `(mul_eq_zero.mp hPD).resolve_right hD`.
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
Introduce `ι _ n G hG P hP`. Use `choose C hC hCd using fun τ => hg n (G τ) (hG τ)`. Establish `hCi : ∀ τ, C τ * (C τ)⁻¹ = 1` using `fun τ => Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hCd τ))`. Establish `hiC : ∀ τ, (C τ)⁻¹ * C τ = 1` using `fun τ => Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hCd τ))`. Establish `h0 : bind₁ (leftSubst (fun τ => (C τ)⁻¹)) P = 0`.

Apply `famUnitDense hs` to reduce the goal to its premises. Introduce `u hu`. Rewrite using `[eval_bind_leftSubst]`. Use `hP (fun τ => (C τ)⁻¹ * u τ) ?_` and prove the remaining obligations. Introduce `τ`.

Rewrite using `[← hC τ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = 1 := by rw [hCi τ, conjTranspose_one, Matrix.one_mul, Matrix.one_mul, hu τ]`. Apply `MvPolynomial.funext` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[map_zero]`. Establish `h4` using `eval_bind_leftSubst (fun τ => (C τ)⁻¹) P (fun τ => C τ * Matrix.of fun i j => x (τ, i, j))`. Rewrite `h4` using `[h0, map_zero]`. Simplify using `only [← Matrix.mul_assoc, hiC, Matrix.one_mul, Matrix.of_apply] at h4`.

Conclude with `h4.symm`.
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
