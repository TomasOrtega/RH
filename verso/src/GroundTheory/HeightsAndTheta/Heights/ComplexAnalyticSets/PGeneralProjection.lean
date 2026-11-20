import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGeneralProjection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix MvPolynomial

noncomputable section

def genericMatrix (d n : ℕ) : Matrix (Fin d) (Fin n) (MvPolynomial (Fin d × Fin n) ℂ) :=
  Matrix.of fun i k => X (i, k)

def detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) : MvPolynomial (Fin d × Fin n) ℂ :=
  Matrix.det (Matrix.of fun i j => ∑ k, genericMatrix d n i k * C (M k j))

/- English proof (translation)
Unfold `detPoly`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `[genericMatrix, Matrix.mul_apply]`.
-/
theorem eval_detPoly {d n : ℕ} (M : Matrix (Fin n) (Fin d) ℂ) (x : Fin d × Fin n → ℂ) :
    eval x (detPoly M) = (Matrix.of (fun i k => x (i, k)) * M).det := by
  unfold detPoly
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext i j
  simp [genericMatrix, Matrix.mul_apply]

/- English proof (translation)
Introduce `n d m L hL`. Use `set M : Fin m → Matrix (Fin n) (Fin d) ℂ := fun b => LinearMap.toMatrix' (L b) with hM`. Establish `hne : ∀ b, detPoly (M b) ≠ 0`. Introduce `b h`. Take `⟨g, hg⟩` from `(L b).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hL b))`.

Establish `h1 : LinearMap.toMatrix' g * M b = 1`. Rewrite using `[hM]`. Simplify using `only`. Rewrite using `[← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`. Use `congrArg (eval (fun p : Fin d × Fin n => LinearMap.toMatrix' g p.1 p.2)) h` as an intermediate fact.

Rewrite `this` using `[eval_detPoly, map_zero]`. Establish `h2 : Matrix.of (fun i k => LinearMap.toMatrix' g i k) = LinearMap.toMatrix' g`. Use extensionality with `i k`. Both sides reduce to the same expression. Rewrite `this` using `[h2, h1, det_one]`.

Conclude with `one_ne_zero this`. Establish `hprod : (∏ b, detPoly (M b)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun b _ => hne b`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : Fin d × Fin n → ℂ, eval x (∏ b, detPoly (M b)) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `hprod (MvPolynomial.funext fun x => ?_)` and prove the remaining obligations.

Rewrite using `[map_zero]`. Assume the negation of the conclusion as `hx`. Conclude with `hcon ⟨x, hx⟩`. Use `⟨Matrix.of fun i k => x (i, k), fun b v w hvw => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[map_prod]`.

Establish `hb : (Matrix.of (fun i k => x (i, k)) * M b).det ≠ 0`. Rewrite using `[← eval_detPoly]`. Conclude with `(Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)`. Establish `key : ∀ u, (Matrix.of fun i k => x (i, k)) *ᵥ L b u = (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ u`. Introduce `u`.

Rewrite using `[← Matrix.mulVec_mulVec, hM]`. Simplify using `only`. Rewrite using `[LinearMap.toMatrix'_mulVec]`. Simplify using `only [key] at hvw`. Establish `h0 : (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ (v - w) = 0`.

Rewrite using `[Matrix.mulVec_sub, hvw, sub_self]`. Conclude with `sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hb h0)`.
-/
theorem GeneralProjection.proof : GeneralProjection.Statement := by
  intro n d m L hL
  classical
  set M : Fin m → Matrix (Fin n) (Fin d) ℂ := fun b => LinearMap.toMatrix' (L b) with hM
  have hne : ∀ b, detPoly (M b) ≠ 0 := by
    intro b h
    obtain ⟨g, hg⟩ := (L b).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (hL b))
    have h1 : LinearMap.toMatrix' g * M b = 1 := by
      rw [hM]; dsimp only
      rw [← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
    have := congrArg (eval (fun p : Fin d × Fin n => LinearMap.toMatrix' g p.1 p.2)) h
    rw [eval_detPoly, map_zero] at this
    have h2 : Matrix.of (fun i k => LinearMap.toMatrix' g i k) = LinearMap.toMatrix' g := by
      ext i k; rfl
    rw [h2, h1, det_one] at this
    exact one_ne_zero this
  have hprod : (∏ b, detPoly (M b)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ => hne b
  obtain ⟨x, hx⟩ : ∃ x : Fin d × Fin n → ℂ, eval x (∏ b, detPoly (M b)) ≠ 0 := by
    by_contra hcon
    refine hprod (MvPolynomial.funext fun x => ?_)
    rw [map_zero]
    by_contra hx
    exact hcon ⟨x, hx⟩
  refine ⟨Matrix.of fun i k => x (i, k), fun b v w hvw => ?_⟩
  rw [map_prod] at hx
  have hb : (Matrix.of (fun i k => x (i, k)) * M b).det ≠ 0 := by
    rw [← eval_detPoly]
    exact (Finset.prod_ne_zero_iff.mp hx) b (Finset.mem_univ b)
  have key : ∀ u, (Matrix.of fun i k => x (i, k)) *ᵥ L b u = (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ u := by
    intro u
    rw [← Matrix.mulVec_mulVec, hM]
    dsimp only
    rw [LinearMap.toMatrix'_mulVec]
  simp only [key] at hvw
  have h0 : (Matrix.of (fun i k => x (i, k)) * M b) *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hb h0)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
