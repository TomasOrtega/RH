import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EigenvalueSquare
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CubicCharpolyDiscriminant

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open Matrix Polynomial Loc

/- English proof (translation)
Simplify using `only [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.adjugate_fin_three, Matrix.trace_fin_three]`. Simplify using `[Matrix.diagonal_apply, Matrix.det_fin_three]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem charpoly_three {R : Type} [CommRing R] (N : Matrix (Fin 3) (Fin 3) R) :
    N.charpoly = X ^ 3 - C N.trace * X ^ 2 + C N.adjugate.trace * X - C N.det := by
  simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply, Matrix.adjugate_fin_three,
    Matrix.trace_fin_three]
  simp [Matrix.diagonal_apply, Matrix.det_fin_three]
  ring

/- English proof (translation)
Establish `ha : N.adjugate = star N`. Combine the equalities or inequalities in the displayed calculation. Establish `hs : N.adjugate.trace = N.trace`. Rewrite using `[ha, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, ht]`. Rewrite using `[charpoly_three, hs, hd]`.

Simplify using `only [map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem charpoly_recip {R : Type} [CommRing R] [StarRing R] (N : Matrix (Fin 3) (Fin 3) R)
    (h : N * star N = 1) (hd : N.det = 1) (ht : star N.trace = N.trace) :
    N.charpoly = (X - 1) * (X ^ 2 - C (N.trace - 1) * X + 1) := by
  have ha : N.adjugate = star N := by
    calc N.adjugate = N.adjugate * (N * star N) := by rw [h, mul_one]
      _ = star N := by rw [← mul_assoc, Matrix.adjugate_mul, hd, one_smul, one_mul]
  have hs : N.adjugate.trace = N.trace := by
    rw [ha, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose, ht]
  rw [charpoly_three, hs, hd]
  simp only [map_sub, map_one]
  ring

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.EigenvalueSquare.eig_sq h r hr`.
-/
private theorem eig_sq {A : Matrix (Fin 3) (Fin 3) ℂ} (h : star A * A = 1) (r : ℝ)
    (hr : A.charpoly.eval (r : ℂ) = 0) : r ^ 2 = 1 :=
  _root_.UpperTheory.Reformulated.B.EigenvalueSquare.eig_sq h r hr

/- English proof (translation)
Establish `hr : Real.sqrt (-σ Δ) ^ 2 = -σ Δ` using `Real.sq_sqrt (by linarith)`. Use `set r := Real.sqrt (-σ Δ)`. Establish `hI : ((r : ℂ) * Complex.I) ^ 2 = (σ Δ : ℂ)`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hr]`. Simplify using the standard rewrite rules.

Use `⟨{ toFun := fun x => (σ x.re : ℂ) + σ x.im * (r * Complex.I) map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`. Introduce `x y`. Simplify using the standard rewrite rules. Take the linear combination `(-(σ x.im : ℂ) * σ y.im) * hI`.

Simplify using the standard rewrite rules. Introduce `x y`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Introduce `x`.

Simplify using the standard rewrite rules. Introduce `a`. Simplify using the standard rewrite rules.
-/
private theorem exists_complex {F : Type} [Field F] (σ : F →+* ℝ) (Δ : F) (h : σ Δ < 0) :
    ∃ φ : Lsq F Δ →+* ℂ, (∀ x, φ (star x) = star (φ x)) ∧ ∀ a, φ (algebraMap F _ a) = (σ a : ℂ) := by
  have hr : Real.sqrt (-σ Δ) ^ 2 = -σ Δ := Real.sq_sqrt (by linarith)
  set r := Real.sqrt (-σ Δ)
  have hI : ((r : ℂ) * Complex.I) ^ 2 = (σ Δ : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, hr]
    simp
  refine ⟨{ toFun := fun x => (σ x.re : ℂ) + σ x.im * (r * Complex.I)
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · intro x y
    simp
    linear_combination (-(σ x.im : ℂ) * σ y.im) * hI
  · simp
  · intro x y
    simp
    ring
  · intro x
    simp
  · intro a
    simp

/- English proof (translation)
Use `set A : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := δ.1 with hA`. Establish `hB : ((theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = A.map star` using `rfl`. Establish `hN : ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = A * A.map star`. Rewrite using `[← hB]`. Both sides reduce to the same expression.

Establish `hu : A * star A = 1` using `Matrix.mem_unitaryGroup_iff.1 δ.2`. Rewrite using `[hN]`. Prove the components needed by the constructor for the conclusion. Establish `e : (A * A.map star).map (starRingEnd (Lsq K Δ)) = A.map star * A`. Establish `e1` using `Matrix.map_mul (L := A) (M := A.map star) (f := starRingEnd (Lsq K Δ))`.

Establish `e2 : (A.map star).map (starRingEnd (Lsq K Δ)) = A`. Apply the tactic sequence `ext i j <;> simp [starRingEnd_apply]`. Rewrite using `[e1, e2]`. Both sides reduce to the same expression. Establish `e3 : ∀ M : Matrix (Fin 3) (Fin 3) (Lsq K Δ), star M.trace = (M.map (starRingEnd (Lsq K Δ))).trace` using `fun M => by`.

Simplify using `[Matrix.trace_fin_three, starRingEnd_apply]`. Rewrite using `[e3, e, Matrix.trace_mul_comm]`. Establish `e1 : (A.map star).det = star A.det`. Rewrite using `[← Matrix.det_conjTranspose, ← Matrix.det_transpose]`. Both sides reduce to the same expression.

Establish `e2 : A.det * star A.det = 1`. Rewrite using `[← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hu, Matrix.det_one]`. Rewrite using `[Matrix.det_mul, e1, e2]`.
-/
private theorem trace_det {K : Type} [Field K] {Δ : K} (δ : U3 Δ) :
    star ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).trace =
        ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).trace ∧
      ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)).det = 1 := by
  set A : Matrix (Fin 3) (Fin 3) (Lsq K Δ) := δ.1 with hA
  have hB : ((theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = A.map star := rfl
  have hN : ((δ * theta Δ δ : U3 Δ) : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) = A * A.map star := by
    rw [← hB]; rfl
  have hu : A * star A = 1 := Matrix.mem_unitaryGroup_iff.1 δ.2
  rw [hN]
  constructor
  · have e : (A * A.map star).map (starRingEnd (Lsq K Δ)) = A.map star * A := by
      have e1 := Matrix.map_mul (L := A) (M := A.map star) (f := starRingEnd (Lsq K Δ))
      have e2 : (A.map star).map (starRingEnd (Lsq K Δ)) = A := by
        ext i j <;> simp [starRingEnd_apply]
      rw [e1, e2]
      rfl
    have e3 : ∀ M : Matrix (Fin 3) (Fin 3) (Lsq K Δ), star M.trace = (M.map (starRingEnd (Lsq K Δ))).trace := fun M => by
      simp [Matrix.trace_fin_three, starRingEnd_apply]
    rw [e3, e, Matrix.trace_mul_comm]
  · have e1 : (A.map star).det = star A.det := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
      rfl
    have e2 : A.det * star A.det = 1 := by
      rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hu, Matrix.det_one]
    rw [Matrix.det_mul, e1, e2]

/- English proof (translation)
Establish `h1 : (star t).im = t.im` using `by rw [h]`. Establish `h2 : t.im = 0`. Simplify using `at h1`. Establish `h3 : (2 : K) * t.im = 0` using `by linear_combination -h1`. Simplify using `using h3`.

Apply the tactic sequence `ext <;> simp [h2]`.
-/
private theorem eq_base {K : Type} [Field K] [CharZero K] {Δ : K} (t : Lsq K Δ) (h : star t = t) :
    t = algebraMap K _ t.re := by
  have h1 : (star t).im = t.im := by rw [h]
  have h2 : t.im = 0 := by
    simp at h1
    have h3 : (2 : K) * t.im = 0 := by linear_combination -h1
    simpa using h3
  ext <;> simp [h2]

end UpperTheory.V.Z.Sym.Glob

/- English proof (citation)
Apply `UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FIntegralCasts%2FCapelliIdentities%2FCubicCharpolyDiscriminant.lean&line=81#L81)
-/
theorem UpperTheory.V.Z.Sym.Glob.tauEx :
    UpperTheory.V.Z.Sym.Glob.TauEx :=
  _root_.UpperTheory.Reformulated.B.CubicCharpolyDiscriminant.tauEx
