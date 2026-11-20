import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

/- English proof (translation)
Introduce `k B W J _ _ _ _ _ _ a ha κ ψ hψ T x w h`. Set `bW : Module.Basis (Fin a) k W` to `Module.finBasisOfFinrankEq k W ha`. Establish `hexp : ∀ (y : W) (i : Fin a), ψ y i = ∑ m, κ (bW.repr y m) * ψ (bW m) i`. Introduce `y i`. Use `conv_lhs => rw [← bW.sum_repr y]`.

Rewrite using `[map_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hψ, Pi.smul_apply, smul_eq_mul]`. Set `X : Matrix (Fin a) (Fin a) B` to `Matrix.of fun i m => ψ (bW m) i`. Set `X' : Matrix (Fin a) (Fin a) B` to `Matrix.of fun m i' => ∑ j, w j * κ (bW.repr (x j i') m)`.

Establish `hXX : X * X' = 1`. Use extensionality with `i i'`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply, ← h i i']`. Simplify using `only [X, X', Matrix.of_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hexp (x j i') i, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => by ring`. Establish `hXX' : X' * X = 1` using `mul_eq_one_comm.mp hXX`. Set `Tm : Matrix (Fin a) (Fin a) B` to `(LinearMap.toMatrix bW bW T).map κ`.

Establish `hrepr : ∀ (y : W) (m : Fin a), bW.repr (T y) m = ∑ m', LinearMap.toMatrix bW bW T m m' * bW.repr y m'`. Introduce `y m`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr bW bW T y]`. Both sides reduce to the same expression. Apply the tactic sequence `have hentry : ∀ i i', ∑ j, w j * ψ (T (x j i')) i = (X * Tm * X') i i' := by`.

Introduce `i i'`. Establish `hTX : ∀ y : W, ψ (T y) i = ∑ m, (X * Tm) i m * κ (bW.repr y m)`. Introduce `y`. Rewrite using `[hexp (T y) i]`. Simplify using `only [hrepr, map_sum, map_mul, Matrix.mul_apply, X, Tm, Matrix.of_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hTX, X', Matrix.of_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations. Establish `htr : Matrix.trace Tm = κ (LinearMap.trace k W T)`. Rewrite using `[LinearMap.trace_eq_matrix_trace k bW T]`. Simplify using `[Matrix.trace, Tm, map_sum]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.trace, Matrix.diag_apply, hentry]`. Use `_ = Matrix.trace (X' * X * Tm) := by`. Rewrite using `[Matrix.trace_mul_cycle]`. Use `_ = κ (LinearMap.trace k W T) := by`. Rewrite using `[hXX', one_mul, htr]`.
-/
theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLin_holds :
    TrLin := by
  intro k B W J _ _ _ _ _ _ a ha κ ψ hψ T x w h
  classical
  let bW : Module.Basis (Fin a) k W := Module.finBasisOfFinrankEq k W ha
  have hexp : ∀ (y : W) (i : Fin a), ψ y i = ∑ m, κ (bW.repr y m) * ψ (bW m) i := by
    intro y i
    conv_lhs => rw [← bW.sum_repr y]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hψ, Pi.smul_apply, smul_eq_mul]
  let X : Matrix (Fin a) (Fin a) B := Matrix.of fun i m => ψ (bW m) i
  let X' : Matrix (Fin a) (Fin a) B := Matrix.of fun m i' => ∑ j, w j * κ (bW.repr (x j i') m)
  have hXX : X * X' = 1 := by
    ext i i'
    rw [Matrix.mul_apply, Matrix.one_apply, ← h i i']
    simp only [X, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hexp (x j i') i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hXX' : X' * X = 1 := mul_eq_one_comm.mp hXX
  let Tm : Matrix (Fin a) (Fin a) B := (LinearMap.toMatrix bW bW T).map κ
  have hrepr : ∀ (y : W) (m : Fin a),
      bW.repr (T y) m = ∑ m', LinearMap.toMatrix bW bW T m m' * bW.repr y m' := by
    intro y m
    rw [← LinearMap.toMatrix_mulVec_repr bW bW T y]
    rfl
  have hentry : ∀ i i', ∑ j, w j * ψ (T (x j i')) i = (X * Tm * X') i i' := by
    intro i i'
    have hTX : ∀ y : W, ψ (T y) i = ∑ m, (X * Tm) i m * κ (bW.repr y m) := by
      intro y
      rw [hexp (T y) i]
      simp only [hrepr, map_sum, map_mul, Matrix.mul_apply, X, Tm, Matrix.of_apply,
        Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ => by ring
    rw [Matrix.mul_apply]
    simp only [hTX, X', Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring
  have htr : Matrix.trace Tm = κ (LinearMap.trace k W T) := by
    rw [LinearMap.trace_eq_matrix_trace k bW T]
    simp [Matrix.trace, Tm, map_sum]
  calc ∑ i, ∑ j, w j * ψ (T (x j i)) i = Matrix.trace (X * Tm * X') := by
        simp only [Matrix.trace, Matrix.diag_apply, hentry]
    _ = Matrix.trace (X' * X * Tm) := by
        rw [Matrix.trace_mul_cycle]
    _ = κ (LinearMap.trace k W T) := by
        rw [hXX', one_mul, htr]
