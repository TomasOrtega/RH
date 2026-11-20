import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJMatrixInfinite

namespace GroundTheory.Automorphic.GJMatrix

open MeasureTheory Matrix

noncomputable section

instance measurableSpace_matrix {m n X : Type*} [MeasurableSpace X] :
    MeasurableSpace (Matrix m n X) :=
  inferInstanceAs (MeasurableSpace (m → n → X))

instance borelSpace_matrix {m n X : Type*} [Countable m] [Countable n] [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] :
    BorelSpace (Matrix m n X) :=
  inferInstanceAs (BorelSpace (m → n → X))

variable {n X : Type*} [Fintype n]

def matrixMeasure [MeasurableSpace X] (μ : Measure X) : Measure (Matrix n n X) :=
  Measure.pi fun _ : n ↦ Measure.pi fun _ : n ↦ μ

def matrixCoord (x : Matrix n n X) : n × n → X :=
  fun p ↦ x p.1 p.2

def matrixCoordT (x : Matrix n n X) : n × n → X :=
  fun p ↦ x p.2 p.1

omit [Fintype n] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matrixCoord_neg [Neg X] (x : Matrix n n X) : matrixCoord (-x) = -matrixCoord x := rfl

variable (n X) in

def matrixCoordHomeomorph [TopologicalSpace X] : Matrix n n X ≃ₜ (n × n → X) where
  toFun := matrixCoord
  invFun z := Matrix.of fun i j ↦ z (i, j)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p ↦ (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_apply (i, j)

variable (n X) in

def matrixCoordTHomeomorph [TopologicalSpace X] : Matrix n n X ≃ₜ (n × n → X) where
  toFun := matrixCoordT
  invFun z := Matrix.of fun i j ↦ z (j, i)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_pi fun p ↦ (continuous_apply p.1).comp (continuous_apply p.2)
  continuous_invFun := continuous_pi fun i ↦ continuous_pi fun j ↦ continuous_apply (j, i)

omit [Fintype n] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_matrixCoordHomeomorph [TopologicalSpace X] :
    ⇑(matrixCoordHomeomorph n X) = matrixCoord := rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem measurePreserving_matrixCoord [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (matrixCoord : Matrix n n X → n × n → X) (matrixMeasure μ)
      (Measure.pi fun _ : n × n ↦ μ) :=
  measurePreserving_curry_symm μ

/- English proof (translation)
Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem measurePreserving_matrixCoordT [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (matrixCoordT : Matrix n n X → n × n → X) (matrixMeasure μ)
      (Measure.pi fun _ : n × n ↦ μ) := by
  have h := (measurePreserving_piCongrLeft (fun _ : n × n ↦ μ) (Equiv.prodComm n n)).comp
    (measurePreserving_matrixCoord (n := n) μ)
  convert h using 1
  funext x p
  simp only [Function.comp_apply, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    MeasurableEquiv.coe_mk, matrixCoordT]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem trace_mul_eq_sum {R : Type*} [CommRing R] (x y : Matrix n n R) :
    trace (x * y) = ∑ p, matrixCoord x p * matrixCoordT y p := by
  rw [trace, Fintype.sum_prod_type]
  simp only [diag_apply, mul_apply, matrixCoord, matrixCoordT]

end

end GroundTheory.Automorphic.GJMatrix
