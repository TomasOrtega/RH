import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.IsLocOpOfOk

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD

variable (d : SD σ)

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.map_mul`.
-/
theorem incM_mul' {p : Type} [Fintype p] (M N : Matrix p p E) : incM F (M * N) = incM F M * incM F N := by
  unfold incM
  exact Matrix.map_mul

/- English proof (translation)
Unfold `incM`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem incM_one' {p : Type} [DecidableEq p] : incM F (1 : Matrix p p E) = 1 := by
  unfold incM
  exact Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Rewrite using `[← incM_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one']`.
-/
theorem bb1 : incM F d.b.1 * incM F (d.b⁻¹).1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one']

/- English proof (translation)
Rewrite using `[← incM_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one']`.
-/
theorem bb2 : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := by
  rw [← incM_mul', ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one']

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matrixRep_mul (x y : d.G) : mat2 (x * y) = mat2 x * mat2 y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem matrixRep_one : mat2 (1 : d.G) = 1 := rfl

/- English proof (translation)
Simplify using `only [inFrame, matrixRep_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[d.bb1]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`.
-/
theorem inFrame_mul (x y : d.G) : inFrame d.b (x * y) = inFrame d.b x * inFrame d.b y := by
  simp only [inFrame, matrixRep_mul]
  calc incM F (d.b⁻¹).1 * (mat2 x * mat2 y) * incM F d.b.1
      = incM F (d.b⁻¹).1 * mat2 x * (incM F d.b.1 * incM F (d.b⁻¹).1) * mat2 y * incM F d.b.1 := by
        rw [d.bb1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [inFrame, matrixRep_one, Matrix.mul_one, d.bb2]`.
-/
theorem inFrame_one : inFrame d.b (1 : d.G) = 1 := by
  simp only [inFrame, matrixRep_one, Matrix.mul_one, d.bb2]

/- English proof (translation)
Establish `hx : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1`. Simplify using `only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, d.bb1, Matrix.mul_one]`. Establish `hy : mat2 y = incM F d.b.1 * inFrame d.b y * incM F (d.b⁻¹).1`. Simplify using `only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]`.

Rewrite using `[Matrix.mul_assoc, d.bb1, Matrix.mul_one]`. Establish `: mat2 x = mat2 y` using `by rw [hx, hy, h]`. Conclude with `Subtype.ext (Units.ext this)`.
-/
theorem inFrame_inj {x y : d.G} (h : inFrame d.b x = inFrame d.b y) : x = y := by
  have hx : mat2 x = incM F d.b.1 * inFrame d.b x * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have hy : mat2 y = incM F d.b.1 * inFrame d.b y * incM F (d.b⁻¹).1 := by
    simp only [inFrame, ← Matrix.mul_assoc, d.bb1, Matrix.one_mul]
    rw [Matrix.mul_assoc, d.bb1, Matrix.mul_one]
  have : mat2 x = mat2 y := by rw [hx, hy, h]
  exact Subtype.ext (Units.ext this)

end SD

end PositivityTheory.SiegelWeilFormula

end
