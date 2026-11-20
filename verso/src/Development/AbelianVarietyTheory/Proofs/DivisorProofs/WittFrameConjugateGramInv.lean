import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WittFrame

/- English proof (translation)
Introduce `D V r X Y hW`. Establish `hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x` using `fun _ => rfl`. Establish `hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]`.

Conclude with `V.herm.eq (V.frame j) (V.frame i)`. Establish `hX : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X) = X`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, star_star]`. Establish `h` using `congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) hW.xy`.

Rewrite `h` using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJ, Formalism.UG.cT_one]`. Rewrite using `[Matrix.mul_assoc]` and apply the resulting hypothesis.
-/
theorem yx_eq_one : ∀ (D : D7) (V : HSp D) (r : ℕ) (X Y : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Y * V.gram) * X = 1 := by
  intro D V r X Y hW
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := fun _ => rfl
  have hJ : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, Formalism.BasicNotions.HSpace.gram]
    exact V.herm.eq (V.frame j) (V.frame i)
  have hX : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X) = X := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hσ, star_star]
  have h := congrArg (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E)) hW.xy
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJ, Formalism.UG.cT_one] at h
  rwa [Matrix.mul_assoc]

end GlobalTheory.WittFrame
