import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SumMLSqLeSq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GrowthNorm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

/- English proof (translation)
Unfold `actO`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem actO_smul (c : AF D.host.F) (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (c • x) = c • actO S T g h x := by
  unfold actO
  simp [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Unfold `actO`. Simplify using `[Matrix.mul_add, Matrix.add_mul, smul_add]`.
-/
theorem actO_add (g : GA D S) (h : GA D T) (x y : WO S T) :
    actO S T g h (x + y) = actO S T g h x + actO S T g h y := by
  unfold actO
  simp [Matrix.mul_add, Matrix.add_mul, smul_add]

/- English proof (translation)
Unfold `actO`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (L2.Theta.mt T h)]`. Unfold `L2.Theta.mt`. Simplify using the standard rewrite rules.
-/
theorem actO_inv (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  unfold actO
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (L2.Theta.mt T h)]
  unfold L2.Theta.mt
  simp

/- English proof (translation)
Simplify using `using actO_inv g⁻¹ h⁻¹ x`.
-/
theorem actO_inv' (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  simpa using actO_inv g⁻¹ h⁻¹ x

end Formalism.IndefR.Eqv

end
