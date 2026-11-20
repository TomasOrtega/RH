import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.Imports
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.tweyl
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
/- English proof (translation)
The claim follows from `d.ok.good.std`.
-/
theorem std_k : IsStd d.B.ψ := d.ok.good.std
include d in
/- English proof (translation)
The claim follows from `d.ok.good.1`.
-/
theorem cm_k : IsCMExt F E σ := d.ok.good.1
/- English proof (translation)
The claim follows from `d.ok.dbl.lin`.
-/
theorem hS_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (fun (g : UA σ d.A.J) x => mat g * x) d.S := d.ok.dbl.lin
/- English proof (translation)
The claim follows from `d.ok.dbl.weil.2.1`.
-/
theorem hO_k : IsUSplitting (adeleClass F) d.B.ψ d.dd (actB (cA σ)) d.om := d.ok.dbl.weil.2.1
/- English proof (translation)
The claim follows from `d.ok.dbl.weil.2.2`.
-/
theorem hR_k : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) d.dd d.χ
    (diagCols (Fin d.n)) d.om := d.ok.dbl.weil.2.2
/- English proof (translation)
Use `show g.1.1 * (g⁻¹).1.1 = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]`. Both sides reduce to the same expression.
-/
theorem mat_mul_inv_k (g : UA σ d.A.J) : mat g * mat g⁻¹ = 1 := by
  show g.1.1 * (g⁻¹).1.1 = 1
  rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]; rfl
end PositivityTheory.SiegelWeilFormula.tweyl
end
end
