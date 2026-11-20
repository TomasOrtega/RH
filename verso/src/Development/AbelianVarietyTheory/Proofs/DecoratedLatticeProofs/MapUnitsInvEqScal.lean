import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTraceZeroLocalNormMulIntegralUnitStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdeleTraceZeroNormAdjustRealComponentsStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem compFin_cA_scal {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D z) =
      sigR _ D.sp.cm.sig (GlobalTheory.AdelicU.compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

/- English proof (translation)
Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_units_inv_eq_scal {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a b : Rˣ) (h : f a = f b) :
    f ((a⁻¹ : Rˣ) : R) = f ((b⁻¹ : Rˣ) : R) := by
  calc f ((a⁻¹ : Rˣ) : R) = f ((a⁻¹ : Rˣ) : R) * (f (b : R) * f ((b⁻¹ : Rˣ) : R)) := by
        rw [← map_mul, Units.mul_inv, map_one, mul_one]
    _ = (f ((a⁻¹ : Rˣ) : R) * f (a : R)) * f ((b⁻¹ : Rˣ) : R) := by rw [h, mul_assoc]
    _ = f ((b⁻¹ : Rˣ) : R) := by rw [← map_mul, Units.inv_mul, map_one, one_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem scalData_exists : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∃ u ε : (AE D)ˣ, ScalData μ u ε := by
  intro D
  obtain ⟨μ, hμ, u₀, ε₀, h0, hI, hI'⟩ := GlobalTheory.T.exists_traceZero_localNorm_mul_integralUnit D
  obtain ⟨u, ε, h1, hfin, hinf⟩ := GlobalTheory.T.exists_idele_traceZero_norm_adjust_realComponents D μ hμ u₀
  have key : ∀ v, GlobalTheory.AdelicU.compFin D.host.F D.host.E v (ε : AE D) =
      GlobalTheory.AdelicU.compFin D.host.F D.host.E v (ε₀ : AE D) := by
    intro v
    have e2 : GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u : AE D)) =
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u₀ : AE D)) := by
      rw [compFin_cA_scal, compFin_cA_scal, hfin v]
    have e := congrArg (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) (h1.trans h0.symm)
    simp only [map_mul] at e
    rw [hfin v, e2, mul_assoc, mul_assoc] at e
    have hu : IsUnit (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (u₀ : AE D) *
        GlobalTheory.AdelicU.compFin D.host.F D.host.E v (cA D (u₀ : AE D))) := by
      refine IsUnit.mul (u₀.isUnit.map _) ?_
      have hc : IsUnit (cA D (u₀ : AE D)) := u₀.isUnit.map (cA D)
      exact hc.map _
    exact hu.mul_left_inj.mp e
  have keyInv : ∀ v, GlobalTheory.AdelicU.compFin D.host.F D.host.E v ((ε⁻¹ : (AE D)ˣ) : AE D) =
      GlobalTheory.AdelicU.compFin D.host.F D.host.E v ((ε₀⁻¹ : (AE D)ˣ) : AE D) := by
    intro v
    exact map_units_inv_eq_scal (GlobalTheory.AdelicU.compFin D.host.F D.host.E v) ε ε₀ (key v)
  refine ⟨μ, hμ, u, ε, h1, ?_, ?_, hinf⟩
  · intro v; rw [key v]; exact hI v
  · intro v; rw [keyInv v]; exact hI' v

end GlobalTheory.StdUnn

end
