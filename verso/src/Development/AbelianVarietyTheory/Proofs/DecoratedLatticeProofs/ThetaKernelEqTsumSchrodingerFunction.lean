import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActionsStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

/- English proof (translation)
Introduce `D ψ A B χB omh hW ν 𝓨 hν f hf g h`. Establish `hF` using `hW.om_pres (g, 1) f hf`. Establish `hG` using `hW.om_pres (1, h) _ hF`. Establish `e : omh (g, h) f = omh (1, h) (omh (g, 1) f)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]`.

Establish `hs` using `(GlobalTheory.HeisMixSource.heis_mixS D ψ hW.std (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ _ hG).2.2.2.2 0`. Rewrite `hs` using `[map_zero]`. Establish `hl` using `(GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ A B χB omh hW ν 𝓨 hν _ hF).1 h`. Unfold `thetaKO`. Rewrite using `[e, ← hs.tsum_eq]`.

Conclude with `tsum_congr fun ξ => hl (rat ξ)`.
-/
theorem thetaKO_eq_tsum_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g h, thetaKO omh g h f = ∑' ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E, sch ψ A B ν 𝓨 (omh (g, 1) f) (mt B h⁻¹ ⬝ (rat ξ : Mx D B.rank A.rank)) := by
  intro D ψ A B χB omh hW ν 𝓨 hν f hf g h
  have hF := hW.om_pres (g, 1) f hf
  have hG := hW.om_pres (1, h) _ hF
  have e : omh (g, h) f = omh (1, h) (omh (g, 1) f) := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  have hs := (GlobalTheory.HeisMixSource.heis_mixS D ψ hW.std (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ _ hG).2.2.2.2 0
  rw [map_zero] at hs
  have hl := (GlobalTheory.T.schrodingerFunction_unitary_levi_radical_actions D ψ A B χB omh hW ν 𝓨 hν _ hF).1 h
  unfold thetaKO
  rw [e, ← hs.tsum_eq]
  exact tsum_congr fun ξ => hl (rat ξ)

end GlobalTheory.StdUnn
