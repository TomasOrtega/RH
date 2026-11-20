import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalOrbitPointEqBesselBasePoint
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsRationalOrbitPointEqBesselBasePoint.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.exists_mem_orb_rat_eq_x0 : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B := by
  first | exact @GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint | exact GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint | (intros; apply GlobalTheory.Unf.FB.exists_rationalOrbit_point_eq_besselBasePoint <;> assumption)
