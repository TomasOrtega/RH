import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFramesSameGramOneUnitaryOrbit
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FRationalFramesSameGramOneUnitaryOrbit.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.rational_frames_same_gram_one_unitary_orbit : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → (∀ x ∈ Orb W x₀, ∃ γ ∈ GQ W, mt W γ ⬝ (rat x₀ : Mx D W.rank ρ) = rat x) ∧ ∀ γ ∈ GQ W, ∀ x ∈ Orb W x₀, ∃ x' ∈ Orb W x₀, mt W γ ⬝ (rat x : Mx D W.rank ρ) = rat x' := by
  first | exact @GlobalTheory.WittOrbit.orb_eq_orbit | exact GlobalTheory.WittOrbit.orb_eq_orbit | (intros; apply GlobalTheory.WittOrbit.orb_eq_orbit <;> assumption)
