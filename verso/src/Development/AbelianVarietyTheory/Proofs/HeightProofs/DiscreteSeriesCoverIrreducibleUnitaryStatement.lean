import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DiscreteSeriesCoverIrreducibleUnitary
import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactExponentialSurjective
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RealPar.CoverURep.urep_irred` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FDiscreteSeriesCoverIrreducibleUnitary.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.discreteSeries_cover_irreducibleUnitary : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ := by
  first | exact @GlobalTheory.RealPar.CoverURep.urep_irred | exact GlobalTheory.RealPar.CoverURep.urep_irred | (intros; apply GlobalTheory.RealPar.CoverURep.urep_irred <;> assumption)
