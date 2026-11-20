import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableSetDetImPosAtIndex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeasurableSetDetImPosAtIndex.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.measurableSet_det_im_pos_at_index : ∀ (κ : Type) [Fintype κ] (p q : κ → ℕ) (ρ₀ : κ), MeasurableSet {b : ∀ ρ, UpqT (p ρ) (q ρ) | 0 < (UpqT.mat (b ρ₀)).det.im} := by
  first | exact @GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos | exact GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos | (intros; apply GlobalTheory.CovTop.VolUp.DetImMeas.measurableSet_det_im_pos <;> assumption)
