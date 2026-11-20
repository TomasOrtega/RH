import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBounds
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogLowestKTypeWeylDimensionLeOfSizeBounds.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.log_lowestKTypeWeylDimension_le_of_sizeBounds : ∀ (D : D7) (i : Fin D.R.m) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) (τ : D.what₂.Tau), Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L := by
  first | exact @GlobalTheory.OneMeasDim.log_dimAt_le | exact GlobalTheory.OneMeasDim.log_dimAt_le | (intros; apply GlobalTheory.OneMeasDim.log_dimAt_le <;> assumption)
