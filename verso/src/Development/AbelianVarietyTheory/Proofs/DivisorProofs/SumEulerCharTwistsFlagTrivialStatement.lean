import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumEulerCharTwistsFlagTrivial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagChi.sum_chiPic_flag` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSumEulerCharTwistsFlagTrivial.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.sum_euler_char_twists_flag_trivial : ∀ (k : Type) [Field k] (Z : Scheme.{0}) [IsIntegral Z] [Algebra k Γ(Z, ⊤)], FiniteCohTwists k (structureModule Z) → ∀ (N : ℕ) (g : Fin N → Pic Z), FlagOfTriv g → ∀ c : Pic Z, ∑ i, chiPic k (structureModule Z) (g i + c) = (N : ℤ) * chiPic k (structureModule Z) c := by
  first | exact @GlobalTheory.FlagChi.sum_chiPic_flag | exact GlobalTheory.FlagChi.sum_chiPic_flag | (intros; apply GlobalTheory.FlagChi.sum_chiPic_flag <;> assumption)
