import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagAtOfLocalFlag
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
Apply `GlobalTheory.FrameGlue.flagAt_of_locFlag` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagAtOfLocalFlag.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.flag_at_of_local_flag : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (N : ℕ) (A : Fin N → Adl C Y) (p : ℕ), p.Prime → LocFlag A p → FlagAt A p := by
  first | exact @GlobalTheory.FrameGlue.flagAt_of_locFlag | exact GlobalTheory.FrameGlue.flagAt_of_locFlag | (intros; apply GlobalTheory.FrameGlue.flagAt_of_locFlag <;> assumption)
