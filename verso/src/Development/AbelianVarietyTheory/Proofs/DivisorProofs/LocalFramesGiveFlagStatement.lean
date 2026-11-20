import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFramesGiveFlag
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFrames
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TrivFlag.locFlag_of_locFrames` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalFramesGiveFlag.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.local_frames_give_flag : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {C : CxSt F} {N : ℕ} (A : Fin N → Adl C Y) (p : ℕ), LocFrames A p → LocFlag A p := by
  first | exact @GlobalTheory.TrivFlag.locFlag_of_locFrames | exact GlobalTheory.TrivFlag.locFlag_of_locFrames | (intros; apply GlobalTheory.TrivFlag.locFlag_of_locFrames <;> assumption)
