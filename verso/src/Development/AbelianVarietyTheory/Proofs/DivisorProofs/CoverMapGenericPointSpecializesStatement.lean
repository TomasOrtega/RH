import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverMapGenericPointSpecializes
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoverGenPt.j_genericPoint_specializes` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoverMapGenericPointSpecializes.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.cover_map_generic_point_specializes : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y), V.j (genericPoint V.G) ⤳ genericPoint V.X := by
  first | exact @GlobalTheory.CoverGenPt.j_genericPoint_specializes | exact GlobalTheory.CoverGenPt.j_genericPoint_specializes | (intros; apply GlobalTheory.CoverGenPt.j_genericPoint_specializes <;> assumption)
