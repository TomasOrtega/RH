import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGalois
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIsHeckeGaloisQOfIsHeckeGalois.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.isHeckeGaloisQ_of_isHeckeGalois' : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (r : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)), IsHeckeGalois D.nd i x r → SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) r) := by
  first | exact @GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | exact GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois | (intros; apply GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois <;> assumption)
