import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresenta
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinIsoProof.finIso_nonempty` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitaryFiniteAdeleIdentificationNonemptyPresenta.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) := by
  first | exact @GlobalTheory.FinIsoProof.finIso_nonempty | exact GlobalTheory.FinIsoProof.finIso_nonempty | (intros; apply GlobalTheory.FinIsoProof.finIso_nonempty <;> assumption)
