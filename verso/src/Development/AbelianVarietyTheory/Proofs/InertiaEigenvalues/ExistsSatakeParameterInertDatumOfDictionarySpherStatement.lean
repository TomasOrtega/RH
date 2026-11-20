import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatakeParameterInertDatumOfDictionarySpher
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SatExist.exists_satAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsSatakeParameterInertDatumOfDictionarySpher.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exists_satakeParameter_inertDatum_of_dictionary_spherical : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → π.SphAt v → ∀ Dv : InertDatum L n v w, ∃ α, NG.SatAt π Dv α := by
  first | exact @GlobalTheory.SatExist.exists_satAt | exact GlobalTheory.SatExist.exists_satAt | (intros; apply GlobalTheory.SatExist.exists_satAt <;> assumption)
