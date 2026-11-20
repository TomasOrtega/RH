import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNhdOneInUnitaryPrincipalCongruence
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsOpenNhdOneInUnitaryPrincipalCongruence.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.exists_open_nhd_one_in_unitary_principal_congruence : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (N : ℕ), 0 < N → ∃ O : Set (finU L n), IsOpen O ∧ (1 : finU L n) ∈ O ∧ ∀ k ∈ O, ∀ x : GAf L n, F.j x = (k : UA L n) → NG.Cong L n N x := by
  first | exact @GlobalTheory.CongOpen.exists_open_cong | exact GlobalTheory.CongOpen.exists_open_cong | (intros; apply GlobalTheory.CongOpen.exists_open_cong <;> assumption)
