import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryRationalMatrixOfFirstPresentationPo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RatPtsBridge.exists_ratGL` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsUnitaryRationalMatrixOfFirstPresentationPo.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.exists_unitary_rational_matrix_of_first_presentation_point : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (γQ : GQ L n), ∃ (γ : UA L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ ∧ (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom := by
  first | exact @GlobalTheory.RatPtsBridge.exists_ratGL | exact GlobalTheory.RatPtsBridge.exists_ratGL | (intros; apply GlobalTheory.RatPtsBridge.exists_ratGL <;> assumption)
