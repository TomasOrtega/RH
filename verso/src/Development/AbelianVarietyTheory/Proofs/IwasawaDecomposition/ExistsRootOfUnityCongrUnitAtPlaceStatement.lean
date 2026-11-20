import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlace
import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsRootOfUnityCongrUnitAtPlace.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_rootOfUnity_congr_unit_at_place : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ ζ : Ω, ζ ^ (normV P - 1) = 1 ∧ A.valuation (ζ - algebraMap E Ω (u : E)) < 1 := by
  first | exact @GlobalTheory.TameTau.exists_root_congr_unit | exact GlobalTheory.TameTau.exists_root_congr_unit | (intros; apply GlobalTheory.TameTau.exists_root_congr_unit <;> assumption)
