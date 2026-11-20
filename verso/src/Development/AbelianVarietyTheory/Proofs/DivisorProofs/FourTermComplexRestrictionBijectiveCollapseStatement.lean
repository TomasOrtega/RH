import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexRestrictionBijectiveCollapse
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFourTermComplexRestrictionBijectiveCollapse.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.fourTermComplex_restriction_bijective_collapse : ∀ (C : Type 1) [Category.{0} C] (D : Type) [Category.{0} D] (K : Cx C) (ℓ : D ⥤ C) (q : C ⥤ D) (S : C ⥤ C) (u : 𝟭 C ⟶ S) (w : q ⋙ ℓ ⟶ S) (ε : 𝟭 D ⟶ ℓ ⋙ q), (∀ T, K.QAt (u.app T)) → (∀ U, K.QAt (ℓ.map (ε.app U) ≫ w.app (ℓ.obj U))) → (K.resMap ℓ).Bij := by
  first | exact @GlobalTheory.CxCoh.collapse_resMap_bij | exact GlobalTheory.CxCoh.collapse_resMap_bij | (intros; apply GlobalTheory.CxCoh.collapse_resMap_bij <;> assumption)
