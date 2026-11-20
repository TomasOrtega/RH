import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourTermComplexQuasiIsoAtFormalProperties
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CxCoh.QAtFormal.qAt_formal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFourTermComplexQuasiIsoAtFormalProperties.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.fourTermComplex_quasiIsoAt_formal_properties : ∀ (C : Type 1) [Category.{0} C] (K : Cx C), (∀ (T T' : C) (a : T ⟶ T') [IsIso a], K.QAt a) ∧ (∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T''), K.QAt a → K.QAt b → K.QAt (a ≫ b)) ∧ ∀ (T T' T'' : C) (a : T ⟶ T') (b : T' ⟶ T'') (c : T'' ⟶ T'), b ≫ c = 𝟙 T' → K.QAt (a ≫ b) → K.QAt a := by
  first | exact @GlobalTheory.CxCoh.QAtFormal.qAt_formal | exact GlobalTheory.CxCoh.QAtFormal.qAt_formal | (intros; apply GlobalTheory.CxCoh.QAtFormal.qAt_formal <;> assumption)
