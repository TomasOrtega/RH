import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrincipalCongruenceMapCompletionSubOneValuedLt
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPrincipalCongruenceMapCompletionSubOneValuedLt.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.principalCongruence_map_completion_sub_one_valued_lt : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (g n : ℕ) [Fact g.Prime] (θ : v.adicCompletion F ≃+* ℚ_[g]), (∀ z, ‖θ z‖ < 1 → Valued.v z < 1) → ∀ k ∈ (GlobalTheory.GLp.red g n).ker, ∀ a b : Fin n, Valued.v ((Matrix.GeneralLinearGroup.map θ.symm.toRingHom (GlobalTheory.GLp.inc g n k) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a b - (((((1 : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val : ℕ) : v.adicCompletion F)) < 1 := by
  first | exact @GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | exact GlobalTheory.GLp.inc_map_sub_one_valued_lt_one | (intros; apply GlobalTheory.GLp.inc_map_sub_one_valued_lt_one <;> assumption)
