import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharIsUnitaryOfUnitaryInfinityType
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHeckeCharIsUnitaryOfUnitaryInfinityType.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.heckeChar_isUnitary_of_unitary_infinityType : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ), χ.HasInf φ n → χ.IsUnitary := by
  first | exact @GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | exact GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf | (intros; apply GlobalTheory.HeckeUnitaryInf.isUnitary_of_hasInf <;> assumption)
