import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.SplitChar.locK_mul_locK_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitaryHeckeCharCMSplitPlaceMulConjPlaceEqOne.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_splitPlace_mul_conjPlace_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w u : Pl E, u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ k : Eˣ, μ.locK u k * μ.locK w (Units.map (MonoidHomClass.toMonoidHom (IsCMField.complexConj E)) k) = 1 := by
  first | exact @GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | exact GlobalTheory.BCT.SplitChar.locK_mul_locK_conj | (intros; apply GlobalTheory.BCT.SplitChar.locK_mul_locK_conj <;> assumption)
