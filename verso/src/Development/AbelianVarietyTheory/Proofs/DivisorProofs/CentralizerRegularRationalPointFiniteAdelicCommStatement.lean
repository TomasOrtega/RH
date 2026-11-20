import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicComm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.finCent_comm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCentralizerRegularRationalPointFiniteAdelicComm.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU E n)) (finPt γ), ∀ b ∈ twCent (MonoidHom.id (finU E n)) (finPt γ), a * b = b * a := by
  first | exact @GlobalTheory.BCT.finCent_comm | exact GlobalTheory.BCT.finCent_comm | (intros; apply GlobalTheory.BCT.finCent_comm <;> assumption)
