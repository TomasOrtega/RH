import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitEvalEqKummerClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsUnitEvalEqKummerClass.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_unit_eval_eq_kummer_class : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l n : ℕ) [Fact l.Prime], ∀ a ∈ X.A l, ∃ f ∈ X.Un (l ^ n), AdicCompletion.eval (idl l) (X.Kl l) n a = X.cls l n f := by
  first | exact @GlobalTheory.KZ.ES.exists_un_eval_eq_cls | exact GlobalTheory.KZ.ES.exists_un_eval_eq_cls | (intros; apply GlobalTheory.KZ.ES.exists_un_eval_eq_cls <;> assumption)
