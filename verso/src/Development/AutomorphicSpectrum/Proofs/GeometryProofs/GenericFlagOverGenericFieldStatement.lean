import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFlagOverGenericField
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FGenericFlagOverGenericField.lean&line=94#L94)
-/
theorem _root_.GlobalTheory.T.generic_flag_over_generic_field : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) (r : S → ℕ) (V : S → Submodule Ω E) (c : ∀ s, Fin (r s) → E), (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → IsGenericFlag (Ω' := GenField Ω r) (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom V (genB c) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.genB_isGenericFlag <;> assumption)
