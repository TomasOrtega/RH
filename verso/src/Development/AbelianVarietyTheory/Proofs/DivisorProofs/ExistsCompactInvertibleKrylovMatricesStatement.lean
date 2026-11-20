import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactInvertibleKrylovMatrices
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCompactInvertibleKrylovMatrices.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_compact_invertible_krylovMatrices : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w)), IsCompact Ω → (∀ y ∈ Ω, ∃ e, IsUnit (GlobalTheory.LeviDesc.Krylov.krylov y.val e).det) → ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = GlobalTheory.LeviDesc.Krylov.krylov y.val e := by
  first | exact @GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units | exact GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units | (intros; apply GlobalTheory.LeviDesc.Krylov.exists_isCompact_krylov_units <;> assumption)
