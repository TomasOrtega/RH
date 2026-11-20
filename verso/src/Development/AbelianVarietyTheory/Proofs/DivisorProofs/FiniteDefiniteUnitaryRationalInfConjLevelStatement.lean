import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDefiniteUnitaryRationalInfConjLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteDefiniteUnitaryRationalInfConjLevel.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.finite_definiteUnitaryRational_inf_conj_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ x : finU E n, Finite ↥(ratFinU E n ⊓ (globLev S K').map (MulAut.conj x).toMonoidHom) := by
  first | exact @GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev | exact GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev | (intros; apply GlobalTheory.BCT.finite_ratFinU_inf_conj_globLev <;> assumption)
