import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTestFactorNeZeroOfGlobalProductNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLocalTestFactorNeZeroOfGlobalProductNeZero.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.localTestFactor_ne_zero_of_globalProduct_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU E n, (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w n) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := by
  first | exact @GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero | exact GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero | (intros; apply GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero <;> assumption)
