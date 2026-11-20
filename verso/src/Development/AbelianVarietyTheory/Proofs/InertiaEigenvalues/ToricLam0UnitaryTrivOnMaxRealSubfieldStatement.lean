import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FToricLam0UnitaryTrivOnMaxRealSubfield.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.lam0_isUnitary_and_trivOnF : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m), (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | exact GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | (intros; apply GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield <;> assumption)
