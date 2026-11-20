import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatum
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FToricCharacterIsCMHostValueDatum.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.isHostDatum_kap_lam0_of_ok : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | exact GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum | (intros; apply GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum <;> assumption)
