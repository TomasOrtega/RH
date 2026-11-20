import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimitiveCentralIdempotentEqSimpleRepIdempotent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPrimitiveCentralIdempotentEqSimpleRepIdempotent.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.primitiveCentralIdempotent_eq_simpleRepIdempotent : ∀ (g a : ℕ) [Fact g.Prime] (L : PairedCharacterCondition.LzData g) (τ : L.Irr a), ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧ L.idem τ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  first | exact @GlobalTheory.PrimCentIdem.main | exact GlobalTheory.PrimCentIdem.main | (intros; apply GlobalTheory.PrimCentIdem.main <;> assumption)
