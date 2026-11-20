import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfTypeSpaceNeBotOfIsotypicPart
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FInfTypeSpaceNeBotOfIsotypicPart.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.inf_typeSpace_ne_bot_of_isotypicPart : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (S : Submodule ℂ (GAf L n → W)), Formalism.L2.NG.IsSubrep ρ S → Formalism.L2.NG.isoTyp ρ S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ → S ⊓ Formalism.L2.NG.TypeSp ρ J χ ≠ ⊥ := by
  first | exact @GlobalTheory.MoveTyped.typed_of_isoTyp | exact GlobalTheory.MoveTyped.typed_of_isoTyp | (intros; apply GlobalTheory.MoveTyped.typed_of_isoTyp <;> assumption)
