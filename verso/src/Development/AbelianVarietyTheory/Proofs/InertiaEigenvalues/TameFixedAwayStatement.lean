import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedAway
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTameFixedAway.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.tame_fixed_away : ∀ D : D7, WildOne D → GalAway D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → FullLab D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ k : Fin 2, D.nd.l i ≠ D.host.g k → TameFixed D i [⟨D.R.r, π, 1⟩] ρ k := by
  first | exact @GlobalTheory.TypeLeaf.tameFixed_of_cuspidal | exact GlobalTheory.TypeLeaf.tameFixed_of_cuspidal | (intros; apply GlobalTheory.TypeLeaf.tameFixed_of_cuspidal <;> assumption)
