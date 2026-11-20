import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPerfectPairingFiniteModuleRowsCriterion.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.perfect_pairing_finite_module_rows_criterion : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n), Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A), (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  first | exact @GlobalTheory.NewPrime.charDual_cogenerator | exact GlobalTheory.NewPrime.charDual_cogenerator | (intros; apply GlobalTheory.NewPrime.charDual_cogenerator <;> assumption)
