import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleContragredientSocle
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCosocleContragredientSocle.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.cosocle_contragredient_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin N) k) W) (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → IsCosocle σ π → IsSocle (contra σ) (contra π) := by
  first | exact @GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle | exact GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle | (intros; apply GlobalTheory.CompanionTheory.SocleContra.isSocle_contra_of_isCosocle <;> assumption)
