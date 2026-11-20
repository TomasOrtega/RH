import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCofiniteCenterMonicAnnihilator.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.cofinite_center_monic_annihilator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | exact GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | (intros; apply GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed <;> assumption)
