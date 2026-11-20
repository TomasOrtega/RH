import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalContragredientCentralCharacter
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ContraCusp.contra_facts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalContragredientCentralCharacter.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.cuspidal_contragredient_central_character : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ),
    (contra σ.ρ).IsIrreducible ∧ IsCuspidal (contra σ.ρ) ∧
    ∃ (z : GL (Fin (m + 1)) k) (ϖ : k) (ω : ℂ), (z : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = ϖ • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ∧
      ValuativeRel.valuation k ϖ < 1 ∧ ϖ ≠ 0 ∧ ω ≠ 0 ∧ (∀ a, σ.ρ z a = ω • a) ∧ ∀ l, contra σ.ρ z l = ω⁻¹ • l := by
  first | exact @GlobalTheory.CompanionTheory.ContraCusp.contra_facts | exact GlobalTheory.CompanionTheory.ContraCusp.contra_facts | (intros; apply GlobalTheory.CompanionTheory.ContraCusp.contra_facts <;> assumption)
