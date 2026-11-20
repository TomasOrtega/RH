import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalMirabolicInvariantPairingScalar
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousMulVec
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd GlobalTheory.SplitWeil GlobalTheory.JHMult GlobalTheory.CompanionTheory.BZShell GlobalTheory.CompanionTheory.MirPair
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalMirabolicInvariantPairingScalar.lean&line=461#L461)
-/
theorem _root_.GlobalTheory.T.cuspidal_mirabolic_invariant_pairing_scalar : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (σ : IrrRep (GL (Fin (m + 1)) k)) (hc : IsCuspidal σ.ρ)
    (β : σ.V →ₗ[ℂ] smoothPart σ.ρ.dual →ₗ[ℂ] ℂ)
    (hβ : ∀ g : GL (Fin (m + 1)) k,
      (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k).mulVec (Pi.single (Fin.last m) 1) = Pi.single (Fin.last m) 1 →
      ∀ a l, β (σ.ρ g a) (contra σ.ρ g l) = β a l),
    ∃ c : ℂ, ∀ a l, β a l = c * (l : Module.Dual ℂ σ.V) a := by
  first | exact @GlobalTheory.CompanionTheory.StabForm.form_unique | exact GlobalTheory.CompanionTheory.StabForm.form_unique | (intros; apply GlobalTheory.CompanionTheory.StabForm.form_unique <;> assumption)
