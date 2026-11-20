import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittFrame
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalWittFrame.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.local_witt_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), IsFrame (hR (Fv F v) σ J) (colV v X) (colV v Y) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV | exact GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV | (intros; apply GlobalTheory.CompanionTheory.KFin.FrameLoc.isFrame_colV <;> assumption)
