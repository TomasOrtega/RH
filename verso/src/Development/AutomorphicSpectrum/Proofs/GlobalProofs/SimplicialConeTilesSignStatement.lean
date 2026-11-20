import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilesSign
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FSimplicialConeTilesSign.lean&line=326#L326)
-/
theorem _root_.GlobalTheory.T.simplicial_cone_tiles_sign : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] (P : ConvexCone ℚ V) (l : V →ₗ[ℚ] ℚ) (s : Finset V), LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P →
    Tile (P : Set V) (SignConst l) (coneOn s) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main <;> assumption)
