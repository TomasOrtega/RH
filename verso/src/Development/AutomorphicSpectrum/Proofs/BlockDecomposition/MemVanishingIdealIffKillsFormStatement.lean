import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemVanishingIdealIffKillsForm
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMemVanishingIdealIffKillsForm.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.mem_vanishing_ideal_iff_kills_form : ∀ {R : Type} [CommRing R] {N : ℕ} {Y : Scheme.{0}} (φ : Y ⟶ PSpace R N) (n : ℕ)
    (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n), f ∈ vanIdeal φ ↔ KillsForm φ n f hf := by
  first | exact @GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm | exact GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm | (intros; apply GlobalTheory.CompanionTheory.GE.mem_vanIdeal_iff_killsForm <;> assumption)
