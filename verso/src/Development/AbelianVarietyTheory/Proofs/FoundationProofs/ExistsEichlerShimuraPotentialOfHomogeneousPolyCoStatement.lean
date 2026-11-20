import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCo
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.H3.exists_pot_of_isCoc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsEichlerShimuraPotentialOfHomogeneousPolyCo.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N → ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l), ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_isCoc | exact GlobalTheory.KZ.H3.exists_pot_of_isCoc | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_isCoc <;> assumption)
