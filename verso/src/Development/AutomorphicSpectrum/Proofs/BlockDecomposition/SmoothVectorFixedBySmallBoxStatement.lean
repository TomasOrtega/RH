import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedBySmallBox
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipMir
open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSmoothVectorFixedBySmallBox.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.smooth_vector_fixed_by_small_box : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V), IsSmooth ρ → ∀ v : V, ∃ N : ℤ, ∀ x ∈ box k n N, ρ x v = v := by
  first | exact @GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | exact GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed | (intros; apply GlobalTheory.CompanionTheory.MirFourier.exists_box_fixed <;> assumption)
