import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FWeylAntisymmetrizationRenameSwapNeg.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_swap_neg : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι) (i j : Fin (m τ)), i ≠ j → rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  first | exact @GlobalTheory.AntisymmSwap.rename_swap_antisymm | exact GlobalTheory.AntisymmSwap.rename_swap_antisymm | (intros; apply GlobalTheory.AntisymmSwap.rename_swap_antisymm <;> assumption)
