import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNeg
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FXSubXDvdOfRenameSwapEqNeg.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg : ∀ {σ : Type} [DecidableEq σ] (a b : σ), a ≠ b → ∀ P : MvPolynomial σ ℝ, rename (Equiv.swap a b) P = -P → (X b - X a : MvPolynomial σ ℝ) ∣ P := by
  first | exact @GlobalTheory.swap_odd_dvd | exact GlobalTheory.swap_odd_dvd | (intros; apply GlobalTheory.swap_odd_dvd <;> assumption)
