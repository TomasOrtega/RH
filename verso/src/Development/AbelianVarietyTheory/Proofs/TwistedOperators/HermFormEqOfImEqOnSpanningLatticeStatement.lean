import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermFormEqOfImEqOnSpanningLattice
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHermFormEqOfImEqOnSpanningLattice.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.hermForm_eq_of_im_eq_on_spanning_family : ∀ {g : ℕ} {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ)), Submodule.span ℝ (Set.range P) = ⊤ → ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (h h' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ a b, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h (P a)) (h (P b))).im = (ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' (P a)) (h' (P b))).im) → ∀ x y, ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h x) (h y) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h' x) (h' y) := by
  first | exact @GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | exact GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice | (intros; apply GlobalTheory.hermForm_eq_of_im_eq_on_spanning_lattice <;> assumption)
