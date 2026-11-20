import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogAbsoluteValueRational
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLogAbsoluteValueRational.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.log_absolute_value_rational : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (α : AlgebraicClosure F), α ≠ 0 → ∃ (m : ℕ) (z : ℤ), 0 < m ∧ (m : ℝ) * Real.log (e.w α) = (z : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
  first | exact @GlobalTheory.ExtValueGroup.log_w_rat | exact GlobalTheory.ExtValueGroup.log_w_rat | (intros; apply GlobalTheory.ExtValueGroup.log_w_rat <;> assumption)
