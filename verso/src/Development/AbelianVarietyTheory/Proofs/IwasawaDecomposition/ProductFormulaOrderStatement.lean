import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductFormulaOrder
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FProductFormulaOrder.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.product_formula_order : ∀ (F : Type) [Field F] [NumberField F] (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z] (q : Z ⟶ Sp (𝓞 F)), IsArithVar q 0 → ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (t : Z.functionFieldˣ), ∑ᶠ (z : Z) (_ : (q z).asIdeal = v.asIdeal), (Scheme.ord (t : Z.functionField) z : ℝ) * Real.log (Nat.card (Z.residueField z)) = -∑ᶠ y : {y : Sp (AlgebraicClosure F) ⟶ Z // y ≫ q = spMap (algebraMap (𝓞 F) (AlgebraicClosure F))}, Real.log (e.w (valAt y.1 (t : Z.functionField))) := by
  first | exact @GlobalTheory.TrueGeo.PlaceFormula.main | exact GlobalTheory.TrueGeo.PlaceFormula.main | (intros; apply GlobalTheory.TrueGeo.PlaceFormula.main <;> assumption)
