import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleTrivialNearFibreFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatUnitCocycleLocallyCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFrameInvariantUnderDescentDatumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfDescentInvariantFramesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBDescent

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem exists_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) [IsFinite f] [Flat f] [Surjective f] [IsLocallyNoetherian Y] (L : LB X), L.IsLB → ∀ (φ : ∀ i j, Γ(pullback f f, GlobalTheory.LBDescent.chart f L i j)ˣ), GlobalTheory.LBDescent.DescCompat f L φ → GlobalTheory.LBDescent.DescCocycle f L φ → ∃ L' : LB Y, L'.IsLB ∧ LBIso L (L'.pull f) := by
  intro X Y f _ _ _ _ L hL φ hc hcoc
  refine GlobalTheory.T.exists_lineBundle_of_descentInvariant_frames f L hL φ fun y => ?_
  obtain ⟨V, hy, t, ht⟩ := GlobalTheory.T.exists_lineBundle_trivial_near_fibre_finite f L hL y
  obtain ⟨c, hct, hcc⟩ := GlobalTheory.T.descentDatum_frame_cocycle_unit f L hL φ hc hcoc V t ht
  obtain ⟨V', hle, hy', u, hu⟩ := GlobalTheory.T.finiteFlat_unitCocycle_locally_coboundary f V c hcc y hy
  exact ⟨V', hy', GlobalTheory.T.twisted_frame_invariant_under_descentDatum f L φ V t ht c hct V' hle u hu⟩

end GlobalTheory.LBDescent
