import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupJetsChart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLocalHomValuationExtension

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nonempty_unifChart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), y.IsAlg → ∀ (p : ℕ) [Fact p.Prime] (X : ValExt T p), Nonempty (UnifChart Ch X) := by
  intro E _ _ _ H Dw l Xo c T io y Ch hy p _ X
  let _ := H.starRing
  obtain ⟨T', φ, t', m, hi, hf, -, -, P, -⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T Ch.I.G Ch.I.t' Ch.I.m2 _ Ch.I.m1 hy
  obtain ⟨ι', hl, hι⟩ := ValExt.exists_local_extension T T' φ hi hf p X
  obtain ⟨F', x', act', hF, hA, hc, ha⟩ := GlobalTheory.integralChart_baseChange E H Dw l Xo c T io y Ch T' φ t' m
  have key : ∀ {σ : Type} (f : MvPowerSeries σ T.V),
      MvPowerSeries.map ι' (MvPowerSeries.map φ f) = MvPowerSeries.map X.ι f := by
    intro σ f
    ext n
    simp only [MvPowerSeries.coeff_map, ← hι, RingHom.comp_apply]
  refine ⟨⟨T', ι', hl, t', P, F', x', hc, act', ha, ?_, fun a => ?_⟩⟩
  · funext i
    show MvPowerSeries.map ι' (F'.F i) = _
    rw [hF]
    exact key _
  · funext i
    show MvPowerSeries.map ι' (act'.act a i) = _
    rw [hA]
    exact key _

end GlobalTheory.CharDepth
