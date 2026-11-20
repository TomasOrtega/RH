import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerOriginVectorBundle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootModelOriginCompatibilityStatement

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem sq_of (hT : StTie) (hCmp : StCmp) : StSq := by
  intro hC hG hW E _ _ _ H D Xo l c Y _ T o II hX hII hp hq B a
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have : FiniteDimensional ℚ c.F := c.fin
  have : NumberField c.F := ⟨⟩
  have hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F)) := TowerPropA.mono_spMap_ringOfIntegers c.F
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.toTowerOrigin.S B := by
    intro p hp hdv
    rw [o.toTowerOrigin.S_iff]
    refine ⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hdv 2) _
  obtain ⟨M', t, d, S, K, _, ι, _, P, Re, hgen, hR, hdeg, hpos, hS, hF, hPB⟩ :=
    hT hG hW E H D l (Xo l) c Y (o.S B) _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ (o.Or B a).𝔐.S_prime hdisc hp hq
  obtain ⟨-, ⟨x, hx⟩, -⟩ := HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.root_model_origin_compatibility E H D l (Xo l) c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx hmono (hX.1 a)
  obtain ⟨f₁, f₂⟩ := hCmp hIn hC II hII E H D l (Xo l) c _ _ Y _ _ _ _ t
    (RootFieldNumerics.Sq.tieOf (o.Or B a) ((o.Sys a).reg none).1 (o.omVB B a) t.discr hA) hmono hgen
    (fun p hp => (hX.2 B a p hp).trans (hR p hp).symm) hdeg (o.Or B a).Re_deg
  refine ⟨t.Fl.deg, d, S, K, _, ι, _, P, Re, Nat.cast_pos.2 hpos, by rw [o.j_eq]; exact hF, ?_, hS.trans f₂⟩
  rw [hPB II, f₁, map_smul]
  rfl

end SquareStatements
