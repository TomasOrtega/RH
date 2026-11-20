import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.WeilBound.CoreStatements.FlagImmersions.SumFundOnRoot
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerOriginVectorBundle
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RootModelOriginCompatibilityStatement

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

/- English proof (translation)
Introduce `hC hG hW E _ _ _ H D Xo l c Y _ T o II hX hII hp hq B a`. Establish `hIn : PB.Inputs` using `hG.2.2.2.2.2.2.2.2.2.1`. Establish `: FiniteDimensional ℚ c.F` using `c.fin`. Establish `: NumberField c.F` using `⟨⟩`. Establish `hmono : Mono (spMap (algebraMap (𝓞 c.F) c.F))` using `TowerPropA.mono_spMap_ringOfIntegers c.F`.

Establish `hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.toTowerOrigin.S B`. Introduce `p hp hdv`. Rewrite using `[o.toTowerOrigin.S_iff]`. Use `⟨hp, Or.inr ((o.toTowerOrigin.bad_iff p).2 ⟨hp, ?_⟩)⟩` and prove the remaining obligations. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_left hdv 2) _`.

Take `⟨M', t, d, S, K, _, ι, _, P, Re, hgen, hR, hdeg, hpos, hS, hF, hPB⟩` from `hT hG hW E H D l (Xo l) c Y (o.S B) _ (o.Or B a).𝔐.ξ₀ (o.Or B a).𝔐.gen₀ (o.Or B a).𝔐.S_prime hdisc hp hq`. Take `⟨-, ⟨x, hx⟩, -⟩` from `HodgeCpt.basic _ _ _ _ _ _ _ _ Y _ _ _ _ _ (o.Or B a).𝔐 RingOfIntegers.coe_injective`. Establish `hA` using `GlobalTheory.T.root_model_origin_compatibility E H D l (Xo l) c (𝓞 c.F) _ Y (o.S B) (T.M B a) (o.Sys a) (o.Fx a) (o.Or B a) x hx hmono (hX.1 a)`. Take `⟨f₁, f₂⟩` from `hCmp hIn hC II hII E H D l (Xo l) c _ _ Y _ _ _ _ t (RootFieldNumerics.Sq.tieOf (o.Or B a) ((o.Sys a).reg none).1 (o.omVB B a) t.discr hA) hmono hgen (fun p hp => (hX.2 B a p hp).trans (hR p hp).symm) hdeg (o.Or B a).Re_deg`. Use `⟨t.Fl.deg, d, S, K, _, ι, _, P, Re, Nat.cast_pos.2 hpos, by rw [o.j_eq]; exact hF, ?_, hS.trans f₂⟩` and prove the remaining obligations.

Rewrite using `[hPB II, f₁, map_smul]`. Both sides reduce to the same expression.
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
