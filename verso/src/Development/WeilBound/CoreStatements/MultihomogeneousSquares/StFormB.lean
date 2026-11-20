import Development.WeilBound.CoreStatements.MultihomogeneousSquares.AntisymmetryFibreSquares
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptMultihomogForm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGenericStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalSchemeCoordsInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUnique

noncomputable section

namespace SquareStatements

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ K _ J _ x 𝔐`. Take `⟨hint, -⟩` from `GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J x 𝔐 RingOfIntegers.coe_injective`. Establish `: IsLocallyNoetherian 𝔐.X` using `Cmp.HInterior.isLocallyNoetherian_of_coordTie 𝔐.ξ _ 𝔐.tie 𝔐.all`. Set `U : 𝔐.X.Opens` to `⟨abLocus 𝔐.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian 𝔐.t.G 𝔐.t.semi⟩`. Establish `hU : genPt 𝔐.ξ ∈ U` using `hint`.

Take `⟨β, b, hb, hβ, hw⟩` from `Cmp.HInterior.exists_homog_form_point 𝔐.ξ x 𝔐.tie U hU`. Use `⟨β, b, hb, hβ, fun z w hz hnot => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hmc : w ∈ mcPts (mCoordIdeal x)` using `⟨fun k => (hz.1 k).imp fun _ h => h.ne_zero, fun g hg => by`. Rewrite using `[MvPolynomial.eval_map]`.

Conclude with `((tie_points _ _ 𝔐.ξ K J x 𝔐.tie ℂ).2.2 z _ (𝔐.all _) hz).1 g hg⟩`. Take `⟨z', hz', hzU⟩` from `hw w hmc hne`. Establish `e : z = z'` using `GlobalTheory.T.normal_scheme_coords_injective _ _ 𝔐.ξ K J x 𝔐.tie 𝔐.normal 𝔐.all z z' w hz hz'`. Substitute `e` using the available equality. Conclude with `hnot hzU`.
-/
theorem stFormB : StForm := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ x 𝔐
  obtain ⟨hint, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c _ _ Y S Ω K J x 𝔐 RingOfIntegers.coe_injective
  have : IsLocallyNoetherian 𝔐.X := Cmp.HInterior.isLocallyNoetherian_of_coordTie 𝔐.ξ _ 𝔐.tie 𝔐.all
  let U : 𝔐.X.Opens :=
    ⟨abLocus 𝔐.t.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian 𝔐.t.G 𝔐.t.semi⟩
  have hU : genPt 𝔐.ξ ∈ U := hint
  obtain ⟨β, b, hb, hβ, hw⟩ := Cmp.HInterior.exists_homog_form_point 𝔐.ξ x 𝔐.tie U hU
  refine ⟨β, b, hb, hβ, fun z w hz hnot => ?_⟩
  by_contra hne
  have hmc : w ∈ mcPts (mCoordIdeal x) :=
    ⟨fun k => (hz.1 k).imp fun _ h => h.ne_zero, fun g hg => by
      rw [MvPolynomial.eval_map]
      exact ((tie_points _ _ 𝔐.ξ K J x 𝔐.tie ℂ).2.2 z _ (𝔐.all _) hz).1 g hg⟩
  obtain ⟨z', hz', hzU⟩ := hw w hmc hne
  have e : z = z' := GlobalTheory.T.normal_scheme_coords_injective _ _ 𝔐.ξ K J x 𝔐.tie 𝔐.normal 𝔐.all z z' w hz hz'
  subst e
  exact hnot hzU

end SquareStatements
