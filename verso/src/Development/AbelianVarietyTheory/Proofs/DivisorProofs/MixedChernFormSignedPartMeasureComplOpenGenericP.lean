import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

noncomputable section

namespace GlobalTheory.MixNull

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.ChernNull

/- English proof (translation)
Break down `c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩` into its components or cases. Simplify using `[hs]`. Establish `hne : (c.U : Set X).Nonempty` using `⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩`. Use `haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩`. Take `⟨g, hg0, hgZ⟩` from `exists_sec_vanish c.affine hne hZ hgen`.

Take `⟨Q, hQ, r, hQr⟩` from `exists_poly_dvd _ c.etale g hg0`. Establish `hP : MvPolynomial.map σ Q ≠ 0` using `fun e => hQ (MvPolynomial.map_injective σ hσ (by rw [e, map_zero]))`. Use `measure_mono_null ?_ (volume_poly_zero D _ hP)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨hys, hyZ⟩, rfl⟩`. Establish `hyU` using `c.source_subset hys`.

Establish `hgy : ev p σ c.U g y = 0`. Assume the negation of the conclusion as `hne'`. Conclude with `hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))`. Establish `hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) = MvPolynomial.eval₂Hom σ (fun a => c.e y a)`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)` and prove the remaining obligations.

Simplify using `[← ev_eq hyU, ev_algX hyU]`. Simplify using `[← ev_eq hyU, c.apply_eq y hys]`. Use `congrArg (fun F => F Q) hcomp` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Use `show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0`.

Rewrite using `[MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy, zero_mul]`.
-/
theorem chart_null_dom {k : Type} [CommRing k] [IsDomain k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (σ : k →+* ℂ) (hσ : Function.Injective σ) {D : ℕ} {Z : Set X} (hZ : IsClosed Z)
    (hgen : genericPoint X ∉ Z) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ hσ (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

/- English proof (translation)
Introduce `k _ _ X _ p σ hσ _ D L ε U hU`. Establish `hZ : IsClosed ((U : Set X)ᶜ)` using `U.isOpen.isClosed_compl`. Establish `hgen : genericPoint X ∉ (U : Set X)ᶜ` using `fun h => h hU`. Conclude with `GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl fun c => by`. Establish `e : (ptsIn p σ U)ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ}`.

Use extensionality with `y`. Simplify using `[mem_ptsIn]`. Rewrite using `[e]`. Conclude with `chart_null_dom σ hσ hZ hgen c`.
-/
theorem part_compl_null : ∀ (k : Type) [CommRing k] [IsDomain k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ), Function.Injective σ → IsProjOver p → ∀ (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (U : X.Opens), genericPoint X ∈ U → part L ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ _ X _ p σ hσ _ D L ε U hU
  have hZ : IsClosed ((U : Set X)ᶜ) := U.isOpen.isClosed_compl
  have hgen : genericPoint X ∉ (U : Set X)ᶜ := fun h => h hU
  exact GlueCoverNull.glueMeas_null _ _ (isOpen_ptsIn _).measurableSet.compl
    fun c => by
      have e : (ptsIn p σ U)ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ (U : Set X)ᶜ} := by
        ext y
        simp [mem_ptsIn]
      rw [e]
      exact chart_null_dom σ hσ hZ hgen c

end GlobalTheory.MixNull
