import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialBoundaryFamilyPullUnitaryTraitForm
import Development.AbelianVarietyTheory.Definitions.Divisors.USt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UChart.pull_trait` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMonomialBoundaryFamilyPullUnitaryTraitForm.lean&line=91#L91)
-/
theorem _root_.GlobalTheory.T.monomialBoundaryFamily_pull_unitaryTrait_form : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (ψ : R →+* W), Function.Injective ψ → IsLocalHom ψ → ∀ (ϖ : W), Irreducible ϖ → ∀ (w : Fin C.m → ℕ), (∀ i, Associated (ψ (C.s i)) (ϖ ^ w i)) → ∀ κ : Sp (FractionRing W) ⟶ Sp (FractionRing R), κ ≫ jK R = jK W ≫ spMap ψ → ∃ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))) (P : PELUnif (maximalIdeal W) t), Nonempty (SABMap tK t (jK W)) ∧ Nonempty (SABMap tK Xo.univ.t ((κ ≫ C.y) ≫ pullback.fst _ _)) ∧ ∃ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] ∧ φ.evalZ be = ∑ i, (w i : ℝ) * φ.evalZ ((l.M' : ℤ) • C.δ i) := by
  first | exact @GlobalTheory.UChart.pull_trait | exact GlobalTheory.UChart.pull_trait | (intros; apply GlobalTheory.UChart.pull_trait <;> assumption)
