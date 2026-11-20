import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DvrAdmissibleBaseAndPowerSeriesEvalUniformiser
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `E _ _ _ H Dm l Xo c O _ β Y hN V _ _ _ hV b ϖ a hϖ`. Take `⟨hdvr, hc, hcz⟩` from `(GlobalTheory.LN.cDvr_iff V).1 hV`. Take `⟨⟨h1, h2, -, h4, h5⟩, -⟩` from `GlobalTheory.lawsAndExpansions`. Establish `hT` using `GlobalTheory.twistBaseChange`. Establish `hm : maximalIdeal V = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`.

Take `⟨χ, hχ, -⟩` from `hN V b ϖ a (Or.inr ⟨hdvr, hϖ, hm ▸ hc⟩)`. Take `⟨hs, -, hj, hd⟩` from `(hχ χ).1 rfl`. Take `⟨-, -, ev, hC, hX, -⟩` from `GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser V ϖ hϖ hc`. Establish `hr : Set.range (jK V ≫ spMap ev ≫ χ) ⊆ Set.range Y.j`. Introduce and unpack `_ ⟨x, rfl⟩`.

Establish `e : (jK V ≫ spMap ev ≫ χ) x = χ (spMap ev (jK V x))`. Simplify using `only [Scheme.Hom.comp_apply]`. Rewrite using `[e]`. Apply `hj` to reduce the goal to its premises. Introduce `hx`.

Establish `hx' : algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X)) ∈ x.asIdeal` using `hx`. Establish `hu : IsUnit (algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X)))`. Rewrite using `[map_mul, hC, hX]`. Use `IsUnit.mk0 _ ?_` and prove the remaining obligations. Rewrite using `[Ne, IsFractionRing.to_map_eq_zero_iff]`.

Conclude with `mul_ne_zero hϖ.ne_zero hϖ.ne_zero`. Conclude with `x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx' hu)`. Use `⟨spMap ev ≫ χ, ?_⟩` and prove the remaining obligations. Rewrite using `[hm]`. Conclude with `GlobalTheory.hasArcData_specialise h1 h2 hT h4.unifBaseChange h5 E H Dm l Xo c O β Y V b ϖ a hϖ hc ev hC hX χ hs hr hd`.
-/
theorem exists_point_hasArcData_uniformiser : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (l : Level H) (Xo : Moduli Dm l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), Y.N4 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), Irreducible ϖ → ∃ y : Sp V ⟶ Y.X, Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y := by
  intro E _ _ _ H Dm l Xo c O _ β Y hN V _ _ _ hV b ϖ a hϖ
  obtain ⟨hdvr, hc, hcz⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨⟨h1, h2, -, h4, h5⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hT := GlobalTheory.twistBaseChange
  have hm : maximalIdeal V = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  obtain ⟨χ, hχ, -⟩ := hN V b ϖ a (Or.inr ⟨hdvr, hϖ, hm ▸ hc⟩)
  obtain ⟨hs, -, hj, hd⟩ := (hχ χ).1 rfl
  obtain ⟨-, -, ev, hC, hX, -⟩ := GlobalTheory.UniformiserEval.dvr_admissibleBase_and_powerSeries_evalUniformiser V ϖ hϖ hc
  have hr : Set.range (jK V ≫ spMap ev ≫ χ) ⊆ Set.range Y.j := by
    rintro _ ⟨x, rfl⟩
    have e : (jK V ≫ spMap ev ≫ χ) x = χ (spMap ev (jK V x)) := by
      simp only [Scheme.Hom.comp_apply]
    rw [e]
    apply hj
    intro hx
    have hx' : algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X)) ∈ x.asIdeal := hx
    have hu : IsUnit (algebraMap V (FractionRing V) (ev (PowerSeries.C ϖ * PowerSeries.X))) := by
      rw [map_mul, hC, hX]
      refine IsUnit.mk0 _ ?_
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact mul_ne_zero hϖ.ne_zero hϖ.ne_zero
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx' hu)
  refine ⟨spMap ev ≫ χ, ?_⟩
  rw [hm]
  exact GlobalTheory.hasArcData_specialise h1 h2 hT h4.unifBaseChange h5 E H Dm l Xo c O β Y V b ϖ a hϖ hc ev hC hX χ hs hr hd

end GlobalTheory.Mum
