import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitChartAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelOpenNoetherian

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

/- English proof (translation)
Introduce `F _ _ V p hpr hpV X s Xw hXw hg`. Establish `hirr` using `hg F V.subtype Subtype.val_injective`. Use `set P := pullback (Xw.ι ≫ s) (spMap V.subtype)`. Establish `hI` using `(IrreducibleSpace.isIrreducible_univ P).image (⇑(pullback.fst (Xw.ι ≫ s) (spMap V.subtype) ≫ Xw.ι)) (Scheme.Hom.continuous _).continuousOn`. Rewrite `hI` using `[Set.image_univ]`.

Use `hI using 1` and compare the differences between its conclusion and the goal. Establish `hdvr` using `(GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hpr.out.ne_zero hpV).1`. Rewrite using `[Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst]`. Establish `key : ∀ x : (Xw : Scheme), (Xw.ι ≫ s) x ∈ Set.range (spMap V.subtype)`. Introduce `x`.

Establish `hx : Xw.ι x ∈ X.basicOpen (p : Γ(X, ⊤))`. Apply `hXw` to reduce the goal to its premises. Use `show Xw.ι x ∈ (Xw : Set X)`. Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `⟨x, rfl⟩`.

Establish `h1 : s (Xw.ι x) ∈ (Sp V).basicOpen (p : Γ(Sp V, ⊤))`. Rewrite using `[← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen_top, map_natCast]`. Conclude with `hx`. Rewrite `h1` using `[basicOpen_eq_of_affine', map_natCast]`. Establish `hbot : (s (Xw.ι x)).asIdeal = ⊥`.

Assume the negation of the conclusion as `hne`. Establish `hm` using `Ideal.IsPrime.isMaximal (s (Xw.ι x)).2 hne`. Establish `he` using `IsLocalRing.eq_maximalIdeal hm`. Take `⟨ha, hmem⟩` from `(ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1 hpV`. Apply `h1` to reduce the goal to its premises.

Rewrite using `[he]`. Use `hmem` and compare the differences between its conclusion and the goal. Simplify using the standard rewrite rules. Use `⟨⟨⊥, Ideal.bot_prime⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.comp_apply]`.

Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Rewrite using `[hbot]`. Conclude with `(RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => Subtype.ext ha`. Establish `hu : (⇑(Xw.ι ≫ s) ⁻¹' Set.range ⇑(spMap V.subtype)) = Set.univ` using `Set.eq_univ_of_forall key`. Rewrite using `[hu, Set.image_univ, Scheme.Opens.range_ι]`.
-/
theorem GlobalTheory.FlatModel.isIrreducible_of_geomIrr_of_le_basicOpen : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) (p : ℕ) [Fact p.Prime],
    (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens),
    Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → GeomIrr s Xw → IsIrreducible (Xw : Set X) := by
  intro F _ _ V p hpr hpV X s Xw hXw hg
  have hirr := hg F V.subtype Subtype.val_injective
  set P := pullback (Xw.ι ≫ s) (spMap V.subtype)
  have hI := (IrreducibleSpace.isIrreducible_univ P).image (⇑(pullback.fst (Xw.ι ≫ s) (spMap V.subtype) ≫ Xw.ι))
    (Scheme.Hom.continuous _).continuousOn
  rw [Set.image_univ] at hI
  convert hI using 1
  have hdvr := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField V hpr.out.ne_zero hpV).1
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_fst]
  have key : ∀ x : (Xw : Scheme), (Xw.ι ≫ s) x ∈ Set.range (spMap V.subtype) := by
    intro x
    have hx : Xw.ι x ∈ X.basicOpen (p : Γ(X, ⊤)) := by
      apply hXw
      show Xw.ι x ∈ (Xw : Set X)
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    have h1 : s (Xw.ι x) ∈ (Sp V).basicOpen (p : Γ(Sp V, ⊤)) := by
      rw [← Scheme.Hom.mem_preimage, Scheme.preimage_basicOpen_top, map_natCast]
      exact hx
    rw [basicOpen_eq_of_affine', map_natCast] at h1
    have hbot : (s (Xw.ι x)).asIdeal = ⊥ := by
      by_contra hne
      have hm := Ideal.IsPrime.isMaximal (s (Xw.ι x)).2 hne
      have he := IsLocalRing.eq_maximalIdeal hm
      obtain ⟨ha, hmem⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := V)).1 hpV
      apply h1
      rw [he]
      convert hmem
      simp
    refine ⟨⟨⊥, Ideal.bot_prime⟩, ?_⟩
    rw [Scheme.Hom.comp_apply]
    refine PrimeSpectrum.ext ?_
    rw [hbot]
    exact (RingHom.ker_eq_bot_iff_eq_zero _).2 fun a ha => Subtype.ext ha
  have hu : (⇑(Xw.ι ≫ s) ⁻¹' Set.range ⇑(spMap V.subtype)) = Set.univ := Set.eq_univ_of_forall key
  rw [hu, Set.image_univ, Scheme.Opens.range_ι]
