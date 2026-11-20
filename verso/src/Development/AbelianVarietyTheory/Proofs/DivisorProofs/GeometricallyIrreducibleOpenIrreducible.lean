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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
