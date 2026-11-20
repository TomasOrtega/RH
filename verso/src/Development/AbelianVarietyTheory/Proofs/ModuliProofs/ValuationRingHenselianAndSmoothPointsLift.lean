import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `Polynomial.Splits.of_splits_map_of_injective (IsFractionRing.injective O K) (IsAlgClosed.splits _) fun a ha => ?_` and prove the remaining obligations. Establish `hroot : Polynomial.eval₂ (algebraMap O K) a f = 0`. Rewrite `ha` using `[Polynomial.mem_roots (hf.map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map]`. Conclude with `ha`. Establish `hint : IsIntegral O a` using `⟨f, hf, hroot⟩`.

Take `⟨b, hb⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Conclude with `⟨b, hb⟩`.
-/
theorem splits_of_monic_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K]
    {f : Polynomial O} (hf : f.Monic) : f.Splits := by
  refine Polynomial.Splits.of_splits_map_of_injective (IsFractionRing.injective O K)
    (IsAlgClosed.splits _) fun a ha => ?_
  have hroot : Polynomial.eval₂ (algebraMap O K) a f = 0 := by
    rw [Polynomial.mem_roots (hf.map _).ne_zero, Polynomial.IsRoot, Polynomial.eval_map] at ha
    exact ha
  have hint : IsIntegral O a := ⟨f, hf, hroot⟩
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨b, hb⟩

/- English proof (translation)
Establish `hs` using `splits_of_monic_of_valuationRing_of_isAlgClosed O K hf`. Rewrite `h₁` using `[hs.eval_eq_prod_roots_of_monic hf a₀, (IsLocalRing.maximalIdeal.isMaximal O).isPrime.multiset_prod_mem_iff_exists_mem]`. Take `⟨c, hc, hcm⟩` from `h₁`. Take `⟨r, hr, rfl⟩` from `Multiset.mem_map.mp hc`. Use `⟨r, (Polynomial.mem_roots hf.ne_zero).mp hr, ?_⟩` and prove the remaining obligations.

Rewrite using `[← neg_sub]`. Conclude with `neg_mem hcm`.
-/
theorem henselianLocalRing_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    HenselianLocalRing O where
  is_henselian f hf a₀ h₁ _ := by
    have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hf
    rw [hs.eval_eq_prod_roots_of_monic hf a₀,
      (IsLocalRing.maximalIdeal.isMaximal O).isPrime.multiset_prod_mem_iff_exists_mem] at h₁
    obtain ⟨c, hc, hcm⟩ := h₁
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hc
    refine ⟨r, (Polynomial.mem_roots hf.ne_zero).mp hr, ?_⟩
    rw [← neg_sub]
    exact neg_mem hcm

/- English proof (translation)
Use `IsAlgClosed.of_exists_root _ fun p hp hirr => ?_` and prove the remaining obligations. Take `⟨g, hg, hdeg, hgm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic (Polynomial.map_surjective _ IsLocalRing.residue_surjective p) hp`. Establish `hs` using `splits_of_monic_of_valuationRing_of_isAlgClosed O K hgm`. Establish `hd : g.degree ≠ 0`. Rewrite using `[Polynomial.degree_eq_natDegree hgm.ne_zero, hdeg]`.

Conclude with `(Irreducible.natDegree_pos hirr).ne'` after adjusting the coercions. Take `⟨r, hr⟩` from `hs.exists_eval_eq_zero hd`. Conclude with `⟨IsLocalRing.residue O r, by rw [← hg, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]⟩`.
-/
theorem isAlgClosed_residueField_of_valuationRing_of_isAlgClosed (O K : Type*) [CommRing O]
    [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨g, hg, hdeg, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective _ IsLocalRing.residue_surjective p) hp
  have hs := splits_of_monic_of_valuationRing_of_isAlgClosed O K hgm
  have hd : g.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hgm.ne_zero, hdeg]
    exact_mod_cast (Irreducible.natDegree_pos hirr).ne'
  obtain ⟨r, hr⟩ := hs.exists_eval_eq_zero hd
  exact ⟨IsLocalRing.residue O r, by rw [← hg, Polynomial.eval_map, Polynomial.eval₂_at_apply, hr, map_zero]⟩

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ _`. Use `henselianLocalRing_of_valuationRing_of_isAlgClosed O K` as an intermediate fact. Use `⟨inferInstance, isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O K, ?_⟩` and prove the remaining obligations. Introduce `X f hf x hx`. Use `hf` as an intermediate fact.

Take `⟨⟨y, hy⟩, hy'⟩` from `reducePoint_residue_surjective f O (𝟙 _) ⟨x, by simpa using hx⟩`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val hy'`.
-/
theorem valuationRing_henselian_and_lift_of_isAlgClosed :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K], HenselianLocalRing O ∧ IsAlgClosed (IsLocalRing.ResidueField O) ∧ ∀ (X : Scheme.{0}) (f : X ⟶ Sp O), Smooth f → ∀ x : Sp (IsLocalRing.ResidueField O) ⟶ X, x ≫ f = spMap (IsLocalRing.residue O) → ∃ y : Sp O ⟶ X, y ≫ f = 𝟙 _ ∧ spMap (IsLocalRing.residue O) ≫ y = x := by
  intro O K _ _ _ _ _ _ _
  have := henselianLocalRing_of_valuationRing_of_isAlgClosed O K
  refine ⟨inferInstance, isAlgClosed_residueField_of_valuationRing_of_isAlgClosed O K, ?_⟩
  intro X f hf x hx
  have := hf
  obtain ⟨⟨y, hy⟩, hy'⟩ := reducePoint_residue_surjective f O (𝟙 _) ⟨x, by simpa using hx⟩
  refine ⟨y, hy, ?_⟩
  exact congrArg Subtype.val hy'

end GlobalTheory
