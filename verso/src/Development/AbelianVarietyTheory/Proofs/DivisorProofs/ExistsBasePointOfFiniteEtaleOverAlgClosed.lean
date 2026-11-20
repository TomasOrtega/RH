import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableExtensionMultiplesOfSemistable
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePointsOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSubgroupEqRangeOfLists
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.OActDescendOfGenerators

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.FinEtPoints

/- English proof (translation)
Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap_field (k L : Type) [Field k] [Field L] (f : k →+* L) : Epi (spMap f) := by
  exact Flat.epi_of_flat_of_surjective _

/- English proof (translation)
Introduce `hf he x hx`. Set `Ω` to `AlgebraicClosure K`. Set `i : K →+* Ω` to `algebraMap K Ω`. Set `j : k₀ →+* K` to `algebraMap k₀ K`. Set `t : Sp Ω ⟶ Sp k₀` to `spMap (i.comp j)`.

Establish `ht : spMap i ≫ spMap j = t`. Simplify using `only [t, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Establish `hti : Epi t` using `epi_spMap_field _ _ _`. Establish `hii : Epi (spMap i)` using `epi_spMap_field _ _ _`. Take `⟨zΩ⟩ : Nonempty (Sp Ω)` from `inferInstance`.

Take `⟨z₀⟩ : Nonempty (Sp k₀)` from `inferInstance`. Take `⟨hfin₁, hc₁⟩` from `GlobalTheory.FinEt.card_points_eq_finrank p t zΩ`. Take `⟨hfin₀, hc₀⟩` from `GlobalTheory.FinEt.card_points_eq_finrank p (𝟙 (Sp k₀)) z₀`. Set `F : {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} → {y : Sp Ω ⟶ X // y ≫ p = t}` to `fun y ↦ ⟨t ≫ y.1, by rw [Category.assoc, y.2, Category.comp_id]⟩`. Establish `hFi : Function.Injective F`.

Introduce `a b hab`. Conclude with `Subtype.ext ((cancel_epi t).mp congr(($hab).1))`. Establish `hcard : Nat.card {y : Sp Ω ⟶ X // y ≫ p = t} ≤ Nat.card {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _}`. Rewrite using `[hc₁, hc₀, Subsingleton.elim (t zΩ) ((𝟙 (Sp k₀) : Sp k₀ ⟶ Sp k₀) z₀)]`. Establish `hFb : Function.Bijective F` using `hFi.bijective_of_nat_card_le hcard`.

Take `⟨⟨x₀, hx₀⟩, hF⟩` from `hFb.2 ⟨spMap i ≫ x, by rw [Category.assoc, hx, ht]⟩`. Use `⟨x₀, hx₀, ?_⟩` and prove the remaining obligations. Establish `h1 : spMap i ≫ (spMap j ≫ x₀) = spMap i ≫ x`. Rewrite using `[← Category.assoc, ht]`. Conclude with `congr(($hF).1)`.

Conclude with `(cancel_epi (spMap i)).mp h1`.
-/
theorem exists_point_of_finite_etale (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K]
    [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀) : IsFinite p → Etale p →
    ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) →
      ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := by
  intro hf he x hx
  let Ω := AlgebraicClosure K
  let i : K →+* Ω := algebraMap K Ω
  let j : k₀ →+* K := algebraMap k₀ K
  let t : Sp Ω ⟶ Sp k₀ := spMap (i.comp j)
  have ht : spMap i ≫ spMap j = t := by
    simp only [t, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hti : Epi t := epi_spMap_field _ _ _
  have hii : Epi (spMap i) := epi_spMap_field _ _ _
  obtain ⟨zΩ⟩ : Nonempty (Sp Ω) := inferInstance
  obtain ⟨z₀⟩ : Nonempty (Sp k₀) := inferInstance
  obtain ⟨hfin₁, hc₁⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t zΩ
  obtain ⟨hfin₀, hc₀⟩ := GlobalTheory.FinEt.card_points_eq_finrank p (𝟙 (Sp k₀)) z₀
  let F : {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} → {y : Sp Ω ⟶ X // y ≫ p = t} :=
    fun y ↦ ⟨t ≫ y.1, by rw [Category.assoc, y.2, Category.comp_id]⟩
  have hFi : Function.Injective F := by
    intro a b hab
    exact Subtype.ext ((cancel_epi t).mp congr(($hab).1))
  have hcard : Nat.card {y : Sp Ω ⟶ X // y ≫ p = t} ≤ Nat.card {y : Sp k₀ ⟶ X // y ≫ p = 𝟙 _} := by
    rw [hc₁, hc₀, Subsingleton.elim (t zΩ) ((𝟙 (Sp k₀) : Sp k₀ ⟶ Sp k₀) z₀)]
  have hFb : Function.Bijective F := hFi.bijective_of_nat_card_le hcard
  obtain ⟨⟨x₀, hx₀⟩, hF⟩ := hFb.2 ⟨spMap i ≫ x, by rw [Category.assoc, hx, ht]⟩
  refine ⟨x₀, hx₀, ?_⟩
  have h1 : spMap i ≫ (spMap j ≫ x₀) = spMap i ≫ x := by
    rw [← Category.assoc, ht]
    exact congr(($hF).1)
  exact (cancel_epi (spMap i)).mp h1

end GlobalTheory.FinEtPoints
