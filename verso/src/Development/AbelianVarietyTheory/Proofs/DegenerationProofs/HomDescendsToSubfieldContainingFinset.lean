import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
/- English proof (translation)
Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show Surjective (Spec.map (CommRingCat.ofHom σ))`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Take `⟨y⟩` from `(inferInstance : Nonempty (Spec (CommRingCat.of K)))`.

Conclude with `⟨y, Subsingleton.elim _ _⟩`. Use `show Flat (Spec.map (CommRingCat.ofHom σ))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Use `letI := σ.toAlgebra`. Use `show Module.Flat k K`.

Use `infer_instance`. Use `show QuasiCompact (Spec.map (CommRingCat.ofHom σ)) infer_instance`.
-/
private theorem surjective_flat_quasiCompact_spMap {k K : Type} [Field k] [Field K] (σ : k →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show Surjective (Spec.map (CommRingCat.ofHom σ))
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    exact ⟨y, Subsingleton.elim _ _⟩
  · show Flat (Spec.map (CommRingCat.ofHom σ))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := σ.toAlgebra
    show Module.Flat k K
    infer_instance
  · show QuasiCompact (Spec.map (CommRingCat.ofHom σ))
    infer_instance

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in

/- English proof (translation)
Introduce `k K _ _ σ X Y X₀ Y₀ φ ψ hX hY hqc hqs hft f`. Use `letI : Algebra k K := σ.toAlgebra`. Establish `hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ)` using `surjective_flat_quasiCompact_spMap σ`. Use `haveI := _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc`. Use `haveI := _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc`.

Use `haveI : QuasiCompact X₀.hom := MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqc`. Use `haveI : QuasiSeparated X₀.hom := MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqs`. Use `haveI : LocallyOfFiniteType Y₀.hom := MorphismProperty.of_isPullback_of_descendsAlong hY.flip hσ hft`. Use `haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by show IsLocallyNoetherian (Spec (CommRingCat.of k)); infer_instance`. Use `haveI : LocallyOfFinitePresentation Y₀.hom := LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance`.

Establish `hX' : IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K))` using `hX`. Establish `hΦ : (hX'.isoPullback.inv ≫ f.left ≫ ψ) ≫ Y₀.hom = pullback.fst X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) ≫ X₀.hom`. Simplify using `only [Category.assoc, hY.w, Over.w_assoc]`. Rewrite using `[hX'.isoPullback_inv_snd_assoc]`. Conclude with `pullback.condition.symm`.

Take `⟨R, Ψ, hRfg, hΨ, hRΨ⟩` from `_root_.GlobalTheory.Spread.exists_fg_comp_eq X₀.hom Y₀.hom (hX'.isoPullback.inv ≫ f.left ≫ ψ) hΦ`. Take `⟨s, hs⟩` from `hRfg`. Use `⟨s, ?_⟩` and prove the remaining obligations. Introduce `k₁ _ α β hβα hsβ X₁ Y₁ φ₁ χ ψ₁ ω hX₁ hY₁ hφ₁ hψ₁ hφ₁s hψ₁s`. Use `letI : Algebra k k₁ := α.toAlgebra`.

Establish `hβα' : ∀ r : k, β (α r) = σ r` using `fun r => by rw [← hβα]; rfl`. Set `β' : k₁ →ₐ[k] K` to `{ β with commutes' := fun r => hβα' r }`. Establish `hβinj : Function.Injective β'` using `β.injective`. Establish `hle : R ≤ β'.range`. Rewrite using `[← hs, Algebra.adjoin_le_iff]`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `hsβ hx`. Conclude with `⟨y, rfl⟩`. Set `g : R →ₐ[k] k₁` to `(AlgEquiv.ofInjective β' hβinj).symm.toAlgHom.comp (Subalgebra.inclusion hle)`. Establish `hg : ∀ x : R, β' (g x) = R.val x` using `fun x => congrArg Subtype.val ((AlgEquiv.ofInjective β' hβinj).apply_symm_apply (Subalgebra.inclusion hle x))`.

Establish `hX₁' : IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁))` using `hX₁`. Establish `hY₁' : IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁))` using `hY₁`. Establish `hm : (hX₁'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom g ≫ Ψ) ≫ Y₀.hom = X₁.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)`. Simplify using `only [Category.assoc, hΨ, _root_.GlobalTheory.Spread.bcMap_fst_assoc, hX₁'.isoPullback_hom_fst_assoc]`. Conclude with `hX₁'.w`.

Establish `key : φ₁ ≫ hX₁'.isoPullback.hom = hX'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom β'`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hX₁'.isoPullback_hom_fst, hφ₁, Category.assoc, _root_.GlobalTheory.Spread.bcMap_fst, hX'.isoPullback_hom_fst]`. Rewrite using `[Category.assoc, hX₁'.isoPullback_hom_snd, hφ₁s, Category.assoc, _root_.GlobalTheory.Spread.bcMap_snd, hX'.isoPullback_hom_snd_assoc]`. Use `⟨Over.homMk (hY₁'.lift _ X₁.hom hm) (hY₁'.lift_snd _ _ _), ?_⟩` and prove the remaining obligations.

Use `show φ₁ ≫ hY₁'.lift _ X₁.hom hm = f.left ≫ ψ₁`. Apply `hY₁'.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hY₁'.lift_fst, Category.assoc, hψ₁, reassoc_of% key, _root_.GlobalTheory.Spread.bcMap_comp_of_eq_assoc X₀.hom g β' R.val hg, hRΨ, Iso.hom_inv_id_assoc]`. Rewrite using `[Category.assoc, hY₁'.lift_snd, hφ₁s, Category.assoc, hψ₁s, Over.w_assoc]`.
-/
theorem _root_.GlobalTheory.hom_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (X₀ Y₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → IsPullback ψ Y.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  intro k K _ _ σ X Y X₀ Y₀ φ ψ hX hY hqc hqs hft f
  letI : Algebra k K := σ.toAlgebra
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) :=
    surjective_flat_quasiCompact_spMap σ
  haveI := _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc
  haveI := _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc
  haveI : QuasiCompact X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqc
  haveI : QuasiSeparated X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqs
  haveI : LocallyOfFiniteType Y₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hY.flip hσ hft
  haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k)); infer_instance
  haveI : LocallyOfFinitePresentation Y₀.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hX' : IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) := hX
  have hΦ : (hX'.isoPullback.inv ≫ f.left ≫ ψ) ≫ Y₀.hom =
      pullback.fst X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) ≫ X₀.hom := by
    simp only [Category.assoc, hY.w, Over.w_assoc]
    rw [hX'.isoPullback_inv_snd_assoc]
    exact pullback.condition.symm
  obtain ⟨R, Ψ, hRfg, hΨ, hRΨ⟩ :=
    _root_.GlobalTheory.Spread.exists_fg_comp_eq X₀.hom Y₀.hom (hX'.isoPullback.inv ≫ f.left ≫ ψ) hΦ
  obtain ⟨s, hs⟩ := hRfg
  refine ⟨s, ?_⟩
  intro k₁ _ α β hβα hsβ X₁ Y₁ φ₁ χ ψ₁ ω hX₁ hY₁ hφ₁ hψ₁ hφ₁s hψ₁s
  letI : Algebra k k₁ := α.toAlgebra
  have hβα' : ∀ r : k, β (α r) = σ r := fun r => by rw [← hβα]; rfl
  let β' : k₁ →ₐ[k] K := { β with commutes' := fun r => hβα' r }
  have hβinj : Function.Injective β' := β.injective
  have hle : R ≤ β'.range := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hsβ hx
    exact ⟨y, rfl⟩
  let g : R →ₐ[k] k₁ :=
    (AlgEquiv.ofInjective β' hβinj).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have hg : ∀ x : R, β' (g x) = R.val x := fun x =>
    congrArg Subtype.val ((AlgEquiv.ofInjective β' hβinj).apply_symm_apply (Subalgebra.inclusion hle x))
  have hX₁' : IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hX₁
  have hY₁' : IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hY₁
  have hm : (hX₁'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom g ≫ Ψ) ≫ Y₀.hom =
      X₁.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁) := by
    simp only [Category.assoc, hΨ, _root_.GlobalTheory.Spread.bcMap_fst_assoc,
      hX₁'.isoPullback_hom_fst_assoc]
    exact hX₁'.w
  have key : φ₁ ≫ hX₁'.isoPullback.hom =
      hX'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom β' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hX₁'.isoPullback_hom_fst, hφ₁, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_fst, hX'.isoPullback_hom_fst]
    · rw [Category.assoc, hX₁'.isoPullback_hom_snd, hφ₁s, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_snd, hX'.isoPullback_hom_snd_assoc]
  refine ⟨Over.homMk (hY₁'.lift _ X₁.hom hm) (hY₁'.lift_snd _ _ _), ?_⟩
  show φ₁ ≫ hY₁'.lift _ X₁.hom hm = f.left ≫ ψ₁
  apply hY₁'.hom_ext
  · rw [Category.assoc, hY₁'.lift_fst, Category.assoc, hψ₁, reassoc_of% key,
      _root_.GlobalTheory.Spread.bcMap_comp_of_eq_assoc X₀.hom g β' R.val hg, hRΨ,
      Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hY₁'.lift_snd, hφ₁s, Category.assoc, hψ₁s, Over.w_assoc]

end GlobalTheory
