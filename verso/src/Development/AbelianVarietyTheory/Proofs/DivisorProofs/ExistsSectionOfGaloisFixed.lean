import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GaloisFixedSectionExtension

/- English proof (translation)
Use `haveI : IsAffine X := isAffine_of_isAffineHom p`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (g ≫ X.isoSpec.hom)`. Take `⟨π, hπ⟩` from `Spec.map_surjective (X.isoSpec.inv ≫ p)`. Establish `hfin : π.hom.Finite`. Rewrite using `[← IsFinite.SpecMap_iff, hπ]`.

Use `infer_instance`. Establish `hcomp : π ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V))`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hφ, hπ, Category.assoc, Iso.hom_inv_id_assoc, hg]`. Establish `hc : ∀ v : V, φ.hom (π.hom v) = algebraMap V (FractionRing V) v` using `fun v => congrArg (fun f => f.hom v) hcomp`.

Establish `hmem : ∀ a, φ.hom a ∈ (algebraMap V (FractionRing V)).range`. Introduce `a`. Take `⟨q, hq, hqa⟩` from `hfin.to_isIntegral a`. Establish `hint : IsIntegral V (φ.hom a)`. Use `⟨q, hq, ?_⟩` and prove the remaining obligations.

Establish `h1` using `Polynomial.hom_eval₂ q π.hom φ.hom a`. Rewrite `h1` using `[hqa, map_zero]`. Establish `h2 : φ.hom.comp π.hom = algebraMap V (FractionRing V)` using `RingHom.ext hc`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`.

Conclude with `IsIntegrallyClosed.algebraMap_eq_of_integral hint`. Establish `hinj : Function.Injective (algebraMap V (FractionRing V))` using `IsFractionRing.injective V _`. Set `e` to `RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap V (FractionRing V)).rangeRestrict_surjective⟩`. Set `ψ : Γ(X, ⊤) →+* V` to `e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)`. Establish `hψ : ∀ a, algebraMap V (FractionRing V) (ψ a) = φ.hom a` using `fun a => congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict _ hmem a))`.

Establish `hψφ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V (FractionRing V)) = φ`. Use extensionality with `a`. Conclude with `hψ a`. Establish `hπψ : π ≫ CommRingCat.ofHom ψ = 𝟙 _`. Use extensionality with `v`.

Conclude with `hinj ((hψ _).trans (hc v))`. Use `⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hπ, ← Spec.map_comp, hπψ, Spec.map_id]`. Rewrite using `[← Category.assoc, ← Spec.map_comp, hψφ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]`.
-/
theorem extend_section {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] (X : Scheme.{0})
    (p : X ⟶ Spec (CommRingCat.of V)) [IsFinite p] (g : Spec (CommRingCat.of (FractionRing V)) ⟶ X)
    (hg : g ≫ p = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ p = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) ≫ s = g := by
  haveI : IsAffine X := isAffine_of_isAffineHom p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ X.isoSpec.hom)
  obtain ⟨π, hπ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ p)
  have hfin : π.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hπ]
    infer_instance
  have hcomp : π ≫ φ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hπ, Category.assoc, Iso.hom_inv_id_assoc, hg]
  have hc : ∀ v : V, φ.hom (π.hom v) = algebraMap V (FractionRing V) v := fun v =>
    congrArg (fun f => f.hom v) hcomp
  have hmem : ∀ a, φ.hom a ∈ (algebraMap V (FractionRing V)).range := by
    intro a
    obtain ⟨q, hq, hqa⟩ := hfin.to_isIntegral a
    have hint : IsIntegral V (φ.hom a) := by
      refine ⟨q, hq, ?_⟩
      have h1 := Polynomial.hom_eval₂ q π.hom φ.hom a
      rw [hqa, map_zero] at h1
      have h2 : φ.hom.comp π.hom = algebraMap V (FractionRing V) := RingHom.ext hc
      rw [h2] at h1
      exact h1.symm
    exact IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap V (FractionRing V)).rangeRestrict_surjective⟩
  let ψ : Γ(X, ⊤) →+* V := e.symm.toRingHom.comp (φ.hom.codRestrict _ hmem)
  have hψ : ∀ a, algebraMap V (FractionRing V) (ψ a) = φ.hom a := fun a =>
    congrArg Subtype.val (e.apply_symm_apply (φ.hom.codRestrict _ hmem a))
  have hψφ : CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap V (FractionRing V)) = φ := by
    ext a
    exact hψ a
  have hπψ : π ≫ CommRingCat.ofHom ψ = 𝟙 _ := by
    ext v
    exact hinj ((hψ _).trans (hc v))
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ X.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hπ, ← Spec.map_comp, hπψ, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hψφ, hφ, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/- English proof (translation)
Introduce `V _ _ _ hV N hN nb hfix`. Use `haveI := hV`. Use `haveI := hN`. Use `haveI : IsAffine N.left := isAffine_of_isAffineHom N.hom`. Take `⟨g, hg⟩` from `GlobalTheory.TorsDescent.descend_point (K := FractionRing V) N.left nb.left hfix`.

Establish `hg' : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ g = nb.left` using `hg`. Establish `hw : nb.left ≫ N.hom = Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))` using `Over.w nb`. Establish `hgp : g ≫ N.hom = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))`. Take `⟨χ, hχ⟩` from `Spec.map_surjective (g ≫ N.hom)`. Rewrite using `[← hχ]`.

Use `congr 1`. Establish `h1 : χ ≫ CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) = CommRingCat.ofHom (algebraMap V (FractionRing V)) ≫ CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, Spec.map_comp, hχ, ← hw, ← hg', Category.assoc]`. Use extensionality with `v`.

Conclude with `(algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective (congrArg (fun f => f.hom v) h1)`. Take `⟨s, hs, hsg⟩` from `extend_section N.left N.hom g hgp`. Use `⟨Over.homMk s hs, ?_⟩` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show nb.left = (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) ≫ s`.

Rewrite using `[Category.assoc, hsg, hg']`.
-/
theorem exists_section_of_galoisFixed : ∀ (V : Type) [inst : CommRing V] [inst_1 : IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)), AlgebraicGeometry.IsFinite (CategoryTheory.Over.hom N) → ∀ (nb : ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ (σ : Gal(AlgebraicClosure (FractionRing V)/FractionRing V)), CategoryTheory.CategoryStruct.comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (AlgHom.toRingHom (↑σ : AlgebraicClosure (FractionRing V) →ₐ[FractionRing V] AlgebraicClosure (FractionRing V)))) (CategoryTheory.Over.Hom.left nb) = CategoryTheory.Over.Hom.left nb) → ∃ (s : CategoryTheory.MonoidalCategoryStruct.tensorUnit (CategoryTheory.Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V)) ⟶ N), nb = CategoryTheory.CategoryStruct.comp (CategoryTheory.SemiCartesianMonoidalCategory.toUnit (ReciprocityTheory.ChartRestriction.G.Out.TF (AlgebraicClosure (FractionRing V)))) s := by
  intro V _ _ _ hV N hN nb hfix
  haveI := hV
  haveI := hN
  haveI : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨g, hg⟩ := GlobalTheory.TorsDescent.descend_point (K := FractionRing V) N.left nb.left hfix
  have hg' : Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫ g =
      nb.left := hg
  have hw : nb.left ≫ N.hom =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := Over.w nb
  have hgp : g ≫ N.hom = Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V))) := by
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (g ≫ N.hom)
    rw [← hχ]
    congr 1
    have h1 : χ ≫ CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) =
        CommRingCat.ofHom (algebraMap V (FractionRing V)) ≫
          CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, hχ, ← hw, ← hg', Category.assoc]
    ext v
    exact (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective
      (congrArg (fun f => f.hom v) h1)
  obtain ⟨s, hs, hsg⟩ := extend_section N.left N.hom g hgp
  refine ⟨Over.homMk s hs, ?_⟩
  apply Over.OverMorphism.ext
  show nb.left = (Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))) ≫ s
  rw [Category.assoc, hsg, hg']

end GlobalTheory.GaloisFixedSectionExtension
