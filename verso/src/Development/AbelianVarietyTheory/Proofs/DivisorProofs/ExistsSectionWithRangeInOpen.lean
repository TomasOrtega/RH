import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionOfTransversal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HenselLift

/- English proof (translation)
Take `⟨y, hy⟩ : ∃ y, x₀ (closedPoint (ResidueField R')) = y` from `⟨_, rfl⟩`. Take `⟨α, hs, hα⟩` from `GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R) U.hom y`. Take `⟨χ₀, hχ₀⟩` from `GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of (ResidueField R')) x₀ (y := y) hy`. Use `letI := α.hom.toAlgebra`. Use `letI := ρ.toAlgebra`.

Use `haveI : Algebra.FormallySmooth R (U.left.presheaf.stalk y) := hs`. Use `haveI := hc`. Establish `e₁ : α ≫ χ₀ = CommRingCat.ofHom ((residue R').comp ρ)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hα, reassoc_of% hχ₀, hx]`.

Set `f : U.left.presheaf.stalk y →ₐ[R] R' ⧸ maximalIdeal R'` to `{ χ₀.hom with commutes' := fun r => congrArg (fun g => g.hom r) e₁ }`. Take `⟨g, hg⟩` from `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal R') f`. Establish `hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom (residue R') = χ₀`. Use extensionality with `a`. Conclude with `congr($hg a)`.

Use `⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hα, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `r`. Conclude with `g.commutes r`.

Establish `hcl : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y) (closedPoint R') = y`. Establish `h1 : Spec.map (CommRingCat.ofHom (residue R')) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y = x₀`. Rewrite using `[← Spec.map_comp_assoc, hg', hχ₀]`. Establish `h2` using `congrArg (fun h => h (closedPoint (ResidueField R'))) h1`. Simplify using `only [Scheme.Hom.comp_apply] at h2`.

Rewrite `h2` using `[hy]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Conclude with `congrArg (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y) (comap_closedPoint (residue R')).symm`. Introduce and unpack `_ ⟨p, rfl⟩`. Use `Specializes.mem_open ((specializes_closedPoint p).map (Scheme.Hom.continuous _)) O.isOpen ?_` and prove the remaining obligations.

Rewrite using `[hcl]`. Conclude with `hO ⟨_, hy⟩`.
-/
theorem exists_lift_mem_open (R R' : Type) [CommRing R] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R']
    (hc : IsAdicComplete (maximalIdeal R') R') (ρ : R →+* R') (U : Over (Sp R)) (hU : Smooth U.hom)
    (x₀ : Sp (ResidueField R') ⟶ U.left) (hx : x₀ ≫ U.hom = spMap ((residue R').comp ρ))
    (O : U.left.Opens) (hO : Set.range x₀ ⊆ O) :
    ∃ a : Sp R' ⟶ U.left, a ≫ U.hom = spMap ρ ∧ Set.range a ⊆ O := by
  obtain ⟨y, hy⟩ : ∃ y, x₀ (closedPoint (ResidueField R')) = y := ⟨_, rfl⟩
  obtain ⟨α, hs, hα⟩ := GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R) U.hom y
  obtain ⟨χ₀, hχ₀⟩ := GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of (ResidueField R')) x₀ (y := y) hy
  letI := α.hom.toAlgebra
  letI := ρ.toAlgebra
  haveI : Algebra.FormallySmooth R (U.left.presheaf.stalk y) := hs
  haveI := hc
  have e₁ : α ≫ χ₀ = CommRingCat.ofHom ((residue R').comp ρ) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ₀, hx]
  let f : U.left.presheaf.stalk y →ₐ[R] R' ⧸ maximalIdeal R' :=
    { χ₀.hom with commutes' := fun r => congrArg (fun g => g.hom r) e₁ }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := maximalIdeal R') f
  have hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom (residue R') = χ₀ := by
    ext a
    exact congr($hg a)
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    congr 1
    ext r
    exact g.commutes r
  · have hcl : (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y) (closedPoint R') = y := by
      have h1 : Spec.map (CommRingCat.ofHom (residue R')) ≫ Spec.map (CommRingCat.ofHom g.toRingHom) ≫
          U.left.fromSpecStalk y = x₀ := by
        rw [← Spec.map_comp_assoc, hg', hχ₀]
      have h2 := congrArg (fun h => h (closedPoint (ResidueField R'))) h1
      simp only [Scheme.Hom.comp_apply] at h2
      rw [hy] at h2
      refine Eq.trans ?_ h2
      exact congrArg (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y)
        (comap_closedPoint (residue R')).symm
    rintro _ ⟨p, rfl⟩
    refine Specializes.mem_open ((specializes_closedPoint p).map (Scheme.Hom.continuous _)) O.isOpen ?_
    rw [hcl]
    exact hO ⟨_, hy⟩

end GlobalTheory.HenselLift
