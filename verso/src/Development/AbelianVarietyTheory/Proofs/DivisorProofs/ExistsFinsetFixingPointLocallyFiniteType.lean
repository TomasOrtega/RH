import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfValues
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtFin

/- English proof (translation)
Introduce `K Ω _ _ _ A hA x`. Use `haveI := hA`. Take `⟨⟨p, φ⟩, hx⟩` from `(Scheme.SpecToEquivOfField Ω A.left).symm.surjective x.left`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at hx`. Establish `hxs : x.left ≫ A.hom = spMap (algebraMap K Ω)` using `Over.w x`.

Take `⟨ψ, hψ⟩` from `Spec.map_surjective (A.left.fromSpecResidueField p ≫ A.hom)`. Establish `hess` using `GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType A.hom p ψ hψ`. Rewrite `hxs` using `[← hx, Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj]`. Use `letI : Algebra K (A.left.residueField p) := ψ.hom.toAlgebra`. Use `haveI : Algebra.EssFiniteType K (A.left.residueField p) := hess`.

Set `fa : A.left.residueField p →ₐ[K] Ω` to `{ φ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hxs }`. Use `⟨(Algebra.EssFiniteType.finset K (A.left.residueField p)).image fa, fun σ hσ => ?_⟩` and prove the remaining obligations. Establish `e : (σ : Ω →ₐ[K] Ω).comp fa = fa` using `Algebra.EssFiniteType.algHom_ext Ω _ _ fun c hc => hσ _ (Finset.mem_image_of_mem _ hc)`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `spMap (σ : Ω →+* Ω) ≫ x.left = x.left`.

Rewrite using `[← hx, ← Category.assoc, ← Spec.map_comp]`. Use `congr 2`. Use extensionality with `c`. Conclude with `congrArg (fun g => g c) e`.
-/
theorem exists_finset_fix : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)),
    LocallyOfFiniteType A.hom → ∀ x : ptOver K Ω ⟶ A, ∃ s : Finset Ω, ∀ σ : Ω ≃ₐ[K] Ω,
      (∀ a ∈ s, σ a = a) → specAut σ ≫ x = x := by
  classical
  intro K Ω _ _ _ A hA x
  haveI := hA
  obtain ⟨⟨p, φ⟩, hx⟩ := (Scheme.SpecToEquivOfField Ω A.left).symm.surjective x.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx
  have hxs : x.left ≫ A.hom = spMap (algebraMap K Ω) := Over.w x
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (A.left.fromSpecResidueField p ≫ A.hom)
  have hess := GlobalTheory.SS.essFiniteType_residueField_of_locallyOfFiniteType A.hom p ψ hψ
  rw [← hx, Category.assoc, ← hψ, ← Spec.map_comp, Spec.map_inj] at hxs
  letI : Algebra K (A.left.residueField p) := ψ.hom.toAlgebra
  haveI : Algebra.EssFiniteType K (A.left.residueField p) := hess
  let fa : A.left.residueField p →ₐ[K] Ω :=
    { φ.hom with commutes' := fun c => congrArg (fun g => g.hom c) hxs }
  refine ⟨(Algebra.EssFiniteType.finset K (A.left.residueField p)).image fa, fun σ hσ => ?_⟩
  have e : (σ : Ω →ₐ[K] Ω).comp fa = fa :=
    Algebra.EssFiniteType.algHom_ext Ω _ _ fun c hc => hσ _ (Finset.mem_image_of_mem _ hc)
  apply Over.OverMorphism.ext
  change spMap (σ : Ω →+* Ω) ≫ x.left = x.left
  rw [← hx, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext c
  exact congrArg (fun g => g c) e

end GlobalTheory.PtFin
