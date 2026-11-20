import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hR Z π _ k hk`. Take `⟨⟨hN, -, -, hC⟩, -⟩` from `hR`. Use `haveI := hN`. Use `haveI := hC`. Use `haveI : IsAffine Z := isAffine_of_isAffineHom π`.

Set `i : Spec Γ(Z, ⊤) ≅ Z` to `Z.isoSpec.symm`. Take `⟨θ, hθ⟩` from `Spec.map_surjective (i.hom ≫ π)`. Establish `h₁ : θ.hom.Finite`. Rewrite using `[← IsFinite.SpecMap_iff, hθ]`. Use `infer_instance`.

Take `⟨ψ, hψ⟩` from `Spec.map_surjective (k ≫ i.inv)`. Establish `hc : θ ≫ ψ = CommRingCat.ofHom (algebraMap R (Kb R))`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hψ, hθ, Category.assoc, i.inv_hom_id_assoc, hk]`. Simplify using `only [TF, jFK, jK, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Rewrite using `[← IsScalarTower.algebraMap_eq]`. Set `_ : Algebra R Γ(Z, ⊤)` to `θ.hom.toAlgebra`. Establish `: Module.Finite R Γ(Z, ⊤)` using `h₁`. Set `φ : Γ(Z, ⊤) →ₐ[R] Kb R` to `⟨ψ.hom, fun r => congr(($hc).hom r)⟩`. Set `S : Subalgebra R (Kb R)` to `φ.range`.

Establish `hfin : Module.Finite R S` using `Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective`. Establish `hloc : IsLocalRing S` using `ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S`. Use `⟨S, hfin, hloc, spMap (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ i.hom, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hθ, ← Spec.map_comp]`. Use `congr 1`.

Use extensionality with `r`. Conclude with `congrArg Subtype.val (φ.rangeRestrict.commutes r)`. Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Establish `: CommRingCat.ofHom (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ CommRingCat.ofHom (S.val : S →+* Kb R) = ψ`. Use extensionality with `b`.

Both sides reduce to the same expression. Rewrite using `[this, hψ, Category.assoc, i.inv_hom_id, Category.comp_id]`.
-/
theorem finpt_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (Z : Scheme.{0}) (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z), k ≫ π = (TF (R := R) (Kb R)).hom → ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧ ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k := by
  intro R _ _ _ hR Z π _ k hk
  obtain ⟨⟨hN, -, -, hC⟩, -⟩ := hR
  haveI := hN
  haveI := hC
  haveI : IsAffine Z := isAffine_of_isAffineHom π
  let i : Spec Γ(Z, ⊤) ≅ Z := Z.isoSpec.symm
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (i.hom ≫ π)
  have h₁ : θ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hθ]
    infer_instance
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (k ≫ i.inv)
  have hc : θ ≫ ψ = CommRingCat.ofHom (algebraMap R (Kb R)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hθ, Category.assoc, i.inv_hom_id_assoc, hk]
    simp only [TF, jFK, jK, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← IsScalarTower.algebraMap_eq]
  let _ : Algebra R Γ(Z, ⊤) := θ.hom.toAlgebra
  have : Module.Finite R Γ(Z, ⊤) := h₁
  let φ : Γ(Z, ⊤) →ₐ[R] Kb R := ⟨ψ.hom, fun r => congr(($hc).hom r)⟩
  let S : Subalgebra R (Kb R) := φ.range
  have hfin : Module.Finite R S :=
    Module.Finite.of_surjective φ.rangeRestrict.toLinearMap φ.rangeRestrict_surjective
  have hloc : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  refine ⟨S, hfin, hloc, spMap (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ i.hom, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    congr 1
    ext r
    exact congrArg Subtype.val (φ.rangeRestrict.commutes r)
  · rw [← Category.assoc, ← Spec.map_comp]
    have : CommRingCat.ofHom (φ.rangeRestrict : Γ(Z, ⊤) →+* S) ≫ CommRingCat.ofHom (S.val : S →+* Kb R) = ψ := by
      ext b; rfl
    rw [this, hψ, Category.assoc, i.inv_hom_id, Category.comp_id]

end GlobalTheory.Mum
