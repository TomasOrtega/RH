import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSectionOfTransversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeOfIsNoetherianRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.QuotLift

/- English proof (translation)
Introduce `R₁ R _ _ _ _ _ hc π hπ U hU x₀ hx`. Take `⟨y, hy⟩ : ∃ y, x₀ (closedPoint R) = y` from `⟨_, rfl⟩`. Take `⟨α, hs, hα⟩` from `GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R₁) U.hom y`. Take `⟨χ₀, hχ₀⟩` from `GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of R) x₀ (y := y) hy`. Use `letI := α.hom.toAlgebra`.

Use `haveI : Algebra.FormallySmooth R₁ (U.left.presheaf.stalk y) := hs`. Establish `hle : RingHom.ker π ≤ maximalIdeal R₁`. Apply `le_maximalIdeal` to reduce the goal to its premises. Introduce `h`. Establish `h1 : (1 : R₁) ∈ RingHom.ker π` using `h ▸ Submodule.mem_top`.

Rewrite `h1` using `[RingHom.mem_ker, map_one]`. Conclude with `one_ne_zero h1`. Use `haveI : IsAdicComplete (RingHom.ker π) R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ _ _ hle hc`. Establish `e₁ : α ≫ χ₀ = CommRingCat.ofHom π`. Apply `Spec.map_injective` to reduce the goal to its premises.

Rewrite using `[Spec.map_comp, hα, reassoc_of% hχ₀, hx]`. Set `E` to `RingHom.quotientKerEquivOfSurjective hπ`. Set `f : U.left.presheaf.stalk y →ₐ[R₁] R₁ ⧸ RingHom.ker π` to `{ (E.symm : R →+* R₁ ⧸ RingHom.ker π).comp χ₀.hom with commutes' := fun r => by`. Apply `E.injective` to reduce the goal to its premises. Establish `h2 : χ₀.hom (α.hom r) = π r` using `congrArg (fun g => g.hom r) e₁`.

Express the relevant statement in the definitionally equal form `E (E.symm (χ₀.hom (α.hom r))) = E (Ideal.Quotient.mk _ r)`. Rewrite using `[RingEquiv.apply_symm_apply, h2]`. Use `rfl }`. Take `⟨g, hg⟩` from `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := RingHom.ker π) f`. Establish `hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom π = χ₀`.

Use extensionality with `a`. Establish `h3` using `congr($hg a)`. Express the relevant statement in the definitionally equal form `π (g a) = χ₀.hom a`. Establish `h4 : E (Ideal.Quotient.mk _ (g a)) = E (f a)` using `congrArg E h3`. Rewrite `h4` using `[show f a = E.symm (χ₀.hom a) from rfl, RingEquiv.apply_symm_apply]`.

Conclude with `h4`. Use `⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hα, ← Spec.map_comp]`. Use `(congrArg Spec.map ?_).trans (Spec.map_id _)` and prove the remaining obligations. Use extensionality with `r`.

Conclude with `g.commutes r`. Rewrite using `[spMap, ← Spec.map_comp_assoc, hg', hχ₀]`.
-/
theorem exists_section_lift : ∀ (R₁ R : Type) [CommRing R₁] [IsLocalRing R₁] [IsNoetherianRing R₁] [CommRing R]
    [IsLocalRing R], IsAdicComplete (maximalIdeal R₁) R₁ → ∀ π : R₁ →+* R, Function.Surjective π →
    ∀ (U : Over (Sp R₁)), Smooth U.hom → ∀ x₀ : Sp R ⟶ U.left, x₀ ≫ U.hom = spMap π →
    ∃ x : Sp R₁ ⟶ U.left, x ≫ U.hom = 𝟙 _ ∧ spMap π ≫ x = x₀ := by
  intro R₁ R _ _ _ _ _ hc π hπ U hU x₀ hx
  obtain ⟨y, hy⟩ : ∃ y, x₀ (closedPoint R) = y := ⟨_, rfl⟩
  obtain ⟨α, hs, hα⟩ := GlobalTheory.HenselZero.exists_formallySmooth_stalk (O := CommRingCat.of R₁) U.hom y
  obtain ⟨χ₀, hχ₀⟩ := GlobalTheory.HenselZero.exists_factor_stalk (T := CommRingCat.of R) x₀ (y := y) hy
  letI := α.hom.toAlgebra
  haveI : Algebra.FormallySmooth R₁ (U.left.presheaf.stalk y) := hs
  have hle : RingHom.ker π ≤ maximalIdeal R₁ := by
    apply le_maximalIdeal
    intro h
    have h1 : (1 : R₁) ∈ RingHom.ker π := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  haveI : IsAdicComplete (RingHom.ker π) R₁ := GlobalTheory.T.isAdicComplete_of_le_of_isNoetherianRing' R₁ _ _ hle hc
  have e₁ : α ≫ χ₀ = CommRingCat.ofHom π := by
    apply Spec.map_injective
    rw [Spec.map_comp, hα, reassoc_of% hχ₀, hx]
  let E := RingHom.quotientKerEquivOfSurjective hπ
  let f : U.left.presheaf.stalk y →ₐ[R₁] R₁ ⧸ RingHom.ker π :=
    { (E.symm : R →+* R₁ ⧸ RingHom.ker π).comp χ₀.hom with
      commutes' := fun r => by
        apply E.injective
        have h2 : χ₀.hom (α.hom r) = π r := congrArg (fun g => g.hom r) e₁
        change E (E.symm (χ₀.hom (α.hom r))) = E (Ideal.Quotient.mk _ r)
        rw [RingEquiv.apply_symm_apply, h2]
        rfl }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := RingHom.ker π) f
  have hg' : CommRingCat.ofHom g.toRingHom ≫ CommRingCat.ofHom π = χ₀ := by
    ext a
    have h3 := congr($hg a)
    change π (g a) = χ₀.hom a
    have h4 : E (Ideal.Quotient.mk _ (g a)) = E (f a) := congrArg E h3
    rw [show f a = E.symm (χ₀.hom a) from rfl, RingEquiv.apply_symm_apply] at h4
    exact h4
  refine ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ U.left.fromSpecStalk y, ?_, ?_⟩
  · rw [Category.assoc, ← hα, ← Spec.map_comp]
    refine (congrArg Spec.map ?_).trans (Spec.map_id _)
    ext r
    exact g.commutes r
  · rw [spMap, ← Spec.map_comp_assoc, hg', hχ₀]

end GlobalTheory.QuotLift
