import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionPrimitiveLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveOfBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.SmallStepSurj

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Introduce `R _ _ t R' _ σ' hσ' hker ht hm hfield hR' A _ g hA hg k _ σ hσ X₀ s₀ ψ w`. Establish `hkerσ : RingHom.ker σ = IsLocalRing.maximalIdeal R` using `IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective σ hσ)`. Distinguish the cases in `htm : t ∈ IsLocalRing.maximalIdeal R`. Set `R₀` to `R ⧸ IsLocalRing.maximalIdeal R`. Set `σ₀ : R →+* R₀` to `Ideal.Quotient.mk _`.

Establish `hR₀ : IsField R₀` using `(Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (IsLocalRing.maximalIdeal.isMaximal R)`. Establish `hse : SmallExt t σ' σ₀`. Use `⟨hσ', hker, Ideal.Quotient.mk_surjective, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`. Prove the components needed by the constructor for the conclusion.

Conclude with `hm a`. Introduce `hat`. Assume the negation of the conclusion as `hna`. Establish `hu : IsUnit a`. Assume the negation of the conclusion as `hnu`.

Conclude with `hna ((IsLocalRing.mem_maximalIdeal a).2 hnu)`. Conclude with `ht (hu.mul_right_eq_zero.1 hat)`. Establish `hP'` using `IsPullback.of_hasPullback A.hom (spMap σ')`. Establish `hP₀` using `IsPullback.of_hasPullback A.hom (spMap σ₀)`. Take `⟨i', hg', hab', hsm'⟩` from `GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' σ' A _ _ _ hP'`.

Take `⟨i₀, hg₀, hab₀, hsm₀⟩` from `GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R₀ σ₀ A _ _ _ hP₀`. Establish `hstep` using `GlobalTheory.T.small_extension_primitive_lift R R' R₀ t σ' σ₀ g A _ _ _ _ hg' hg₀ hse hA hg (hR' _ g (hab' hA) (hsm' g hg)).2 (hfield R₀ hR₀ _ g (hab₀ hA) (hsm₀ g hg)).2.1`. Establish `hle : RingHom.ker σ' ≤ RingHom.ker σ`. Rewrite using `[hker, Ideal.span_le, Set.singleton_subset_iff, hkerσ]`. Conclude with `htm`.

Set `τ : R' →+* k` to `RingHom.liftOfRightInverse σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩`. Establish `hτ : ∀ r, τ (σ' r) = σ r` using `fun r => RingHom.liftOfRightInverse_comp_apply σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩ r`. Establish `hτs : Function.Surjective τ` using `fun y => by`. Take `⟨x, rfl⟩` from `hσ y`. Conclude with `⟨σ' x, hτ x⟩`.

Establish `hcomp : spMap σ = spMap τ ≫ spMap σ'`. Rewrite using `[← spMap_comp_hom]`. Use `congr 1`. Use extensionality with `r`. Conclude with `(hτ r).symm`.

Set `ψ' : X₀ ⟶ pullback A.hom (spMap σ')` to `hP'.lift ψ (s₀ ≫ spMap τ) (by rw [w.w, hcomp, Category.assoc])`. Establish `hψ' : ψ' ≫ pullback.fst A.hom (spMap σ') = ψ` using `hP'.lift_fst _ _ _`. Establish `w' : IsPullback ψ' s₀ (pullback.snd A.hom (spMap σ')) (spMap τ)`. Use `IsPullback.of_right ?_ (hP'.lift_snd _ _ _) hP'` and prove the remaining obligations. Rewrite using `[hψ', ← hcomp]`.

Conclude with `w`. Establish `hsurj` using `(hR' (Over.mk (pullback.snd A.hom (spMap σ'))) g (hab' hA) (hsm' g hg)).1 k τ hτs X₀ s₀ ψ' w'`. Introduce `y`. Take `⟨x', rfl⟩` from `hsurj y`. Take `⟨a, rfl⟩` from `hstep x'`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Conclude with `((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R' A.left (pullback A.hom (spMap σ')) A.hom (pullback.snd A.hom (spMap σ')) σ' (pullback.fst A.hom (spMap σ')) hg'.1.w k X₀ s₀ τ ψ' w'.w σ ψ w.w hψ'.symm (fun r => (hτ r).symm)).1 a |>.symm`. Establish `hu : IsUnit t`. Assume the negation of the conclusion as `hnu`. Conclude with `htm ((IsLocalRing.mem_maximalIdeal t).2 hnu)`.

Establish `hinj : Function.Injective σ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Establish `hma : a ∈ IsLocalRing.maximalIdeal R` using `by rw [← hkerσ]; exact ha`. Conclude with `(hu.mul_left_eq_zero).1 (hm a hma)`.

Conclude with `GlobalTheory.T.pull_h1_surjective_of_bijective R k σ A.left X₀ A.hom s₀ ψ w ⟨hinj, hσ⟩`.
-/
theorem surj_of_smallExt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (∀ (k : Type) [Field k] (σ : R' →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ B.left) (w : IsPullback ψ s₀ B.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) := by
  intro R _ _ t R' _ σ' hσ' hker ht hm hfield hR' A _ g hA hg k _ σ hσ X₀ s₀ ψ w
  have hkerσ : RingHom.ker σ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective σ hσ)
  by_cases htm : t ∈ IsLocalRing.maximalIdeal R
  ·
    let R₀ := R ⧸ IsLocalRing.maximalIdeal R
    let σ₀ : R →+* R₀ := Ideal.Quotient.mk _
    have hR₀ : IsField R₀ :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (IsLocalRing.maximalIdeal.isMaximal R)
    have hse : SmallExt t σ' σ₀ := by
      refine ⟨hσ', hker, Ideal.Quotient.mk_surjective, fun a => ?_⟩
      rw [Ideal.Quotient.eq_zero_iff_mem]
      constructor
      · exact hm a
      · intro hat
        by_contra hna
        have hu : IsUnit a := by
          by_contra hnu
          exact hna ((IsLocalRing.mem_maximalIdeal a).2 hnu)
        exact ht (hu.mul_right_eq_zero.1 hat)

    have hP' := IsPullback.of_hasPullback A.hom (spMap σ')
    have hP₀ := IsPullback.of_hasPullback A.hom (spMap σ₀)
    obtain ⟨i', hg', hab', hsm'⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' σ' A _ _ _ hP'
    obtain ⟨i₀, hg₀, hab₀, hsm₀⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R₀ σ₀ A _ _ _ hP₀
    have hstep := GlobalTheory.T.small_extension_primitive_lift R R' R₀ t σ' σ₀ g A _ _ _ _ hg' hg₀ hse hA hg
      (hR' _ g (hab' hA) (hsm' g hg)).2 (hfield R₀ hR₀ _ g (hab₀ hA) (hsm₀ g hg)).2.1

    have hle : RingHom.ker σ' ≤ RingHom.ker σ := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff, hkerσ]; exact htm
    let τ : R' →+* k := RingHom.liftOfRightInverse σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩
    have hτ : ∀ r, τ (σ' r) = σ r := fun r =>
      RingHom.liftOfRightInverse_comp_apply σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩ r
    have hτs : Function.Surjective τ := fun y => by
      obtain ⟨x, rfl⟩ := hσ y; exact ⟨σ' x, hτ x⟩
    have hcomp : spMap σ = spMap τ ≫ spMap σ' := by
      rw [← spMap_comp_hom]; congr 1; ext r; exact (hτ r).symm
    let ψ' : X₀ ⟶ pullback A.hom (spMap σ') := hP'.lift ψ (s₀ ≫ spMap τ) (by rw [w.w, hcomp, Category.assoc])
    have hψ' : ψ' ≫ pullback.fst A.hom (spMap σ') = ψ := hP'.lift_fst _ _ _
    have w' : IsPullback ψ' s₀ (pullback.snd A.hom (spMap σ')) (spMap τ) := by
      refine IsPullback.of_right ?_ (hP'.lift_snd _ _ _) hP'
      rw [hψ', ← hcomp]; exact w
    have hsurj := (hR' (Over.mk (pullback.snd A.hom (spMap σ'))) g (hab' hA) (hsm' g hg)).1 k τ hτs X₀ s₀ ψ' w'
    intro y
    obtain ⟨x', rfl⟩ := hsurj y
    obtain ⟨a, rfl⟩ := hstep x'
    refine ⟨a, ?_⟩
    exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R' A.left (pullback A.hom (spMap σ')) A.hom (pullback.snd A.hom (spMap σ'))
      σ' (pullback.fst A.hom (spMap σ')) hg'.1.w k X₀ s₀ τ ψ' w'.w σ ψ w.w hψ'.symm (fun r => (hτ r).symm)).1 a |>.symm
  ·
    have hu : IsUnit t := by
      by_contra hnu
      exact htm ((IsLocalRing.mem_maximalIdeal t).2 hnu)
    have hinj : Function.Injective σ := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      have hma : a ∈ IsLocalRing.maximalIdeal R := by rw [← hkerσ]; exact ha
      exact (hu.mul_left_eq_zero).1 (hm a hma)
    exact GlobalTheory.T.pull_h1_surjective_of_bijective R k σ A.left X₀ A.hom s₀ ψ w ⟨hinj, hσ⟩

end GlobalTheory.AbCoh.SmallStepSurj
