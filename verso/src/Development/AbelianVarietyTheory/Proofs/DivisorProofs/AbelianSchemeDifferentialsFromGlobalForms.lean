import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueVectorFieldOfGlobalOneFormValuesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
namespace GlobalTheory.ParForm

/- English proof (translation)
Set `F : B ⊗[R] M →ₗ[B] N` to `f.liftBaseChange B`. Establish `hF : ∀ w, F (1 ⊗ₜ w) = f w` using `fun w ↦ by simp [F]`. Establish `hd : Function.Bijective F.dualMap`. Rewrite using `[Function.bijective_iff_existsUnique]`. Introduce `φ`.

Take `⟨δ, h1, h2⟩` from `h ((φ.restrictScalars R).comp (TensorProduct.mk R B M 1))`. Use `⟨δ, ?_, fun δ' e ↦ h2 δ' fun w ↦ ?_⟩` and prove the remaining obligations. Use `(LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun w ↦ ?_)` and prove the remaining obligations. Simplify `h1 w` using `[hF]`. Rewrite using `[← hF]`.

Conclude with `LinearMap.congr_fun e (1 ⊗ₜ w)`. Establish `hdd : Function.Bijective F.dualMap.dualMap` using `(LinearEquiv.ofBijective _ hd).dualMap.bijective`. Establish `hb : Function.Bijective F`. Establish `e : ⇑(Module.Dual.eval B N) ∘ ⇑F = ⇑F.dualMap.dualMap ∘ ⇑(Module.Dual.eval B (B ⊗[R] M))`. Use function extensionality and compare the values at `fun x ↦ rfl`.

Rewrite using `[← Function.Bijective.of_comp_iff' (Module.bijective_dual_eval B N), e]`. Conclude with `hdd.comp (Module.bijective_dual_eval B _)`. Conclude with `IsBaseChange.of_equiv (LinearEquiv.ofBijective F hb) hF`.
-/
theorem isBaseChange_of_dual {R B M N : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite B N] [Module.Projective B N] (f : M →ₗ[R] N)
    (h : ∀ l : M →ₗ[R] B, ∃! δ : N →ₗ[B] B, ∀ w, δ (f w) = l w) : IsBaseChange B f := by
  let F : B ⊗[R] M →ₗ[B] N := f.liftBaseChange B
  have hF : ∀ w, F (1 ⊗ₜ w) = f w := fun w ↦ by simp [F]
  have hd : Function.Bijective F.dualMap := by
    rw [Function.bijective_iff_existsUnique]
    intro φ
    obtain ⟨δ, h1, h2⟩ := h ((φ.restrictScalars R).comp (TensorProduct.mk R B M 1))
    refine ⟨δ, ?_, fun δ' e ↦ h2 δ' fun w ↦ ?_⟩
    · refine (LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun w ↦ ?_)
      simpa [hF] using h1 w
    · rw [← hF]
      exact LinearMap.congr_fun e (1 ⊗ₜ w)
  have hdd : Function.Bijective F.dualMap.dualMap :=
    (LinearEquiv.ofBijective _ hd).dualMap.bijective
  have hb : Function.Bijective F := by
    have e : ⇑(Module.Dual.eval B N) ∘ ⇑F = ⇑F.dualMap.dualMap ∘ ⇑(Module.Dual.eval B (B ⊗[R] M)) :=
      funext fun x ↦ rfl
    rw [← Function.Bijective.of_comp_iff' (Module.bijective_dual_eval B N), e]
    exact hdd.comp (Module.bijective_dual_eval B _)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hb) hF

/- English proof (translation)
Establish `h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom` using `HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top`. Establish `h2 : RingHom.Smooth (secMap s U.1).hom` using `RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1`. Conclude with `h2`.
-/
theorem smooth_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

/- English proof (translation)
Introduce `H H' R _ A _ g hA hg U`. Establish `hs : Smooth A.hom` using `SmoothOfRelativeDimension.smooth g A.hom`. Use `smooth_sec A.hom hs U.unop` as an intermediate fact. Take `⟨-, -, ⟨h1, h2, -⟩, -⟩` from `H' R A g hA hg`. Conclude with `isBaseChange_of_dual _ (GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values H H' R A g hA hg U)`.
-/
theorem par : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  intro H H' R _ A _ g hA hg U
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have := smooth_sec A.hom hs U.unop
  obtain ⟨-, -, ⟨h1, h2, -⟩, -⟩ := H' R A g hA hg
  exact isBaseChange_of_dual _ (GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values H H' R A g hA hg U)

end GlobalTheory.ParForm
