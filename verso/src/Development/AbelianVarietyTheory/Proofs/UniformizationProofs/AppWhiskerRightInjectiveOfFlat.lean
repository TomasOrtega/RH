import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `S B T T' _ _ _ φ hφ U`. Establish `hd : IsSchemeTheoreticallyDominant φ.left`. Use `⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.Hom.ker_apply]`. Simplify using `only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]`.

Rewrite using `[← RingHom.injective_iff_ker_eq_bot]`. Conclude with `hφ`. Establish `pb : IsPullback (pullback.fst T'.hom B.hom) (φ ▷ B).left φ.left (pullback.fst T.hom B.hom)`. Use `(IsPullback.of_right (h₁₁ := (φ ▷ B).left) (v₁₁ := pullback.fst T'.hom B.hom) (h₂₁ := φ.left) (v₁₂ := pullback.fst T.hom B.hom) ?_ (Over.whiskerRight_left_fst φ) (IsPullback.of_hasPullback T.hom B.hom).flip).flip` and prove the remaining obligations. Rewrite using `[Over.whiskerRight_left_snd, Over.w]`.

Conclude with `(IsPullback.of_hasPullback T'.hom B.hom).flip`. Establish `: IsSchemeTheoreticallyDominant (φ ▷ B).left` using `.of_isPullback pb`. Establish `: QuasiCompact (φ ▷ B).left` using `MorphismProperty.of_isPullback pb inferInstance`. Conclude with `(φ ▷ B).left.app_injective U`.
-/
theorem app_whiskerRight_injective_of_flat :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (φ : T' ⟶ T), Function.Injective φ.left.appTop.hom → ∀ U : (T ⊗ B).left.Opens, Function.Injective ((φ ▷ B).left.app U).hom := by
  intro S B T T' _ _ _ φ hφ U
  have hd : IsSchemeTheoreticallyDominant φ.left := by
    refine ⟨Scheme.IdealSheafData.ext_of_isAffine ?_⟩
    rw [Scheme.Hom.ker_apply]
    simp only [Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    rw [← RingHom.injective_iff_ker_eq_bot]
    exact hφ
  have pb : IsPullback (pullback.fst T'.hom B.hom) (φ ▷ B).left φ.left (pullback.fst T.hom B.hom) := by
    refine (IsPullback.of_right (h₁₁ := (φ ▷ B).left) (v₁₁ := pullback.fst T'.hom B.hom)
      (h₂₁ := φ.left) (v₁₂ := pullback.fst T.hom B.hom) ?_ (Over.whiskerRight_left_fst φ)
      (IsPullback.of_hasPullback T.hom B.hom).flip).flip
    rw [Over.whiskerRight_left_snd, Over.w]
    exact (IsPullback.of_hasPullback T'.hom B.hom).flip
  have : IsSchemeTheoreticallyDominant (φ ▷ B).left := .of_isPullback pb
  have : QuasiCompact (φ ▷ B).left := MorphismProperty.of_isPullback pb inferInstance
  exact (φ ▷ B).left.app_injective U

end GlobalTheory
