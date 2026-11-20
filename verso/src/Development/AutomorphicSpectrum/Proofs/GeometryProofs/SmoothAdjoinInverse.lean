import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtOfMulRight

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

/- English proof (translation)
Use `letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra`. Establish `hmap : ∀ a : A, ((algebraMap A (invAdj A g) a : invAdj A g) : Ω) = a` using `fun _ => rfl`. Use `IsLocalization.Away.mk (⟨g, hg⟩ : A) ?_ ?_ ?_` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `[hmap, h0]`.

Introduce `s`. Take `⟨k, hk⟩` from `exists_mul_pow_mem hg h0 s.2`. Use `⟨k, ⟨_, hk⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[hmap]`. Introduce `a b hab`.

Establish `hab' : a = b` using `Subtype.ext (by simpa [hmap] using congrArg Subtype.val hab)`. Conclude with `⟨0, by rw [hab']⟩`.
-/
theorem isLocalizationAway_invAdj {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : Subalgebra ℚ Ω} {g : Ω}
    (hg : g ∈ A) (h0 : g ≠ 0) :
    letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
    IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := by
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  have hmap : ∀ a : A, ((algebraMap A (invAdj A g) a : invAdj A g) : Ω) = a := fun _ => rfl
  refine IsLocalization.Away.mk (⟨g, hg⟩ : A) ?_ ?_ ?_
  · refine IsUnit.of_mul_eq_one (⟨g⁻¹, inv_mem_invAdj A g⟩ : invAdj A g) (Subtype.ext ?_)
    simp [hmap, h0]
  · intro s
    obtain ⟨k, hk⟩ := exists_mul_pow_mem hg h0 s.2
    refine ⟨k, ⟨_, hk⟩, Subtype.ext ?_⟩
    simp [hmap]
  · intro a b hab
    have hab' : a = b := Subtype.ext (by simpa [hmap] using congrArg Subtype.val hab)
    exact ⟨0, by rw [hab']⟩

/- English proof (translation)
Introduce `Ω _ _ A g hg h0 hA`. Use `letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ A (invAdj A g) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := isLocalizationAway_invAdj hg h0`. Use `haveI : Algebra.Smooth A (invAdj A g) := Algebra.Smooth.of_isLocalization_Away (⟨g, hg⟩ : A)`.

Conclude with `Algebra.Smooth.comp ℚ A (invAdj A g)`.
-/
theorem smooth_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 →
    Algebra.Smooth ℚ A → Algebra.Smooth ℚ (invAdj A g) := by
  intro Ω _ _ A g hg h0 hA
  letI : Algebra A (invAdj A g) := (Subalgebra.inclusion (le_invAdj A g)).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ A (invAdj A g) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.Away (⟨g, hg⟩ : A) (invAdj A g) := isLocalizationAway_invAdj hg h0
  haveI : Algebra.Smooth A (invAdj A g) := Algebra.Smooth.of_isLocalization_Away (⟨g, hg⟩ : A)
  exact Algebra.Smooth.comp ℚ A (invAdj A g)

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
