import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem

open CategoryTheory AlgebraicGeometry Limits

namespace GlobalTheory.CompanionTheory.Ar.Approx

/- English proof (translation)
Establish `huc : UniversallyClosed p`. Prove the components needed by the constructor for the conclusion. Introduce `X' Y' i₁ i₂ f' hpb Z hZ`. Establish `hW : ∀ i, IsPullback (pullback.fst i₁ (π i) ≫ f') (pullback.snd i₁ (π i)) i₂ (π i ≫ p)` using `fun i => (IsPullback.of_hasPullback i₁ (π i)).paste_horiz hpb`. Establish `hc : ∀ i, IsClosedMap ⇑(pullback.fst i₁ (π i) ≫ f')` using `fun i => @UniversallyClosed.universally_isClosedMap _ _ _ (hprop i).toUniversallyClosed _ _ _ _ _ (hW i)`.

Establish `key : ⇑f' '' Z = ⋃ i, ⇑(pullback.fst i₁ (π i) ≫ f') '' (⇑(pullback.fst i₁ (π i)) ⁻¹' Z)`. Use extensionality with `y`. Simplify using `only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`.

Take `⟨i, y', hy'⟩` from `hcov (i₁ x)`. Take `⟨w, hw, -⟩` from `Scheme.Pullback.exists_preimage_pullback x y' hy'.symm`. Use `⟨i, w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`. Conclude with `hx`.

Use `show f' (pullback.fst i₁ (π i) w) = f' x`. Rewrite using `[hw]`. Introduce and unpack `⟨i, w, hw, rfl⟩`. Conclude with `⟨pullback.fst i₁ (π i) w, hw, rfl⟩`. Use `isClosed_iUnion_of_finite fun i => hc i _ (hZ.preimage (pullback.fst i₁ (π i)).continuous) using 1` and compare the differences between its conclusion and the goal.

Conclude with `@IsProper.mk _ _ _ hsep huc hft`.
-/
theorem isProper_of_finite_cover (X S : Scheme.{0}) (p : X ⟶ S) (n : ℕ) (Y : Fin n → Scheme.{0})
    (π : ∀ i, Y i ⟶ X) (hsep : IsSeparated p) (hft : LocallyOfFiniteType p)
    (hprop : ∀ i, IsProper (π i ≫ p)) (hcov : ∀ x : X, ∃ i, x ∈ Set.range (π i)) :
    IsProper p := by
  have huc : UniversallyClosed p := by
    constructor
    intro X' Y' i₁ i₂ f' hpb Z hZ
    have hW : ∀ i, IsPullback (pullback.fst i₁ (π i) ≫ f') (pullback.snd i₁ (π i)) i₂
        (π i ≫ p) := fun i => (IsPullback.of_hasPullback i₁ (π i)).paste_horiz hpb
    have hc : ∀ i, IsClosedMap ⇑(pullback.fst i₁ (π i) ≫ f') := fun i =>
      @UniversallyClosed.universally_isClosedMap _ _ _ (hprop i).toUniversallyClosed
        _ _ _ _ _ (hW i)
    have key : ⇑f' '' Z =
        ⋃ i, ⇑(pullback.fst i₁ (π i) ≫ f') '' (⇑(pullback.fst i₁ (π i)) ⁻¹' Z) := by
      ext y
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y', hy'⟩ := hcov (i₁ x)
        obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y' hy'.symm
        refine ⟨i, w, ?_, ?_⟩
        · rw [hw]
          exact hx
        · show f' (pullback.fst i₁ (π i) w) = f' x
          rw [hw]
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨pullback.fst i₁ (π i) w, hw, rfl⟩
    convert isClosed_iUnion_of_finite fun i =>
      hc i _ (hZ.preimage (pullback.fst i₁ (π i)).continuous) using 1
  exact @IsProper.mk _ _ _ hsep huc hft

end GlobalTheory.CompanionTheory.Ar.Approx
