import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Tube

/- English proof (translation)
Introduce `X S f _ s W hW`. Establish `hc : IsClosed (f '' (W : Set X)ᶜ)` using `f.isClosedMap _ W.isOpen.isClosed_compl`. Establish `hs : s ∈ (f '' (W : Set X)ᶜ)ᶜ`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hx (hW x rfl)`.

Take `⟨U, hU, hsU, hUV⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens) (show s ∈ (⟨_, hc.isOpen_compl⟩ : S.Opens) from hs)`. Use `⟨U, hU, hsU, fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hxW`. Conclude with `hUV hx ⟨x, hxW, rfl⟩`.
-/
theorem exists_affine_preimage_le :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) [UniversallyClosed f] (s : S) (W : X.Opens), (∀ x, f x = s → x ∈ W) → ∃ U : S.Opens, IsAffineOpen U ∧ s ∈ U ∧ f ⁻¹ᵁ U ≤ W := by
  intro X S f _ s W hW
  have hc : IsClosed (f '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  have hs : s ∈ (f '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, rfl⟩
    exact hx (hW x rfl)
  obtain ⟨U, hU, hsU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
    (show s ∈ (⟨_, hc.isOpen_compl⟩ : S.Opens) from hs)
  refine ⟨U, hU, hsU, fun x hx => ?_⟩
  by_contra hxW
  exact hUV hx ⟨x, hxW, rfl⟩

end GlobalTheory.Tube
