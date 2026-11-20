import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

/- English proof (translation)
Introduce `H X X' p hp L hL x`. Take `⟨W₀, hW₀, hxW₀, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)`. Establish `hA : IsAffineOpen (p ⁻¹ᵁ W₀)` using `IsAffineOpen.preimage hW₀ p`. Establish `hF : (p.base ⁻¹' {x}).Finite` using `Scheme.Hom.finite_preimage_singleton p x`. Establish `hFW : p.base ⁻¹' {x} ⊆ (p ⁻¹ᵁ W₀ : Set X')`.

Introduce `y hy`. Use `show p.base y ∈ W₀`. Rewrite `hy` using `[Set.mem_preimage, Set.mem_singleton_iff]`. Rewrite using `[hy]`. Conclude with `hxW₀`.

Take `⟨V, a, hFV, ha⟩` from `H X' L hL (p ⁻¹ᵁ W₀) hA _ hF hFW`. Establish `hcl : IsClosed (p.base '' (V : Set X')ᶜ)` using `p.isClosedMap _ V.isOpen.isClosed_compl`. Set `W : X.Opens` to `⟨(p.base '' (V : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩`. Establish `hWV : p ⁻¹ᵁ W ≤ V`. Introduce `y hy`.

Assume the negation of the conclusion as `h`. Conclude with `hy ⟨y, h, rfl⟩`. Establish `hxW : x ∈ W`. Introduce and unpack `⟨y, hy, hyx⟩`. Conclude with `hy (hFV (show p.base y = x from hyx))`.

Use `⟨W, fun k ↦ res (inf_le_inf_right _ hWV) (a k), hxW, ?_⟩` and prove the remaining obligations. Introduce `y k k' hy hk hk'`. Rewrite using `[gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk⟩, gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk'⟩]`. Conclude with `ha y k k' (hWV hy) hk hk'`.
-/
theorem locGen_near_fibre_of_finite : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  intro H X X' p hp L hL x
  obtain ⟨W₀, hW₀, hxW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineOpen.preimage hW₀ p
  have hF : (p.base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton p x
  have hFW : p.base ⁻¹' {x} ⊆ (p ⁻¹ᵁ W₀ : Set X') := by
    intro y hy
    show p.base y ∈ W₀
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy]; exact hxW₀
  obtain ⟨V, a, hFV, ha⟩ := H X' L hL (p ⁻¹ᵁ W₀) hA _ hF hFW
  have hcl : IsClosed (p.base '' (V : Set X')ᶜ) := p.isClosedMap _ V.isOpen.isClosed_compl
  let W : X.Opens := ⟨(p.base '' (V : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hWV : p ⁻¹ᵁ W ≤ V := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hxW : x ∈ W := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hFV (show p.base y = x from hyx))
  refine ⟨W, fun k ↦ res (inf_le_inf_right _ hWV) (a k), hxW, ?_⟩
  intro y k k' hy hk hk'
  rw [gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk⟩, gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk'⟩]
  exact ha y k k' (hWV hy) hk hk'

end GlobalTheory.Pinch
