import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSectionAtRingPointSpMapCompRestrictStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRatIffExistsRatFunc

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `F _ Y ξ hrat`. Take `⟨h1, -, -, h4, h5, h6, -⟩` from `GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk`. Take `⟨U, hUa, hy, -⟩` from `(Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens) (show ξ (IsLocalRing.closedPoint (PowerSeries F)) ∈ (⊤ : Y.Opens) from trivial)`. Establish `hξ : ⊤ ≤ ξ ⁻¹ᵁ U` using `(h4 _ Y ξ U).2 hy`. Use `set ψ := evAt ξ hξ`.

Use `set ιR := algebraMap (RatFunc F) (LaurentSeries F)`. Use `set ιP := algebraMap (PowerSeries F) (LaurentSeries F)`. Establish `hR : Function.Injective ιR` using `ιR.injective`. Establish `hmem : ∀ f, (ιP.comp ψ) f ∈ ιR.range` using `fun f => by`. Take `⟨ρ, hρ⟩` from `(isRat_iff_exists_ratFunc F (ψ f)).1 (hrat U hUa hξ f)`.

Conclude with `⟨ρ, hρ⟩`. Set `e` to `RingEquiv.ofBijective ιR.rangeRestrict ⟨fun a b hab => hR (congrArg Subtype.val hab), ιR.rangeRestrict_surjective⟩`. Set `φ : Γ(Y, U) →+* RatFunc F` to `e.symm.toRingHom.comp ((ιP.comp ψ).codRestrict ιR.range hmem)`. Establish `hφ : ∀ f, ιR (φ f) = ιP (ψ f)` using `fun f => by`. Use `congrArg Subtype.val (e.apply_symm_apply ((ιP.comp ψ).codRestrict ιR.range hmem f))` as an intermediate fact.

Conclude with `this`. Take `⟨β, hβ, hβφ⟩` from `h6 (RatFunc F) Y U hUa φ`. Use `⟨β, ?_⟩` and prove the remaining obligations. Establish `ha : ⊤ ≤ (spMap ιR ≫ β) ⁻¹ᵁ U` using `fun x _ => hβ (Set.mem_univ ((spMap ιR) x))`. Establish `hb : ⊤ ≤ (spMap ιP ≫ ξ) ⁻¹ᵁ U` using `fun x _ => hξ (Set.mem_univ ((spMap ιP) x))`.

Use `h5 (LaurentSeries F) Y _ _ U hUa ha hb ?_` and prove the remaining obligations. Use `RingHom.ext fun f => ?_` and prove the remaining obligations. Rewrite using `[h1 _ _ Y ιR β U hβ ha f, h1 _ _ Y ιP ξ U hξ hb f, hβφ]`. Conclude with `hφ f`.
-/
theorem isRatPath_of_isRat : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (ξ : Sp (PowerSeries F) ⟶ Y),
    (∀ (U : Y.Opens), IsAffineOpen U → ∀ (h : ⊤ ≤ ξ ⁻¹ᵁ U) (f : Γ(Y, U)), IsRat (evAt ξ h f)) → IsRatPath ξ := by
  intro F _ Y ξ hrat
  obtain ⟨h1, -, -, h4, h5, h6, -⟩ := GlobalTheory.T.evalSectionAtRingPoint_spMap_comp_restrict_stalk
  obtain ⟨U, hUa, hy, -⟩ := (Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens)
    (show ξ (IsLocalRing.closedPoint (PowerSeries F)) ∈ (⊤ : Y.Opens) from trivial)
  have hξ : ⊤ ≤ ξ ⁻¹ᵁ U := (h4 _ Y ξ U).2 hy
  set ψ := evAt ξ hξ
  set ιR := algebraMap (RatFunc F) (LaurentSeries F)
  set ιP := algebraMap (PowerSeries F) (LaurentSeries F)
  have hR : Function.Injective ιR := ιR.injective
  have hmem : ∀ f, (ιP.comp ψ) f ∈ ιR.range := fun f => by
    obtain ⟨ρ, hρ⟩ := (isRat_iff_exists_ratFunc F (ψ f)).1 (hrat U hUa hξ f)
    exact ⟨ρ, hρ⟩
  let e := RingEquiv.ofBijective ιR.rangeRestrict ⟨fun a b hab => hR (congrArg Subtype.val hab), ιR.rangeRestrict_surjective⟩
  let φ : Γ(Y, U) →+* RatFunc F := e.symm.toRingHom.comp ((ιP.comp ψ).codRestrict ιR.range hmem)
  have hφ : ∀ f, ιR (φ f) = ιP (ψ f) := fun f => by
    have := congrArg Subtype.val (e.apply_symm_apply ((ιP.comp ψ).codRestrict ιR.range hmem f))
    exact this
  obtain ⟨β, hβ, hβφ⟩ := h6 (RatFunc F) Y U hUa φ
  refine ⟨β, ?_⟩
  have ha : ⊤ ≤ (spMap ιR ≫ β) ⁻¹ᵁ U := fun x _ => hβ (Set.mem_univ ((spMap ιR) x))
  have hb : ⊤ ≤ (spMap ιP ≫ ξ) ⁻¹ᵁ U := fun x _ => hξ (Set.mem_univ ((spMap ιP) x))
  refine h5 (LaurentSeries F) Y _ _ U hUa ha hb ?_
  refine RingHom.ext fun f => ?_
  rw [h1 _ _ Y ιR β U hβ ha f, h1 _ _ Y ιP ξ U hξ hb f, hβφ]
  exact hφ f

end GlobalTheory.Nef
