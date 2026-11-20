import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KernelBasic

/- English proof (translation)
Establish `hS : IsCompact (U * tsupport φ * V⁻¹)` using `(hU.mul hφ.isCompact).mul hV.inv`. Use `(X.proper _ hS).subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨x, hx, y, hy, h⟩`. Use `Set.mem_setOf_eq ▸ ?_` and prove the remaining obligations. Establish `e : (γ : X.G) = x * (x⁻¹ * (γ : X.G) * y) * y⁻¹` using `by group`.

Rewrite using `[e]`. Conclude with `Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ (Function.mem_support.2 h))) (Set.inv_mem_inv.2 hy)`.
-/
theorem finite_of_compact (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) {U V : Set X.G}
    (hU : IsCompact U) (hV : IsCompact V) :
    {γ : X.Γ | ∃ x ∈ U, ∃ y ∈ V, φ (x⁻¹ * (γ : X.G) * y) ≠ 0}.Finite := by
  have hS : IsCompact (U * tsupport φ * V⁻¹) := (hU.mul hφ.isCompact).mul hV.inv
  refine (X.proper _ hS).subset ?_
  rintro γ ⟨x, hx, y, hy, h⟩
  refine Set.mem_setOf_eq ▸ ?_
  have e : (γ : X.G) = x * (x⁻¹ * (γ : X.G) * y) * y⁻¹ := by group
  rw [e]
  exact Set.mul_mem_mul (Set.mul_mem_mul hx (subset_tsupport _ (Function.mem_support.2 h)))
    (Set.inv_mem_inv.2 hy)

/- English proof (translation)
Use `(finite_of_compact X hφ (isCompact_singleton (x := x)) (isCompact_singleton (x := y))).subset ?_` and prove the remaining obligations. Introduce `γ h`. Conclude with `⟨x, rfl, y, rfl, h⟩`.
-/
theorem support_finite (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    (Function.support fun γ : X.Γ => φ (x⁻¹ * (γ : X.G) * y)).Finite := by
  refine (finite_of_compact X hφ (isCompact_singleton (x := x))
    (isCompact_singleton (x := y))).subset ?_
  intro γ h
  exact ⟨x, rfl, y, rfl, h⟩

/- English proof (translation)
Establish `e : Function.uncurry (ker X.Γ φ) = fun p : X.G × X.G => ∑ᶠ γ : X.Γ, φ (p.1⁻¹ * (γ : X.G) * p.2)`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Rewrite using `[e]`. Use `continuous_finsum (fun γ => ?_) ?_` and prove the remaining obligations.

Conclude with `hφ.1.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd)`. Introduce and unpack `⟨x, y⟩`. Take `⟨U, hU, hUx⟩` from `exists_compact_mem_nhds x`. Take `⟨V, hV, hVy⟩` from `exists_compact_mem_nhds y`. Use `⟨U ×ˢ V, prod_mem_nhds hUx hVy, ?_⟩` and prove the remaining obligations.

Use `(finite_of_compact X hφ.2 hU hV).subset ?_` and prove the remaining obligations. Introduce and unpack `γ ⟨⟨a, b⟩, hs, hab⟩`. Conclude with `⟨a, hab.1, b, hab.2, hs⟩`.
-/
theorem continuous_ker (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) :
    Continuous (Function.uncurry (ker X.Γ φ)) := by
  have e : Function.uncurry (ker X.Γ φ) =
      fun p : X.G × X.G => ∑ᶠ γ : X.Γ, φ (p.1⁻¹ * (γ : X.G) * p.2) := by
    funext p
    rfl
  rw [e]
  refine continuous_finsum (fun γ => ?_) ?_
  · exact hφ.1.comp ((continuous_fst.inv.mul continuous_const).mul continuous_snd)
  · rintro ⟨x, y⟩
    obtain ⟨U, hU, hUx⟩ := exists_compact_mem_nhds x
    obtain ⟨V, hV, hVy⟩ := exists_compact_mem_nhds y
    refine ⟨U ×ˢ V, prod_mem_nhds hUx hVy, ?_⟩
    refine (finite_of_compact X hφ.2 hU hV).subset ?_
    rintro γ ⟨⟨a, b⟩, hs, hab⟩
    exact ⟨a, hab.1, b, hab.2, hs⟩

/- English proof (translation)
Unfold `ker`. Rewrite using `[← finsum_comp_equiv (Equiv.mulLeft (⟨γ, hγ⟩ : X.Γ))]`. Use `finsum_congr fun δ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [Equiv.coe_mulLeft, Subgroup.coe_mul]`.

Use `group`.
-/
theorem ker_mul_left (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ (γ * x) y = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulLeft (⟨γ, hγ⟩ : X.Γ))]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
  group

/- English proof (translation)
Unfold `ker`. Rewrite using `[← finsum_comp_equiv (Equiv.mulRight (⟨γ, hγ⟩ : X.Γ)⁻¹)]`. Use `finsum_congr fun δ => ?_` and prove the remaining obligations. Use `congr 1`. Simplify using `only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv]`.

Use `group`.
-/
theorem ker_mul_right (X : Ctx) (φ : X.G → ℂ) {γ : X.G} (hγ : γ ∈ X.Γ) (x y : X.G) :
    ker X.Γ φ x (γ * y) = ker X.Γ φ x y := by
  unfold ker
  rw [← finsum_comp_equiv (Equiv.mulRight (⟨γ, hγ⟩ : X.Γ)⁻¹)]
  refine finsum_congr fun δ => ?_
  congr 1
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv]
  group

/- English proof (translation)
Use `⟨Complex.continuous_conj.comp (hφ.1.comp continuous_inv), ?_⟩` and prove the remaining obligations. Establish `h : HasCompactSupport (φ ∘ (Homeomorph.inv X.G))` using `hφ.2.comp_homeomorph (Homeomorph.inv X.G)`. Conclude with `h.comp_left (g := starRingEnd ℂ) (map_zero _)`.
-/
theorem tst_adj (X : Ctx) {φ : X.G → ℂ} (hφ : Tst φ) : Tst (adj φ) := by
  refine ⟨Complex.continuous_conj.comp (hφ.1.comp continuous_inv), ?_⟩
  have h : HasCompactSupport (φ ∘ (Homeomorph.inv X.G)) :=
    hφ.2.comp_homeomorph (Homeomorph.inv X.G)
  exact h.comp_left (g := starRingEnd ℂ) (map_zero _)

/- English proof (translation)
Unfold `ker`. Rewrite using `[map_finsum _ (support_finite X hφ y x), ← finsum_comp_equiv (Equiv.inv X.Γ)]`. Use `finsum_congr fun δ => ?_` and prove the remaining obligations. Simplify using `only [adj, Equiv.inv_apply, Subgroup.coe_inv]`. Use `congr 2`.

Use `group`.
-/
theorem ker_adj (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ker X.Γ (adj φ) x y = starRingEnd ℂ (ker X.Γ φ y x) := by
  unfold ker
  rw [map_finsum _ (support_finite X hφ y x), ← finsum_comp_equiv (Equiv.inv X.Γ)]
  refine finsum_congr fun δ => ?_
  simp only [adj, Equiv.inv_apply, Subgroup.coe_inv]
  congr 2
  group

/- English proof (translation)
Unfold `ker`. Rewrite using `[finsum_eq_sum _ (support_finite X hφ x y)]`. Conclude with `(enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)`.
-/
theorem enorm_ker_le (X : Ctx) {φ : X.G → ℂ} (hφ : HasCompactSupport φ) (x y : X.G) :
    ‖ker X.Γ φ x y‖ₑ ≤ ∑' γ : X.Γ, ‖φ (x⁻¹ * (γ : X.G) * y)‖ₑ := by
  unfold ker
  rw [finsum_eq_sum _ (support_finite X hφ x y)]
  exact (enorm_sum_le _ _).trans (ENNReal.sum_le_tsum _)

/- English proof (translation)
Introduce `X φ hφ`. Conclude with `⟨support_finite X hφ.2, continuous_ker X hφ, fun γ hγ x y => ⟨ker_mul_left X φ hγ x y, ker_mul_right X φ hγ x y⟩, tst_adj X hφ, ker_adj X hφ.2, enorm_ker_le X hφ.2⟩`.
-/
theorem kerBasic : KerBasic := by
  intro X φ hφ
  exact ⟨support_finite X hφ.2, continuous_ker X hφ,
    fun γ hγ x y => ⟨ker_mul_left X φ hγ x y, ker_mul_right X φ hγ x y⟩,
    tst_adj X hφ, ker_adj X hφ.2, enorm_ker_le X hφ.2⟩

end GlobalTheory.CompanionTheory.KernelBasic

end
