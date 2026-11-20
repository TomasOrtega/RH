import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WchartCompLe
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HomFixGerm

open GlobalTheory.AmpleSpan

/- English proof (translation)
Establish `mem : ∀ x l, f₁ x ∈ nonzeroLocus (s l) ↔ f₂ x ∈ nonzeroLocus (s l)`. Introduce `x l`. Take `⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩` from `h x`. Rewrite using `[mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁, mem_nonzeroLocus_iff_gs (s l) f₂ x hp₂, e₁ l, e₂ l, Units.isUnit_units_mul, Units.isUnit_units_mul]`. Establish `rat : ∀ (l : κ) (r : κ → Γ(Y, nonzeroLocus (s l))), (∀ j, IsRatio (s j) (s l) (r j)) → ∀ x j, f₁ x ∈ nonzeroLocus (s l) → gs f₁ x _ (r j) = gs f₂ x _ (r j)`.

Introduce `l r hr x j hx`. Establish `hx₂` using `(mem x l).1 hx`. Take `⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩` from `h x`. Establish `a₁` using `(hr j).gs f₁ x hx hp₁`. Establish `a₂` using `(hr j).gs f₂ x hx₂ hp₂`.

Rewrite `a₁` using `[e₁ j, e₁ l]`. Rewrite `a₂` using `[e₂ j, e₂ l]`. Establish `hσ : IsUnit (σ l)`. Use `(mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁).1 hx` as an intermediate fact. Rewrite `this` using `[e₁ l, Units.isUnit_units_mul]`. Then use the resulting hypothesis.

Establish `b₁ : σ j = gs f₁ x _ (r j) * σ l`. Apply `u₁.isUnit.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[a₁]`. Expand and normalize the polynomial expressions, which then agree. Establish `b₂ : σ j = gs f₂ x _ (r j) * σ l`.

Apply `u₂.isUnit.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[a₂]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `hσ.mul_right_cancel (b₁.symm.trans b₂)`. Establish `loc : ∀ l, (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₁ = (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₂`.

Introduce `l`. Take `⟨haff, r, hr, hsurj⟩` from `hs.2 l`. Establish `hV : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ f₂ ⁻¹ᵁ nonzeroLocus (s l)` using `fun x hx => (mem x l).1 hx`. Establish `happ : f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl = f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV`. Establish `hcomp : (f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl).hom.comp (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) = (f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV).hom.comp (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l …`.

Use `MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]`. Use `fn_ext fun x hx => ?_` and prove the remaining obligations. Rewrite using `[gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp, Category.id_comp, gs_appLE π ⊤ _ le_top f₁ x hx, gs_appLE π ⊤ _ le_top f₂ x (hV hx), hπ]`. Simplify using `only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']`.

Use `fn_ext fun x hx => ?_` and prove the remaining obligations. Rewrite using `[gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp, Category.id_comp]`. Conclude with `rat l r hr x j hx`. Use extensionality with `a`. Take `⟨P, rfl⟩` from `hsurj a`.

Conclude with `congrArg (fun φ : MvPolynomial κ Γ(Z, ⊤) →+* _ => φ P) hcomp`. Use `haveI : IsAffine (nonzeroLocus (s l)) := haff`. Establish `hres : f₁.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl = f₂.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV`. Use `ext_of_isAffine ?_` and prove the remaining obligations. Simplify using `only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happ]`.

Rewrite using `[← Scheme.Hom.resLE_comp_ι f₁ (le_rfl : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ _), ← Scheme.Hom.resLE_comp_ι f₂ hV, hres]`. Establish `hcov : TopologicalSpace.IsOpenCover (fun l => f₁ ⁻¹ᵁ nonzeroLocus (s l))`. Use `top_le_iff.1 fun x _ => ?_` and prove the remaining obligations. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show f₁ x ∈ ⨆ l, nonzeroLocus (s l) by rw [hs.1]; trivial)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨l, hl⟩`.

Conclude with `Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _ hcov) f₁ f₂ fun l => loc l`.
-/
theorem eq_of_germs {X Y Z : Scheme.{0}} (π : Y ⟶ Z) {N : LB Y} {κ : Type} (s : κ → LB.Sec N)
    (hs : EmbedsBy π s) (f₁ f₂ : X ⟶ Y) (hπ : f₁ ≫ π = f₂ ≫ π)
    (h : ∀ x : X, ∃ σ : κ → X.presheaf.stalk x,
      (∃ p, f₁ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₁ x (N.U p) ((s l).f p) = u * σ l) ∧
      (∃ p, f₂ x ∈ N.U p ∧ ∃ u : (X.presheaf.stalk x)ˣ, ∀ l, gs f₂ x (N.U p) ((s l).f p) = u * σ l)) :
    f₁ = f₂ := by
  have mem : ∀ x l, f₁ x ∈ nonzeroLocus (s l) ↔ f₂ x ∈ nonzeroLocus (s l) := by
    intro x l
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    rw [mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁, mem_nonzeroLocus_iff_gs (s l) f₂ x hp₂, e₁ l, e₂ l,
      Units.isUnit_units_mul, Units.isUnit_units_mul]
  have rat : ∀ (l : κ) (r : κ → Γ(Y, nonzeroLocus (s l))), (∀ j, IsRatio (s j) (s l) (r j)) →
      ∀ x j, f₁ x ∈ nonzeroLocus (s l) → gs f₁ x _ (r j) = gs f₂ x _ (r j) := by
    intro l r hr x j hx
    have hx₂ := (mem x l).1 hx
    obtain ⟨σ, ⟨p₁, hp₁, u₁, e₁⟩, ⟨p₂, hp₂, u₂, e₂⟩⟩ := h x
    have a₁ := (hr j).gs f₁ x hx hp₁
    have a₂ := (hr j).gs f₂ x hx₂ hp₂
    rw [e₁ j, e₁ l] at a₁
    rw [e₂ j, e₂ l] at a₂
    have hσ : IsUnit (σ l) := by
      have := (mem_nonzeroLocus_iff_gs (s l) f₁ x hp₁).1 hx
      rwa [e₁ l, Units.isUnit_units_mul] at this
    have b₁ : σ j = gs f₁ x _ (r j) * σ l := by
      apply u₁.isUnit.mul_left_cancel
      rw [a₁]; ring
    have b₂ : σ j = gs f₂ x _ (r j) * σ l := by
      apply u₂.isUnit.mul_left_cancel
      rw [a₂]; ring
    exact hσ.mul_right_cancel (b₁.symm.trans b₂)
  have loc : ∀ l, (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₁ = (f₁ ⁻¹ᵁ nonzeroLocus (s l)).ι ≫ f₂ := by
    intro l
    obtain ⟨haff, r, hr, hsurj⟩ := hs.2 l
    have hV : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ f₂ ⁻¹ᵁ nonzeroLocus (s l) := fun x hx => (mem x l).1 hx
    have happ : f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      have hcomp : (f₁.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) =
          (f₂.appLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV).hom.comp
            (MvPolynomial.eval₂Hom (π.appLE ⊤ (nonzeroLocus (s l)) le_top).hom r) := by
        refine MvPolynomial.ringHom_ext (fun b => ?_) (fun j => ?_)
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp, gs_appLE π ⊤ _ le_top f₁ x hx, gs_appLE π ⊤ _ le_top f₂ x (hV hx), hπ]
        · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
          refine fn_ext fun x hx => ?_
          rw [gs_appLE f₁ _ _ le_rfl (𝟙 X) x hx, gs_appLE f₂ _ _ hV (𝟙 X) x hx, Category.id_comp,
            Category.id_comp]
          exact rat l r hr x j hx
      ext a
      obtain ⟨P, rfl⟩ := hsurj a
      exact congrArg (fun φ : MvPolynomial κ Γ(Z, ⊤) →+* _ => φ P) hcomp
    haveI : IsAffine (nonzeroLocus (s l)) := haff
    have hres : f₁.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) le_rfl =
        f₂.resLE (nonzeroLocus (s l)) (f₁ ⁻¹ᵁ nonzeroLocus (s l)) hV := by
      refine ext_of_isAffine ?_
      simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happ]
    rw [← Scheme.Hom.resLE_comp_ι f₁ (le_rfl : f₁ ⁻¹ᵁ nonzeroLocus (s l) ≤ _),
      ← Scheme.Hom.resLE_comp_ι f₂ hV, hres]
  have hcov : TopologicalSpace.IsOpenCover (fun l => f₁ ⁻¹ᵁ nonzeroLocus (s l)) := by
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show f₁ x ∈ ⨆ l, nonzeroLocus (s l) by rw [hs.1]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hl⟩
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _ hcov) f₁ f₂ fun l => loc l

end GlobalTheory.HomFixGerm
