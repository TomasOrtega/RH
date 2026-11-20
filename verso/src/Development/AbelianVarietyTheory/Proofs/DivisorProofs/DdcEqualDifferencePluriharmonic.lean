import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

/- English proof (translation)
Establish `hopen : IsOpen (cov B g)` using `hB.prod isOpen_univ`. Establish `hat : ∀ y : Fin g → ℂ, ContDiffAt ℝ ∞ F (b, y)` using `fun y => hF.contDiffAt (hopen.mem_nhds ⟨hb, Set.mem_univ _⟩)`. Establish `hfd : ∀ y : Fin g → ℂ, fderiv ℝ (fun z : Fin g → ℂ => F (b, z)) y = (fderiv ℝ F (b, y)).comp (ContinuousLinearMap.inr ℝ E (Fin g → ℂ))` using `fun y => (((hat y).differentiableAt (by simp)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) b y)).fderiv`. Establish `hfun : (fun y => fderiv ℝ (fun z : Fin g → ℂ => F (b, z)) y c) = (fun Q => fderiv ℝ F Q (0, c)) ∘ (fun y : Fin g → ℂ => (b, y))`. Use function extensionality and compare the values at `y`.

Simplify using `[hfd y]`. Establish `hG : DifferentiableAt ℝ (fun Q => fderiv ℝ F Q (0, c)) (b, z)`. Establish `h1 : ContDiffAt ℝ 1 (fderiv ℝ F) (b, z)` using `(hat z).fderiv_right (WithTop.coe_le_coe.2 le_top)`. Conclude with `(h1.differentiableAt (by simp)).clm_apply (differentiableAt_const _)`. Establish `hcomp` using `hG.hasFDerivAt.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) b z)`.

Rewrite using `[hfun]`. Use `⟨hcomp.differentiableAt, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp.fderiv]`. Both sides reduce to the same expression.
-/
theorem fibre_secondDeriv {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Set E)
    (hB : IsOpen B) (b : E) (hb : b ∈ B) (F : Pt E g → ℝ) (hF : ContDiffOn ℝ ∞ F (cov B g))
    (c z : Fin g → ℂ) :
    DifferentiableAt ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F (b, z)) y c) z ∧
    ∀ w, fderiv ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F (b, z)) y c) z w =
      fderiv ℝ (fun Q => fderiv ℝ F Q (0, c)) (b, z) (0, w) := by
  have hopen : IsOpen (cov B g) := hB.prod isOpen_univ
  have hat : ∀ y : Fin g → ℂ, ContDiffAt ℝ ∞ F (b, y) := fun y =>
    hF.contDiffAt (hopen.mem_nhds ⟨hb, Set.mem_univ _⟩)
  have hfd : ∀ y : Fin g → ℂ, fderiv ℝ (fun z : Fin g → ℂ => F (b, z)) y =
      (fderiv ℝ F (b, y)).comp (ContinuousLinearMap.inr ℝ E (Fin g → ℂ)) := fun y =>
    (((hat y).differentiableAt (by simp)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) b y)).fderiv
  have hfun : (fun y => fderiv ℝ (fun z : Fin g → ℂ => F (b, z)) y c) =
      (fun Q => fderiv ℝ F Q (0, c)) ∘ (fun y : Fin g → ℂ => (b, y)) := by
    funext y; simp [hfd y]
  have hG : DifferentiableAt ℝ (fun Q => fderiv ℝ F Q (0, c)) (b, z) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ F) (b, z) :=
      (hat z).fderiv_right (WithTop.coe_le_coe.2 le_top)
    exact (h1.differentiableAt (by simp)).clm_apply (differentiableAt_const _)
  have hcomp := hG.hasFDerivAt.comp z (hasFDerivAt_prodMk_right (𝕜 := ℝ) b z)
  rw [hfun]
  refine ⟨hcomp.differentiableAt, fun w => ?_⟩
  rw [hcomp.fderiv]
  rfl

/- English proof (translation)
Introduce `g E _ _ B hB b hb F₁ F₂ h1 h2 hddc`. Establish `hopen : IsOpen (cov B g)` using `hB.prod isOpen_univ`. Establish `hres : ∀ F : Pt E g → ℝ, ContDiffOn ℝ ∞ F (cov B g) → ContDiff ℝ ∞ (fun z : Fin g → ℂ => F (b, z))` using `fun F hF => contDiff_iff_contDiffAt.2 fun z => (hF.contDiffAt (hopen.mem_nhds ⟨hb, Set.mem_univ _⟩)).comp z (contDiff_const.prodMk contDiff_id).contDiffAt`. Establish `s1` using `hres F₁ h1`. Establish `s2` using `hres F₂ h2`.

Use `⟨s1.sub s2, fun z a w => ?_⟩` and prove the remaining obligations. Establish `hd : ∀ y, fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y = fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z)) y - fderiv ℝ (fun z : Fin g → ℂ => F₂ (b, z)) y` using `fun y => fderiv_sub ((s1.differentiable (by simp)) y) ((s2.differentiable (by simp)) y)`. Establish `hsplit : ∀ c : Fin g → ℂ, (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y c) = fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z)) y c - fderiv ℝ (fun z : Fin g → ℂ => F₂ (b, z)) y c` using `fun c => by`. Use function extensionality and compare the values at `y`. Rewrite using `[hd y]`.

Both sides reduce to the same expression. Establish `hsec : ∀ c d : Fin g → ℂ, fderiv ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y c) z d = fderiv ℝ (fun Q => fderiv ℝ F₁ Q (0, c)) (b, z) (0, d) - fderiv ℝ (fun Q => fderiv ℝ F₂ Q (0, c)) (b, z) (0, d)` using `fun c d => by`. Take `⟨d1, e1⟩` from `fibre_secondDeriv B hB b hb F₁ h1 c z`. Take `⟨d2, e2⟩` from `fibre_secondDeriv B hB b hb F₂ h2 c z`. Rewrite using `[hsplit c, fderiv_fun_sub d1 d2, ContinuousLinearMap.sub_apply, e1, e2]`.

Establish `h` using `hddc (b, z) ⟨hb, Set.mem_univ _⟩ (0, a) (0, w)`. Simplify using `only [ddc, Prod.smul_mk, smul_zero] at h`. Establish `hpi : (1 / (4 * π) : ℝ) ≠ 0` using `by positivity`. Establish `h'` using `mul_left_cancel₀ hpi h`. Rewrite using `[hsec, hsec]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem fibre_diff_ddc_eq_zero : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (B : Set E), IsOpen B → ∀ b ∈ B, ∀ F₁ F₂ : Pt E g → ℝ, ContDiffOn ℝ ∞ F₁ (cov B g) → ContDiffOn ℝ ∞ F₂ (cov B g) → (∀ P ∈ cov B g, ∀ v w : Pt E g, ddc F₁ P v w = ddc F₂ P v w) → ContDiff ℝ ∞ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) ∧ ∀ z a w : Fin g → ℂ, fderiv ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y (Complex.I • a)) z w = fderiv ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y (Complex.I • w)) z a := by
  intro g E _ _ B hB b hb F₁ F₂ h1 h2 hddc
  have hopen : IsOpen (cov B g) := hB.prod isOpen_univ
  have hres : ∀ F : Pt E g → ℝ, ContDiffOn ℝ ∞ F (cov B g) →
      ContDiff ℝ ∞ (fun z : Fin g → ℂ => F (b, z)) := fun F hF =>
    contDiff_iff_contDiffAt.2 fun z =>
      (hF.contDiffAt (hopen.mem_nhds ⟨hb, Set.mem_univ _⟩)).comp z
        (contDiff_const.prodMk contDiff_id).contDiffAt
  have s1 := hres F₁ h1
  have s2 := hres F₂ h2
  refine ⟨s1.sub s2, fun z a w => ?_⟩
  have hd : ∀ y, fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y =
      fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z)) y - fderiv ℝ (fun z : Fin g → ℂ => F₂ (b, z)) y :=
    fun y => fderiv_sub ((s1.differentiable (by simp)) y) ((s2.differentiable (by simp)) y)
  have hsplit : ∀ c : Fin g → ℂ,
      (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y c) =
      fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z)) y c -
        fderiv ℝ (fun z : Fin g → ℂ => F₂ (b, z)) y c := fun c => by
    funext y; rw [hd y]; rfl
  have hsec : ∀ c d : Fin g → ℂ,
      fderiv ℝ (fun y => fderiv ℝ (fun z : Fin g → ℂ => F₁ (b, z) - F₂ (b, z)) y c) z d =
      fderiv ℝ (fun Q => fderiv ℝ F₁ Q (0, c)) (b, z) (0, d) -
        fderiv ℝ (fun Q => fderiv ℝ F₂ Q (0, c)) (b, z) (0, d) := fun c d => by
    obtain ⟨d1, e1⟩ := fibre_secondDeriv B hB b hb F₁ h1 c z
    obtain ⟨d2, e2⟩ := fibre_secondDeriv B hB b hb F₂ h2 c z
    rw [hsplit c, fderiv_fun_sub d1 d2, ContinuousLinearMap.sub_apply, e1, e2]
  have h := hddc (b, z) ⟨hb, Set.mem_univ _⟩ (0, a) (0, w)
  simp only [ddc, Prod.smul_mk, smul_zero] at h
  have hpi : (1 / (4 * π) : ℝ) ≠ 0 := by positivity
  have h' := mul_left_cancel₀ hpi h
  rw [hsec, hsec]
  linarith

end GlobalTheory
