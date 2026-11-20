import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasKOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTestFunctionReproducingLaplacianPolySolutiStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.HCF GlobalTheory.CuspQuot GlobalTheory.HCAlpha MeasureTheory
open scoped ContDiff

noncomputable section
namespace GlobalTheory.HCParam

section Local
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

end Local
end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

section Degenerate
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

end Degenerate
end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

section Transpose
variable {E : Type} [Field E] [NumberField E] {a : ℕ} (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure]

def Transposable (T : (Lie E a → ℂ) → Lie E a → ℂ) : Prop :=
  (∀ G, ContDiffOn ℝ ∞ G (invSet E a) → ContDiffOn ℝ ∞ (T G) (invSet E a)) ∧
    ∀ β, IsTest (invSet E a) β → ∃ γ, IsTest (invSet E a) γ ∧
      ∀ G, ContDiffOn ℝ ∞ G (invSet E a) → ∫ y, β y * T G y ∂ν = ∫ y, γ y * G y ∂ν

/- English proof (translation)
Use `⟨fun G hG => hS.1 _ (hT.1 G hG), fun β hβ => ?_⟩` and prove the remaining obligations. Take `⟨γ₁, h₁, e₁⟩` from `hS.2 β hβ`. Take `⟨γ₂, h₂, e₂⟩` from `hT.2 γ₁ h₁`. Conclude with `⟨γ₂, h₂, fun G hG => (e₁ _ (hT.1 G hG)).trans (e₂ G hG)⟩`.
-/
theorem Transposable.comp {S T : (Lie E a → ℂ) → Lie E a → ℂ} (hS : Transposable ν S) (hT : Transposable ν T) :
    Transposable ν (S ∘ T) := by
  refine ⟨fun G hG => hS.1 _ (hT.1 G hG), fun β hβ => ?_⟩
  obtain ⟨γ₁, h₁, e₁⟩ := hS.2 β hβ
  obtain ⟨γ₂, h₂, e₂⟩ := hT.2 γ₁ h₁
  exact ⟨γ₂, h₂, fun G hG => (e₁ _ (hT.1 G hG)).trans (e₂ G hG)⟩

/- English proof (translation)
Use `⟨fun G hG => (hS.1 G hG).add (hT.1 G hG), fun β hβ => ?_⟩` and prove the remaining obligations. Take `⟨γ₁, h₁, e₁⟩` from `hS.2 β hβ`. Take `⟨γ₂, h₂, e₂⟩` from `hT.2 β hβ`. Use `⟨γ₁ + γ₂, h₁.add h₂, fun G hG => ?_⟩` and prove the remaining obligations. Establish `i1` using `hβ.integrable_mul ν isOpen_invSet (hS.1 G hG).continuousOn`.

Establish `i2` using `hβ.integrable_mul ν isOpen_invSet (hT.1 G hG).continuousOn`. Establish `j1` using `h₁.integrable_mul ν isOpen_invSet hG.continuousOn`. Establish `j2` using `h₂.integrable_mul ν isOpen_invSet hG.continuousOn`. Simplify using `only [Pi.add_apply, mul_add, add_mul]`. Rewrite using `[integral_add i1 i2, integral_add j1 j2, e₁ G hG, e₂ G hG]`.
-/
theorem Transposable.add {S T : (Lie E a → ℂ) → Lie E a → ℂ} (hS : Transposable ν S) (hT : Transposable ν T) :
    Transposable ν (fun G => S G + T G) := by
  refine ⟨fun G hG => (hS.1 G hG).add (hT.1 G hG), fun β hβ => ?_⟩
  obtain ⟨γ₁, h₁, e₁⟩ := hS.2 β hβ
  obtain ⟨γ₂, h₂, e₂⟩ := hT.2 β hβ
  refine ⟨γ₁ + γ₂, h₁.add h₂, fun G hG => ?_⟩
  have i1 := hβ.integrable_mul ν isOpen_invSet (hS.1 G hG).continuousOn
  have i2 := hβ.integrable_mul ν isOpen_invSet (hT.1 G hG).continuousOn
  have j1 := h₁.integrable_mul ν isOpen_invSet hG.continuousOn
  have j2 := h₂.integrable_mul ν isOpen_invSet hG.continuousOn
  simp only [Pi.add_apply, mul_add, add_mul]
  rw [integral_add i1 i2, integral_add j1 j2, e₁ G hG, e₂ G hG]

/- English proof (translation)
Use `⟨fun G hG => (hT.1 G hG).const_smul c, fun β hβ => ?_⟩` and prove the remaining obligations. Take `⟨γ, h, e⟩` from `hT.2 β hβ`. Use `⟨fun x => γ x * c, h.mul contDiff_const, fun G hG => ?_⟩` and prove the remaining obligations. Establish `e1 : (fun y => β y * (c • T G) y) = fun y => c * (β y * T G y)`. Use function extensionality and compare the values at `y`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (fun y => γ y * c * G y) = fun y => c * (γ y * G y)` using `by funext y; ring`. Rewrite using `[e1, e2, integral_const_mul, integral_const_mul, e G hG]`.
-/
theorem Transposable.smul {T : (Lie E a → ℂ) → Lie E a → ℂ} (hT : Transposable ν T) (c : ℂ) :
    Transposable ν (fun G => c • T G) := by
  refine ⟨fun G hG => (hT.1 G hG).const_smul c, fun β hβ => ?_⟩
  obtain ⟨γ, h, e⟩ := hT.2 β hβ
  refine ⟨fun x => γ x * c, h.mul contDiff_const, fun G hG => ?_⟩
  have e1 : (fun y => β y * (c • T G) y) = fun y => c * (β y * T G y) := by
    funext y; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have e2 : (fun y => γ y * c * G y) = fun y => c * (γ y * G y) := by funext y; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, e G hG]

end Transpose

end GlobalTheory.HCParam

noncomputable section
namespace GlobalTheory.HCParam

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_testFunction_reproducing_laplacianPoly_solutions`.
-/
theorem reproduce : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ν : Measure (Lie E a)),
    ν.IsAddHaarMeasure → ∀ p : Polynomial ℂ, p ≠ 0 → ∃ α : Lie E a → ℂ, IsTest (invSet E a) α ∧
      ∀ f : Lie E a → ℂ, ContDiffOn ℝ ∞ f (invSet E a) → (∀ y ∈ invSet E a, polyF E a p f y = 0) →
        ∫ y, α y * f y ∂ν = f (oneL E a) :=
  GlobalTheory.T.exists_testFunction_reproducing_laplacianPoly_solutions

end GlobalTheory.HCParam
