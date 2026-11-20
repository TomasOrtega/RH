import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

noncomputable section

open GlobalTheory.RealWeil MeasureTheory Complex
open scoped SchwartzMap Matrix Real RealInnerProductSpace

namespace GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phase_eq_eChar (w : l ⊕ l → ℝ) (x : EuclideanSpace ℝ l) :
    phase w x = GlobalTheory.Published.Metaplectic.eChar (⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2) := by
  rw [GlobalTheory.Published.Metaplectic.eChar_apply, phase]
  congr 1
  push_cast
  ring

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem hasTemperateGrowth_phase' (w : l ⊕ l → ℝ) : Function.HasTemperateGrowth (phase w) := by
  have h1 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth
  have h := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (h1.add (Function.HasTemperateGrowth.const
    (⟪pPart w, qPart w⟫ / 2)))
  have e : phase w = (GlobalTheory.Published.Metaplectic.eChar : ℝ → ℂ) ∘
      ((fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫) + fun _ => ⟪pPart w, qPart w⟫ / 2) := by
    funext x
    simp [phase_eq_eChar]
  rw [e]
  exact h

def rhoSch (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l :=
  SchwartzMap.smulLeftCLM ℂ (phase w) ∘L SchwartzMap.compSubConstCLM ℂ (-pPart w)

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem coe_rhoSch (w : l ⊕ l → ℝ) (f : Sch l) : ⇑(rhoSch w f) = rhoFun w ⇑f := by
  funext x
  rw [rhoSch, ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase' w),
    SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, smul_eq_mul, rhoFun]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem exists_schwartz_rhoFun : ∀ (l : Type) [Fintype l] (w : l ⊕ l → ℝ) (f : Sch l), ∃ f₁ : Sch l, ⇑f₁ = rhoFun w ⇑f :=
  fun _ _ w f => ⟨rhoSch w f, coe_rhoSch w f⟩

end GlobalTheory.RealWeil
