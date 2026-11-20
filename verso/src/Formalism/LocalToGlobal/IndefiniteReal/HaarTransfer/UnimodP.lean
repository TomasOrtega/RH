import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.Unimod

namespace Formalism.IndefR.Leaf.Proofs
open Formalism.IndefR.Leaf MeasureTheory

/- English proof (translation)
Introduce `G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ μ hμ`. Establish `: (Measure.haar : Measure G₁).IsMulRightInvariant` using `h₁ _ inferInstance`. Establish `: (Measure.haar : Measure G₂).IsMulRightInvariant` using `h₂ _ inferInstance`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂))]`. Use `infer_instance`.
-/
theorem prodStatement_holds : HaarRightInvProd := by
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ μ hμ
  have : (Measure.haar : Measure G₁).IsMulRightInvariant := h₁ _ inferInstance
  have : (Measure.haar : Measure G₂).IsMulRightInvariant := h₂ _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ ((Measure.haar : Measure G₁).prod (Measure.haar : Measure G₂))]
  infer_instance

/- English proof (translation)
Introduce `ι _ G _ _ _ _ _ _ _ _ h μ hμ`. Establish `: ∀ i, (Measure.haar : Measure (G i)).IsMulRightInvariant` using `fun i => h i _ inferInstance`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul μ (Measure.pi fun i => (Measure.haar : Measure (G i)))]`. Use `infer_instance`.
-/
theorem piStatement_holds : HaarRightInvPi := by
  intro ι _ G _ _ _ _ _ _ _ _ h μ hμ
  have : ∀ i, (Measure.haar : Measure (G i)).IsMulRightInvariant := fun i => h i _ inferInstance
  rw [Measure.isMulLeftInvariant_eq_smul μ (Measure.pi fun i => (Measure.haar : Measure (G i)))]
  infer_instance

/- English proof (translation)
Introduce `G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ e h ν hν`. Establish `hμ : (ν.map e.symm).IsHaarMeasure` using `ContinuousMulEquiv.isHaarMeasure_map ν e.symm`. Establish `hr : (ν.map e.symm).IsMulRightInvariant` using `h _ hμ`. Establish `he : Measurable e` using `e.continuous.measurable`. Establish `hes : Measurable e.symm` using `e.symm.continuous.measurable`.

Establish `hν' : ν = (ν.map e.symm).map e`. Rewrite using `[Measure.map_map he hes]`. Establish `: (e : G → H) ∘ e.symm = id` using `funext fun x => e.apply_symm_apply x`. Rewrite using `[this, Measure.map_id]`. Use `⟨fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[hν', Measure.map_map (measurable_mul_const g) he]`. Establish `hc : (fun x => x * g) ∘ (e : G → H) = (e : G → H) ∘ (fun x => x * e.symm g)`. Use function extensionality and compare the values at `x`. Simplify using `[map_mul]`. Rewrite using `[hc, ← Measure.map_map he (measurable_mul_const _), hr.map_mul_right_eq_self (e.symm g)]`.
-/
theorem transferStatement_holds : HaarRightInvTransfer := by
  intro G H _ _ _ _ _ _ _ _ _ _ _ _ _ _ e h ν hν
  have hμ : (ν.map e.symm).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map ν e.symm
  have hr : (ν.map e.symm).IsMulRightInvariant := h _ hμ
  have he : Measurable e := e.continuous.measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  have hν' : ν = (ν.map e.symm).map e := by
    rw [Measure.map_map he hes]
    have : (e : G → H) ∘ e.symm = id := funext fun x => e.apply_symm_apply x
    rw [this, Measure.map_id]
  refine ⟨fun g => ?_⟩
  rw [hν', Measure.map_map (measurable_mul_const g) he]
  have hc : (fun x => x * g) ∘ (e : G → H) = (e : G → H) ∘ (fun x => x * e.symm g) := by
    funext x; simp [map_mul]
  rw [hc, ← Measure.map_map he (measurable_mul_const _), hr.map_mul_right_eq_self (e.symm g)]

end Formalism.IndefR.Leaf.Proofs
