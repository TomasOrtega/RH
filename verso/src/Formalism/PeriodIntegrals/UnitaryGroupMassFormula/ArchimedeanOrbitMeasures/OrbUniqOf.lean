import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushCut

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

def OrbRep : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf →
    ∀ ν : Measure (TupI X), InvI X ν → ν (FbI X u' hT)ᶜ = 0 → LFI X ν →
      ∃ c : ENNReal, c ≠ ⊤ ∧ ν = c • X.measG.μGinf.map (orbM X u')

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP ν₁ ν₂ i₁ i₂ s₁ s₂ l₁ l₂ hne`. Take `⟨c₁, -, e₁⟩` from `h X u' ψ hT μinf νinf fibInf hP ν₁ i₁ s₁ l₁`. Take `⟨c₂, t₂, e₂⟩` from `h X u' ψ hT μinf νinf fibInf hP ν₂ i₂ s₂ l₂`. Establish `h0 : c₂ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `e₂` using `[zero_smul]`. Conclude with `hne e₂`. Use `⟨c₁ / c₂, ?_⟩` and prove the remaining obligations. Rewrite using `[e₁, e₂, smul_smul, ENNReal.div_mul_cancel h0 t₂]`.
-/
theorem orbUniq_of (h : OrbRep) : OrbUniq := by
  intro D X u' ψ hT μinf νinf fibInf hP ν₁ ν₂ i₁ i₂ s₁ s₂ l₁ l₂ hne
  obtain ⟨c₁, -, e₁⟩ := h X u' ψ hT μinf νinf fibInf hP ν₁ i₁ s₁ l₁
  obtain ⟨c₂, t₂, e₂⟩ := h X u' ψ hT μinf νinf fibInf hP ν₂ i₂ s₂ l₂
  have h0 : c₂ ≠ 0 := by
    rintro rfl; rw [zero_smul] at e₂; exact hne e₂
  refine ⟨c₁ / c₂, ?_⟩
  rw [e₁, e₂, smul_smul, ENNReal.div_mul_cancel h0 t₂]

end PI.AprimeInfW
