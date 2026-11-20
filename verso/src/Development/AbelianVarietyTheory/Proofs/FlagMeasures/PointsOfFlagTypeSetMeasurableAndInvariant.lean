import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas

/- English proof (translation)
Introduce `I a j B hB`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hm, he⟩` from `type_measurable I a j`. Establish `: typeSet I j B = {x : I.GA | ∃ τ, HasType I x j τ} ∩ s ⁻¹' B`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, h1, h2⟩`. Conclude with `⟨⟨τ, h2⟩, by rw [Set.mem_preimage, he x τ h2]; exact h1⟩`. Introduce and unpack `⟨⟨τ, h2⟩, h1⟩`. Rewrite `h1` using `[Set.mem_preimage, he x τ h2]`.

Conclude with `⟨τ, h1, h2⟩`. Rewrite using `[this]`. Conclude with `hm.inter (hs hB)`. Introduce and unpack `γ ⟨g, hg, h1, h2⟩ x ⟨τ, hτ, h⟩`. Conclude with `⟨τ, hτ, ((GlobalTheory.PointEquivariance.equivariance I x g γ hg h1 h2).2.2.2.2.1 a j τ).2 h⟩`.

Introduce and unpack `x ⟨τ, hτ, h⟩ k hk`. Use `⟨τ, hτ, GlobalTheory.PointEquivariance.hasType_of I x (x.1, x.2 * k) (OrderIso.refl _) ?_ (fun _ => rfl) (fun _ => rfl) j τ h⟩` and prove the remaining obligations. Establish `e : ((x.1, x.2 * k) : I.GA) = x * (1, k)` using `Prod.ext (mul_one _).symm rfl`. Rewrite using `[e]`. Conclude with `(GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (1, k)).1 hk`.
-/
theorem typeSet_measurable_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  intro I a j B hB
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs, hm, he⟩ := type_measurable I a j
    have : typeSet I j B = {x : I.GA | ∃ τ, HasType I x j τ} ∩ s ⁻¹' B := by
      ext x
      constructor
      · rintro ⟨τ, h1, h2⟩
        exact ⟨⟨τ, h2⟩, by rw [Set.mem_preimage, he x τ h2]; exact h1⟩
      · rintro ⟨⟨τ, h2⟩, h1⟩
        rw [Set.mem_preimage, he x τ h2] at h1
        exact ⟨τ, h1, h2⟩
    rw [this]
    exact hm.inter (hs hB)
  · rintro γ ⟨g, hg, h1, h2⟩ x ⟨τ, hτ, h⟩
    exact ⟨τ, hτ, ((GlobalTheory.PointEquivariance.equivariance I x g γ hg h1 h2).2.2.2.2.1 a j τ).2 h⟩
  · rintro x ⟨τ, hτ, h⟩ k hk
    refine ⟨τ, hτ, GlobalTheory.PointEquivariance.hasType_of I x (x.1, x.2 * k) (OrderIso.refl _) ?_
      (fun _ => rfl) (fun _ => rfl) j τ h⟩
    have e : ((x.1, x.2 * k) : I.GA) = x * (1, k) := Prod.ext (mul_one _).symm rfl
    rw [e]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (1, k)).1 hk

end GlobalTheory.FlagMeas
