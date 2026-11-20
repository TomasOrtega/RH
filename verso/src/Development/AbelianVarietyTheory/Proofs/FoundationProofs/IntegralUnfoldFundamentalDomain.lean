import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ _ μ _ Λ _ Fd hFd g hg`. Establish `hv : ∀ (y : Λ) (z : V), y +ᵥ z = z + y` using `fun y z => by`. Rewrite using `[add_comm]`. Both sides reduce to the same expression. Establish `hm : ∀ y : Λ, AEStronglyMeasurable (fun z => g (z + y)) (μ.restrict Fd)` using `fun y => by`.

Establish `h` using `(hg.comp_add_left (y : V)).aestronglyMeasurable`. Simplify using `only [add_comm (y : V)] at h`. Conclude with `h.restrict`. Establish `hfin : ∑' y : Λ, ∫⁻ z in Fd, ‖g (z + y)‖ₑ ∂μ ≠ ⊤`. Establish `h` using `hFd.lintegral_eq_tsum'' (fun z => ‖g z‖ₑ)`.

Simplify using `only [hv] at h`. Rewrite using `[← h]`. Conclude with `hg.2.ne`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: AEMeasurable (fun z => ∑' y : Λ, g (z + y)) (μ.restrict Fd)` using `AEMeasurable.tsum fun y => (hm y).aemeasurable`.

Conclude with `this.aestronglyMeasurable`. Use `lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_` and prove the remaining obligations. Rewrite using `[lintegral_tsum fun y => (hm y).enorm]`. Conclude with `hfin.lt_top`. Rewrite using `[integral_tsum hm hfin, hFd.integral_eq_tsum'' g hg]`.

Simplify using `only [hv]`.
-/
theorem integral_unfold_fundamentalDomain : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  intro V _ _ _ _ μ _ Λ _ Fd hFd g hg
  have hv : ∀ (y : Λ) (z : V), y +ᵥ z = z + y := fun y z => by
    rw [add_comm]; rfl
  have hm : ∀ y : Λ, AEStronglyMeasurable (fun z => g (z + y)) (μ.restrict Fd) := fun y => by
    have h := (hg.comp_add_left (y : V)).aestronglyMeasurable
    simp only [add_comm (y : V)] at h
    exact h.restrict
  have hfin : ∑' y : Λ, ∫⁻ z in Fd, ‖g (z + y)‖ₑ ∂μ ≠ ⊤ := by
    have h := hFd.lintegral_eq_tsum'' (fun z => ‖g z‖ₑ)
    simp only [hv] at h
    rw [← h]
    exact hg.2.ne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : AEMeasurable (fun z => ∑' y : Λ, g (z + y)) (μ.restrict Fd) :=
      AEMeasurable.tsum fun y => (hm y).aemeasurable
    exact this.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun y => (hm y).enorm]
    exact hfin.lt_top
  · rw [integral_tsum hm hfin, hFd.integral_eq_tsum'' g hg]
    simp only [hv]

end GlobalTheory
