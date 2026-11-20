import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DstInvContinuousOn
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAtStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hR hS`. Take `⟨hz, hT, -, -, hW, hN, hG, hq⟩` from `hS`. Establish `hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r`. Take `⟨h0, h1⟩` from `Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN`. Conclude with `Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq`.

Establish `hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}`. Use `(Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `hrestr : νq.restrict {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} = νq` using `Measure.restrict_eq_self_of_ae_mem hae`.

Establish `hcont : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq`. Introduce `V _ _ φ hφ`. Establish `hof : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r))` using `continuous_id`. Establish `h1 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r}` using `hφ.comp hof.continuousOn (fun x hx => hx)`. Establish `h2` using `h1.aestronglyMeasurable (μ := νq) hmeas`.

Rewrite `h2` using `[hrestr]`. Then use the resulting hypothesis. Use `⟨hae, hcont, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Conclude with `(hcont ℝ _ (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable`. Introduce `l hl w hw`.

Conclude with `hcont Wp _ (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1`.
-/
theorem quotMeas_ae_mem_and_measurable : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)), R.IsDS ε mu → SideG k r z π u μW μN μG νq → (∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r) ∧ (∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V), ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq) ∧ (∀ a, AEMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => lenA k r z (Matrix.of x) a) νq) ∧ ∀ l, IsBes R z π l → ∀ w ∈ R.sm, AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => l (R.σ (Matrix.of x) w)) νq := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq hR hS
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  have hae : ∀ᵐ x ∂νq, (Matrix.of x) ∈ GG k r := by
    obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
    exact Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  have hmeas : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} := by
    convert (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl using 1
    ext x
    simp
  have hrestr : νq.restrict {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} = νq :=
    Measure.restrict_eq_self_of_ae_mem hae
  have hcont : ∀ (V : Type) [NormedAddCommGroup V] [SecondCountableTopology V] (φ : Mx k r → V),
      ContinuousOn φ (GG k r) → AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x)) νq := by
    intro V _ _ φ hφ
    have hof : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mx k r)) := continuous_id
    have h1 : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => φ (Matrix.of x))
        {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ GG k r} :=
      hφ.comp hof.continuousOn (fun x hx => hx)
    have h2 := h1.aestronglyMeasurable (μ := νq) hmeas
    rwa [hrestr] at h2
  refine ⟨hae, hcont, ?_, ?_⟩
  · intro a
    exact (hcont ℝ _ (GlobalTheory.LengthCont.lenA_continuousOn k r z hz hT a)).aemeasurable
  · intro l hl w hw
    exact hcont Wp _ (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 w hw).1

end GlobalTheory
