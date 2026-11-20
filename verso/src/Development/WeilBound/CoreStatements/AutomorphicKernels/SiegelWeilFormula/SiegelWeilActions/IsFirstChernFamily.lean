import Mathlib

noncomputable section

open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.Act

def LatHaar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : AddSubgroup V) [Countable Γ] (φ : V ≃ₜ+ V), (∀ x, φ x ∈ Γ ↔ x ∈ Γ) →
    ∀ s : Set V, IsAddFundamentalDomain Γ s μ → μ s ≠ 0 → μ s ≠ ⊤ → μ.map φ = μ

/- English proof (translation)
Unfold `LatHaar`. Introduce `V _ _ _ _ _ _ _ _ μ _ Γ _ φ hΓ s hs hs0 hstop`. Establish `hmeas : Measurable φ` using `φ.continuous.measurable`. Establish `: (μ.map φ).IsAddHaarMeasure` using `inferInstance`. Establish `hc` using `Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ`.

Establish `hqmp : Measure.QuasiMeasurePreserving φ μ μ`. Use `⟨hmeas, fun t ht => ?_⟩` and prove the remaining obligations. Rewrite using `[hc, Measure.smul_apply, ht, smul_zero]`. Set `e : Γ → Γ` to `fun g => ⟨φ.symm g, (hΓ _).1 (by simp)⟩`. Establish `he : Function.Bijective e`.

Prove the components needed by the constructor for the conclusion. Introduce `g g' h`. Establish `h2 : φ (φ.symm (g : V)) = φ (φ.symm (g' : V))` using `congrArg (fun x : Γ => φ (x : V)) h`. Conclude with `Subtype.ext (by simpa using h2)`. Introduce `g`.

Conclude with `⟨⟨φ g, (hΓ g).2 g.2⟩, Subtype.ext (by simp [e])⟩`. Establish `hef : ∀ g : Γ, Function.Semiconj φ (e g +ᵥ ·) (g +ᵥ ·)`. Introduce `g x`. Use `show φ ((e g : V) + x) = (g : V) + φ x`. Rewrite using `[map_add]`.

Simplify using `[e]`. Establish `hs' : IsAddFundamentalDomain Γ (φ ⁻¹' s) μ` using `hs.preimage_of_equiv hqmp he hef`. Establish `heq : μ (φ ⁻¹' s) = μ s` using `hs'.measure_eq hs`. Establish `hνs : (μ.map φ) s = μ s`. Rewrite using `[← heq]`.

Conclude with `(φ.toHomeomorph.toMeasurableEquiv).map_apply s`. Rewrite `hνs` using `[hc, Measure.coe_nnreal_smul_apply]`. Establish `h1 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) = 1`. Establish `h3 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) * μ s = 1 * μ s`. Rewrite using `[one_mul]`.

Conclude with `hνs`. Conclude with `(ENNReal.mul_left_inj hs0 hstop).1 h3`. Establish `h2 : Measure.addHaarScalarFactor (μ.map φ) μ = 1` using `by exact_mod_cast h1`. Rewrite using `[hc, h2, one_smul]`.
-/
theorem latHaar : LatHaar := by
  unfold LatHaar
  intro V _ _ _ _ _ _ _ _ μ _ Γ _ φ hΓ s hs hs0 hstop
  have hmeas : Measurable φ := φ.continuous.measurable
  have : (μ.map φ).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  have hqmp : Measure.QuasiMeasurePreserving φ μ μ := by
    refine ⟨hmeas, fun t ht => ?_⟩
    rw [hc, Measure.smul_apply, ht, smul_zero]
  let e : Γ → Γ := fun g => ⟨φ.symm g, (hΓ _).1 (by simp)⟩
  have he : Function.Bijective e := by
    constructor
    · intro g g' h
      have h2 : φ (φ.symm (g : V)) = φ (φ.symm (g' : V)) := congrArg (fun x : Γ => φ (x : V)) h
      exact Subtype.ext (by simpa using h2)
    · intro g
      exact ⟨⟨φ g, (hΓ g).2 g.2⟩, Subtype.ext (by simp [e])⟩
  have hef : ∀ g : Γ, Function.Semiconj φ (e g +ᵥ ·) (g +ᵥ ·) := by
    intro g x
    show φ ((e g : V) + x) = (g : V) + φ x
    rw [map_add]
    simp [e]
  have hs' : IsAddFundamentalDomain Γ (φ ⁻¹' s) μ := hs.preimage_of_equiv hqmp he hef
  have heq : μ (φ ⁻¹' s) = μ s := hs'.measure_eq hs
  have hνs : (μ.map φ) s = μ s := by
    rw [← heq]
    exact (φ.toHomeomorph.toMeasurableEquiv).map_apply s
  rw [hc, Measure.coe_nnreal_smul_apply] at hνs
  have h1 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) = 1 := by
    have h3 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) * μ s = 1 * μ s := by
      rw [one_mul]
      exact hνs
    exact (ENNReal.mul_left_inj hs0 hstop).1 h3
  have h2 : Measure.addHaarScalarFactor (μ.map φ) μ = 1 := by exact_mod_cast h1
  rw [hc, h2, one_smul]

end PositivityTheory.SiegelWeilFormula.Act

end
