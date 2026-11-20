import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

open scoped Pointwise

namespace GlobalTheory.SnMass.SkewDom

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem im_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w : InfinitePlace E) (z : E) :
    (w.embedding (σ z)).im = -(w.embedding z).im := by
  rw [h.2.2.2 w.embedding z]; simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace E))
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem mem_skewLat_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ x ∈ I, σ x ∈ I)
    {θ : 𝓞 E} (hθ : (θ : E) + σ θ = 1) (c : ℝ) (z : InfinitePlace E → ℝ) :
    z ∈ (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) ↔
      ∃ b ∈ {b | ∃ x ∈ I, imV x = b}, z = (2 * c) • b := by
  change (∃ y ∈ I, (σ : E →+* E) y = -y ∧ ∀ w, z w = c * (w.embedding y).im) ↔ _
  simp only [AlgHom.coe_toRingHom]
  constructor
  · rintro ⟨y, hy, hs, hz⟩
    have hθy : (θ : E) * y ∈ I := by
      have := (I : Submodule (𝓞 E) E).smul_mem θ hy
      rwa [Algebra.smul_def] at this
    refine ⟨imV ((θ : E) * y), ⟨(θ : E) * y, hθy, rfl⟩, ?_⟩
    funext w
    have hy2 : y = (θ : E) * y - σ ((θ : E) * y) := by
      rw [map_mul, hs]; linear_combination (-y) * hθ
    rw [hz w, Pi.smul_apply, smul_eq_mul, imV]
    conv_lhs => rw [hy2]
    rw [map_sub, Complex.sub_im, im_sigma hcm]; ring
  · rintro ⟨b, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x - σ x, (I : Submodule (𝓞 E) E).sub_mem hx (hI x hx), ?_, fun w => ?_⟩
    · rw [map_sub, sigma_sigma hcm]; ring
    · rw [Pi.smul_apply, smul_eq_mul, imV, map_sub, Complex.sub_im, im_sigma hcm]; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem skewDom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : FractionalIdeal (𝓞 E)⁰ E), (∀ x ∈ I, σ x ∈ I) → ∀ (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ (c : ℝ), 0 < c → ∀ (D : Set (InfinitePlace E → ℝ)) (m : ℝ≥0∞), MeasurableSet D → (∀ y, ∃! l, l ∈ {b | ∃ x ∈ I, imV x = b} ∧ y + l ∈ D) → volume D = m → HasDom volume (skewLat (σ : E →+* E) I c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal ((2 * c) ^ Fintype.card (InfinitePlace E)) * m) := by
  intro F E _ _ _ _ _ σ hcm I hI θ hθ c hc D m hD hU hm
  have hmem := mem_skewLat_iff hcm hI hθ c
  have h2c : (2 * c) ≠ 0 := by positivity
  refine ⟨(2 * c) • D, hD.const_smul₀ _, fun v => ?_, ?_⟩
  · obtain ⟨l, ⟨hl, hlD⟩, hu⟩ := hU ((2 * c)⁻¹ • v)
    refine ⟨(2 * c) • l, ⟨(hmem _).2 ⟨l, hl, rfl⟩, ?_⟩, ?_⟩
    · refine Set.mem_smul_set.2 ⟨_, hlD, ?_⟩
      rw [smul_add, smul_inv_smul₀ h2c]
    · rintro l' ⟨hl', hl'D⟩
      obtain ⟨b, hb, rfl⟩ := (hmem _).1 hl'
      obtain ⟨d, hd, hdv⟩ := Set.mem_smul_set.1 hl'D
      have hbd : (2 * c)⁻¹ • v + b = d := by
        rw [← inv_smul_smul₀ h2c d, hdv, smul_add, inv_smul_smul₀ h2c]
      rw [hu b ⟨hb, hbd ▸ hd⟩]
  · rw [Measure.addHaar_smul, hm, Module.finrank_fintype_fun_eq_card, abs_of_pos (by positivity)]

end GlobalTheory.SnMass.SkewDom
