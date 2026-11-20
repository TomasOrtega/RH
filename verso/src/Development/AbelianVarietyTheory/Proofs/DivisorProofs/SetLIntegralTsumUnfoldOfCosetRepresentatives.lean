import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine

/- English proof (translation)
Use `haveI : Countable Λ := (Subgroup.inclusion_injective hle).countable`. Set `e0 : T × Λ → Γ` to `fun p => Subgroup.inclusion hle p.2 * p.1.1`. Establish `hbij : Function.Bijective e0`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨t, ht⟩, l⟩ ⟨⟨s, hs⟩, m⟩ h`.

Simplify using `only [e0] at h`. Establish `hts : t = s`. Use `(hT (Subgroup.inclusion hle l * t)).unique ⟨ht, ?_⟩ ⟨hs, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Substitute `hts` using the available equality. Use `Subgroup.inclusion_injective hle (mul_right_cancel h)` as an intermediate fact. Substitute `this` using the available equality. Both sides reduce to the same expression.

Introduce `γ`. Take `⟨t, ⟨ht, hm⟩, -⟩` from `hT γ`. Use `⟨(⟨t, ht⟩, ⟨_, hm⟩), ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[e0]`.

Establish `h1 : ∀ t : T, ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ = ∑' l : Λ, ∫⁻ g in D ∩ (e0 (t, l)) • 𝓕, f g ∂μ`. Introduce `t`. Establish `h2 : ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ = ∫⁻ g in t.1 • 𝓕, f g ∂μ` using `(measurePreserving_smul t.1 μ).setLIntegral_comp_emb (measurableEmbedding_const_smul t.1) f 𝓕`. Rewrite using `[h2, hD.setLIntegral_eq_tsum' f]`. Use `tsum_congr fun l => ?_` and prove the remaining obligations.

Establish `h3 : l • t.1 • 𝓕 = (e0 (t, l)) • 𝓕`. Simplify using `only [e0, mul_smul]`. Both sides reduce to the same expression. Rewrite using `[h3, Set.inter_comm]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Conclude with `hinv _ (l⁻¹).2 x`. Rewrite using `[lintegral_tsum (f := fun (t : T) g => f (t.1.1 * g)) (fun t : T => (hf.comp (measurable_const_mul t.1.1)).aemeasurable), hF.setLIntegral_eq_tsum f D, ← (Equiv.ofBijective e0 hbij).tsum_eq, ENNReal.tsum_prod']`. Conclude with `tsum_congr h1`.
-/
theorem setLIntegral_tsum_unfold (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) (Γ Λ : Subgroup G) [Countable Γ] (T : Set Γ) (𝓕 D : Set G)
    (hμ : μ.IsHaarMeasure) (hle : Λ ≤ Γ)
    (hT : ∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ)
    (hF : IsFundamentalDomain Γ 𝓕 μ) (hD : IsFundamentalDomain Λ D μ)
    (f : G → ℝ≥0∞) (hf : Measurable f) (hinv : ∀ γ ∈ Λ, ∀ g, f (γ * g) = f g) :
    ∫⁻ g in 𝓕, ∑' t : T, f (t.1.1 * g) ∂μ = ∫⁻ g in D, f g ∂μ := by
  haveI : Countable Λ := (Subgroup.inclusion_injective hle).countable
  let e0 : T × Λ → Γ := fun p => Subgroup.inclusion hle p.2 * p.1.1
  have hbij : Function.Bijective e0 := by
    constructor
    · rintro ⟨⟨t, ht⟩, l⟩ ⟨⟨s, hs⟩, m⟩ h
      simp only [e0] at h
      have hts : t = s := by
        refine (hT (Subgroup.inclusion hle l * t)).unique ⟨ht, ?_⟩ ⟨hs, ?_⟩
        · simp
        · rw [h]; simp
      subst hts
      have := Subgroup.inclusion_injective hle (mul_right_cancel h)
      subst this
      rfl
    · intro γ
      obtain ⟨t, ⟨ht, hm⟩, -⟩ := hT γ
      refine ⟨(⟨t, ht⟩, ⟨_, hm⟩), ?_⟩
      apply Subtype.ext
      simp [e0]
  have h1 : ∀ t : T, ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ
      = ∑' l : Λ, ∫⁻ g in D ∩ (e0 (t, l)) • 𝓕, f g ∂μ := by
    intro t
    have h2 : ∫⁻ g in 𝓕, f (t.1.1 * g) ∂μ = ∫⁻ g in t.1 • 𝓕, f g ∂μ :=
      (measurePreserving_smul t.1 μ).setLIntegral_comp_emb (measurableEmbedding_const_smul t.1) f 𝓕
    rw [h2, hD.setLIntegral_eq_tsum' f]
    refine tsum_congr fun l => ?_
    have h3 : l • t.1 • 𝓕 = (e0 (t, l)) • 𝓕 := by
      simp only [e0, mul_smul]
      rfl
    rw [h3, Set.inter_comm]
    refine lintegral_congr fun x => ?_
    exact hinv _ (l⁻¹).2 x
  rw [lintegral_tsum (f := fun (t : T) g => f (t.1.1 * g)) (fun t : T => (hf.comp (measurable_const_mul t.1.1)).aemeasurable),
    hF.setLIntegral_eq_tsum f D, ← (Equiv.ofBijective e0 hbij).tsum_eq, ENNReal.tsum_prod']
  exact tsum_congr h1

end GlobalTheory.ResLine
