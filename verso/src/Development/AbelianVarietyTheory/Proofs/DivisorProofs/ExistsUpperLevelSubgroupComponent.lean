import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ r U C _ _ M c`. Establish `h1 : M.tr 1 c ∈ (M.comp c).Γ`. Establish `h` using `M.tr_mul 1 1 c`. Simplify using `only [one_mul, one_smul] at h`. Establish `h' : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ`.

Simplify `h` using `[mul_inv_rev, mul_assoc]`. Simplify using `using inv_mem h'`. Use `⟨{ carrier := M.upper c mul_mem' := ?_ one_mem' := ?_ inv_mem' := ?_ }, fun β => Iff.rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `a b ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, γ', hγ', rfl⟩`. Establish `hc` using `(M.tr_conj u c γ').1 hγ'`.

Rewrite `hc` using `[hu]`. Establish `hm` using `M.tr_mul u v c`. Rewrite `hm` using `[mul_smul, hv, hu]`. Use `⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * γ' * (M.tr u c)⁻¹) * (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem (mul_mem hγ hc) (inv_mem hm)`.

Use `group`. Conclude with `⟨1, one_smul _ _, (M.tr 1 c)⁻¹, inv_mem h1, by group⟩`. Introduce and unpack `a ⟨u, hu, γ, hγ, rfl⟩`. Establish `hu' : u⁻¹ • c = c` using `by rw [inv_smul_eq_iff, hu]`. Establish `hm` using `M.tr_mul u⁻¹ u c`.

Rewrite `hm` using `[inv_mul_cancel, one_smul, hu]`. Establish `hw : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ`. Use `mul_mem (inv_mem h1) hm` as an intermediate fact. Simplify `inv_mem this` using `[mul_assoc]`. Establish `hc` using `(M.tr_conj u⁻¹ c γ⁻¹).1 (inv_mem hγ)`.

Rewrite `hc` using `[hu']`. Use `⟨u⁻¹, hu', (M.tr u⁻¹ c * M.tr u c)⁻¹ * (M.tr u⁻¹ c * γ⁻¹ * (M.tr u⁻¹ c)⁻¹), ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_mem (inv_mem hw) hc`. Use `group`. Introduce `γ hγ`.

Conclude with `⟨1, one_smul _ _, γ * (M.tr 1 c)⁻¹, mul_mem hγ (inv_mem h1), by group⟩`.
-/
theorem upperLevel_isSubgroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∃ G : Subgroup (GL (Fin r) E), (∀ β, β ∈ G ↔ β ∈ M.upper c) ∧ (M.comp c).Γ ≤ G := by
  intro E _ _ _ r U C _ _ M c
  have h1 : M.tr 1 c ∈ (M.comp c).Γ := by
    have h := M.tr_mul 1 1 c
    simp only [one_mul, one_smul] at h
    have h' : (M.tr 1 c)⁻¹ ∈ (M.comp c).Γ := by
      simpa [mul_inv_rev, mul_assoc] using h
    simpa using inv_mem h'
  refine ⟨{ carrier := M.upper c
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun β => Iff.rfl, ?_⟩
  · rintro a b ⟨u, hu, γ, hγ, rfl⟩ ⟨v, hv, γ', hγ', rfl⟩
    have hc := (M.tr_conj u c γ').1 hγ'
    rw [hu] at hc
    have hm := M.tr_mul u v c
    rw [mul_smul, hv, hu] at hm
    refine ⟨u * v, by rw [mul_smul, hv, hu], γ * (M.tr u c * γ' * (M.tr u c)⁻¹) *
      (M.tr (u * v) c * (M.tr u c * M.tr v c)⁻¹)⁻¹, ?_, ?_⟩
    · exact mul_mem (mul_mem hγ hc) (inv_mem hm)
    · group
  · exact ⟨1, one_smul _ _, (M.tr 1 c)⁻¹, inv_mem h1, by group⟩
  · rintro a ⟨u, hu, γ, hγ, rfl⟩
    have hu' : u⁻¹ • c = c := by rw [inv_smul_eq_iff, hu]
    have hm := M.tr_mul u⁻¹ u c
    rw [inv_mul_cancel, one_smul, hu] at hm
    have hw : M.tr u⁻¹ c * M.tr u c ∈ (M.comp c).Γ := by
      have := mul_mem (inv_mem h1) hm
      simpa [mul_assoc] using inv_mem this
    have hc := (M.tr_conj u⁻¹ c γ⁻¹).1 (inv_mem hγ)
    rw [hu'] at hc
    refine ⟨u⁻¹, hu', (M.tr u⁻¹ c * M.tr u c)⁻¹ * (M.tr u⁻¹ c * γ⁻¹ * (M.tr u⁻¹ c)⁻¹), ?_, ?_⟩
    · exact mul_mem (inv_mem hw) hc
    · group
  · intro γ hγ
    exact ⟨1, one_smul _ _, γ * (M.tr 1 c)⁻¹, mul_mem hγ (inv_mem h1), by group⟩

end GlobalTheory
