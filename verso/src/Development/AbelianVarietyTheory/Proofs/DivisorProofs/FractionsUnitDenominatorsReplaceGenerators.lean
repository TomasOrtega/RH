import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `L _ ψ V P s₀ h1 h2`. Use `choose b d hb hd hd0 hdV hx using h1`. Set `t : Finset L` to `(s₀.attach.image (fun x => b x.1 x.2)) ∪ (s₀.attach.image (fun x => d x.1 x.2))`. Use `⟨t, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx'`.

Simplify using `only [t, Finset.mem_union, Finset.mem_image] at hx'`. Break down `hx' with ⟨⟨y, hy⟩, _, rfl⟩ | ⟨⟨y, hy⟩, _, rfl⟩` into its components or cases. Conclude with `hb y hy`. Conclude with `hd y hy`. Set `S : Subring L` to `Subring.closure (Set.range ψ ∪ (t : Set L))`.

Establish `hVone : (1 : L)⁻¹ ∈ V` using `by simpa using V.one_mem`. Set `F : Subring L` to `{ carrier := {y | ∃ b ∈ S, ∃ d ∈ S, d ≠ 0 ∧ d⁻¹ ∈ V ∧ y = b / d} mul_mem' := by`. Introduce and unpack `_ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩`. Use `⟨b₁ * b₂, S.mul_mem hb₁ hb₂, d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv]`.

Conclude with `mul_mem i₁ i₂`. Rewrite using `[div_mul_div_comm]`. Use the proof step `one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩`. Use the proof step `add_mem' := by`. Introduce and unpack `_ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩`.

Use `⟨b₁ * d₂ + d₁ * b₂, S.add_mem (S.mul_mem hb₁ hd₂) (S.mul_mem hd₁ hb₂), d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv]`. Conclude with `mul_mem i₁ i₂`. Rewrite using `[div_add_div _ _ h₁ h₂]`. Use the proof step `zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩`.

Use the proof step `neg_mem' := by`. Introduce and unpack `_ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩`. Conclude with `⟨-b₁, S.neg_mem hb₁, d₁, hd₁, h₁, i₁, by rw [neg_div]⟩ }`. Establish `htS : ∀ x ∈ t, x ∈ S` using `fun x hx' => Subring.subset_closure (Or.inr hx')`. Establish `hle : Subring.closure (Set.range ψ ∪ (s₀ : Set L)) ≤ F`.

Rewrite using `[Subring.closure_le]`. Introduce and unpack `x (⟨c, rfl⟩ | hx')`. Conclude with `⟨ψ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), 1, S.one_mem, one_ne_zero, hVone, by simp⟩`. Use `⟨b x hx', htS _ ?_, d x hx', htS _ ?_, hd0 x hx', hdV x hx', hx x hx'⟩` and prove the remaining obligations. Conclude with `Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y : s₀ => b y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))`.

Conclude with `Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y : s₀ => d y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))`. Introduce `s hs`. Take `⟨B, hB, D, hD, hD0, hDV, rfl⟩` from `h2 s hs`. Take `⟨b₁, hb₁, b₂, hb₂, hb₂0, hb₂V, rfl⟩` from `hle hB`. Take `⟨d₁, hd₁, d₂, hd₂, hd₂0, hd₂V, rfl⟩` from `hle hD`.

Establish `hd₁0 : d₁ ≠ 0`. Introduce and unpack `rfl; exact hD0 (by simp)`. Establish `hd₁V : d₁⁻¹ ∈ V`. Establish `: d₁⁻¹ = (d₁ / d₂)⁻¹ * d₂⁻¹`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `mul_mem hDV hd₂V`. Use `⟨b₁ * d₂, S.mul_mem hb₁ hd₂, b₂ * d₁, S.mul_mem hb₂ hd₁, mul_ne_zero hb₂0 hd₁0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv]`. Conclude with `mul_mem hb₂V hd₁V`.

Rewrite using `[div_div_div_eq]`.
-/
theorem fractions_unit_denominators_replace_generators : ∀ (L : Type) [Field L] (ψ : ℂ →+* L) (V : ValuationSubring L) (P : L → Prop) (s₀ : Finset L), (∀ x ∈ s₀, ∃ b d : L, P b ∧ P d ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ x = b / d) → (∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑s₀), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑s₀), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d) → ∃ t : Finset L, (∀ x ∈ t, P x) ∧ ∀ s ∈ V, ∃ b ∈ Subring.closure (Set.range ψ ∪ ↑t), ∃ d ∈ Subring.closure (Set.range ψ ∪ ↑t), d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro L _ ψ V P s₀ h1 h2
  classical
  choose b d hb hd hd0 hdV hx using h1
  let t : Finset L := (s₀.attach.image (fun x => b x.1 x.2)) ∪ (s₀.attach.image (fun x => d x.1 x.2))
  refine ⟨t, ?_, ?_⟩
  · intro x hx'
    simp only [t, Finset.mem_union, Finset.mem_image] at hx'
    rcases hx' with ⟨⟨y, hy⟩, _, rfl⟩ | ⟨⟨y, hy⟩, _, rfl⟩
    · exact hb y hy
    · exact hd y hy
  · let S : Subring L := Subring.closure (Set.range ψ ∪ (t : Set L))
    have hVone : (1 : L)⁻¹ ∈ V := by simpa using V.one_mem
    let F : Subring L :=
      { carrier := {y | ∃ b ∈ S, ∃ d ∈ S, d ≠ 0 ∧ d⁻¹ ∈ V ∧ y = b / d}
        mul_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * b₂, S.mul_mem hb₁ hb₂, d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_mul_div_comm]
        one_mem' := ⟨1, S.one_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        add_mem' := by
          rintro _ _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩ ⟨b₂, hb₂, d₂, hd₂, h₂, i₂, rfl⟩
          refine ⟨b₁ * d₂ + d₁ * b₂, S.add_mem (S.mul_mem hb₁ hd₂) (S.mul_mem hd₁ hb₂),
            d₁ * d₂, S.mul_mem hd₁ hd₂, mul_ne_zero h₁ h₂, ?_, ?_⟩
          · rw [mul_inv]; exact mul_mem i₁ i₂
          · rw [div_add_div _ _ h₁ h₂]
        zero_mem' := ⟨0, S.zero_mem, 1, S.one_mem, one_ne_zero, hVone, by simp⟩
        neg_mem' := by
          rintro _ ⟨b₁, hb₁, d₁, hd₁, h₁, i₁, rfl⟩
          exact ⟨-b₁, S.neg_mem hb₁, d₁, hd₁, h₁, i₁, by rw [neg_div]⟩ }
    have htS : ∀ x ∈ t, x ∈ S := fun x hx' => Subring.subset_closure (Or.inr hx')
    have hle : Subring.closure (Set.range ψ ∪ (s₀ : Set L)) ≤ F := by
      rw [Subring.closure_le]
      rintro x (⟨c, rfl⟩ | hx')
      · exact ⟨ψ c, Subring.subset_closure (Or.inl ⟨c, rfl⟩), 1, S.one_mem, one_ne_zero, hVone, by simp⟩
      · refine ⟨b x hx', htS _ ?_, d x hx', htS _ ?_, hd0 x hx', hdV x hx', hx x hx'⟩
        · exact Finset.mem_union_left _ (Finset.mem_image_of_mem (fun y : s₀ => b y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
        · exact Finset.mem_union_right _ (Finset.mem_image_of_mem (fun y : s₀ => d y.1 y.2) (Finset.mem_attach _ ⟨x, hx'⟩))
    intro s hs
    obtain ⟨B, hB, D, hD, hD0, hDV, rfl⟩ := h2 s hs
    obtain ⟨b₁, hb₁, b₂, hb₂, hb₂0, hb₂V, rfl⟩ := hle hB
    obtain ⟨d₁, hd₁, d₂, hd₂, hd₂0, hd₂V, rfl⟩ := hle hD
    have hd₁0 : d₁ ≠ 0 := by
      rintro rfl; exact hD0 (by simp)
    have hd₁V : d₁⁻¹ ∈ V := by
      have : d₁⁻¹ = (d₁ / d₂)⁻¹ * d₂⁻¹ := by
        field_simp
      rw [this]; exact mul_mem hDV hd₂V
    refine ⟨b₁ * d₂, S.mul_mem hb₁ hd₂, b₂ * d₁, S.mul_mem hb₂ hd₁, mul_ne_zero hb₂0 hd₁0, ?_, ?_⟩
    · rw [mul_inv]; exact mul_mem hb₂V hd₁V
    · rw [div_div_div_eq]

end GlobalTheory
