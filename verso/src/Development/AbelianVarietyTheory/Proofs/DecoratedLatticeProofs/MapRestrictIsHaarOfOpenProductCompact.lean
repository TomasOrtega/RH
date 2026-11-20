import Mathlib
open MeasureTheory

namespace GlobalTheory.ChainOnto

/- English proof (translation)
Introduce `G B _ _ _ _ _ _ _ _ _ _ _ ν _ A i p hA hi hp hpi hiA hK`. Establish `hpm : Measurable p` using `hp.measurable`. Establish `hAm : MeasurableSet (A : Set G)` using `hA.measurableSet`. Establish `happ : ∀ S : Set B, MeasurableSet S → Measure.map p (ν.restrict A) S = ν (p ⁻¹' S ∩ A)`. Introduce `S hS`.

Rewrite using `[Measure.map_apply hpm hS, Measure.restrict_apply (hpm hS)]`. Establish `hpre : ∀ S : Set B, p ⁻¹' S ∩ A = (fun x : G × G => x.1 * x.2) '' ((i '' S) ×ˢ {g : G | g ∈ A ∧ p g = 1})`. Introduce `S`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hgS, hgA⟩`. Use `⟨(i (p g), (i (p g))⁻¹ * g), ⟨⟨p g, hgS, rfl⟩, ?_, ?_⟩, by simp⟩` and prove the remaining obligations. Conclude with `A.mul_mem (A.inv_mem (hiA _)) hgA`. Simplify using `[hpi]`. Introduce and unpack `⟨⟨x, y⟩, ⟨⟨s, hs, rfl⟩, hyA, hy1⟩, rfl⟩`.

Use `⟨?_, A.mul_mem (hiA s) hyA⟩` and prove the remaining obligations. Simplify using `[hpi, hy1, hs]`. Use `{ lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }` and prove the remaining obligations. Introduce `C hC`. Rewrite using `[happ C hC.isClosed.measurableSet, hpre C]`.

Conclude with `((hC.image hi).prod hK).image continuous_mul |>.measure_lt_top`. Introduce `b`. Use extensionality with `S hS`. Rewrite using `[Measure.map_apply (measurable_const_mul b) hS, happ _ (measurable_const_mul b hS), happ S hS]`. Establish `: p ⁻¹' ((fun x => b * x) ⁻¹' S) ∩ A = (fun g => i b * g) ⁻¹' (p ⁻¹' S ∩ A)`.

Use extensionality with `g`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, map_mul, hpi, SetLike.mem_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h1, A.mul_mem (hiA b) h2⟩`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Use `A.mul_mem (A.inv_mem (hiA b)) h2` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, measure_preimage_mul]`.

Introduce `U hU hne`. Rewrite using `[happ U hU.measurableSet]`. Take `⟨u, hu⟩` from `hne`. Conclude with `(hU.preimage hp |>.inter hA).measure_ne_zero ν ⟨i u, by simp [hpi, hu], hiA u⟩`.
-/
theorem map_restrict_isHaar : ∀ (G B : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [MeasurableSpace B] [BorelSpace B] [T2Space B] (ν : Measure G) [ν.IsHaarMeasure] (A : Subgroup G) (i : B →* G) (p : G →* B), IsOpen (A : Set G) → Continuous i → Continuous p → (∀ b, p (i b) = b) → (∀ b, i b ∈ A) → IsCompact {g : G | g ∈ A ∧ p g = 1} → (Measure.map p (ν.restrict A)).IsHaarMeasure := by
  intro G B _ _ _ _ _ _ _ _ _ _ _ ν _ A i p hA hi hp hpi hiA hK
  have hpm : Measurable p := hp.measurable
  have hAm : MeasurableSet (A : Set G) := hA.measurableSet
  have happ : ∀ S : Set B, MeasurableSet S → Measure.map p (ν.restrict A) S = ν (p ⁻¹' S ∩ A) := by
    intro S hS
    rw [Measure.map_apply hpm hS, Measure.restrict_apply (hpm hS)]

  have hpre : ∀ S : Set B, p ⁻¹' S ∩ A = (fun x : G × G => x.1 * x.2) '' ((i '' S) ×ˢ {g : G | g ∈ A ∧ p g = 1}) := by
    intro S
    ext g
    constructor
    · rintro ⟨hgS, hgA⟩
      refine ⟨(i (p g), (i (p g))⁻¹ * g), ⟨⟨p g, hgS, rfl⟩, ?_, ?_⟩, by simp⟩
      · exact A.mul_mem (A.inv_mem (hiA _)) hgA
      · simp [hpi]
    · rintro ⟨⟨x, y⟩, ⟨⟨s, hs, rfl⟩, hyA, hy1⟩, rfl⟩
      refine ⟨?_, A.mul_mem (hiA s) hyA⟩
      simp [hpi, hy1, hs]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro C hC
    rw [happ C hC.isClosed.measurableSet, hpre C]
    exact ((hC.image hi).prod hK).image continuous_mul |>.measure_lt_top
  · intro b
    ext S hS
    rw [Measure.map_apply (measurable_const_mul b) hS, happ _ (measurable_const_mul b hS), happ S hS]
    have : p ⁻¹' ((fun x => b * x) ⁻¹' S) ∩ A = (fun g => i b * g) ⁻¹' (p ⁻¹' S ∩ A) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, hpi, SetLike.mem_coe]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, A.mul_mem (hiA b) h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have := A.mul_mem (A.inv_mem (hiA b)) h2
        simpa using this
    rw [this, measure_preimage_mul]
  · intro U hU hne
    rw [happ U hU.measurableSet]
    obtain ⟨u, hu⟩ := hne
    exact (hU.preimage hp |>.inter hA).measure_ne_zero ν ⟨i u, by simp [hpi, hu], hiA u⟩

end GlobalTheory.ChainOnto
