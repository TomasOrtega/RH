import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsCoordArithOfFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PowerBlockArith

variable {K : Type} [Fintype K] {ι : K → Type}

/- English proof (translation)
Establish `hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y`. Introduce `s hs`. Establish `: chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨p, rfl⟩`.

Conclude with `IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩`. Conclude with `this hs`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[blockFnField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩`.

Establish `hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)`. Establish `e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ = (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k)))`. Rewrite using `[mul_div_mul_right _ _ hP0]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))`. Conclude with `absurd hpq (by simp)`. Conclude with `absurd hpq (by simp)`. Take `rfl : k = k'` from `Option.some_injective _ hpq`. Conclude with `IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩`.

Rewrite using `[blockFnField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `t ⟨p, q, hpq, rfl⟩`. Conclude with `IntermediateField.subset_adjoin ℚ _ ⟨(⟨some p.1, p.2⟩ : Σ k, addIdx ι N k), (⟨some q.1, (hpq ▸ q.2 : ι q.1)⟩ : Σ k, addIdx ι N k), by simp [hpq], by cases p; cases q; simp at hpq; subst hpq; rfl⟩`.
-/
theorem blockFnField_addBlock {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m N : ℕ}
    {v : Fin N → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y a m) :
    blockFnField (addBlock y v) = blockFnField y := by
  have hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y := by
    intro s hs
    have : chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
    exact this hs
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩
    · have hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ =
          (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) := by
        rw [mul_div_mul_right _ _ hP0]
        rfl
      rw [e]
      exact div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · obtain rfl : k = k' := Option.some_injective _ hpq
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _
      ⟨(⟨some p.1, p.2⟩ : Σ k, addIdx ι N k), (⟨some q.1, (hpq ▸ q.2 : ι q.1)⟩ : Σ k, addIdx ι N k),
        by simp [hpq], by cases p; cases q; simp at hpq; subst hpq; rfl⟩

end PowerBlockArith

open PowerBlockArith in

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D a m N v hy hv hgen`. Establish `hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hy.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Use `show mConeMap _ (X _) = 0`.

Simplify using `[mConeMap, h0]`. Use `choose c hc using hnz`. Choose the witnesses or unpack the hypotheses as in `⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by`. Take `⟨u, -, hu⟩` from `hgen c hc`. Assume the negation of the conclusion as `h`.

Simplify using `only [not_exists, not_not] at h`. Simplify using `[h] at hu`. Conclude with `hF K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩ (fun k => by`. Consider the cases of `k with`. Consider the case `none => exact ⟨j₀, hj₀⟩`.

Consider the case `some k => exact ⟨c k, hc k⟩)`. Use the proof step `(blockFnField_addBlock c hc hv).symm hy`.
-/
theorem PowerBlockArith.proof (hF : CoordArithOfFnField.Statement) : PowerBlockArith.Statement := by
  intro K _ ι _ Ω _ _ y D a m N v hy hv hgen

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0]
  choose c hc using hnz

  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨u, -, hu⟩ := hgen c hc
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hu
  exact hF K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩
    (fun k => by
      cases k with
      | none => exact ⟨j₀, hj₀⟩
      | some k => exact ⟨c k, hc k⟩)
    (blockFnField_addBlock c hc hv).symm hy

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
