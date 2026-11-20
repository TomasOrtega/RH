import Mathlib

open MeasureTheory

namespace GlobalTheory.SeparatedSetCardBound

/- English proof (translation)
Use `letI : MeasurableSpace E := borel E`. Use `haveI : BorelSpace E := ⟨rfl⟩`. Take `⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure` from `⟨Measure.addHaar, inferInstance⟩`. Use `haveI := hμ`. Use `set d := Module.finrank ℝ E`.

Establish `hdisj : Set.PairwiseDisjoint (T : Set G) (fun h => Metric.ball (φ h) r)`. Introduce `a ha b hb hab`. Rewrite using `[Function.onFun, Set.disjoint_iff]`. Introduce and unpack `z ⟨hza, hzb⟩`. Establish `hs` using `hsep a ha b hb hab`.

Rewrite `hza`, `hzb` using `[Metric.mem_ball, dist_eq_norm]`. Establish `h3 : ‖φ a - φ b‖ ≤ ‖z - φ b‖ + ‖z - φ a‖`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : (⋃ h ∈ T, Metric.ball (φ h) r) ⊆ Metric.ball (0 : E) (R + r)`.

Introduce `z hz`. Simplify using `only [Set.mem_iUnion] at hz`. Take `⟨h, hh, hz⟩` from `hz`. Rewrite `hz` using `[Metric.mem_ball, dist_eq_norm]`. Rewrite using `[Metric.mem_ball, dist_zero_right]`.

Establish `h4 : ‖z‖ ≤ ‖z - φ h‖ + ‖φ h‖`. Combine the equalities or inequalities in the displayed calculation. Combine the linear relations using `[hT h hh]`. Establish `hle : μ (⋃ h ∈ T, Metric.ball (φ h) r) ≤ μ (Metric.ball (0 : E) (R + r))` using `measure_mono hsub`. Rewrite `hle` using `[measure_biUnion_finset hdisj (fun h _ => measurableSet_ball)]`.

Simplify using `only [Measure.addHaar_ball_of_pos _ _ hr, Measure.addHaar_ball_of_pos _ _ (by linarith : (0 : ℝ) < R + r), Finset.sum_const, nsmul_eq_mul] at hle`. Establish `hB0 : μ (Metric.ball (0 : E) 1) ≠ 0` using `(Metric.measure_ball_pos μ _ one_pos).ne'`. Establish `hBt : μ (Metric.ball (0 : E) 1) ≠ ⊤` using `measure_ball_lt_top.ne`. Rewrite `hle` using `[← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBt]`. Rewrite `hle` using `[← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)]`.

Establish `hrd : 0 < r ^ d` using `pow_pos hr d`. Rewrite using `[div_pow, le_div_iff₀ hrd]`. Conclude with `hle`.
-/
theorem card_le_of_separated {G E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (φ : G → E) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (T : Finset G)
    (hT : ∀ h ∈ T, ‖φ h‖ ≤ R) (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖) :
    (T.card : ℝ) ≤ ((R + r) / r) ^ Module.finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure E, μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  haveI := hμ
  set d := Module.finrank ℝ E
  have hdisj : Set.PairwiseDisjoint (T : Set G) (fun h => Metric.ball (φ h) r) := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_iff]
    rintro z ⟨hza, hzb⟩
    have hs := hsep a ha b hb hab
    rw [Metric.mem_ball, dist_eq_norm] at hza hzb
    have h3 : ‖φ a - φ b‖ ≤ ‖z - φ b‖ + ‖z - φ a‖ := by
      calc ‖φ a - φ b‖ = ‖(z - φ b) - (z - φ a)‖ := by congr 1; abel
        _ ≤ ‖z - φ b‖ + ‖z - φ a‖ := norm_sub_le _ _
    linarith
  have hsub : (⋃ h ∈ T, Metric.ball (φ h) r) ⊆ Metric.ball (0 : E) (R + r) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨h, hh, hz⟩ := hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_zero_right]
    have h4 : ‖z‖ ≤ ‖z - φ h‖ + ‖φ h‖ := by
      calc ‖z‖ = ‖(z - φ h) + φ h‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - φ h‖ + ‖φ h‖ := norm_add_le _ _
    linarith [hT h hh]
  have hle : μ (⋃ h ∈ T, Metric.ball (φ h) r) ≤ μ (Metric.ball (0 : E) (R + r)) := measure_mono hsub
  rw [measure_biUnion_finset hdisj (fun h _ => measurableSet_ball)] at hle
  simp only [Measure.addHaar_ball_of_pos _ _ hr, Measure.addHaar_ball_of_pos _ _ (by linarith : (0 : ℝ) < R + r),
    Finset.sum_const, nsmul_eq_mul] at hle
  have hB0 : μ (Metric.ball (0 : E) 1) ≠ 0 := (Metric.measure_ball_pos μ _ one_pos).ne'
  have hBt : μ (Metric.ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [← mul_assoc, ENNReal.mul_le_mul_iff_left hB0 hBt] at hle
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
  have hrd : 0 < r ^ d := pow_pos hr d
  rw [div_pow, le_div_iff₀ hrd]
  exact hle

/- English proof (translation)
Introduce `G E _ _ _ _ _ _ μ _ _ _ _ _ φ _ W R r hR hr hW`. Set `P : Finset G → Prop` to `fun T => (∀ h ∈ T, ‖φ h‖ ≤ R) ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖`. Set `A : Set ℕ` to `{n | ∃ T, P T ∧ T.card = n}`. Establish `hA0 : A.Nonempty` using `⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩`. Establish `hAb : BddAbove A`.

Use `⟨⌈((R + r) / r) ^ Module.finrank ℝ E⌉₊, ?_⟩` and prove the remaining obligations. Introduce and unpack `n ⟨T, hT, rfl⟩`. Establish `h1` using `card_le_of_separated φ R r hR hr T hT.1 hT.2`. Establish `h2` using `h1.trans (Nat.le_ceil _)`. Conclude with `h2` after adjusting the coercions.

Take `⟨T, hT, hTc⟩` from `Nat.sSup_mem hA0 hAb`. Establish `hcover : {g : G | ‖φ g‖ ≤ R} ⊆ ⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W`. Introduce `g hg`. Assume the negation of the conclusion as `hne`. Simplify using `only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hne`.

Establish `hg' : ‖φ g‖ ≤ R` using `hg`. Establish `hgT : g ∉ T` using `fun hgT => hne g hgT (hW g g hg' (by simp; positivity))`. Establish `far : ∀ h ∈ T, 2 * r < ‖φ g - φ h‖`. Introduce `h hh`. Assume the negation of the conclusion as `hle`.

Use `push_neg at hle`. Conclude with `hne h hh (hW g h (hT.1 h hh) hle)`. Establish `hP : P (insert g T)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h hh`.

Rewrite `hh` using `[Finset.mem_insert]`. Break down `hh with rfl | hh` into its components or cases. Conclude with `hg'`. Conclude with `hT.1 h hh`. Introduce `a ha b hb hab`.

Rewrite `ha`, `hb` using `[Finset.mem_insert]`. Apply the tactic sequence `rcases ha with rfl | ha <;> rcases hb with rfl | hb`. Conclude with `absurd rfl hab`. Conclude with `far b hb`. Rewrite using `[norm_sub_rev]`.

Conclude with `far a ha`. Conclude with `hT.2 a ha b hb hab`. Establish `hmem : (insert g T).card ∈ A` using `⟨_, hP, rfl⟩`. Establish `hle` using `le_csSup hAb hmem`. Rewrite `hle` using `[Finset.card_insert_of_notMem hgT, ← hTc]`.

Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_natCast]`. Conclude with `ENNReal.ofReal_le_ofReal (card_le_of_separated φ R r hR hr T hT.1 hT.2)`.
-/
theorem main : ∀ {G E : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [inst_3 : MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] (μ : MeasureTheory.Measure G) [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.SFinite μ] [inst_8 : NormedAddCommGroup E] [inst_9 : NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : G → E), Continuous φ → ∀ (W : Set G) (R r : ℝ), (0 : ℝ) ≤ R → (0 : ℝ) < r → (∀ (g h : G), ‖φ h‖ ≤ R → ‖φ g - φ h‖ ≤ (2 : ℝ) * r → h⁻¹ * g ∈ W) → (μ : Set G → ENNReal) {g : G | ‖φ g‖ ≤ R} ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * (μ : Set G → ENNReal) W := by
  intro G E _ _ _ _ _ _ μ _ _ _ _ _ φ _ W R r hR hr hW
  classical
  let P : Finset G → Prop := fun T =>
    (∀ h ∈ T, ‖φ h‖ ≤ R) ∧ ∀ a ∈ T, ∀ b ∈ T, a ≠ b → 2 * r < ‖φ a - φ b‖
  let A : Set ℕ := {n | ∃ T, P T ∧ T.card = n}
  have hA0 : A.Nonempty := ⟨0, ∅, ⟨by simp, by simp⟩, rfl⟩
  have hAb : BddAbove A := by
    refine ⟨⌈((R + r) / r) ^ Module.finrank ℝ E⌉₊, ?_⟩
    rintro n ⟨T, hT, rfl⟩
    have h1 := card_le_of_separated φ R r hR hr T hT.1 hT.2
    have h2 := h1.trans (Nat.le_ceil _)
    exact_mod_cast h2
  obtain ⟨T, hT, hTc⟩ := Nat.sSup_mem hA0 hAb
  have hcover : {g : G | ‖φ g‖ ≤ R} ⊆ ⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W := by
    intro g hg
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_preimage, not_exists] at hne
    have hg' : ‖φ g‖ ≤ R := hg
    have hgT : g ∉ T := fun hgT => hne g hgT (hW g g hg' (by simp; positivity))
    have far : ∀ h ∈ T, 2 * r < ‖φ g - φ h‖ := by
      intro h hh
      by_contra hle
      push_neg at hle
      exact hne h hh (hW g h (hT.1 h hh) hle)
    have hP : P (insert g T) := by
      refine ⟨?_, ?_⟩
      · intro h hh
        rw [Finset.mem_insert] at hh
        rcases hh with rfl | hh
        · exact hg'
        · exact hT.1 h hh
      · intro a ha b hb hab
        rw [Finset.mem_insert] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · exact absurd rfl hab
        · exact far b hb
        · rw [norm_sub_rev]; exact far a ha
        · exact hT.2 a ha b hb hab
    have hmem : (insert g T).card ∈ A := ⟨_, hP, rfl⟩
    have hle := le_csSup hAb hmem
    rw [Finset.card_insert_of_notMem hgT, ← hTc] at hle
    omega
  calc μ {g : G | ‖φ g‖ ≤ R} ≤ μ (⋃ h ∈ T, (fun x => h⁻¹ * x) ⁻¹' W) := measure_mono hcover
    _ ≤ ∑ h ∈ T, μ ((fun x => h⁻¹ * x) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = T.card * μ W := by simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (((R + r) / r) ^ Module.finrank ℝ E) * μ W := by
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (card_le_of_separated φ R r hR hr T hT.1 hT.2)

end GlobalTheory.SeparatedSetCardBound
