import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open MeasureTheory Metric

noncomputable section

/- English proof (translation)
Set `_ : MeasurableSpace E` to `borel E`. Establish `_ : BorelSpace E` using `⟨rfl⟩`. Use `set μ : Measure E := Measure.addHaar`. Use `set d := Module.finrank ℝ E`. Establish `hd : Set.PairwiseDisjoint (↑T : Set E) (fun x => ball x (lam / 2))`.

Introduce `x hx y hy hxy`. Apply `Metric.ball_disjoint_ball` to reduce the goal to its premises. Rewrite using `[dist_eq_norm]`. Use `hsep x hx y hy hxy` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsub : (⋃ x ∈ T, ball x (lam / 2)) ⊆ ball (0 : E) (R + lam / 2)`. Introduce `z hz`. Simplify using `only [Set.mem_iUnion] at hz`. Take `⟨x, hx, hz⟩` from `hz`. Rewrite `hz`, the goal using `[mem_ball]`.

Establish `h1 : dist x 0 < R` using `by rw [dist_zero_right]; exact hT x hx`. Establish `h2` using `dist_triangle z x 0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `measure_mono (μ := μ) hsub`. Rewrite `h2` using `[measure_biUnion_finset hd (fun x _ => measurableSet_ball)]`.

Rewrite `h2` using `[Finset.sum_congr rfl (fun x _ => Measure.addHaar_ball_of_pos μ x (half_pos hlam))]`. Rewrite `h2` using `[Finset.sum_const, nsmul_eq_mul, Measure.addHaar_ball_of_pos μ (0 : E) (r := R + lam / 2) (by positivity), ← mul_assoc]`. Establish `hc0 : μ (ball 0 1) ≠ 0` using `(measure_ball_pos μ (0 : E) one_pos).ne'`. Establish `hc1 : μ (ball 0 1) ≠ ⊤` using `measure_ball_lt_top.ne`. Rewrite `h2` using `[ENNReal.mul_le_mul_iff_left hc0 hc1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)]`.

Conclude with `h2`.
-/
theorem PackingCount.card_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Finset E) {lam R : ℝ} (hlam : 0 < lam) (hR : 0 ≤ R)
    (hT : ∀ x ∈ T, ‖x‖ < R) (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → lam ≤ ‖x - y‖) :
    (T.card : ℝ) * (lam / 2) ^ Module.finrank ℝ E ≤ (R + lam / 2) ^ Module.finrank ℝ E := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  set d := Module.finrank ℝ E
  have hd : Set.PairwiseDisjoint (↑T : Set E) (fun x => ball x (lam / 2)) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    rw [dist_eq_norm]
    have := hsep x hx y hy hxy
    linarith
  have hsub : (⋃ x ∈ T, ball x (lam / 2)) ⊆ ball (0 : E) (R + lam / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    rw [mem_ball] at hz ⊢
    have h1 : dist x 0 < R := by rw [dist_zero_right]; exact hT x hx
    have h2 := dist_triangle z x 0
    linarith
  have h2 := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hd (fun x _ => measurableSet_ball)] at h2
  rw [Finset.sum_congr rfl (fun x _ => Measure.addHaar_ball_of_pos μ x (half_pos hlam))] at h2
  rw [Finset.sum_const, nsmul_eq_mul, Measure.addHaar_ball_of_pos μ (0 : E) (r := R + lam / 2) (by positivity),
    ← mul_assoc] at h2
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hc1 : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.mul_le_mul_iff_left hc0 hc1, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul
    (Nat.cast_nonneg _), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  exact h2

/- English proof (translation)
Introduce `V _ _ L W lam r a h`. Establish `: FiniteDimensional ℝ W` using `Module.finite_of_finrank_pos (by rw [h.finrank_eq]; exact h.one_le_a)`. Establish `hlam` using `h.lam_pos`. Establish `hr : 0 < r` using `lt_of_lt_of_le hlam h.lam_le_r`. Use `set B : ℝ := (1 + 2 * r / lam) ^ a with hB`.

Use `set S : Set V := {v | v ∈ L ∧ ‖v‖ < r} with hS`. Establish `key : ∀ T : Finset V, ↑T ⊆ S → (T.card : ℝ) ≤ B`. Introduce `T hT`. Establish `hW : ∀ v ∈ T, v ∈ W` using `fun v hv => h.short_mem v (hT hv).1 (hT hv).2`. Use `set T' : Finset W := T.subtype (· ∈ W)`.

Establish `hcard : T'.card = T.card`. Rewrite using `[Finset.card_subtype, Finset.filter_true_of_mem hW]`. Establish `hbd` using `PackingCount.card_mul_le T' hlam hr.le (fun x hx => by`. Rewrite `hx` using `[Finset.mem_subtype]`. Rewrite using `[Submodule.coe_norm]`.

Conclude with `(hT hx).2)`. Use the proof step `(fun x hx y hy hxy => by`. Rewrite `hx`, `hy` using `[Finset.mem_subtype]`. Rewrite using `[Submodule.coe_norm, Submodule.coe_sub]`. Apply `h.lam_le_norm _ (h.sub_mem _ (hT hx).1 _ (hT hy).1)` to reduce the goal to its premises.

Introduce `h0`. Conclude with `hxy (Subtype.ext (sub_eq_zero.mp h0)))`. Rewrite `hbd` using `[hcard, h.finrank_eq]`. Establish `hpos : 0 < (lam / 2) ^ a` using `by positivity`. Rewrite `hbd` using `[← le_div_iff₀ hpos, ← div_pow]`.

Establish `he : (r + lam / 2) / (lam / 2) = 1 + 2 * r / lam`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite `hbd` using `[he]`. Then use the resulting hypothesis. Establish `hfin : S.Finite`.

Assume the negation of the conclusion as `hinf`. Take `⟨T, hT, hTc⟩` from `(Set.not_finite.mp hinf).exists_subset_card_eq (⌈B⌉₊ + 1)`. Use `key T hT` as an intermediate fact. Rewrite `this` using `[hTc]`. Move the coercions through the operations in `at this`.

Combine the linear relations using `[Nat.le_ceil B]`. Establish `hsub : {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} ⊆ S` using `fun v hv => ⟨hv.1, hv.2.2⟩`. Establish `hSB : (S.ncard : ℝ) ≤ B`. Rewrite using `[Set.ncard_eq_toFinset_card S hfin]`. Conclude with `key _ (by simp)`.

Establish `hB3 : B ≤ (3 * r / lam) ^ a`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Establish `: lam ≤ r` using `h.lam_le_r`. Rewrite using `[show (1 : ℝ) + 2 * r / lam = (lam + 2 * r) / lam by field_simp]`. Conclude with `div_le_div_of_nonneg_right (by linarith) hlam.le`.

Use `⟨hfin.subset hsub, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `Set.ncard_le_ncard hsub hfin` after adjusting the coercions. Use `_ ≤ B := hSB`. Use `_ ≤ (3 * r / lam) ^ a := hB3`.
-/
theorem PackingCount.proof : PackingCount.Statement := by
  intro V _ _ L W lam r a h
  classical
  have : FiniteDimensional ℝ W :=
    Module.finite_of_finrank_pos (by rw [h.finrank_eq]; exact h.one_le_a)
  have hlam := h.lam_pos
  have hr : 0 < r := lt_of_lt_of_le hlam h.lam_le_r
  set B : ℝ := (1 + 2 * r / lam) ^ a with hB
  set S : Set V := {v | v ∈ L ∧ ‖v‖ < r} with hS

  have key : ∀ T : Finset V, ↑T ⊆ S → (T.card : ℝ) ≤ B := by
    intro T hT
    have hW : ∀ v ∈ T, v ∈ W := fun v hv => h.short_mem v (hT hv).1 (hT hv).2
    set T' : Finset W := T.subtype (· ∈ W)
    have hcard : T'.card = T.card := by
      rw [Finset.card_subtype, Finset.filter_true_of_mem hW]
    have hbd := PackingCount.card_mul_le T' hlam hr.le
      (fun x hx => by
        rw [Finset.mem_subtype] at hx
        rw [Submodule.coe_norm]
        exact (hT hx).2)
      (fun x hx y hy hxy => by
        rw [Finset.mem_subtype] at hx hy
        rw [Submodule.coe_norm, Submodule.coe_sub]
        apply h.lam_le_norm _ (h.sub_mem _ (hT hx).1 _ (hT hy).1)
        intro h0
        exact hxy (Subtype.ext (sub_eq_zero.mp h0)))
    rw [hcard, h.finrank_eq] at hbd
    have hpos : 0 < (lam / 2) ^ a := by positivity
    rw [← le_div_iff₀ hpos, ← div_pow] at hbd
    have he : (r + lam / 2) / (lam / 2) = 1 + 2 * r / lam := by
      field_simp
      ring
    rwa [he] at hbd
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨T, hT, hTc⟩ := (Set.not_finite.mp hinf).exists_subset_card_eq (⌈B⌉₊ + 1)
    have := key T hT
    rw [hTc] at this
    push_cast at this
    linarith [Nat.le_ceil B]
  have hsub : {v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} ⊆ S := fun v hv => ⟨hv.1, hv.2.2⟩
  have hSB : (S.ncard : ℝ) ≤ B := by
    rw [Set.ncard_eq_toFinset_card S hfin]
    exact key _ (by simp)
  have hB3 : B ≤ (3 * r / lam) ^ a := by
    apply pow_le_pow_left₀ (by positivity)
    have : lam ≤ r := h.lam_le_r
    rw [show (1 : ℝ) + 2 * r / lam = (lam + 2 * r) / lam by field_simp]
    exact div_le_div_of_nonneg_right (by linarith) hlam.le
  refine ⟨hfin.subset hsub, ?_⟩
  calc (({v | v ∈ L ∧ v ≠ 0 ∧ ‖v‖ < r} : Set V).ncard : ℝ) ≤ S.ncard := by
        exact_mod_cast Set.ncard_le_ncard hsub hfin
    _ ≤ B := hSB
    _ ≤ (3 * r / lam) ^ a := hB3

end

end GroundTheory.Heights₂.Heights.LowerBound
