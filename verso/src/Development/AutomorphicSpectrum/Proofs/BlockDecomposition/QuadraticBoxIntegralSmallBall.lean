import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
open MeasureTheory Topology GlobalTheory.CompanionTheory.WeilSiegel.Inf0
open scoped ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail

variable {P ι : Type} [Fintype P] [Fintype ι]

/- English proof (translation)
Establish `h : (boxR t : Set (P → ι → ℝ)) = ⋂ w, {x | ‖x w‖ ≤ t w}`. Use extensionality with `x`. Simplify using `[boxR]`. Rewrite using `[h]`. Conclude with `MeasurableSet.iInter fun w => measurableSet_le (continuous_apply w).norm.measurable measurable_const`.
-/
lemma measurableSet_boxR (t : P → ℝ) : MeasurableSet (boxR t : Set (P → ι → ℝ)) := by
  have h : (boxR t : Set (P → ι → ℝ)) = ⋂ w, {x | ‖x w‖ ≤ t w} := by
    ext x; simp [boxR]
  rw [h]
  exact MeasurableSet.iInter fun w =>
    measurableSet_le (continuous_apply w).norm.measurable measurable_const

/- English proof (translation)
Establish `hs0 : 0 ≤ ∑ w, ‖x w‖` using `Finset.sum_nonneg (fun _ _ => norm_nonneg _)`. Establish `hle : ∀ w, ‖x w‖ ≤ ∑ w, ‖x w‖` using `fun w => Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)`. Establish `hex : ∃ j : ℕ, x ∈ (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ))`. Take `⟨j, hj⟩` from `pow_unbounded_of_one_lt (∑ w, ‖x w‖) (by norm_num : (1 : ℝ) < 2)`. Conclude with `⟨j, fun w => (hle w).trans hj.le⟩`.

Use `⟨Nat.find hex, Nat.find_spec hex, ?_⟩` and prove the remaining obligations. Establish `h2 : (2 : ℝ) ^ (Nat.find hex) ≤ 2 * (1 + ∑ w, ‖x w‖)`. Break down `Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos` into its components or cases. Rewrite using `[h0]`. Evaluate the numerical expressions.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1` from `⟨Nat.find hex - 1, by omega⟩`. Establish `hnot : x ∉ (boxR (fun _ => (2 : ℝ) ^ k) : Set (P → ι → ℝ))` using `Nat.find_min hex (by omega)`. Simplify using `only [boxR, Set.mem_setOf_eq, not_forall, not_le] at hnot`. Take `⟨w, hw⟩` from `hnot`.

Use `hle w` as an intermediate fact. Rewrite using `[hk, pow_succ]`. Combine the linear equalities and inequalities to obtain the conclusion. Generalize the expression as in `Nat.find hex = j at h2`. Establish `h3 : ((2 : ℝ) ^ j) ^ N ≤ 2 ^ N * (1 + ∑ w, ‖x w‖) ^ N`.

Rewrite using `[← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 N`. Establish `h4 : f x * ((2 : ℝ) ^ j) ^ N ≤ K * 2 ^ N`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : ((2 : ℝ) ^ j) ^ N * ((1 : ℝ) / 2) ^ (j * N) = 1`. Rewrite using `[← pow_mul, ← mul_pow]`.

Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.
-/
lemma exists_dyadic_bound (f : (P → ι → ℝ) → ℝ) (N : ℕ) (K : ℝ) (x : P → ι → ℝ)
    (hf : 0 ≤ f x) (hx : f x * (1 + ∑ w, ‖x w‖) ^ N ≤ K) :
    ∃ j : ℕ, x ∈ (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)) ∧
      f x ≤ K * 2 ^ N * (1 / 2) ^ (j * N) := by
  classical
  have hs0 : 0 ≤ ∑ w, ‖x w‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hle : ∀ w, ‖x w‖ ≤ ∑ w, ‖x w‖ := fun w =>
    Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have hex : ∃ j : ℕ, x ∈ (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)) := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (∑ w, ‖x w‖) (by norm_num : (1 : ℝ) < 2)
    exact ⟨j, fun w => (hle w).trans hj.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  have h2 : (2 : ℝ) ^ (Nat.find hex) ≤ 2 * (1 + ∑ w, ‖x w‖) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0]; norm_num; linarith
    · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hnot : x ∉ (boxR (fun _ => (2 : ℝ) ^ k) : Set (P → ι → ℝ)) :=
        Nat.find_min hex (by omega)
      simp only [boxR, Set.mem_setOf_eq, not_forall, not_le] at hnot
      obtain ⟨w, hw⟩ := hnot
      have := hle w
      rw [hk, pow_succ]
      linarith
  generalize Nat.find hex = j at h2
  have h3 : ((2 : ℝ) ^ j) ^ N ≤ 2 ^ N * (1 + ∑ w, ‖x w‖) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h2 N
  have h4 : f x * ((2 : ℝ) ^ j) ^ N ≤ K * 2 ^ N := by
    calc f x * ((2 : ℝ) ^ j) ^ N ≤ f x * (2 ^ N * (1 + ∑ w, ‖x w‖) ^ N) :=
          mul_le_mul_of_nonneg_left h3 hf
      _ = (f x * (1 + ∑ w, ‖x w‖) ^ N) * 2 ^ N := by ring
      _ ≤ K * 2 ^ N := by gcongr
  have h5 : ((2 : ℝ) ^ j) ^ N * ((1 : ℝ) / 2) ^ (j * N) = 1 := by
    rw [← pow_mul, ← mul_pow]; norm_num
  calc f x = f x * (((2 : ℝ) ^ j) ^ N * (1 / 2) ^ (j * N)) := by rw [h5, mul_one]
    _ = (f x * ((2 : ℝ) ^ j) ^ N) * (1 / 2) ^ (j * N) := by ring
    _ ≤ K * 2 ^ N * (1 / 2) ^ (j * N) := by gcongr

/- English proof (translation)
Set `c : ℕ → ℝ≥0∞` to `fun j => ENNReal.ofReal (K * 2 ^ (M + 1) * (1 / 2) ^ (j * (M + 1)))`. Establish `h1 : ∫⁻ x in T, ENNReal.ofReal (f x) ≤ ∫⁻ x in T, ∑' j, (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)).indicator (fun _ => c j) x`. Use `setLIntegral_mono' hT fun x hx => ?_` and prove the remaining obligations. Take `⟨j, hj, hfj⟩` from `exists_dyadic_bound f (M + 1) K x (hf x) (hTK x hx)`. Use `le_trans ?_ (ENNReal.le_tsum j)` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem hj]`. Conclude with `ENNReal.ofReal_le_ofReal hfj`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[lintegral_tsum (fun j => (measurable_const.indicator (measurableSet_boxR _)).aemeasurable)]`. Establish `h2 : ∀ j : ℕ, ∫⁻ x in T, (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)).indicator (fun _ => c j) x ≤ ENNReal.ofReal (K * 2 ^ (M + 1)) * B * ENNReal.ofReal ((1 / 2 : ℝ) ^ j)`.

Introduce `j`. Rewrite using `[lintegral_indicator_const (measurableSet_boxR _), Measure.restrict_apply (measurableSet_boxR _), Set.inter_comm]`. Establish `e : ((1 : ℝ) / 2) ^ (j * (M + 1)) * ((2 : ℝ) ^ j) ^ M = (1 / 2) ^ j`. Establish `: ((1 : ℝ) / 2) ^ (j * (M + 1)) = (1 / 2) ^ j * ((1 / 2) ^ j) ^ M`. Rewrite using `[← pow_mul, ← pow_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, mul_assoc, ← mul_pow, ← mul_pow]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [c]`. Rewrite using `[ENNReal.ofReal_mul (by positivity)]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [← ENNReal.ofReal_mul (by positivity), e]`. Use `(ENNReal.tsum_le_tsum h2).trans ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) summable_geometric_two, tsum_geometric_two]`. Establish `e : (2 * K * 2 ^ (M + 1) : ℝ) = K * 2 ^ (M + 1) * 2` using `by ring`. Rewrite using `[e, ENNReal.ofReal_mul (p := K * 2 ^ (M + 1)) (q := 2) (by positivity)]`. Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.
-/
lemma setLIntegral_le_of_dyadic (f : (P → ι → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x) (M : ℕ) (K : ℝ)
    (hK : 0 ≤ K) (T : Set (P → ι → ℝ)) (hT : MeasurableSet T)
    (hTK : ∀ x ∈ T, f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) ≤ K) (B : ℝ≥0∞)
    (hB : ∀ j : ℕ, volume (T ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      B * ENNReal.ofReal (((2 : ℝ) ^ j) ^ M)) :
    ∫⁻ x in T, ENNReal.ofReal (f x) ≤ ENNReal.ofReal (2 * K * 2 ^ (M + 1)) * B := by
  let c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (K * 2 ^ (M + 1) * (1 / 2) ^ (j * (M + 1)))
  have h1 : ∫⁻ x in T, ENNReal.ofReal (f x) ≤ ∫⁻ x in T, ∑' j,
      (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)).indicator (fun _ => c j) x := by
    refine setLIntegral_mono' hT fun x hx => ?_
    obtain ⟨j, hj, hfj⟩ := exists_dyadic_bound f (M + 1) K x (hf x) (hTK x hx)
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem hj]
    exact ENNReal.ofReal_le_ofReal hfj
  refine h1.trans ?_
  rw [lintegral_tsum (fun j => (measurable_const.indicator (measurableSet_boxR _)).aemeasurable)]
  have h2 : ∀ j : ℕ, ∫⁻ x in T,
      (boxR (fun _ => (2 : ℝ) ^ j) : Set (P → ι → ℝ)).indicator (fun _ => c j) x ≤
      ENNReal.ofReal (K * 2 ^ (M + 1)) * B * ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
    intro j
    rw [lintegral_indicator_const (measurableSet_boxR _),
      Measure.restrict_apply (measurableSet_boxR _), Set.inter_comm]
    have e : ((1 : ℝ) / 2) ^ (j * (M + 1)) * ((2 : ℝ) ^ j) ^ M = (1 / 2) ^ j := by
      have : ((1 : ℝ) / 2) ^ (j * (M + 1)) = (1 / 2) ^ j * ((1 / 2) ^ j) ^ M := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [this, mul_assoc, ← mul_pow, ← mul_pow]; norm_num
    calc c j * volume (T ∩ boxR (fun _ => (2 : ℝ) ^ j))
        ≤ c j * (B * ENNReal.ofReal (((2 : ℝ) ^ j) ^ M)) := by gcongr; exact hB j
      _ = ENNReal.ofReal (K * 2 ^ (M + 1)) * B *
            (ENNReal.ofReal ((1 / 2) ^ (j * (M + 1))) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ M)) := by
          simp only [c]
          rw [ENNReal.ofReal_mul (by positivity)]
          ring
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), e]
  refine (ENNReal.tsum_le_tsum h2).trans ?_
  rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
    summable_geometric_two, tsum_geometric_two]
  have e : (2 * K * 2 ^ (M + 1) : ℝ) = K * 2 ^ (M + 1) * 2 := by ring
  rw [e, ENNReal.ofReal_mul (p := K * 2 ^ (M + 1)) (q := 2) (by positivity)]
  apply le_of_eq
  ring

/- English proof (translation)
Use `set t : P → ℝ := Function.update (fun _ : P => (2 : ℝ) ^ j) v δ with ht_def`. Establish `htv : t v = δ` using `by simp [ht_def]`. Establish `htw : ∀ w, w ≠ v → t w = (2 : ℝ) ^ j` using `fun w h => by simp [ht_def, h]`. Establish `ht : ∀ w, 0 < t w`. Introduce `w`.

Distinguish the cases in `h : w = v`. Rewrite using `[h, htv]`. Conclude with `hδ`. Rewrite using `[htw w h]`. Check the signs of the components of the expression.

Establish `hsub : (Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j) ⊆ Q ⁻¹' U ∩ boxR t`. Introduce and unpack `x ⟨⟨hxU, hxv⟩, hxb⟩`. Use `⟨hxU, fun w => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : w = v`. Rewrite using `[h, htv]`.

Conclude with `le_of_lt hxv`. Rewrite using `[htw w h]`. Conclude with `hxb w`. Establish `hprod : ∏ w, t w ^ a ≤ δ ^ a * ((2 : ℝ) ^ j) ^ (a * Fintype.card P)`. Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), htv]`.

Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Establish `h : ∀ w ∈ Finset.univ.erase v, t w ^ a = ((2 : ℝ) ^ j) ^ a` using `fun w hw => by`. Rewrite using `[htw w (Finset.ne_of_mem_erase hw)]`. Rewrite using `[Finset.prod_congr rfl h, Finset.prod_const, ← pow_mul]`. Apply `pow_le_pow_right₀ (one_le_pow₀ (by norm_num))` to reduce the goal to its premises.

Apply `Nat.mul_le_mul_left` to reduce the goal to its premises. Conclude with `Finset.card_le_card (Finset.erase_subset _ _)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.ofReal_mul (by positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma volume_near_le {a : ℕ} {Q : (P → ι → ℝ) → (P → ℝ)} {C : ℝ≥0}
    (hbox : ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (v : P) {U : Set (P → ℝ)} (hU : MeasurableSet U)
    (j : ℕ) :
    (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      ((C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a) * volume U) *
        ENNReal.ofReal (((2 : ℝ) ^ j) ^ (a * Fintype.card P)) := by
  classical
  set t : P → ℝ := Function.update (fun _ : P => (2 : ℝ) ^ j) v δ with ht_def
  have htv : t v = δ := by simp [ht_def]
  have htw : ∀ w, w ≠ v → t w = (2 : ℝ) ^ j := fun w h => by simp [ht_def, h]
  have ht : ∀ w, 0 < t w := by
    intro w
    by_cases h : w = v
    · rw [h, htv]; exact hδ
    · rw [htw w h]; positivity
  have hsub : (Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j) ⊆
      Q ⁻¹' U ∩ boxR t := by
    rintro x ⟨⟨hxU, hxv⟩, hxb⟩
    refine ⟨hxU, fun w => ?_⟩
    by_cases h : w = v
    · rw [h, htv]; exact le_of_lt hxv
    · rw [htw w h]; exact hxb w
  have hprod : ∏ w, t w ^ a ≤ δ ^ a * ((2 : ℝ) ^ j) ^ (a * Fintype.card P) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), htv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h : ∀ w ∈ Finset.univ.erase v, t w ^ a = ((2 : ℝ) ^ j) ^ a := fun w hw => by
      rw [htw w (Finset.ne_of_mem_erase hw)]
    rw [Finset.prod_congr rfl h, Finset.prod_const, ← pow_mul]
    apply pow_le_pow_right₀ (one_le_pow₀ (by norm_num))
    apply Nat.mul_le_mul_left
    exact Finset.card_le_card (Finset.erase_subset _ _)
  calc (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∩ boxR (fun _ => (2 : ℝ) ^ j))
      ≤ volume (Q ⁻¹' U ∩ boxR t) := measure_mono hsub
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U := hbox t ht U hU
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a * ((2 : ℝ) ^ j) ^ (a * Fintype.card P)) * volume U := by
        gcongr
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity)]
        ring

/- English proof (translation)
Establish `hsub : (Q ⁻¹' U ∩ Y) ∩ boxR (fun _ => (2 : ℝ) ^ j) ⊆ Q ⁻¹' U ∩ boxR (fun _ => (2 : ℝ) ^ j)` using `fun x hx => ⟨hx.1.1, hx.2⟩`. Establish `hprod : ∏ _w : P, ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ j) ^ (a * Fintype.card P)`. Rewrite using `[Finset.prod_const, ← pow_mul, Finset.card_univ]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma volume_far_le {a : ℕ} {Q : (P → ι → ℝ) → (P → ℝ)} {C : ℝ≥0}
    (hbox : ∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U)
    (Y : Set (P → ι → ℝ)) {U : Set (P → ℝ)} (hU : MeasurableSet U) (j : ℕ) :
    (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ Y) ∩ boxR (fun _ => (2 : ℝ) ^ j)) ≤
      ((C : ℝ≥0∞) * volume U) * ENNReal.ofReal (((2 : ℝ) ^ j) ^ (a * Fintype.card P)) := by
  have hsub : (Q ⁻¹' U ∩ Y) ∩ boxR (fun _ => (2 : ℝ) ^ j) ⊆
      Q ⁻¹' U ∩ boxR (fun _ => (2 : ℝ) ^ j) := fun x hx => ⟨hx.1.1, hx.2⟩
  have hprod : ∏ _w : P, ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ j) ^ (a * Fintype.card P) := by
    rw [Finset.prod_const, ← pow_mul, Finset.card_univ]
  calc (volume : Measure (P → ι → ℝ)) ((Q ⁻¹' U ∩ Y) ∩ boxR (fun _ => (2 : ℝ) ^ j))
      ≤ volume (Q ⁻¹' U ∩ boxR (fun _ => (2 : ℝ) ^ j)) := measure_mono hsub
    _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (∏ _w : P, ((2 : ℝ) ^ j) ^ a) * volume U :=
        hbox _ (fun _ => by positivity) U hU
    _ = _ := by rw [hprod]; ring

/- English proof (translation)
Introduce `P ι _ _ a ha Q hQ C hbox f _hfm hf0 hdec ε hε`. Take `⟨M, hM⟩ : ∃ M, M = a * Fintype.card P` from `⟨_, rfl⟩`. Take `⟨C1, hC1⟩` from `hdec (M + 1)`. Take `⟨C2, hC2⟩` from `hdec (M + 1 + 1)`. Establish `hsn : ∀ x : P → ι → ℝ, 0 ≤ ∑ w, ‖x w‖` using `fun x => Finset.sum_nonneg (fun _ _ => norm_nonneg _)`.

Establish `hC1n : 0 ≤ C1` using `(mul_nonneg (hf0 0) (pow_nonneg (by have := hsn 0; linarith) _)).trans (hC1 0)`. Establish `hC2n : 0 ≤ C2` using `(mul_nonneg (hf0 0) (pow_nonneg (by have := hsn 0; linarith) _)).trans (hC2 0)`. Take `⟨c, hc⟩ : ∃ c : ℝ, c = (C : ℝ)` from `⟨_, rfl⟩`. Establish `hcn : 0 ≤ c` using `hc ▸ C.2`. Establish `hCc : (C : ℝ≥0∞) = ENNReal.ofReal c` using `by rw [hc, ENNReal.ofReal_coe_nnreal]`.

Take `⟨A1, hA1⟩ : ∃ A : ℝ, A = 2 * C1 * 2 ^ (M + 1) * c` from `⟨_, rfl⟩`. Take `⟨A2, hA2⟩ : ∃ A : ℝ, A = 2 * C2 * 2 ^ (M + 1) * c` from `⟨_, rfl⟩`. Establish `hA1n : 0 ≤ A1` using `hA1 ▸ by positivity`. Establish `hA2n : 0 ≤ A2` using `hA2 ▸ by positivity`. Take `⟨r, hr⟩ : ∃ r : ℝ, r = (Fintype.card P : ℝ)` from `⟨_, rfl⟩`.

Establish `hrn : 0 ≤ r` using `hr ▸ by positivity`. Take `⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε / (2 * (r * A1 + 1)))` from `⟨_, rfl⟩`. Take `⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * A2 / ε + 1` from `⟨_, rfl⟩`. Establish `hD : 0 < r * A1 + 1` using `by positivity`. Establish `hδ : 0 < δ` using `by rw [hδdef]; exact lt_min one_pos (by positivity)`.

Establish `hδ1 : δ ≤ 1` using `by rw [hδdef]; exact min_le_left _ _`. Establish `hδ2 : δ ≤ ε / (2 * (r * A1 + 1))` using `by rw [hδdef]; exact min_le_right _ _`. Establish `hR : 0 < R` using `by rw [hRdef]; positivity`. Use `⟨δ, R, hδ, hR, fun U hU => ?_⟩` and prove the remaining obligations. Establish `hnear : ∀ v, ∫⁻ x in Q ⁻¹' U ∩ {x | ‖x v‖ < δ}, ENNReal.ofReal (f x) ≤ ENNReal.ofReal (A1 * δ ^ a) * volume U`.

Introduce `v`. Establish `hT : MeasurableSet (Q ⁻¹' U ∩ {x : P → ι → ℝ | ‖x v‖ < δ})` using `(hQ hU).inter (measurableSet_lt (continuous_apply v).norm.measurable measurable_const)`. Use `setLIntegral_le_of_dyadic f hf0 M C1 hC1n _ hT (fun x _ => hC1 x) ((C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a) * volume U) (fun j => by rw [hM]; exact volume_near_le hbox hδ hδ1 v hU j)` as an intermediate fact. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hA1, hCc, mul_assoc (2 * C1 * 2 ^ (M + 1)) c, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * C1 * 2 ^ (M + 1)), ENNReal.ofReal_mul hcn]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hfar : ∫⁻ x in Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}, ENNReal.ofReal (f x) ≤ ENNReal.ofReal (A2 / (1 + R)) * volume U`. Establish `hY : {x : P → ι → ℝ | ∃ w, R < ‖x w‖} = ⋃ w, {x | R < ‖x w‖}`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `hT : MeasurableSet (Q ⁻¹' U ∩ {x : P → ι → ℝ | ∃ w, R < ‖x w‖})`. Use `(hQ hU).inter ?_` and prove the remaining obligations. Rewrite using `[hY]`. Conclude with `MeasurableSet.iUnion fun w => measurableSet_lt measurable_const (continuous_apply w).norm.measurable`. Establish `hK : ∀ x ∈ Q ⁻¹' U ∩ {x : P → ι → ℝ | ∃ w, R < ‖x w‖}, f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) ≤ C2 / (1 + R)`.

Introduce and unpack `x ⟨-, w, hw⟩`. Establish `hle : ‖x w‖ ≤ ∑ w, ‖x w‖` using `Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)`. Establish `h1 : 1 + R ≤ 1 + ∑ w, ‖x w‖` using `by linarith`. Establish `hnn : 0 ≤ f x * (1 + ∑ w, ‖x w‖) ^ (M + 1)` using `mul_nonneg (hf0 x) (pow_nonneg (by have := hsn x; linarith) _)`. Rewrite using `[le_div_iff₀ (by positivity)]`.

Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_le_of_dyadic f hf0 M (C2 / (1 + R)) (by positivity) _ hT hK ((C : ℝ≥0∞) * volume U) (fun j => by rw [hM]; exact volume_far_le hbox _ hU j)` as an intermediate fact. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Establish `e : A2 / (1 + R) = (2 * (C2 / (1 + R)) * 2 ^ (M + 1)) * c` using `by rw [hA2]; ring`. Rewrite using `[e, hCc, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (C2 / (1 + R)) * 2 ^ (M + 1))]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsub : Q ⁻¹' U ∩ (coreR δ R : Set (P → ι → ℝ))ᶜ ⊆ (⋃ v, Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∪ (Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖})`. Introduce and unpack `x ⟨hxU, hxc⟩`. Simplify using `only [coreR, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hxc`. Take `⟨w, hw⟩` from `hxc`.

Distinguish the cases in `h : δ ≤ ‖x w‖`. Conclude with `Or.inr ⟨hxU, w, not_le.mp fun h' => hw ⟨h, h'⟩⟩`. Conclude with `Or.inl (Set.mem_iUnion.mpr ⟨w, hxU, not_le.mp h⟩)`. Establish `hreal : r * (A1 * δ ^ a) + A2 / (1 + R) ≤ ε`. Establish `h1 : δ ^ a ≤ δ` using `pow_le_of_le_one hδ.le hδ1 ha.ne'`.

Establish `h2 : r * A1 * δ ≤ ε / 2`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (by linarith) hδ2 hδ.le hD.le` to reduce the goal to its premises. Use `_ = ε / 2 := by field_simp`. Establish `h3 : A2 / (1 + R) ≤ ε / 2`.

Rewrite using `[div_le_iff₀ (by positivity), hRdef]`. Establish `: ε / 2 * (1 + (2 * A2 / ε + 1)) = ε + A2` using `by field_simp; ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : r * (A1 * δ ^ a) ≤ r * A1 * δ`.

Rewrite using `[← mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by positivity)`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation. Use `add_le_add ?_ hfar` and prove the remaining obligations. Use `(lintegral_iUnion_le _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[tsum_fintype]`. Conclude with `Finset.sum_le_sum fun v _ => hnear v`. Use `_ = ENNReal.ofReal (r * (A1 * δ ^ a) + A2 / (1 + R)) * volume U := by`. Establish `hpos : 0 ≤ A1 * δ ^ a` using `by positivity`. Rewrite using `[ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hrn, hr, ENNReal.ofReal_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_mul, mul_assoc]`.

Use `_ ≤ ENNReal.ofReal ε * volume U := by gcongr`.
-/
theorem tail_small : ∀ (P ι : Type) [Fintype P] [Fintype ι] (a : ℕ), 0 < a →
    ∀ (Q : (P → ι → ℝ) → (P → ℝ)), Measurable Q → ∀ C : ℝ≥0,
    (∀ t : P → ℝ, (∀ w, 0 < t w) → ∀ U : Set (P → ℝ), MeasurableSet U →
      (volume : Measure (P → ι → ℝ)) (Q ⁻¹' U ∩ boxR t) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal (∏ w, t w ^ a) * volume U) →
    ∀ f : (P → ι → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) →
    (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') →
    ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (P → ℝ), MeasurableSet U →
      ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
  intro P ι _ _ a ha Q hQ C hbox f _hfm hf0 hdec ε hε
  obtain ⟨M, hM⟩ : ∃ M, M = a * Fintype.card P := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ := hdec (M + 1)
  obtain ⟨C2, hC2⟩ := hdec (M + 1 + 1)
  have hsn : ∀ x : P → ι → ℝ, 0 ≤ ∑ w, ‖x w‖ := fun x =>
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hC1n : 0 ≤ C1 :=
    (mul_nonneg (hf0 0) (pow_nonneg (by have := hsn 0; linarith) _)).trans (hC1 0)
  have hC2n : 0 ≤ C2 :=
    (mul_nonneg (hf0 0) (pow_nonneg (by have := hsn 0; linarith) _)).trans (hC2 0)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (C : ℝ) := ⟨_, rfl⟩
  have hcn : 0 ≤ c := hc ▸ C.2
  have hCc : (C : ℝ≥0∞) = ENNReal.ofReal c := by rw [hc, ENNReal.ofReal_coe_nnreal]
  obtain ⟨A1, hA1⟩ : ∃ A : ℝ, A = 2 * C1 * 2 ^ (M + 1) * c := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A : ℝ, A = 2 * C2 * 2 ^ (M + 1) * c := ⟨_, rfl⟩
  have hA1n : 0 ≤ A1 := hA1 ▸ by positivity
  have hA2n : 0 ≤ A2 := hA2 ▸ by positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (Fintype.card P : ℝ) := ⟨_, rfl⟩
  have hrn : 0 ≤ r := hr ▸ by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε / (2 * (r * A1 + 1))) := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * A2 / ε + 1 := ⟨_, rfl⟩
  have hD : 0 < r * A1 + 1 := by positivity
  have hδ : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδ2 : δ ≤ ε / (2 * (r * A1 + 1)) := by rw [hδdef]; exact min_le_right _ _
  have hR : 0 < R := by rw [hRdef]; positivity
  refine ⟨δ, R, hδ, hR, fun U hU => ?_⟩
  have hnear : ∀ v, ∫⁻ x in Q ⁻¹' U ∩ {x | ‖x v‖ < δ}, ENNReal.ofReal (f x) ≤
      ENNReal.ofReal (A1 * δ ^ a) * volume U := by
    intro v
    have hT : MeasurableSet (Q ⁻¹' U ∩ {x : P → ι → ℝ | ‖x v‖ < δ}) :=
      (hQ hU).inter (measurableSet_lt (continuous_apply v).norm.measurable measurable_const)
    have := setLIntegral_le_of_dyadic f hf0 M C1 hC1n _ hT (fun x _ => hC1 x)
      ((C : ℝ≥0∞) * ENNReal.ofReal (δ ^ a) * volume U)
      (fun j => by rw [hM]; exact volume_near_le hbox hδ hδ1 v hU j)
    refine this.trans (le_of_eq ?_)
    rw [hA1, hCc, mul_assoc (2 * C1 * 2 ^ (M + 1)) c,
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * C1 * 2 ^ (M + 1)),
      ENNReal.ofReal_mul hcn]
    ring
  have hfar : ∫⁻ x in Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}, ENNReal.ofReal (f x) ≤
      ENNReal.ofReal (A2 / (1 + R)) * volume U := by
    have hY : {x : P → ι → ℝ | ∃ w, R < ‖x w‖} = ⋃ w, {x | R < ‖x w‖} := by
      ext x; simp
    have hT : MeasurableSet (Q ⁻¹' U ∩ {x : P → ι → ℝ | ∃ w, R < ‖x w‖}) := by
      refine (hQ hU).inter ?_
      rw [hY]
      exact MeasurableSet.iUnion fun w =>
        measurableSet_lt measurable_const (continuous_apply w).norm.measurable
    have hK : ∀ x ∈ Q ⁻¹' U ∩ {x : P → ι → ℝ | ∃ w, R < ‖x w‖},
        f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) ≤ C2 / (1 + R) := by
      rintro x ⟨-, w, hw⟩
      have hle : ‖x w‖ ≤ ∑ w, ‖x w‖ :=
        Finset.single_le_sum (f := fun w => ‖x w‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
      have h1 : 1 + R ≤ 1 + ∑ w, ‖x w‖ := by linarith
      have hnn : 0 ≤ f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) :=
        mul_nonneg (hf0 x) (pow_nonneg (by have := hsn x; linarith) _)
      rw [le_div_iff₀ (by positivity)]
      calc f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) * (1 + R)
          ≤ f x * (1 + ∑ w, ‖x w‖) ^ (M + 1) * (1 + ∑ w, ‖x w‖) :=
            mul_le_mul_of_nonneg_left h1 hnn
        _ = f x * (1 + ∑ w, ‖x w‖) ^ (M + 1 + 1) := by ring
        _ ≤ C2 := hC2 x
    have := setLIntegral_le_of_dyadic f hf0 M (C2 / (1 + R)) (by positivity) _ hT hK
      ((C : ℝ≥0∞) * volume U) (fun j => by rw [hM]; exact volume_far_le hbox _ hU j)
    refine this.trans (le_of_eq ?_)
    have e : A2 / (1 + R) = (2 * (C2 / (1 + R)) * 2 ^ (M + 1)) * c := by rw [hA2]; ring
    rw [e, hCc, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (C2 / (1 + R)) * 2 ^ (M + 1))]
    ring
  have hsub : Q ⁻¹' U ∩ (coreR δ R : Set (P → ι → ℝ))ᶜ ⊆
      (⋃ v, Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∪ (Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}) := by
    rintro x ⟨hxU, hxc⟩
    simp only [coreR, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hxc
    obtain ⟨w, hw⟩ := hxc
    by_cases h : δ ≤ ‖x w‖
    · exact Or.inr ⟨hxU, w, not_le.mp fun h' => hw ⟨h, h'⟩⟩
    · exact Or.inl (Set.mem_iUnion.mpr ⟨w, hxU, not_le.mp h⟩)
  have hreal : r * (A1 * δ ^ a) + A2 / (1 + R) ≤ ε := by
    have h1 : δ ^ a ≤ δ := pow_le_of_le_one hδ.le hδ1 ha.ne'
    have h2 : r * A1 * δ ≤ ε / 2 := by
      calc r * A1 * δ ≤ (r * A1 + 1) * (ε / (2 * (r * A1 + 1))) := by
            apply mul_le_mul (by linarith) hδ2 hδ.le hD.le
        _ = ε / 2 := by field_simp
    have h3 : A2 / (1 + R) ≤ ε / 2 := by
      rw [div_le_iff₀ (by positivity), hRdef]
      have : ε / 2 * (1 + (2 * A2 / ε + 1)) = ε + A2 := by field_simp; ring
      rw [this]; linarith
    have h4 : r * (A1 * δ ^ a) ≤ r * A1 * δ := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  calc ∫⁻ x in Q ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x)
      ≤ ∫⁻ x in (⋃ v, Q ⁻¹' U ∩ {x | ‖x v‖ < δ}) ∪ (Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}),
          ENNReal.ofReal (f x) := lintegral_mono_set hsub
    _ ≤ (∫⁻ x in ⋃ v, Q ⁻¹' U ∩ {x | ‖x v‖ < δ}, ENNReal.ofReal (f x)) +
        (∫⁻ x in Q ⁻¹' U ∩ {x | ∃ w, R < ‖x w‖}, ENNReal.ofReal (f x)) :=
          lintegral_union_le _ _ _
    _ ≤ (∑ v : P, ENNReal.ofReal (A1 * δ ^ a) * volume U) +
        ENNReal.ofReal (A2 / (1 + R)) * volume U := by
          refine add_le_add ?_ hfar
          refine (lintegral_iUnion_le _ _).trans ?_
          rw [tsum_fintype]
          exact Finset.sum_le_sum fun v _ => hnear v
    _ = ENNReal.ofReal (r * (A1 * δ ^ a) + A2 / (1 + R)) * volume U := by
          have hpos : 0 ≤ A1 * δ ^ a := by positivity
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hrn,
            hr, ENNReal.ofReal_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
            add_mul, mul_assoc]
    _ ≤ ENNReal.ofReal ε * volume U := by
          gcongr

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.RealTail
