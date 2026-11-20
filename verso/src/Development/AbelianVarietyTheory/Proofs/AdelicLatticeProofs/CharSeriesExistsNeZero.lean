import Mathlib

open scoped ContDiff

namespace GlobalTheory

/- English proof (translation)
Use `Finset.induction_on s ⟨c, rfl, by simp, fun i => le_rfl, hF⟩ ?_` and prove the remaining obligations. Introduce `j s _ ih`. Take `⟨c', h1, h2, h3, h4⟩` from `ih`. Distinguish the cases in `hji : j = i₀`. Substitute `hji` using the available equality.

Use `⟨c', h1, ?_, h3, h4⟩` and prove the remaining obligations. Introduce `i hi hne`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `absurd rfl hne`. Conclude with `h2 i hi hne`.

Take `⟨b, hb⟩` from `hneg j hji`. Use `⟨fun i => c' i * (1 + e i b) / 2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show c' i₀ * (1 + e i₀ b) / 2 = c i₀`. Rewrite using `[h0 b, h1]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i hi hne show c' i * (1 + e i b) / 2 = 0`. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Rewrite using `[hb]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2 i hi hne]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `i show ‖c' i * (1 + e i b) / 2‖ ≤ ‖c i‖`. Establish `h2b : ‖(1 : ℂ) + e i b‖ ≤ 2` using `(norm_add_le _ _).trans (by rw [norm_one]; linarith [hle i b])`. Rewrite using `[norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]`. Combine the equalities or inequalities in the displayed calculation.

Introduce `a show ∑' i, c' i * (1 + e i b) / 2 * e i a = 0`. Establish `hsum : ∀ x, Summable (fun i => c' i * e i x)` using `fun x => Summable.of_norm_bounded hs (fun i => by`. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (hle i x)).trans (h3 i))`. Establish `key : ∀ i, c' i * (1 + e i b) / 2 * e i a = (c' i * e i a + c' i * e i (b + a)) / 2`.

Introduce `i`. Rewrite using `[hmul i b a]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [key]`. Rewrite using `[tsum_div_const, (hsum a).tsum_add (hsum (b + a)), h4 a, h4 (b + a)]`.

Simplify using the standard rewrite rules.
-/
theorem charSeries_kill_finset {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (h0 : ∀ a, e i₀ a = 1) (hneg : ∀ i, i ≠ i₀ → ∃ a, e i a = -1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) (s : Finset I) :
    ∃ c' : I → ℂ, c' i₀ = c i₀ ∧ (∀ i ∈ s, i ≠ i₀ → c' i = 0) ∧ (∀ i, ‖c' i‖ ≤ ‖c i‖) ∧
      ∀ a, ∑' i, c' i * e i a = 0 := by
  classical
  refine Finset.induction_on s ⟨c, rfl, by simp, fun i => le_rfl, hF⟩ ?_
  intro j s _ ih
  obtain ⟨c', h1, h2, h3, h4⟩ := ih
  by_cases hji : j = i₀
  · subst hji
    refine ⟨c', h1, ?_, h3, h4⟩
    intro i hi hne
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact absurd rfl hne
    · exact h2 i hi hne
  · obtain ⟨b, hb⟩ := hneg j hji
    refine ⟨fun i => c' i * (1 + e i b) / 2, ?_, ?_, ?_, ?_⟩
    · show c' i₀ * (1 + e i₀ b) / 2 = c i₀
      rw [h0 b, h1]; ring
    · intro i hi hne
      show c' i * (1 + e i b) / 2 = 0
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hb]; ring
      · rw [h2 i hi hne]; ring
    · intro i
      show ‖c' i * (1 + e i b) / 2‖ ≤ ‖c i‖
      have h2b : ‖(1 : ℂ) + e i b‖ ≤ 2 :=
        (norm_add_le _ _).trans (by rw [norm_one]; linarith [hle i b])
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      calc ‖c' i‖ * ‖1 + e i b‖ / 2 ≤ ‖c' i‖ * 2 / 2 := by gcongr
        _ = ‖c' i‖ := by ring
        _ ≤ ‖c i‖ := h3 i
    · intro a
      show ∑' i, c' i * (1 + e i b) / 2 * e i a = 0
      have hsum : ∀ x, Summable (fun i => c' i * e i x) := fun x =>
        Summable.of_norm_bounded hs (fun i => by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (hle i x)).trans (h3 i))
      have key : ∀ i, c' i * (1 + e i b) / 2 * e i a = (c' i * e i a + c' i * e i (b + a)) / 2 := by
        intro i; rw [hmul i b a]; ring
      simp only [key]
      rw [tsum_div_const, (hsum a).tsum_add (hsum (b + a)), h4 a, h4 (b + a)]
      simp

/- English proof (translation)
Introduce `A I _ e c i₀ hmul hle h0 hneg hs hc`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `he0 : ∀ i, e i 0 = 1`. Introduce `i`.

Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Conclude with `h0 0`. Take `⟨a, ha⟩` from `hneg i hi`. Establish `h` using `hmul i a 0`.

Rewrite `h` using `[add_zero, ha]`. Take the linear combination `h`. Establish `hpos : 0 < ‖c i₀‖` using `norm_pos_iff.2 hc`. Take `⟨s, hs1, hs2⟩` from `(((tendsto_order.1 (tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖))).2 _ hpos).and (Filter.eventually_ge_atTop {i₀})).exists`. Establish `htail : ∑' x : {x // x ∉ s}, ‖c x‖ < ‖c i₀‖` using `hs1`.

Establish `hi0 : i₀ ∈ s` using `hs2 (Finset.mem_singleton_self i₀)`. Take `⟨c', hc'0, hc's, hc'le, hc'F⟩` from `charSeries_kill_finset e c i₀ hmul hle h0 hneg hs hcon s`. Establish `hsum' : Summable c'` using `Summable.of_norm_bounded hs hc'le`. Establish `key` using `hc'F 0`. Simplify using `only [he0, mul_one] at key`.

Rewrite `key` using `[← hsum'.sum_add_tsum_subtype_compl s]`. Establish `hfin : ∑ x ∈ s, c' x = c i₀`. Rewrite using `[Finset.sum_eq_single i₀ (fun b hb hne => hc's b hb hne) (fun h => absurd hi0 h)]`. Conclude with `hc'0`. Rewrite `key` using `[hfin]`.

Establish `hbound : ‖∑' x : {x // x ∉ s}, c' x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖` using `tsum_of_norm_bounded ((hs.subtype _).hasSum) (fun x => hc'le x)`. Establish `hnorm : ‖c i₀‖ = ‖∑' x : {x // x ∉ s}, c' x‖`. Rewrite using `[eq_neg_of_add_eq_zero_left key, norm_neg]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem charSeries_exists_ne_zero : ∀ (A I : Type) [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I), (∀ i a b, e i (a + b) = e i a * e i b) → (∀ i a, ‖e i a‖ ≤ 1) → (∀ a, e i₀ a = 1) → (∀ i, i ≠ i₀ → ∃ a, e i a = -1) → Summable (fun i => ‖c i‖) → c i₀ ≠ 0 → ∃ a, ∑' i, c i * e i a ≠ 0 := by
  intro A I _ e c i₀ hmul hle h0 hneg hs hc
  by_contra hcon
  push Not at hcon
  have he0 : ∀ i, e i 0 = 1 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; exact h0 0
    · obtain ⟨a, ha⟩ := hneg i hi
      have h := hmul i a 0
      rw [add_zero, ha] at h
      linear_combination h
  have hpos : 0 < ‖c i₀‖ := norm_pos_iff.2 hc
  obtain ⟨s, hs1, hs2⟩ := (((tendsto_order.1
    (tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖))).2 _ hpos).and
    (Filter.eventually_ge_atTop {i₀})).exists
  have htail : ∑' x : {x // x ∉ s}, ‖c x‖ < ‖c i₀‖ := hs1
  have hi0 : i₀ ∈ s := hs2 (Finset.mem_singleton_self i₀)
  obtain ⟨c', hc'0, hc's, hc'le, hc'F⟩ :=
    charSeries_kill_finset e c i₀ hmul hle h0 hneg hs hcon s
  have hsum' : Summable c' := Summable.of_norm_bounded hs hc'le
  have key := hc'F 0
  simp only [he0, mul_one] at key
  rw [← hsum'.sum_add_tsum_subtype_compl s] at key
  have hfin : ∑ x ∈ s, c' x = c i₀ := by
    rw [Finset.sum_eq_single i₀ (fun b hb hne => hc's b hb hne) (fun h => absurd hi0 h)]
    exact hc'0
  rw [hfin] at key
  have hbound : ‖∑' x : {x // x ∉ s}, c' x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖ :=
    tsum_of_norm_bounded ((hs.subtype _).hasSum) (fun x => hc'le x)
  have hnorm : ‖c i₀‖ = ‖∑' x : {x // x ∉ s}, c' x‖ := by
    rw [eq_neg_of_add_eq_zero_left key, norm_neg]
  linarith

end GlobalTheory
