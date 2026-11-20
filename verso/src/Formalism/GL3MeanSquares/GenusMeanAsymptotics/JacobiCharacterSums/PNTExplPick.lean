import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplBox

open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

/- English proof (translation)
Use `set h : ℝ := (b - a) / (2 * ((S.card : ℝ) + 1)) with hh`. Establish `hn : (0 : ℝ) < 2 * ((S.card : ℝ) + 1)` using `by positivity`. Establish `hpos : 0 < h` using `div_pos (by linarith) hn`. Establish `hmul : h * (2 * ((S.card : ℝ) + 1)) = b - a`. Rewrite using `[hh]`.

Clear the denominators using the available nonvanishing facts. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `key : ∀ i ∈ Finset.range (S.card + 1), ∃ s ∈ S, |a + (2 * (i : ℝ) + 1) * h - s| < h`. Introduce `i hi`.

Establish `hi' : (i : ℝ) ≤ S.card`. Use `Finset.mem_range.mp hi` as an intermediate fact. Conclude with `Nat.lt_succ_iff.mp this` after adjusting the coercions. Establish `hi0 : (0 : ℝ) ≤ i` using `Nat.cast_nonneg i`. Apply `hcon` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Use `choose! f hfS hf using key`. Establish `hcard : S.card < (Finset.range (S.card + 1)).card` using `by simp`. Take `⟨i, hi, j, hj, hij, hfij⟩` from `Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun i hi => hfS i hi)`.

Establish `h1` using `hf i hi`. Establish `h2` using `hf j hj`. Rewrite `h1` using `[hfij]`. Rewrite `h1`, `h2` using `[abs_lt]`. Break down `lt_or_gt_of_ne hij with hlt | hlt` into its components or cases.

Establish `: (i : ℝ) + 1 ≤ j` using `by exact_mod_cast hlt`. Use the polynomial consequences of the given equalities and inequalities. Establish `: (j : ℝ) + 1 ≤ i` using `by exact_mod_cast hlt`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ex_pick (S : Finset ℝ) (a b : ℝ) (hab : a < b) :
    ∃ x : ℝ, a ≤ x ∧ x ≤ b ∧ ∀ s ∈ S, (b - a) / (2 * ((S.card : ℝ) + 1)) ≤ |x - s| := by
  set h : ℝ := (b - a) / (2 * ((S.card : ℝ) + 1)) with hh
  have hn : (0 : ℝ) < 2 * ((S.card : ℝ) + 1) := by positivity
  have hpos : 0 < h := div_pos (by linarith) hn
  have hmul : h * (2 * ((S.card : ℝ) + 1)) = b - a := by
    rw [hh]; field_simp
  by_contra hcon
  push Not at hcon
  have key : ∀ i ∈ Finset.range (S.card + 1), ∃ s ∈ S, |a + (2 * (i : ℝ) + 1) * h - s| < h := by
    intro i hi
    have hi' : (i : ℝ) ≤ S.card := by
      have := Finset.mem_range.mp hi
      exact_mod_cast Nat.lt_succ_iff.mp this
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    apply hcon
    · nlinarith
    · nlinarith
  choose! f hfS hf using key
  have hcard : S.card < (Finset.range (S.card + 1)).card := by simp
  obtain ⟨i, hi, j, hj, hij, hfij⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun i hi => hfS i hi)
  have h1 := hf i hi
  have h2 := hf j hj
  rw [hfij] at h1
  rw [abs_lt] at h1 h2
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
    nlinarith
  · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
    nlinarith

/- English proof (translation)
Take `⟨C0, hC0, hbox⟩` from `ex_box`. Use `⟨8 * (4 * C0 + 1), by positivity, ?_⟩` and prove the remaining obligations. Introduce `κ hκ hκ' M _ χ T hM hT`. Take `⟨Z, hZ, -, hcard⟩` from `hbox M χ (T + 3) hM (by linarith)`. Establish `hMr : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`.

Use `set N : ℝ := (Z.card : ℝ) with hN`. Establish `hN0 : 0 ≤ N` using `Nat.cast_nonneg _`. Use `set lg : ℝ := Real.log ((M : ℝ) * (T + 2)) with hlg`. Establish `hx12 : (12 : ℝ) ≤ (M : ℝ) * (T + 2)` using `by nlinarith`. Establish `hlg1 : 1 ≤ lg`.

Rewrite using `[hlg, Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlg2 : Real.log ((M : ℝ) * (T + 3 + 2)) ≤ 2 * lg`. Establish `h1 : (M : ℝ) * (T + 3 + 2) ≤ ((M : ℝ) * (T + 2)) ^ 2` using `by nlinarith`.

Establish `h2 : Real.log (((M : ℝ) * (T + 2)) ^ 2) = 2 * lg`. Rewrite using `[Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h2]`.

Conclude with `Real.log_le_log (by nlinarith) h1`. Establish `hNb : 8 * (N + 1) ≤ 8 * (4 * C0 + 1) * (T + 1) * lg`. Establish `h1 : C0 * (T + 3 + 1) * Real.log ((M : ℝ) * (T + 3 + 2)) ≤ C0 * (2 * (T + 1)) * (2 * lg)`. Apply `mul_le_mul _ hlg2 _ (by positivity)` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left (by linarith) hC0.le` to reduce the goal to its premises.

Apply `Real.log_nonneg` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : 1 ≤ (T + 1) * lg` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨σ₁, hσa, hσb, hσ⟩` from `ex_pick (Z.image Complex.re) (1 - κ) (1 - 3 * κ / 4) (by linarith)`.

Take `⟨T', hTa, hTb, hT'⟩` from `ex_pick (Z.image (fun ρ => |ρ.im|)) T (T + 1) (by linarith)`. Establish `hc1 : (((Z.image Complex.re).card : ℕ) : ℝ) ≤ N`. Rewrite using `[hN]`. Conclude with `Nat.cast_le.mpr Finset.card_image_le`. Establish `hc2 : (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℕ) : ℝ) ≤ N`.

Rewrite using `[hN]`. Conclude with `Nat.cast_le.mpr Finset.card_image_le`. Establish `hδpos : 0 < κ / (8 * (N + 1))` using `by positivity`. Establish `hg1 : κ / (8 * (N + 1)) ≤ (1 - 3 * κ / 4 - (1 - κ)) / (2 * (((Z.image Complex.re).card : ℝ) + 1))`. Establish `e : (1 - 3 * κ / 4 - (1 - κ)) = κ / 4` using `by ring`.

Rewrite using `[e, div_le_div_iff₀ (by positivity) (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hg2 : κ / (8 * (N + 1)) ≤ (T + 1 - T) / (2 * (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) + 1))`. Establish `e : (T + 1 - T) = 1` using `by ring`. Rewrite using `[e, div_le_div_iff₀ (by positivity) (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hδle : κ / (8 * (N + 1)) ≤ 1 / 20`. Rewrite using `[div_le_div_iff₀ (by positivity) (by norm_num)]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨σ₁, T', κ / (8 * (N + 1)), hσa, hσb, hTa, hTb, hδpos, hδle, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `div_le_div_of_nonneg_left hκ.le (by positivity) hNb`. Introduce `ρ h0 hre him`. Establish `hmem : ρ ∈ Z` using `(hZ ρ).2 ⟨h0, hre, him⟩`. Conclude with `hg1.trans (hσ _ (Finset.mem_image_of_mem _ hmem))`. Introduce `ρ h0 hre`.

Distinguish the cases in `him : |ρ.im| ≤ T + 3`. Establish `hmem : ρ ∈ Z` using `(hZ ρ).2 ⟨h0, hre, him⟩`. Use `hT' _ (Finset.mem_image_of_mem (fun ρ : ℂ => |ρ.im|) hmem)` as an intermediate fact. Rewrite `this` using `[abs_sub_comm]`. Conclude with `hg2.trans this`.

Use `push Not at him`. Establish `: (2 : ℝ) ≤ |ρ.im| - T'` using `by linarith`. Establish `h3` using `le_abs_self (|ρ.im| - T')`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ex_choose : ∃ C : ℝ, 0 < C ∧ ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 20 →
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M) (T : ℝ), 3 ≤ M → 2 ≤ T →
    ∃ σ₁ T' δ : ℝ, 1 - κ ≤ σ₁ ∧ σ₁ ≤ 1 - 3 * κ / 4 ∧ T ≤ T' ∧ T' ≤ T + 1 ∧ 0 < δ ∧ δ ≤ 1 / 20 ∧
      κ / (C * (T + 1) * Real.log ((M : ℝ) * (T + 2))) ≤ δ ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → |ρ.im| ≤ T + 3 → δ ≤ |σ₁ - ρ.re|) ∧
      (∀ ρ : ℂ, exLF χ ρ = 0 → 9 / 10 ≤ ρ.re → δ ≤ |(|ρ.im| - T')|) := by
  obtain ⟨C0, hC0, hbox⟩ := ex_box
  refine ⟨8 * (4 * C0 + 1), by positivity, ?_⟩
  intro κ hκ hκ' M _ χ T hM hT
  obtain ⟨Z, hZ, -, hcard⟩ := hbox M χ (T + 3) hM (by linarith)
  have hMr : (3 : ℝ) ≤ M := by exact_mod_cast hM
  set N : ℝ := (Z.card : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set lg : ℝ := Real.log ((M : ℝ) * (T + 2)) with hlg
  have hx12 : (12 : ℝ) ≤ (M : ℝ) * (T + 2) := by nlinarith
  have hlg1 : 1 ≤ lg := by
    rw [hlg, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlg2 : Real.log ((M : ℝ) * (T + 3 + 2)) ≤ 2 * lg := by
    have h1 : (M : ℝ) * (T + 3 + 2) ≤ ((M : ℝ) * (T + 2)) ^ 2 := by nlinarith
    have h2 : Real.log (((M : ℝ) * (T + 2)) ^ 2) = 2 * lg := by
      rw [Real.log_pow]; push_cast; ring
    rw [← h2]
    exact Real.log_le_log (by nlinarith) h1
  have hNb : 8 * (N + 1) ≤ 8 * (4 * C0 + 1) * (T + 1) * lg := by
    have h1 : C0 * (T + 3 + 1) * Real.log ((M : ℝ) * (T + 3 + 2)) ≤ C0 * (2 * (T + 1)) * (2 * lg) := by
      apply mul_le_mul _ hlg2 _ (by positivity)
      · apply mul_le_mul_of_nonneg_left (by linarith) hC0.le
      · apply Real.log_nonneg; nlinarith
    have h2 : 1 ≤ (T + 1) * lg := by nlinarith
    nlinarith

  obtain ⟨σ₁, hσa, hσb, hσ⟩ := ex_pick (Z.image Complex.re) (1 - κ) (1 - 3 * κ / 4) (by linarith)
  obtain ⟨T', hTa, hTb, hT'⟩ := ex_pick (Z.image (fun ρ => |ρ.im|)) T (T + 1) (by linarith)
  have hc1 : (((Z.image Complex.re).card : ℕ) : ℝ) ≤ N := by
    rw [hN]; exact Nat.cast_le.mpr Finset.card_image_le
  have hc2 : (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℕ) : ℝ) ≤ N := by
    rw [hN]; exact Nat.cast_le.mpr Finset.card_image_le
  have hδpos : 0 < κ / (8 * (N + 1)) := by positivity
  have hg1 : κ / (8 * (N + 1)) ≤
      (1 - 3 * κ / 4 - (1 - κ)) / (2 * (((Z.image Complex.re).card : ℝ) + 1)) := by
    have e : (1 - 3 * κ / 4 - (1 - κ)) = κ / 4 := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hg2 : κ / (8 * (N + 1)) ≤
      (T + 1 - T) / (2 * (((Z.image (fun ρ : ℂ => |ρ.im|)).card : ℝ) + 1)) := by
    have e : (T + 1 - T) = 1 := by ring
    rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hδle : κ / (8 * (N + 1)) ≤ 1 / 20 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  refine ⟨σ₁, T', κ / (8 * (N + 1)), hσa, hσb, hTa, hTb, hδpos, hδle, ?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_left hκ.le (by positivity) hNb
  · intro ρ h0 hre him
    have hmem : ρ ∈ Z := (hZ ρ).2 ⟨h0, hre, him⟩
    exact hg1.trans (hσ _ (Finset.mem_image_of_mem _ hmem))
  · intro ρ h0 hre
    by_cases him : |ρ.im| ≤ T + 3
    · have hmem : ρ ∈ Z := (hZ ρ).2 ⟨h0, hre, him⟩
      have := hT' _ (Finset.mem_image_of_mem (fun ρ : ℂ => |ρ.im|) hmem)
      rw [abs_sub_comm] at this
      exact hg2.trans this
    · push Not at him
      have : (2 : ℝ) ≤ |ρ.im| - T' := by linarith
      have h3 := le_abs_self (|ρ.im| - T')
      linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions
