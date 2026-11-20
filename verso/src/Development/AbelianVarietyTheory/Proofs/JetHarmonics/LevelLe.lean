import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RowBudgets

/- English proof (translation)
Establish `h` using `GlobalTheory.LevelsOrbits.levelBound k l hk hl`. Establish `e : RF.i0 k l = Formalism.L2.FormalSeriesBounds.i0 k l` using `rfl`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma level_le (k l : ℕ) (hk : 1 ≤ k) (hl : 5 ≤ l) :
    ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * Real.log k := by
  have h := GlobalTheory.LevelsOrbits.levelBound k l hk hl
  have e : RF.i0 k l = Formalism.L2.FormalSeriesBounds.i0 k l := rfl
  rw [e]
  linarith

/- English proof (translation)
Introduce `r f n m nW T l k b L A hm hmn hnr hf hT hk hL hkL hW`. Establish `hm' : (1 : ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hmn' : (m : ℝ) ≤ n` using `by exact_mod_cast hmn`. Establish `hnr' : (n : ℝ) ≤ r` using `by exact_mod_cast hnr`. Establish `hf' : (2 : ℝ) ≤ f` using `by exact_mod_cast hf`.

Establish `hT' : (1 : ℝ) ≤ T` using `by exact_mod_cast hT`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `hlog : 0 ≤ Real.log k` using `Real.log_nonneg (by exact_mod_cast hk1)`. Establish `hn' : (1 : ℝ) ≤ n` using `hm'.trans hmn'`. Establish `hr' : (1 : ℝ) ≤ r` using `hn'.trans hnr'`.

Establish `hD : (0 : ℝ) < T * f * (n : ℝ) ^ 3 * L` using `by positivity`. Take `⟨Y, hY⟩ : ∃ Y : ℝ, Y = f * (n : ℝ) ^ 3 * L / m` from `⟨_, rfl⟩`. Establish `hYm : Y * m = f * (n : ℝ) ^ 3 * L` using `by rw [hY]; field_simp`. Establish `hW' : 10 * ((r : ℝ) * f) + 10 * L * (r * f * Y) ≤ nW`. Use `le_of_eq_of_le ?_ hW` and prove the remaining obligations.

Rewrite using `[hY]`. Expand and normalize the polynomial expressions, which then agree. Establish `hYL : L ≤ Y`. Rewrite using `[hY, le_div_iff₀ (by positivity)]`. Establish `h1 : (m : ℝ) ≤ (n : ℝ) ^ 3` using `hmn'.trans (le_self_pow₀ hn' (by norm_num))`.

Establish `h2 : (n : ℝ) ^ 3 ≤ f * (n : ℝ) ^ 3` using `le_mul_of_one_le_left (by positivity) (by linarith)`. Establish `h3` using `mul_le_mul_of_nonneg_right (h1.trans h2) (show 0 ≤ L by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrf : (0 : ℝ) ≤ r * f` using `by positivity`. Establish `hP : (0 : ℝ) ≤ r * f * Y` using `mul_nonneg hrf (by linarith)`.

Establish `hPL : 3 * (r * f * Y) ≤ L * (r * f * Y)` using `mul_le_mul_of_nonneg_right hL hP`. Use `⟨?_, fun hl => ?_, fun hl hb h => ?_, fun hl h hA => ?_⟩` and prove the remaining obligations. Establish `: (8 * r * f : ℝ) ≤ nW` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `h1 : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 * Y`.

Use `level_le k l hk1 hl` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ((RF.i0 k l : ℕ) : ℝ) * n ≤ 3 * Y * r` using `mul_le_mul h1 hnr' (by positivity) (by linarith)`. Establish `h3` using `mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ f by positivity)`. Establish `: (f * (((RF.i0 k l : ℕ) : ℝ) * n) + 2 * r * f : ℝ) ≤ nW` using `by linarith`.

Conclude with `this` after adjusting the coercions. Establish `hl' : (3 : ℝ) ≤ l` using `by exact_mod_cast hl`. Establish `hq : (0 : ℝ) < T * ((l : ℝ) - 1)` using `mul_pos (by linarith) (by linarith)`. Rewrite `h` using `[div_le_iff₀ hD]`. Establish `hbY : b ≤ l * T * Y`.

Use `le_of_mul_le_mul_left (a := (m : ℝ)) ?_ (by linarith)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hTY : (0 : ℝ) ≤ T * Y` using `mul_nonneg (by linarith) (by linarith)`. Establish `hz : 3 * b / (T * ((l : ℝ) - 1)) ≤ 6 * Y`. Rewrite using `[div_le_iff₀ hq]`.

Use `mul_le_mul_of_nonneg_right hl' hTY` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `⟨⌈3 * b / (T * ((l : ℝ) - 1))⌉₊, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `(Nat.ceil_lt_add_one (show 0 ≤ 3 * b / (T * ((l : ℝ) - 1)) by positivity)).le`. Establish `h2` using `mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left hz 1)) hrf`.

Establish `: (4 * r * (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * f : ℝ) ≤ nW` using `by linarith`. Conclude with `this` after adjusting the coercions. Establish `h1` using `Nat.le_ceil (3 * b / (T * ((l : ℝ) - 1)))`. Rewrite `h1` using `[div_le_iff₀ hq]`. Establish `h2 : (x : ℝ) ≤ (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * ((l : ℝ) - 1)`.

Use `le_of_mul_le_mul_left (a := (T : ℝ)) ?_ (by linarith)` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3 : ((l : ℝ) - 1) = ((l - 1 : ℕ) : ℝ)`. Rewrite using `[Nat.cast_sub (by omega)]; simp`. Generalize the expression as in `⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ = s at h2 ⊢`.

Rewrite `h2` using `[h3]`. Conclude with `h2` after adjusting the coercions. Establish `hl' : (0 : ℝ) < l` using `by exact_mod_cast hl`. Rewrite `h` using `[lt_div_iff₀ hD]`. Rewrite using `[le_div_iff₀ hl']`.

Establish `h1 : (m : ℝ) * b ≤ m * A` using `mul_le_mul_of_nonneg_left hA (by linarith)`. Establish `h2 : l * (T * f * (n : ℝ) ^ 3 * Real.log k) ≤ l * (T * f * (n : ℝ) ^ 3 * L)` using `by gcongr`. Establish `h3` using `mul_le_mul_of_nonneg_left (h2.trans (h.le.trans h1)) hlog`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ (r f n m nW T l k : ℕ) (b L A : ℝ), 1 ≤ m → m ≤ n → n ≤ r → 2 ≤ f → 1 ≤ T → n + 1 = k → 3 ≤ L → Real.log k ≤ L → 10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * L ^ 2 / m) ≤ nW →
  8 * r * f ≤ nW ∧ (5 ≤ l → f * (RF.i0 k l * n) + 2 * r * f ≤ nW) ∧
  (3 ≤ l → 0 ≤ b → m * b / (T * f * (n : ℝ) ^ 3 * L) ≤ l → ∃ s : ℕ, 4 * r * s * f ≤ nW ∧ ∀ x : ℕ, (T : ℝ) * x ≤ 3 * b → x ≤ s * (l - 1)) ∧
  (0 < l → (l : ℝ) < m * b / (T * f * (n : ℝ) ^ 3 * L) → b ≤ A → T * f * (n : ℝ) ^ 3 * Real.log k ^ 2 ≤ Real.log k * m * A / l) := by
  intro r f n m nW T l k b L A hm hmn hnr hf hT hk hL hkL hW
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hk1 : 1 ≤ k := by omega
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hn' : (1 : ℝ) ≤ n := hm'.trans hmn'
  have hr' : (1 : ℝ) ≤ r := hn'.trans hnr'
  have hD : (0 : ℝ) < T * f * (n : ℝ) ^ 3 * L := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = f * (n : ℝ) ^ 3 * L / m := ⟨_, rfl⟩
  have hYm : Y * m = f * (n : ℝ) ^ 3 * L := by rw [hY]; field_simp
  have hW' : 10 * ((r : ℝ) * f) + 10 * L * (r * f * Y) ≤ nW := by
    refine le_of_eq_of_le ?_ hW
    rw [hY]; ring
  have hYL : L ≤ Y := by
    rw [hY, le_div_iff₀ (by positivity)]
    have h1 : (m : ℝ) ≤ (n : ℝ) ^ 3 := hmn'.trans (le_self_pow₀ hn' (by norm_num))
    have h2 : (n : ℝ) ^ 3 ≤ f * (n : ℝ) ^ 3 := le_mul_of_one_le_left (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (show 0 ≤ L by linarith)
    linarith
  have hrf : (0 : ℝ) ≤ r * f := by positivity
  have hP : (0 : ℝ) ≤ r * f * Y := mul_nonneg hrf (by linarith)
  have hPL : 3 * (r * f * Y) ≤ L * (r * f * Y) := mul_le_mul_of_nonneg_right hL hP
  refine ⟨?_, fun hl => ?_, fun hl hb h => ?_, fun hl h hA => ?_⟩
  · have : (8 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have h1 : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 * Y := by
      have := level_le k l hk1 hl
      linarith
    have h2 : ((RF.i0 k l : ℕ) : ℝ) * n ≤ 3 * Y * r :=
      mul_le_mul h1 hnr' (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ f by positivity)
    have : (f * (((RF.i0 k l : ℕ) : ℝ) * n) + 2 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
    have hq : (0 : ℝ) < T * ((l : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    rw [div_le_iff₀ hD] at h
    have hbY : b ≤ l * T * Y := by
      refine le_of_mul_le_mul_left (a := (m : ℝ)) ?_ (by linarith)
      calc (m : ℝ) * b ≤ l * (T * f * (n : ℝ) ^ 3 * L) := h
        _ = l * T * (Y * m) := by rw [hYm]; ring
        _ = _ := by ring
    have hTY : (0 : ℝ) ≤ T * Y := mul_nonneg (by linarith) (by linarith)
    have hz : 3 * b / (T * ((l : ℝ) - 1)) ≤ 6 * Y := by
      rw [div_le_iff₀ hq]
      have := mul_le_mul_of_nonneg_right hl' hTY
      nlinarith
    refine ⟨⌈3 * b / (T * ((l : ℝ) - 1))⌉₊, ?_, fun x hx => ?_⟩
    · have h1 := (Nat.ceil_lt_add_one (show 0 ≤ 3 * b / (T * ((l : ℝ) - 1)) by positivity)).le
      have h2 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left hz 1)) hrf
      have : (4 * r * (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * f : ℝ) ≤ nW := by linarith
      exact_mod_cast this
    · have h1 := Nat.le_ceil (3 * b / (T * ((l : ℝ) - 1)))
      rw [div_le_iff₀ hq] at h1
      have h2 : (x : ℝ) ≤ (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * ((l : ℝ) - 1) := by
        refine le_of_mul_le_mul_left (a := (T : ℝ)) ?_ (by linarith)
        linarith
      have h3 : ((l : ℝ) - 1) = ((l - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      generalize ⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ = s at h2 ⊢
      rw [h3] at h2
      exact_mod_cast h2
  · have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    rw [lt_div_iff₀ hD] at h
    rw [le_div_iff₀ hl']
    have h1 : (m : ℝ) * b ≤ m * A := mul_le_mul_of_nonneg_left hA (by linarith)
    have h2 : l * (T * f * (n : ℝ) ^ 3 * Real.log k) ≤ l * (T * f * (n : ℝ) ^ 3 * L) := by
      gcongr
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (h.le.trans h1)) hlog
    linarith

end GlobalTheory.RowBudgets
