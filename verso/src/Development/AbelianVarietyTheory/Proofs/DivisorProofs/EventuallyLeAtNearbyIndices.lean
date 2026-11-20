import Mathlib
open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Establish `hu' : Tendsto (fun M : ℕ => (u M : ℝ)) atTop atTop`. Establish `h1 : Tendsto (fun M : ℕ => (u M : ℝ) / M * M) atTop atTop` using `Tendsto.pos_mul_atTop hr hu tendsto_natCast_atTop_atTop`. Use `h1.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with M hM`. Establish `: (M : ℝ) ≠ 0` using `by exact_mod_cast hM.ne'`.

Clear the denominators using the available nonvanishing facts. Establish `huN : Tendsto u atTop atTop` using `tendsto_natCast_atTop_iff.1 hu'`. Use `⟨?_, huN⟩` and prove the remaining obligations. Establish `h2` using `(hh.comp huN).mul (hu.pow d)`. Use `h2.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_gt_atTop 0, huN.eventually (eventually_gt_atTop 0)] with M hM huM`. Establish `a : (M : ℝ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `b : (u M : ℝ) ≠ 0` using `by exact_mod_cast huM.ne'`. Simplify using `only [Function.comp]`. Rewrite using `[div_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem tendsto_comp_div_pow_of_ratio (d : ℕ) (h : ℕ → ℝ) (L r : ℝ) (u : ℕ → ℕ) (hr : 0 < r)
    (hh : Tendsto (fun j : ℕ => h j / (j : ℝ) ^ d) atTop (𝓝 L))
    (hu : Tendsto (fun M : ℕ => (u M : ℝ) / M) atTop (𝓝 r)) :
    Tendsto (fun M : ℕ => h (u M) / (M : ℝ) ^ d) atTop (𝓝 (L * r ^ d)) ∧
      Tendsto u atTop atTop := by
  have hu' : Tendsto (fun M : ℕ => (u M : ℝ)) atTop atTop := by
    have h1 : Tendsto (fun M : ℕ => (u M : ℝ) / M * M) atTop atTop :=
      Tendsto.pos_mul_atTop hr hu tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM
    have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    field_simp
  have huN : Tendsto u atTop atTop := tendsto_natCast_atTop_iff.1 hu'
  refine ⟨?_, huN⟩
  have h2 := (hh.comp huN).mul (hu.pow d)
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0, huN.eventually (eventually_gt_atTop 0)] with M hM huM
  have a : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have b : (u M : ℝ) ≠ 0 := by exact_mod_cast huM.ne'
  simp only [Function.comp]
  rw [div_pow]
  field_simp

/- English proof (translation)
Establish `hnR : (0:ℝ) < n` using `by exact_mod_cast hn`. Establish `hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n))`. Use `(tendsto_one_div_atTop_nhds_zero_nat).const_sub (1 / (n:ℝ))` as an intermediate fact. Rewrite `this` using `[sub_zero]`. Then use the resulting hypothesis. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_gt_atTop 0] with M hM`. Establish `hMR : (0:ℝ) < M` using `by exact_mod_cast hM`. Establish `key : (M:ℝ) / n - 1 ≤ ((M / n : ℕ) : ℝ)`. Use `Nat.lt_floor_add_one ((M:ℝ) / n)` as an intermediate fact. Rewrite `this` using `[Nat.floor_div_eq_div]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[le_div_iff₀ hMR]`. Establish `: (1 / (n:ℝ) - 1 / M) * M = M / n - 1` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Use `filter_upwards [eventually_gt_atTop 0] with M hM`.

Establish `hMR : (0:ℝ) < M` using `by exact_mod_cast hM`. Rewrite using `[div_le_iff₀ hMR]`. Use `Nat.cast_div_le (α := ℝ) (m := M) (n := n)` as an intermediate fact. Establish `e : 1 / (n:ℝ) * M = M / n` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem tendsto_natDiv_div_self (n : ℕ) (hn : 0 < n) :
    Tendsto (fun M : ℕ => ((M / n : ℕ) : ℝ) / M) atTop (𝓝 (1 / n)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlow : Tendsto (fun M : ℕ => 1 / (n:ℝ) - 1 / (M:ℝ)) atTop (𝓝 (1 / n)) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_sub (1 / (n:ℝ))
    rwa [sub_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    have key : (M:ℝ) / n - 1 ≤ ((M / n : ℕ) : ℝ) := by
      have := Nat.lt_floor_add_one ((M:ℝ) / n)
      rw [Nat.floor_div_eq_div] at this
      linarith
    rw [le_div_iff₀ hMR]
    have : (1 / (n:ℝ) - 1 / M) * M = M / n - 1 := by field_simp
    linarith
  · filter_upwards [eventually_gt_atTop 0] with M hM
    have hMR : (0:ℝ) < M := by exact_mod_cast hM
    rw [div_le_iff₀ hMR]
    have := Nat.cast_div_le (α := ℝ) (m := M) (n := n)
    have e : 1 / (n:ℝ) * M = M / n := by ring
    linarith

/- English proof (translation)
Introduce `d b c f g f₀ α β _hd hb hf hf₀ hg ε hε`. Establish `hbR : (0:ℝ) < b` using `by exact_mod_cast hb`. Establish `hlim : Tendsto (fun n : ℕ => α * ((b:ℝ) + 1 / (n:ℝ)) ^ d) atTop (𝓝 (α * (b:ℝ) ^ d))`. Use `((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul α` as an intermediate fact. Rewrite `this` using `[add_zero]`. Then use the resulting hypothesis.

Establish `hn : ∀ᶠ n : ℕ in atTop, α * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * (b:ℝ) ^ d + ε / 3` using `(tendsto_order.1 hlim).2 _ (by linarith)`. Use `filter_upwards [hn, eventually_gt_atTop 0] with n hn hn0`. Establish `hnR : (0:ℝ) < n` using `by exact_mod_cast hn0`. Establish `hrpos : (0:ℝ) < (b:ℝ) + 1 / (n:ℝ)` using `by positivity`. Choose the witnesses or unpack the hypotheses as in `⟨η, hη, hηlt⟩ : ∃ η : ℝ, 0 < η ∧ (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 := by`.

Establish `hcont : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝[>] 0) (𝓝 (α * ((b:ℝ) + 1 / (n:ℝ)) ^ d))`. Establish `: Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝 0) (𝓝 ((α + β * 0) * ((b:ℝ) + 1 / (n:ℝ)) ^ d))` using `((continuous_const.add (continuous_const.mul continuous_id)).mul continuous_const).tendsto 0`. Rewrite `this` using `[mul_zero, add_zero]`. Conclude with `this.mono_left nhdsWithin_le_nhds`. Establish `hev` using `(hcont.eventually (gt_mem_nhds (show α * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 by linarith))).and (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioi 0)`.

Take `⟨η, h1, h2⟩` from `hev.exists`. Conclude with `⟨η, h2, h1⟩`. Establish `hc0 : Tendsto (fun M : ℕ => (c:ℝ) / M) atTop (𝓝 0)` using `tendsto_const_div_atTop_nhds_zero_nat _`. Establish `hr₁ : Tendsto (fun M : ℕ => ((b * M + M / n - c : ℕ) : ℝ) / M) atTop (𝓝 ((b:ℝ) + 1 / (n:ℝ)))`. Establish `: Tendsto (fun M : ℕ => (b:ℝ) + ((M / n : ℕ) : ℝ) / M - (c:ℝ) / M) atTop (𝓝 ((b:ℝ) + 1 / n - 0))` using `((tendsto_natDiv_div_self n hn0).const_add _).sub hc0`.

Rewrite `this` using `[sub_zero]`. Use `this.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0`. Establish `hMR : (M:ℝ) ≠ 0` using `by exact_mod_cast hM0.ne'`. Establish `hle : c ≤ b * M + M / n` using `le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))`.

Rewrite using `[Nat.cast_sub hle]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hr₀ : Tendsto (fun M : ℕ => ((b * M - c : ℕ) : ℝ) / M) atTop (𝓝 (b:ℝ))`. Establish `: Tendsto (fun M : ℕ => (b:ℝ) - (c:ℝ) / M) atTop (𝓝 ((b:ℝ) - 0))` using `tendsto_const_nhds.sub hc0`.

Rewrite `this` using `[sub_zero]`. Use `this.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0`. Establish `hMR : (M:ℝ) ≠ 0` using `by exact_mod_cast hM0.ne'`. Establish `hle : c ≤ b * M` using `le_trans hMc (Nat.le_mul_of_pos_left M hb)`.

Rewrite using `[Nat.cast_sub hle]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take `⟨hA, hu₁⟩` from `tendsto_comp_div_pow_of_ratio d (f η) (α + β * η) _ _ hrpos (hf η hη.le) hr₁`. Take `⟨hB, -⟩` from `tendsto_comp_div_pow_of_ratio d (f 0) (α + β * 0) _ _ hbR (hf 0 le_rfl) hr₀`.

Establish `hev : ∀ᶠ M : ℕ in atTop, f η (b * M + M / n - c) / (M:ℝ) ^ d - f 0 (b * M - c) / (M:ℝ) ^ d < ε` using `(tendsto_order.1 (hA.sub hB)).2 ε (by rw [mul_zero, add_zero]; linarith)`. Use `filter_upwards [hev, hu₁.eventually (hg η hη), eventually_ge_atTop c, eventually_gt_atTop 0] with M hM hgM hMc hM0`. Establish `hMR : (0:ℝ) < M` using `by exact_mod_cast hM0`. Establish `hle1 : c ≤ b * M + M / n` using `le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))`. Establish `hle0 : c ≤ b * M` using `le_trans hMc (Nat.le_mul_of_pos_left M hb)`.

Establish `e1 : ((b:ℤ) * M + ((M / n : ℕ) : ℤ) - c) = ((b * M + M / n - c : ℕ) : ℤ)`. Rewrite using `[Nat.cast_sub hle1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e0 : ((b:ℤ) * M - c) = ((b * M - c : ℕ) : ℤ)`.

Rewrite using `[Nat.cast_sub hle0]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e0, hf₀]`. Establish `hpos : 0 < (M:ℝ) ^ d` using `pow_pos hMR d`.

Rewrite `hM` using `[← sub_div, div_lt_iff₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eventually_le_at_nearby_indices :
    ∀ (d b c : ℕ) (f : ℝ → ℕ → ℝ) (g : ℤ → ℝ) (f₀ : ℤ → ℝ) (α β : ℝ), 0 < d → 0 < b →
      (∀ η, 0 ≤ η → Tendsto (fun j : ℕ => f η j / (j : ℝ) ^ d) atTop (𝓝 (α + β * η))) →
      (∀ j : ℕ, f₀ j = f 0 j) → (∀ η, 0 < η → ∀ᶠ j : ℕ in atTop, g j ≤ f η j) →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
        g (b * M + (M / n : ℕ) - c) ≤ f₀ (b * M - c) + ε * (M : ℝ) ^ d := by
  intro d b c f g f₀ α β _hd hb hf hf₀ hg ε hε
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hlim : Tendsto (fun n : ℕ => α * ((b:ℝ) + 1 / (n:ℝ)) ^ d) atTop
      (𝓝 (α * (b:ℝ) ^ d)) := by
    have := ((tendsto_one_div_atTop_nhds_zero_nat.const_add (b : ℝ)).pow d).const_mul α
    rwa [add_zero] at this
  have hn : ∀ᶠ n : ℕ in atTop, α * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * (b:ℝ) ^ d + ε / 3 :=
    (tendsto_order.1 hlim).2 _ (by linarith)
  filter_upwards [hn, eventually_gt_atTop 0] with n hn hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hrpos : (0:ℝ) < (b:ℝ) + 1 / (n:ℝ) := by positivity
  obtain ⟨η, hη, hηlt⟩ : ∃ η : ℝ, 0 < η ∧
      (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d < α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 := by
    have hcont : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝[>] 0)
        (𝓝 (α * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) := by
      have : Tendsto (fun η : ℝ => (α + β * η) * ((b:ℝ) + 1 / (n:ℝ)) ^ d) (𝓝 0)
          (𝓝 ((α + β * 0) * ((b:ℝ) + 1 / (n:ℝ)) ^ d)) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).mul
          continuous_const).tendsto 0
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev := (hcont.eventually (gt_mem_nhds (show α * ((b:ℝ) + 1 / (n:ℝ)) ^ d <
      α * ((b:ℝ) + 1 / (n:ℝ)) ^ d + ε / 3 by linarith))).and
      (self_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0:ℝ), x ∈ Set.Ioi 0)
    obtain ⟨η, h1, h2⟩ := hev.exists
    exact ⟨η, h2, h1⟩
  have hc0 : Tendsto (fun M : ℕ => (c:ℝ) / M) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hr₁ : Tendsto (fun M : ℕ => ((b * M + M / n - c : ℕ) : ℝ) / M) atTop
      (𝓝 ((b:ℝ) + 1 / (n:ℝ))) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) + ((M / n : ℕ) : ℝ) / M - (c:ℝ) / M) atTop
        (𝓝 ((b:ℝ) + 1 / n - 0)) :=
      ((tendsto_natDiv_div_self n hn0).const_add _).sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M + M / n :=
      le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  have hr₀ : Tendsto (fun M : ℕ => ((b * M - c : ℕ) : ℝ) / M) atTop (𝓝 (b:ℝ)) := by
    have : Tendsto (fun M : ℕ => (b:ℝ) - (c:ℝ) / M) atTop (𝓝 ((b:ℝ) - 0)) :=
      tendsto_const_nhds.sub hc0
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop c, eventually_gt_atTop 0] with M hMc hM0
    have hMR : (M:ℝ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hle : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
    rw [Nat.cast_sub hle]
    push_cast
    field_simp
  obtain ⟨hA, hu₁⟩ := tendsto_comp_div_pow_of_ratio d (f η) (α + β * η) _ _ hrpos
    (hf η hη.le) hr₁
  obtain ⟨hB, -⟩ := tendsto_comp_div_pow_of_ratio d (f 0) (α + β * 0) _ _ hbR
    (hf 0 le_rfl) hr₀
  have hev : ∀ᶠ M : ℕ in atTop,
      f η (b * M + M / n - c) / (M:ℝ) ^ d - f 0 (b * M - c) / (M:ℝ) ^ d < ε :=
    (tendsto_order.1 (hA.sub hB)).2 ε (by rw [mul_zero, add_zero]; linarith)
  filter_upwards [hev, hu₁.eventually (hg η hη), eventually_ge_atTop c, eventually_gt_atTop 0]
    with M hM hgM hMc hM0
  have hMR : (0:ℝ) < M := by exact_mod_cast hM0
  have hle1 : c ≤ b * M + M / n :=
    le_trans hMc (le_trans (Nat.le_mul_of_pos_left M hb) (Nat.le_add_right _ _))
  have hle0 : c ≤ b * M := le_trans hMc (Nat.le_mul_of_pos_left M hb)
  have e1 : ((b:ℤ) * M + ((M / n : ℕ) : ℤ) - c) = ((b * M + M / n - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle1]; push_cast; ring
  have e0 : ((b:ℤ) * M - c) = ((b * M - c : ℕ) : ℤ) := by
    rw [Nat.cast_sub hle0]; push_cast; ring
  rw [e1, e0, hf₀]
  have hpos : 0 < (M:ℝ) ^ d := pow_pos hMR d
  rw [← sub_div, div_lt_iff₀ hpos] at hM
  linarith

end GlobalTheory
