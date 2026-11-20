import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCardSupNormBallLeGramDetStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

/- English proof (translation)
Establish `hδ : 0 < t - Real.log C` using `sub_pos.2 ht`. Establish `hc1 : 0 < |c| + 1` using `by positivity`. Establish `h1` using `(isLittleO_pow_exp_pos_mul_atTop n hδ).bound (c := 1 / (|c| + 1)) (by positivity)`. Establish `h2` using `tendsto_natCast_atTop_atTop.eventually h1`. Use `filter_upwards [h2] with m hm`.

Establish `hCpos : 0 < C` using `by linarith`. Rewrite `hm` using `[Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le]`. Establish `hexp : Real.exp (t * m) = Real.exp ((t - Real.log C) * m) * C ^ m`. Rewrite using `[← Real.rpow_natCast, Real.rpow_def_of_pos hCpos, ← Real.exp_add]`. Put the polynomial expressions in normal form.

Rewrite using `[hexp]`. Establish `hmn : (0 : ℝ) ≤ (m : ℝ) ^ n` using `by positivity`. Establish `hle : c * (m : ℝ) ^ n ≤ Real.exp ((t - Real.log C) * m)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_le_mul_of_nonneg_right hle (by positivity)`.
-/
theorem eventually_poly_mul_pow_le_exp (c C t : ℝ) (n : ℕ) (hC : 1 ≤ C) (ht : Real.log C < t) :
    ∀ᶠ m : ℕ in atTop, c * (m : ℝ) ^ n * C ^ m ≤ Real.exp (t * m) := by
  have hδ : 0 < t - Real.log C := sub_pos.2 ht
  have hc1 : 0 < |c| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop n hδ).bound (c := 1 / (|c| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  have hCpos : 0 < C := by linarith
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_pos _).le] at hm
  have hexp : Real.exp (t * m) = Real.exp ((t - Real.log C) * m) * C ^ m := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hCpos, ← Real.exp_add]; ring_nf
  rw [hexp]
  have hmn : (0 : ℝ) ≤ (m : ℝ) ^ n := by positivity
  have hle : c * (m : ℝ) ^ n ≤ Real.exp ((t - Real.log C) * m) := by
    calc c * (m : ℝ) ^ n ≤ (|c| + 1) * (m : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right (by linarith [le_abs_self c]) hmn
      _ ≤ (|c| + 1) * (1 / (|c| + 1) * Real.exp ((t - Real.log C) * m)) :=
          mul_le_mul_of_nonneg_left hm hc1.le
      _ = _ := by field_simp
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/- English proof (translation)
Introduce `k _ X _ p D hX hS P hP ω r f hf hli g hg C hC hball t ht`. Use `haveI := hX.finite_emb`. Use `letI := Fintype.ofFinite (k →+* ℂ)`. Establish `hρ` using `fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hS P.L hP σ (ω σ)`. Use `choose ρ hρr hρ0 _ using hρ`.

Establish `hbd : ∀ σ, ∃ b : ℝ, ∀ y, ρ σ y ≤ b` using `fun σ => by haveI := hX.compactSpace σ`. Take `⟨b, hb⟩` from `(isCompact_range (hρr σ).1).bddAbove`. Conclude with `⟨b, fun y => hb ⟨y, rfl⟩⟩`. Use `choose b hb using hbd`. Use `set B : ℝ := ∑ σ, |b σ| with hBdef`.

Establish `hB0 : 0 ≤ B` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`. Establish `hρB : ∀ σ y, ρ σ y ≤ B` using `fun σ y => (hb σ y).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |b σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))`. Use `set K : ℝ := B / D.factorial + 1 with hKdef`. Establish `hK : 1 ≤ K`. Establish `: 0 ≤ B / D.factorial` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set V : ℝ := max 1 (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) with hVdef`. Establish `hV : 1 ≤ V` using `le_max_left _ _`. Establish `hmorse` using `GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hS P hP ω ρ hρr 1 one_pos`. Establish `hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ (g + 1) * (m : ℝ) ^ D` using `by filter_upwards [hg.eventually (gt_mem_nhds (lt_add_one g)), eventually_ge_atTop 1] with m hm h1`.

Establish `h0 : (0 : ℝ) < (m : ℝ) ^ D` using `pow_pos (by exact_mod_cast h1) D`. Conclude with `((div_lt_iff₀ h0).1 hm).le`. Establish `hexp` using `eventually_poly_mul_pow_le_exp (2 * (g + 1) * K * V) C t (2 * D) hC ht`. Use `squeeze_zero_norm' (a := fun m : ℕ => 2 * ((r m : ℝ) / (m : ℝ) ^ D) * ((Real.log (2 * K * V) + D * Real.log m) / m)) ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hmorse, hr, hexp, eventually_ge_atTop 1] with m hm hrm hem h1`.

Establish `hm1 : (1 : ℝ) ≤ m` using `by exact_mod_cast h1`. Establish `hm0 : (0 : ℝ) < m` using `by linarith`. Establish `hmD : (0 : ℝ) < (m : ℝ) ^ D` using `pow_pos hm0 D`. Establish `hM : 1 ≤ K * (m : ℝ) ^ D` using `one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm1)`. Establish `hcmb : ∀ (c : Fin (r m) → ℂ) σ y, cmb (vals P m 1 (f m)) c σ y ≤ K * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c`.

Introduce `c σ y`. Establish `h` using `hm (Fin (r m)) (f m) (hf m) c σ y`. Establish `hl2 : 0 ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c` using `finsum_nonneg fun σ => integral_nonneg fun y => by unfold cmb; positivity`. Use `h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hmD.le) hl2)` and prove the remaining obligations. Establish `: ρ σ y / D.factorial ≤ B / D.factorial` using `div_le_div_of_nonneg_right (hρB σ y) (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR : 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V) ≤ Real.exp (t * m)`. Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ C ^ m * (K * (m : ℝ) ^ D * V)`. Establish `: 0 ≤ C` using `by linarith`.

Check the signs of the components of the expression. Use the polynomial consequences of the given equalities and inequalities. Use `_ = 2 * (g + 1) * K * V * (m : ℝ) ^ (2 * D) * C ^ m := by ring`. Use `_ ≤ _ := hem`. Establish `key` using `GlobalTheory.T.abs_log_card_ballIn_sub_gramVolume_le k X p D hX hS P ω (m : ℤ) 1 (r m) (f m) (hf m) (hli m) (K * (m : ℝ) ^ D) V (C ^ m) (Real.exp (t * m)) hM hV (le_max_right _ _) (by positivity) (Real.exp_pos _) hcmb (hball m h1) hR`.

Rewrite `key` using `[Real.log_exp]`. Establish `hlog : Real.log (2 * (K * (m : ℝ) ^ D * V)) = Real.log (2 * K * V) + D * Real.log m`. Establish `e : 2 * (K * (m : ℝ) ^ D * V) = (2 * K * V) * (m : ℝ) ^ D` using `by ring`. Rewrite using `[e, Real.log_mul (by positivity) hmD.ne', Real.log_pow]`. Establish `hmD1 : (0 : ℝ) < (m : ℝ) ^ (D + 1)` using `pow_pos hm0 _`.

Rewrite using `[Real.norm_eq_abs, abs_div, abs_of_pos hmD1, div_le_iff₀ hmD1]`. Use `key.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hlog, pow_succ]`. Clear the denominators using the available nonvanishing facts. Establish `h1 : Tendsto (fun m : ℕ => 2 * ((r m : ℝ) / (m : ℝ) ^ D)) atTop (𝓝 (2 * g))` using `hg.const_mul 2`.

Establish `hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0)`. Simplify using `using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero`. Establish `h2 : Tendsto (fun m : ℕ => (Real.log (2 * K * V) + D * Real.log m) / m) atTop (𝓝 0)`. Use `((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (2 * K * V))).add ((hl.comp tendsto_natCast_atTop_atTop).const_mul (D : ℝ))` as an intermediate fact. Simplify using `only [mul_zero, add_zero] at this`.

Use `this.congr fun m => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `using h1.mul h2`.
-/
theorem count_ball_asymp : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → ∀ g : ℝ, Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 g) → ∀ C : ℝ, 1 ≤ C → (∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤ AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m))) → ∀ t : ℝ, Real.log C < t → Tendsto (fun m : ℕ => (Real.log ((ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (Real.exp (t * m))).ncard : ℝ) - (r m * (t * m) - Real.log (gram (fun σ => (ω σ).meas) (vals P m 1 (f m))).det.re / 2 + Real.log (volume {x : Fin (r m) → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 0) := by
  intro k _ X _ p D hX hS P hP ω r f hf hli g hg C hC hball t ht
  haveI := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hρ := fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hS P.L hP σ (ω σ)
  choose ρ hρr hρ0 _ using hρ
  have hbd : ∀ σ, ∃ b : ℝ, ∀ y, ρ σ y ≤ b := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨b, hb⟩ := (isCompact_range (hρr σ).1).bddAbove
    exact ⟨b, fun y => hb ⟨y, rfl⟩⟩
  choose b hb using hbd
  set B : ℝ := ∑ σ, |b σ| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hρB : ∀ σ y, ρ σ y ≤ B := fun σ y => (hb σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |b σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set K : ℝ := B / D.factorial + 1 with hKdef
  have hK : 1 ≤ K := by
    have : 0 ≤ B / D.factorial := by positivity
    linarith
  set V : ℝ := max 1 (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) with hVdef
  have hV : 1 ≤ V := le_max_left _ _
  have hmorse := GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hS P hP ω ρ hρr 1 one_pos
  have hr : ∀ᶠ m : ℕ in atTop, (r m : ℝ) ≤ (g + 1) * (m : ℝ) ^ D := by
    filter_upwards [hg.eventually (gt_mem_nhds (lt_add_one g)), eventually_ge_atTop 1] with m hm h1
    have h0 : (0 : ℝ) < (m : ℝ) ^ D := pow_pos (by exact_mod_cast h1) D
    exact ((div_lt_iff₀ h0).1 hm).le
  have hexp := eventually_poly_mul_pow_le_exp (2 * (g + 1) * K * V) C t (2 * D) hC ht
  refine squeeze_zero_norm' (a := fun m : ℕ =>
    2 * ((r m : ℝ) / (m : ℝ) ^ D) * ((Real.log (2 * K * V) + D * Real.log m) / m)) ?_ ?_
  · filter_upwards [hmorse, hr, hexp, eventually_ge_atTop 1] with m hm hrm hem h1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast h1
    have hm0 : (0 : ℝ) < m := by linarith
    have hmD : (0 : ℝ) < (m : ℝ) ^ D := pow_pos hm0 D
    have hM : 1 ≤ K * (m : ℝ) ^ D := one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hm1)
    have hcmb : ∀ (c : Fin (r m) → ℂ) σ y, cmb (vals P m 1 (f m)) c σ y ≤
        K * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c := by
      intro c σ y
      have h := hm (Fin (r m)) (f m) (hf m) c σ y
      have hl2 : 0 ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 (f m)) c :=
        finsum_nonneg fun σ => integral_nonneg fun y => by unfold cmb; positivity
      refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hmD.le) hl2)
      have : ρ σ y / D.factorial ≤ B / D.factorial :=
        div_le_div_of_nonneg_right (hρB σ y) (by positivity)
      linarith
    have hR : 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V) ≤ Real.exp (t * m) := by
      calc 2 * (r m : ℝ) * C ^ m * (K * (m : ℝ) ^ D * V)
          ≤ 2 * ((g + 1) * (m : ℝ) ^ D) * C ^ m * (K * (m : ℝ) ^ D * V) := by
            have : 0 ≤ C ^ m * (K * (m : ℝ) ^ D * V) := by
              have : 0 ≤ C := by linarith
              positivity
            nlinarith
        _ = 2 * (g + 1) * K * V * (m : ℝ) ^ (2 * D) * C ^ m := by ring
        _ ≤ _ := hem
    have key := GlobalTheory.T.abs_log_card_ballIn_sub_gramVolume_le k X p D hX hS P ω (m : ℤ) 1 (r m) (f m) (hf m) (hli m) (K * (m : ℝ) ^ D) V (C ^ m)
      (Real.exp (t * m)) hM hV (le_max_right _ _) (by positivity) (Real.exp_pos _) hcmb (hball m h1) hR
    rw [Real.log_exp] at key
    have hlog : Real.log (2 * (K * (m : ℝ) ^ D * V)) = Real.log (2 * K * V) + D * Real.log m := by
      have e : 2 * (K * (m : ℝ) ^ D * V) = (2 * K * V) * (m : ℝ) ^ D := by ring
      rw [e, Real.log_mul (by positivity) hmD.ne', Real.log_pow]
    have hmD1 : (0 : ℝ) < (m : ℝ) ^ (D + 1) := pow_pos hm0 _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hmD1, div_le_iff₀ hmD1]
    refine key.trans (le_of_eq ?_)
    rw [hlog, pow_succ]
    field_simp
  · have h1 : Tendsto (fun m : ℕ => 2 * ((r m : ℝ) / (m : ℝ) ^ D)) atTop (𝓝 (2 * g)) := hg.const_mul 2
    have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h2 : Tendsto (fun m : ℕ => (Real.log (2 * K * V) + D * Real.log m) / m) atTop (𝓝 0) := by
      have := ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log (2 * K * V))).add
        ((hl.comp tendsto_natCast_atTop_atTop).const_mul (D : ℝ))
      simp only [mul_zero, add_zero] at this
      refine this.congr fun m => ?_
      simp only [Function.comp_apply]
      ring
    simpa using h1.mul h2

end GlobalTheory.HSAmp
