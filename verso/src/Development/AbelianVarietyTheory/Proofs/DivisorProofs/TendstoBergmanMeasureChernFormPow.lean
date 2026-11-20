import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BergmanFunctionTotalMassExtremalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFinsumIntegralWeightSubLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChernTopPowerVolumeDensityRatioStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

/- English proof (translation)
Rewrite using `[Metric.tendsto_nhds]`. Introduce `e he`. Establish `hK : 0 < |W| + C * |V| + 1` using `by positivity`. Use `set ε := e / (2 * (|W| + C * |V| + 1)) with hε`. Establish `hε0 : 0 < ε` using `by positivity`.

Establish `hq'` using `Metric.tendsto_nhds.1 hq (e / (2 * (C + 1))) (by positivity)`. Use `filter_upwards [h ε hε0, hq'] with m hm hqm`. Rewrite `hqm`, the goal using `[Real.dist_eq]`. Establish `h1 : |a m - I| ≤ |a m - I - ε * W| + ε * |W|`. Use `abs_add_le (a m - I - ε * W) (ε * W)` as an intermediate fact.

Rewrite `this` using `[abs_mul, abs_of_pos hε0]`. Simplify using `using this`. Establish `h2 : C * (G + ε * V - q m) ≤ C * |q m - G| + C * (ε * |V|)`. Rewrite using `[← mul_add]`. Use `mul_le_mul_of_nonneg_left ?_ hC` and prove the remaining obligations.

Use `neg_abs_le (q m - G)` as an intermediate fact. Use `le_abs_self V` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : C * |q m - G| ≤ (C + 1) * |q m - G|` using `by nlinarith [abs_nonneg (q m - G)]`. Establish `h4 : (C + 1) * |q m - G| < e / 2`.

Use `mul_lt_mul_of_pos_left hqm (by linarith : (0:ℝ) < C + 1)` as an intermediate fact. Rewrite `this` using `[mul_div_assoc', mul_comm 2 (C + 1), ← div_div, mul_div_cancel_left₀ _ (by linarith : (C + 1) ≠ 0)]`. Then use the resulting hypothesis. Establish `h5 : ε * (|W| + C * |V|) < e / 2`. Rewrite using `[hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]`. Use polynomial arithmetic with `[abs_nonneg W, abs_nonneg V]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem tendsto_of_abs_sub_le_eventually (a q : ℕ → ℝ) (I G W V C : ℝ) (hC : 0 ≤ C) (hq : Tendsto q atTop (𝓝 G))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ m in atTop, |a m - I - ε * W| ≤ C * (G + ε * V - q m)) : Tendsto a atTop (𝓝 I) := by
  rw [Metric.tendsto_nhds]
  intro e he
  have hK : 0 < |W| + C * |V| + 1 := by positivity
  set ε := e / (2 * (|W| + C * |V| + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have hq' := Metric.tendsto_nhds.1 hq (e / (2 * (C + 1))) (by positivity)
  filter_upwards [h ε hε0, hq'] with m hm hqm
  rw [Real.dist_eq] at hqm ⊢
  have h1 : |a m - I| ≤ |a m - I - ε * W| + ε * |W| := by
    have := abs_add_le (a m - I - ε * W) (ε * W)
    rw [abs_mul, abs_of_pos hε0] at this
    simpa using this
  have h2 : C * (G + ε * V - q m) ≤ C * |q m - G| + C * (ε * |V|) := by
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hC
    have := neg_abs_le (q m - G)
    have := le_abs_self V
    nlinarith
  have h3 : C * |q m - G| ≤ (C + 1) * |q m - G| := by nlinarith [abs_nonneg (q m - G)]
  have h4 : (C + 1) * |q m - G| < e / 2 := by
    have := mul_lt_mul_of_pos_left hqm (by linarith : (0:ℝ) < C + 1)
    rwa [mul_div_assoc', mul_comm 2 (C + 1), ← div_div, mul_div_cancel_left₀ _ (by linarith : (C + 1) ≠ 0)] at this
  have h5 : ε * (|W| + C * |V|) < e / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg W, abs_nonneg V]
  nlinarith

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

/- English proof (translation)
Introduce `k _ X _ p D hX hG P hpos ω r f hf hli hr w hw`. Use `haveI : Finite (k →+* ℂ) := hX.finite_emb`. Use `letI := Fintype.ofFinite (k →+* ℂ)`. Establish `hcpt : ∀ σ, CompactSpace (CxPts p σ)` using `hX.compactSpace`. Establish `hfm : ∀ σ, IsFiniteMeasure (ω σ).meas` using `fun σ => (GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)).1`.

Use `choose ρ hρR hρ0 hρint using fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hG P.L hpos σ (ω σ)`. Establish `hbd : ∀ σ (g : CxPts p σ → ℝ), Continuous g → ∃ C, ∀ y, |g y| ≤ C` using `fun σ g hg => by haveI := hcpt σ`. Take `⟨C, hC⟩` from `isCompact_univ.exists_bound_of_continuousOn hg.continuousOn`. Conclude with `⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩`. Establish `hint : ∀ σ (g : CxPts p σ → ℝ), Continuous g → Integrable g (ω σ).meas` using `fun σ g hg => by haveI := hfm σ`.

Take `⟨C, hC⟩` from `hbd σ g hg`. Conclude with `Integrable.of_bound hg.aestronglyMeasurable C (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)`. Use `choose Cw hCw using fun σ => hbd σ (w σ) (hw σ)`. Use `set C : ℝ := ∑ σ, |Cw σ| with hCdef`. Establish `hC0 : 0 ≤ C` using `Finset.sum_nonneg fun _ _ => abs_nonneg _`.

Establish `hwC : ∀ σ y, |w σ y| ≤ C` using `fun σ y => (hCw σ y).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |Cw σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))`. Use `set Iw : ℝ := ∑ σ, ∫ y, w σ y * ρ σ y ∂(ω σ).meas with hIw`. Use `set G' : ℝ := ∑ σ, ∫ y, ρ σ y ∂(ω σ).meas with hG'`. Use `set W : ℝ := ∑ σ, ∫ y, w σ y ∂(ω σ).meas with hW`. Use `set V : ℝ := ∑ σ, ∫ _y, (1 : ℝ) ∂(ω σ).meas with hV`.

Establish `hch : chInt P.L D w = Iw`. Simplify using `only [chInt, finsum_eq_sum_of_fintype]`. Conclude with `Finset.sum_congr rfl fun σ _ => hρint σ (w σ) (hw σ)`. Establish `hgd : gdeg P.L D = G'`. Simplify using `only [gdeg, chInt, finsum_eq_sum_of_fintype]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[hρint σ _ continuous_const]`. Simplify using the standard rewrite rules. Rewrite using `[hch]`. Rewrite `hr` using `[hgd]`.

Use `tendsto_of_abs_sub_le_eventually _ (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) (Iw / D.factorial) (G' / D.factorial) W V C hC0 hr fun ε hε => ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hG P hpos ω ρ hρR ε hε, eventually_ge_atTop 1] with m hmo hm1`. Take `⟨hfam, hpd, -⟩` from `GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)`. Take `⟨hBi, hBs, hB0, hBx⟩` from `GlobalTheory.T.bergman_function_total_mass_extremal (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m)) (fun σ => (ω σ).meas) (vals P m 1 (f m)) hfam hpd`. Use `set M : ℝ := (m : ℝ) ^ D with hMdef`.

Establish `hM : 0 < M` using `pow_pos (by exact_mod_cast hm1) D`. Establish `hDf : (0 : ℝ) < D.factorial` using `by exact_mod_cast D.factorial_pos`. Establish `hle : ∀ σ y, bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ≤ (ρ σ y / D.factorial + ε) * M` using `fun σ y => hBx σ y _ (mul_nonneg (add_nonneg (div_nonneg (hρ0 σ y) hDf.le) hε.le) hM.le) fun c => hmo (Fin (r m)) (f m) (hf m) c σ y`. Establish `hβi : ∀ σ, Integrable (fun y => (ρ σ y / D.factorial + ε) * M) (ω σ).meas` using `fun σ => by haveI := hfm σ`. Conclude with `(((hint σ _ (hρR σ).1).div_const _).add (integrable_const ε)).mul_const M`.

Establish `hl1` using `abs_finsum_integral_weight_sub_le (k →+* ℂ) (fun σ => CxPts p σ) (fun σ => (ω σ).meas) (bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m))) (fun σ y => (ρ σ y / D.factorial + ε) * M) w C hBi hβi hle (fun σ => (hw σ).measurable) hC0 hwC`. Establish `e1 : ∀ σ, ∫ y, w σ y * ((ρ σ y / D.factorial + ε) * M) ∂(ω σ).meas = M / D.factorial * ∫ y, w σ y * ρ σ y ∂(ω σ).meas + M * ε * ∫ y, w σ y ∂(ω σ).meas` using `fun σ => by`. Establish `h1 : Integrable (fun y => w σ y * ρ σ y) (ω σ).meas` using `hint σ _ ((hw σ).mul (hρR σ).1)`. Establish `h2` using `hint σ _ (hw σ)`. Rewrite using `[← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _) (h2.const_mul _)]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ σ, ∫ y, (ρ σ y / D.factorial + ε) * M ∂(ω σ).meas = M / D.factorial * ∫ y, ρ σ y ∂(ω σ).meas + M * ε * ∫ _y, (1 : ℝ) ∂(ω σ).meas` using `fun σ => by haveI := hfm σ`. Rewrite using `[← integral_const_mul, ← integral_const_mul, ← integral_add ((hint σ _ (hρR σ).1).const_mul _) ((integrable_const (1 : ℝ)).const_mul _)]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [finsum_eq_sum_of_fintype] at hl1 hBs ⊢`. Simplify using `only [Fintype.card_fin] at hBs`.

Rewrite `hl1` using `[Finset.sum_congr rfl fun σ _ => e1 σ, Finset.sum_congr rfl fun σ _ => e2 σ, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hBs]`. Rewrite `hl1` using `[← hIw, ← hW, ← hG', ← hV]`. Use `set A : ℝ := ∑ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas with hA`. Establish `eq1 : A / M - Iw / D.factorial - ε * W = (A - (M / D.factorial * Iw + M * ε * W)) / M`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq1, abs_div, abs_of_pos hM, div_le_iff₀ hM]`. Establish `eq2 : C * (G' / D.factorial + ε * V - (r m : ℝ) / M) * M = C * (M / D.factorial * G' + M * ε * V - (r m : ℝ))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[eq2]`.

Conclude with `hl1`.
-/
theorem tendsto_finsum_integral_berg : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (r : ℕ → ℕ) (f : ∀ m, Fin (r m) → X.functionField), (∀ (m : ℕ) i, f m i ∈ P.H m 1) → (∀ m, LinearIndependent ℤ (f m)) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (gdeg P.L D / D.factorial)) → ∀ w : ∀ σ, CxPts p σ → ℝ, (∀ σ, Continuous (w σ)) → Tendsto (fun m : ℕ => (∑ᶠ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas) / (m : ℝ) ^ D) atTop (𝓝 (chInt P.L D w / D.factorial)) := by
  intro k _ X _ p D hX hG P hpos ω r f hf hli hr w hw
  classical
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  letI := Fintype.ofFinite (k →+* ℂ)
  have hcpt : ∀ σ, CompactSpace (CxPts p σ) := hX.compactSpace
  have hfm : ∀ σ, IsFiniteMeasure (ω σ).meas := fun σ => (GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos k X p D hX hG σ (ω σ)).1
  choose ρ hρR hρ0 hρint using fun σ => GlobalTheory.T.exists_chernTopPower_volumeDensity_ratio k X p D hX hG P.L hpos σ (ω σ)
  have hbd : ∀ σ (g : CxPts p σ → ℝ), Continuous g → ∃ C, ∀ y, |g y| ≤ C := fun σ g hg => by
    haveI := hcpt σ
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y (Set.mem_univ y)⟩
  have hint : ∀ σ (g : CxPts p σ → ℝ), Continuous g → Integrable g (ω σ).meas := fun σ g hg => by
    haveI := hfm σ
    obtain ⟨C, hC⟩ := hbd σ g hg
    exact Integrable.of_bound hg.aestronglyMeasurable C
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  choose Cw hCw using fun σ => hbd σ (w σ) (hw σ)
  set C : ℝ := ∑ σ, |Cw σ| with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hwC : ∀ σ y, |w σ y| ≤ C := fun σ y => (hCw σ y).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |Cw σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ)))
  set Iw : ℝ := ∑ σ, ∫ y, w σ y * ρ σ y ∂(ω σ).meas with hIw
  set G' : ℝ := ∑ σ, ∫ y, ρ σ y ∂(ω σ).meas with hG'
  set W : ℝ := ∑ σ, ∫ y, w σ y ∂(ω σ).meas with hW
  set V : ℝ := ∑ σ, ∫ _y, (1 : ℝ) ∂(ω σ).meas with hV
  have hch : chInt P.L D w = Iw := by
    simp only [chInt, finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hρint σ (w σ) (hw σ)
  have hgd : gdeg P.L D = G' := by
    simp only [gdeg, chInt, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hρint σ _ continuous_const]
    simp
  rw [hch]
  rw [hgd] at hr
  refine tendsto_of_abs_sub_le_eventually _ (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) (Iw / D.factorial)
    (G' / D.factorial) W V C hC0 hr fun ε hε => ?_
  filter_upwards [GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform k X p D hX hG P hpos ω ρ hρR ε hε, eventually_ge_atTop 1] with m hmo hm1
  obtain ⟨hfam, hpd, -⟩ := GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep k X p D hX hG P ω m 1 (Fin (r m)) (f m) (hf m) (hli m)
  obtain ⟨hBi, hBs, hB0, hBx⟩ := GlobalTheory.T.bergman_function_total_mass_extremal (k →+* ℂ) (fun σ => CxPts p σ) (Fin (r m))
    (fun σ => (ω σ).meas) (vals P m 1 (f m)) hfam hpd
  set M : ℝ := (m : ℝ) ^ D with hMdef
  have hM : 0 < M := pow_pos (by exact_mod_cast hm1) D
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hle : ∀ σ y, bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ≤ (ρ σ y / D.factorial + ε) * M :=
    fun σ y => hBx σ y _ (mul_nonneg (add_nonneg (div_nonneg (hρ0 σ y) hDf.le) hε.le) hM.le)
      fun c => hmo (Fin (r m)) (f m) (hf m) c σ y
  have hβi : ∀ σ, Integrable (fun y => (ρ σ y / D.factorial + ε) * M) (ω σ).meas := fun σ => by
    haveI := hfm σ
    exact (((hint σ _ (hρR σ).1).div_const _).add (integrable_const ε)).mul_const M
  have hl1 := abs_finsum_integral_weight_sub_le (k →+* ℂ) (fun σ => CxPts p σ) (fun σ => (ω σ).meas)
    (bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m))) (fun σ y => (ρ σ y / D.factorial + ε) * M) w C hBi hβi hle
    (fun σ => (hw σ).measurable) hC0 hwC
  have e1 : ∀ σ, ∫ y, w σ y * ((ρ σ y / D.factorial + ε) * M) ∂(ω σ).meas =
      M / D.factorial * ∫ y, w σ y * ρ σ y ∂(ω σ).meas + M * ε * ∫ y, w σ y ∂(ω σ).meas := fun σ => by
    have h1 : Integrable (fun y => w σ y * ρ σ y) (ω σ).meas := hint σ _ ((hw σ).mul (hρR σ).1)
    have h2 := hint σ _ (hw σ)
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul _) (h2.const_mul _)]
    congr 1; funext y; ring
  have e2 : ∀ σ, ∫ y, (ρ σ y / D.factorial + ε) * M ∂(ω σ).meas =
      M / D.factorial * ∫ y, ρ σ y ∂(ω σ).meas + M * ε * ∫ _y, (1 : ℝ) ∂(ω σ).meas := fun σ => by
    haveI := hfm σ
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hint σ _ (hρR σ).1).const_mul _) ((integrable_const (1 : ℝ)).const_mul _)]
    congr 1; funext y; ring
  simp only [finsum_eq_sum_of_fintype] at hl1 hBs ⊢
  simp only [Fintype.card_fin] at hBs
  rw [Finset.sum_congr rfl fun σ _ => e1 σ, Finset.sum_congr rfl fun σ _ => e2 σ, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hBs] at hl1
  rw [← hIw, ← hW, ← hG', ← hV] at hl1
  set A : ℝ := ∑ σ, ∫ y, w σ y * bergmanDensity (fun σ => (ω σ).meas) (vals P m 1 (f m)) σ y ∂(ω σ).meas with hA
  have eq1 : A / M - Iw / D.factorial - ε * W = (A - (M / D.factorial * Iw + M * ε * W)) / M := by
    field_simp
    ring
  rw [eq1, abs_div, abs_of_pos hM, div_le_iff₀ hM]
  have eq2 : C * (G' / D.factorial + ε * V - (r m : ℝ) / M) * M =
      C * (M / D.factorial * G' + M * ε * V - (r m : ℝ)) := by
    field_simp
  rw [eq2]
  exact hl1

end GlobalTheory.HSAmp
