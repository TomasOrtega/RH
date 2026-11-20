import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm CompanionTheory.Bmu
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuQBound

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `nil`. Use `⟨h.one_mem, ?_⟩` and prove the remaining obligations. Simplify using `[h.map_one]`.

Consider the case `cons a l ih`. Take `⟨hP, hBP⟩` from `ih`. Simplify using `only [List.map_cons, List.prod_cons]`. Use `⟨h.mul_mem _ (hg a) _ hP, ?_⟩` and prove the remaining obligations. Rewrite using `[h.apply_mul (hg a) hP, hc a _ (IsSm.apply h hv hP), hBP, ContinuousLinearMap.mul_apply]`.
-/
theorem factor_prod {n : ℕ} {H V ι : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
    (h : RepOn G σ) (B : H → V) (g : ι → Mat n) (c : ι → (V →L[ℂ] V)) (hg : ∀ j, g j ∈ G)
    (hc : ∀ j v, IsSm G σ v → B (σ (g j) v) = c j (B v)) (v : H) (hv : IsSm G σ v) :
    ∀ l : List ι, (l.map g).prod ∈ G ∧ B (σ (l.map g).prod v) = (l.map c).prod (B v) := by
  intro l
  induction l with
  | nil =>
    refine ⟨h.one_mem, ?_⟩
    simp [h.map_one]
  | cons a l ih =>
    obtain ⟨hP, hBP⟩ := ih
    simp only [List.map_cons, List.prod_cons]
    refine ⟨h.mul_mem _ (hg a) _ hP, ?_⟩
    rw [h.apply_mul (hg a) hP, hc a _ (IsSm.apply h hv hP), hBP, ContinuousLinearMap.mul_apply]

/- English proof (translation)
Establish `hφi : Integrable φ` using `hφ.integrable_of_hasCompactSupport hc`. Establish `hcC : HasCompactSupport (fun t => (φ t : ℂ))` using `hc.comp_left Complex.ofReal_zero`. Establish `hφf : Integrable (fun t => (φ t : ℂ) • f t)` using `((Complex.continuous_ofReal.comp hφ).smul hf).integrable_of_hasCompactSupport hcC.smul_right`. Establish `h2 : Integrable (fun t => (φ t : ℂ) • b)` using `hφi.ofReal.smul_const b`. Establish `hbi : ∫ t, (φ t : ℂ) • b = b`.

Rewrite using `[integral_smul_const, integral_complex_ofReal, h1, Complex.ofReal_one, one_smul]`. Establish `key : ∫ t, (φ t : ℂ) • f t = b + ∫ t, (φ t : ℂ) • (f t - b)`. Repeatedly rewrite using `[smul_sub]`. Rewrite using `[integral_sub hφf h2, hbi]`. Normalize the expressions using the abelian group laws.

Establish `hbound : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ‖b‖ / 2`. Establish `hle : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ∫ t, φ t * (‖b‖ / 2)` using `norm_integral_le_of_norm_le (hφi.mul_const (‖b‖ / 2)) (ae_of_all _ fun t => ?_)`. Rewrite `hle` using `[integral_mul_const, h1, one_mul]`. Then use the resulting hypothesis. Distinguish the cases in `ht : φ t = 0`. Simplify using `[ht]`.

Rewrite using `[norm_smul, Complex.norm_real, Real.norm_of_nonneg (h0 t)]`. Conclude with `mul_le_mul_of_nonneg_left (hb t ht) (h0 t)`. Rewrite using `[key]`. Establish `h3 : ‖b‖ ≤ ‖b + ∫ t, (φ t : ℂ) • (f t - b)‖ + ‖∫ t, (φ t : ℂ) • (f t - b)‖`. Simplify using `using norm_sub_le (b + ∫ t, (φ t : ℂ) • (f t - b)) (∫ t, (φ t : ℂ) • (f t - b))`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_le_avg {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ) (h0 : ∀ t, 0 ≤ φ t)
    (h1 : ∫ t, φ t = 1) (f : (Fin d → ℝ) → V) (hf : Continuous f) (b : V)
    (hb : ∀ t, φ t ≠ 0 → ‖f t - b‖ ≤ ‖b‖ / 2) : ‖b‖ ≤ 2 * ‖∫ t, (φ t : ℂ) • f t‖ := by
  have hφi : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hcC : HasCompactSupport (fun t => (φ t : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hφf : Integrable (fun t => (φ t : ℂ) • f t) :=
    ((Complex.continuous_ofReal.comp hφ).smul hf).integrable_of_hasCompactSupport hcC.smul_right
  have h2 : Integrable (fun t => (φ t : ℂ) • b) := hφi.ofReal.smul_const b
  have hbi : ∫ t, (φ t : ℂ) • b = b := by
    rw [integral_smul_const, integral_complex_ofReal, h1, Complex.ofReal_one, one_smul]
  have key : ∫ t, (φ t : ℂ) • f t = b + ∫ t, (φ t : ℂ) • (f t - b) := by
    simp_rw [smul_sub]
    rw [integral_sub hφf h2, hbi]
    abel
  have hbound : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ‖b‖ / 2 := by
    have hle : ‖∫ t, (φ t : ℂ) • (f t - b)‖ ≤ ∫ t, φ t * (‖b‖ / 2) :=
      norm_integral_le_of_norm_le (hφi.mul_const (‖b‖ / 2)) (ae_of_all _ fun t => ?_)
    · rwa [integral_mul_const, h1, one_mul] at hle
    · by_cases ht : φ t = 0
      · simp [ht]
      · rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (h0 t)]
        exact mul_le_mul_of_nonneg_left (hb t ht) (h0 t)
  rw [key]
  have h3 : ‖b‖ ≤ ‖b + ∫ t, (φ t : ℂ) • (f t - b)‖ + ‖∫ t, (φ t : ℂ) • (f t - b)‖ := by
    simpa using norm_sub_le (b + ∫ t, (φ t : ℂ) • (f t - b)) (∫ t, (φ t : ℂ) • (f t - b))
  linarith

/- English proof (translation)
Introduce `n Hm H _ _ _ σ hU V _ _ _ B hB d e X Q hX hQ hS χ hχc hχ0 hχB`. Take `⟨N, W, β, hW, hBW⟩` from `hF n Hm H σ hU V B hB`. Take `⟨U, hCh⟩` from `hC n Hm hU.sq d e X Q hX hQ hS`. Establish `hrep` using `hU.rep`. Establish `hmem : ∀ t, prodEx X t ∈ UH Hm` using `hCh.mem`.

Establish `hsc : Continuous (prodEx X)` using `hCh.smooth.continuous`. Use `set Φ : (Fin d → ℝ) → (V →L[ℂ] V) := fun t => ((List.finRange d).map fun j => χ j (t j)).prod with hΦdef`. Establish `hΦc : Continuous Φ` using `continuous_list_prod _ fun j _ => (hχc j).comp (continuous_apply j)`. Establish `hΦ0 : Φ 0 = 1` using `by simp [hΦdef, hχ0]`. Establish `hfac : ∀ v, IsSm (UH Hm) σ v → ∀ t, B (σ (prodEx X t) v) = Φ t (B v)`.

Introduce `v hv t`. Use `show B (σ ((List.ofFn fun j => ex (X j) (t j)).prod) v) = _`. Rewrite using `[List.ofFn_eq_map]`. Conclude with `(factor_prod hrep B (fun j => ex (X j) (t j)) (fun j => χ j (t j)) (fun j => ex_mem_of_lie (hX j) (t j)) (fun j w hw => hχB j (t j) w hw) v hv (List.finRange d)).2`. Take `⟨r, hr, hrΦ⟩ : ∃ r > 0, ∀ t : Fin d → ℝ, dist t 0 < r → dist (Φ t) (Φ 0) < 1 / 2` from `Metric.continuous_iff.1 hΦc 0 (1 / 2) (by norm_num)`.

Take `⟨r', hr', hr'U⟩` from `Metric.isOpen_iff.1 hCh.isOpen 0 hCh.zero`. Establish `hmin : 0 < min r r'` using `lt_min hr hr'`. Use `set ρ := min r r' / 2 with hρ`. Establish `hρpos : 0 < ρ` using `half_pos hmin`. Establish `hρr : ρ < r` using `by rw [hρ]; linarith [min_le_left r r']`.

Establish `hρr' : ρ < r'` using `by rw [hρ]; linarith [min_le_right r r']`. Set `bump : ContDiffBump (0 : Fin d → ℝ)` to `⟨ρ / 2, ρ, half_pos hρpos, half_lt_self hρpos⟩`. Use `set φ := bump.normed volume with hφdef`. Establish `hφs : ContDiff ℝ ∞ φ` using `bump.contDiff_normed`. Establish `hφcs : HasCompactSupport φ` using `bump.hasCompactSupport_normed`.

Establish `hts : tsupport φ = Metric.closedBall 0 ρ` using `bump.tsupport_normed_eq`. Establish `hφU : tsupport φ ⊆ U`. Rewrite using `[hts]`. Introduce `t ht`. Apply `hr'U` to reduce the goal to its premises.

Rewrite using `[Metric.mem_ball]`. Rewrite `ht` using `[Metric.mem_closedBall]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hφ0 : ∀ t, 0 ≤ φ t` using `bump.nonneg_normed`. Establish `hφ1 : ∫ t, φ t = 1` using `bump.integral_normed`.

Establish `hnear : ∀ t, φ t ≠ 0 → ‖Φ t - 1‖ ≤ 1 / 2`. Introduce `t ht`. Establish `htm : t ∈ tsupport φ` using `subset_tsupport _ ht`. Rewrite `htm` using `[hts, Metric.mem_closedBall]`. Establish `hd` using `hrΦ t (by linarith)`.

Rewrite `hd` using `[dist_eq_norm, hΦ0]`. Conclude with `hd.le`. Establish `hRi` using `fun i => hR n Hm H σ hU d e Q (prodEx X) U hCh (W i) (hW i) φ hφs hφcs hφU`. Use `choose Cr hCr0 hCr using hRi`. Use `⟨2 * ∑ i, ‖β i‖ * Cr i, Finset.univ.sup fun i => (W i).length, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hCr0 i))`. Introduce `v hv R hRb`. Establish `hlie : ∀ i, LieW (UH Hm) (W i)` using `fun i X' hX' t => ex_mem_of_lie (hW i X' hX') t`. Establish `hgc : ∀ i, Continuous fun t => dsW σ (W i) (σ (prodEx X t) v)` using `fun i => (continuousOn_dsW_orbit hrep hv (hlie i)).comp_continuous hsc hmem`. Establish `hint : ∀ i, Integrable fun t => (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v)` using `fun i => ((Complex.continuous_ofReal.comp hφs.continuous).smul (hgc i)).integrable_of_hasCompactSupport (hφcs.comp_left Complex.ofReal_zero).smul_right`.

Establish `hsum : ∫ t, (φ t : ℂ) • Φ t (B v) = ∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v))`. Establish `e1 : ∀ t, (φ t : ℂ) • Φ t (B v) = ∑ i, β i ((φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v))`. Introduce `t`. Rewrite using `[← hfac v hv t, hBW _ (IsSm.apply hrep hv (hmem t)), Finset.smul_sum]`. Simplify using `only [ContinuousLinearMap.map_smul]`.

Repeatedly rewrite using `[e1]`. Rewrite using `[integral_finsetSum _ fun i _ => (β i).integrable_comp (hint i)]`. Conclude with `Finset.sum_congr rfl fun i _ => (β i).integral_comp_comm (hint i)`. Establish `havg` using `norm_le_avg φ hφs.continuous hφcs hφ0 hφ1 (fun t => Φ t (B v)) (hΦc.clm_apply continuous_const) (B v) (fun t ht => ?_)`. Rewrite `havg` using `[hsum]`.

Establish `hb2 : ‖∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v))‖ ≤ ∑ i, ‖β i‖ * Cr i * R`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations. Use `((β i).le_opNorm _).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (hCr i v hv R fun P hP => hRb P (hP.trans (Finset.le_sup (f := fun i => (W i).length) (Finset.mem_univ i)))) (norm_nonneg _)`.

Rewrite `hb2` using `[← Finset.sum_mul]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsub : Φ t (B v) - B v = (Φ t - 1) (B v)`. Rewrite using `[ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]`. Rewrite using `[hsub]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem qBound (hF : Factor) (hR : Reduce) (hC : ChartExists) : QBound := by
  intro n Hm H _ _ _ σ hU V _ _ _ B hB d e X Q hX hQ hS χ hχc hχ0 hχB
  obtain ⟨N, W, β, hW, hBW⟩ := hF n Hm H σ hU V B hB
  obtain ⟨U, hCh⟩ := hC n Hm hU.sq d e X Q hX hQ hS
  have hrep := hU.rep
  have hmem : ∀ t, prodEx X t ∈ UH Hm := hCh.mem
  have hsc : Continuous (prodEx X) := hCh.smooth.continuous
  set Φ : (Fin d → ℝ) → (V →L[ℂ] V) := fun t => ((List.finRange d).map fun j => χ j (t j)).prod with hΦdef
  have hΦc : Continuous Φ := continuous_list_prod _ fun j _ => (hχc j).comp (continuous_apply j)
  have hΦ0 : Φ 0 = 1 := by simp [hΦdef, hχ0]
  have hfac : ∀ v, IsSm (UH Hm) σ v → ∀ t, B (σ (prodEx X t) v) = Φ t (B v) := by
    intro v hv t
    show B (σ ((List.ofFn fun j => ex (X j) (t j)).prod) v) = _
    rw [List.ofFn_eq_map]
    exact (factor_prod hrep B (fun j => ex (X j) (t j)) (fun j => χ j (t j))
      (fun j => ex_mem_of_lie (hX j) (t j)) (fun j w hw => hχB j (t j) w hw) v hv (List.finRange d)).2
  obtain ⟨r, hr, hrΦ⟩ : ∃ r > 0, ∀ t : Fin d → ℝ, dist t 0 < r → dist (Φ t) (Φ 0) < 1 / 2 :=
    Metric.continuous_iff.1 hΦc 0 (1 / 2) (by norm_num)
  obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hCh.isOpen 0 hCh.zero
  have hmin : 0 < min r r' := lt_min hr hr'
  set ρ := min r r' / 2 with hρ
  have hρpos : 0 < ρ := half_pos hmin
  have hρr : ρ < r := by rw [hρ]; linarith [min_le_left r r']
  have hρr' : ρ < r' := by rw [hρ]; linarith [min_le_right r r']
  let bump : ContDiffBump (0 : Fin d → ℝ) := ⟨ρ / 2, ρ, half_pos hρpos, half_lt_self hρpos⟩
  set φ := bump.normed volume with hφdef
  have hφs : ContDiff ℝ ∞ φ := bump.contDiff_normed
  have hφcs : HasCompactSupport φ := bump.hasCompactSupport_normed
  have hts : tsupport φ = Metric.closedBall 0 ρ := bump.tsupport_normed_eq
  have hφU : tsupport φ ⊆ U := by
    rw [hts]
    intro t ht
    apply hr'U
    rw [Metric.mem_ball]
    rw [Metric.mem_closedBall] at ht
    linarith
  have hφ0 : ∀ t, 0 ≤ φ t := bump.nonneg_normed
  have hφ1 : ∫ t, φ t = 1 := bump.integral_normed
  have hnear : ∀ t, φ t ≠ 0 → ‖Φ t - 1‖ ≤ 1 / 2 := by
    intro t ht
    have htm : t ∈ tsupport φ := subset_tsupport _ ht
    rw [hts, Metric.mem_closedBall] at htm
    have hd := hrΦ t (by linarith)
    rw [dist_eq_norm, hΦ0] at hd
    exact hd.le
  have hRi := fun i => hR n Hm H σ hU d e Q (prodEx X) U hCh (W i) (hW i) φ hφs hφcs hφU
  choose Cr hCr0 hCr using hRi
  refine ⟨2 * ∑ i, ‖β i‖ * Cr i, Finset.univ.sup fun i => (W i).length, ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hCr0 i))
  intro v hv R hRb
  have hlie : ∀ i, LieW (UH Hm) (W i) := fun i X' hX' t => ex_mem_of_lie (hW i X' hX') t
  have hgc : ∀ i, Continuous fun t => dsW σ (W i) (σ (prodEx X t) v) := fun i =>
    (continuousOn_dsW_orbit hrep hv (hlie i)).comp_continuous hsc hmem
  have hint : ∀ i, Integrable fun t => (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v) := fun i =>
    ((Complex.continuous_ofReal.comp hφs.continuous).smul (hgc i)).integrable_of_hasCompactSupport
      (hφcs.comp_left Complex.ofReal_zero).smul_right
  have hsum : ∫ t, (φ t : ℂ) • Φ t (B v) =
      ∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v)) := by
    have e1 : ∀ t, (φ t : ℂ) • Φ t (B v) =
        ∑ i, β i ((φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v)) := by
      intro t
      rw [← hfac v hv t, hBW _ (IsSm.apply hrep hv (hmem t)), Finset.smul_sum]
      simp only [ContinuousLinearMap.map_smul]
    simp_rw [e1]
    rw [integral_finsetSum _ fun i _ => (β i).integrable_comp (hint i)]
    exact Finset.sum_congr rfl fun i _ => (β i).integral_comp_comm (hint i)
  have havg := norm_le_avg φ hφs.continuous hφcs hφ0 hφ1 (fun t => Φ t (B v))
    (hΦc.clm_apply continuous_const) (B v) (fun t ht => ?_)
  · rw [hsum] at havg
    have hb2 : ‖∑ i, β i (∫ t, (φ t : ℂ) • dsW σ (W i) (σ (prodEx X t) v))‖ ≤
        ∑ i, ‖β i‖ * Cr i * R := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine ((β i).le_opNorm _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hCr i v hv R fun P hP => hRb P
        (hP.trans (Finset.le_sup (f := fun i => (W i).length) (Finset.mem_univ i)))) (norm_nonneg _)
    rw [← Finset.sum_mul] at hb2
    nlinarith
  · have hsub : Φ t (B v) - B v = (Φ t - 1) (B v) := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    rw [hsub]
    calc ‖(Φ t - 1) (B v)‖ ≤ ‖Φ t - 1‖ * ‖B v‖ := (Φ t - 1).le_opNorm _
      _ ≤ 1 / 2 * ‖B v‖ := mul_le_mul_of_nonneg_right (hnear t ht) (norm_nonneg _)
      _ = ‖B v‖ / 2 := by ring

end GlobalTheory.CompanionTheory.BmuQBound

end
