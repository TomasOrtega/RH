import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA

open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Asymptotics

noncomputable section

/- English proof (translation)
Set `e : V n ≃L[ℂ] (Fin n → ℂ)` to `EuclideanSpace.equiv (Fin n) ℂ`. Establish `hU' : IsOpen (e.symm ⁻¹' U)` using `hU.preimage e.symm.continuous`. Establish `hf' : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U)` using `hf.comp (e.symm : (Fin n → ℂ) →L[ℂ] V n).differentiableOn (fun y hy => hy)`. Establish `hz' : e z ∈ e.symm ⁻¹' U` using `by simpa using hz`. Establish `ha` using `ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU' hf' (e z) hz'`.

Establish `hfe : f = (f ∘ e.symm) ∘ e`. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules. Rewrite using `[hfe]`. Conclude with `ha.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt z)`.
-/
theorem analyticAt_of_diffOn {n : ℕ} {f : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {z : V n} (hz : z ∈ U) : AnalyticAt ℂ f z := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU' : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hf' : DifferentiableOn ℂ (f ∘ e.symm) (e.symm ⁻¹' U) :=
    hf.comp (e.symm : (Fin n → ℂ) →L[ℂ] V n).differentiableOn (fun y hy => hy)
  have hz' : e z ∈ e.symm ⁻¹' U := by simpa using hz
  have ha := ReciprocityTheory.AnForm.Osgood.osgood n _ _ hU' hf' (e z) hz'
  have hfe : f = (f ∘ e.symm) ∘ e := by
    funext w
    simp
  rw [hfe]
  exact ha.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt z)

/- English proof (translation)
Use `Asymptotics.IsBigO.of_bound 1 ?_` and prove the remaining obligations. Use `filter_upwards [Metric.ball_mem_nhds (0 : F) one_pos] with y hy`. Rewrite `hy` using `[mem_ball_zero_iff]`. Simplify using `only [norm_pow, norm_norm, one_mul]`. Conclude with `pow_le_pow_of_le_one (norm_nonneg _) hy.le h`.
-/
theorem isBigO_norm_pow_of_le {F : Type*} [NormedAddCommGroup F] {k d : ℕ} (h : k ≤ d) :
    (fun y : F => ‖y‖ ^ d) =O[𝓝 0] (fun y => ‖y‖ ^ k) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : F) one_pos] with y hy
  rw [mem_ball_zero_iff] at hy
  simp only [norm_pow, norm_norm, one_mul]
  exact pow_le_pow_of_le_one (norm_nonneg _) hy.le h

/- English proof (translation)
Take `⟨p, hp⟩` from `hG`. Establish `hvan : ∀ m, m < d → ∀ y : V n, p m (fun _ => y) = 0`. Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`.

Introduce `hm y0`. Establish `hps : ∀ y : V n, p.partialSum (m + 1) y = p m (fun _ => y)`. Introduce `y`. Simplify using `only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]`. Rewrite using `[Finset.sum_eq_zero (fun j hj => ih j (Finset.mem_range.mp hj) (by have := Finset.mem_range.mp hj; omega) y), zero_add]`.

Establish `hA` using `hp.isBigO_sub_partialSum_pow (m + 1)`. Simplify using `only [zero_add, hps] at hA`. Establish `hB : G =O[𝓝 0] fun z => ‖z‖ ^ (m + 1)` using `hO.trans (isBigO_norm_pow_of_le (by omega))`. Establish `h : (fun y : V n => p m (fun _ => y)) =O[𝓝 0] fun y => ‖y‖ ^ (m + 1)` using `(hB.sub hA).congr_left (fun y => by ring)`. Establish `htend : Tendsto (fun t : ℂ => t • y0) (𝓝 0) (𝓝 0)`.

Establish `hc : Continuous fun t : ℂ => t • y0` using `continuous_id.smul continuous_const`. Use `hc.tendsto 0` as an intermediate fact. Simplify using `using this`. Establish `h2` using `h.comp_tendsto htend`. Take `⟨C, hC⟩` from `h2.bound`.

Establish `hhom : ∀ t : ℂ, p m (fun _ => t • y0) = t ^ m * p m (fun _ => y0)`. Introduce `t`. Use `(p m).map_smul_univ (fun _ => t) (fun _ => y0)` as an intermediate fact. Rewrite using `[this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]`. Establish `hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖p m (fun _ => y0)‖ ≤ C * ‖y0‖ ^ (m + 1) * ‖t‖` using `by filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with t ht ht0`.

Simplify using `only [Function.comp_apply, hhom, norm_mul, norm_pow, norm_smul, mul_pow, norm_norm] at ht`. Establish `htpos : 0 < ‖t‖ ^ m` using `pow_pos (norm_pos_iff.mpr (by simpa using ht0)) m`. Use `le_of_mul_le_mul_left ?_ htpos` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the linear relations using `[ht]`.

Use `_ = ‖t‖ ^ m * (C * ‖y0‖ ^ (m + 1) * ‖t‖) := by ring`. Establish `hlim : Tendsto (fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖) (𝓝[≠] 0) (𝓝 0)`. Establish `hc : Continuous fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖` using `continuous_const.mul continuous_norm`. Use `hc.tendsto 0` as an intermediate fact. Simplify using `using this.mono_left nhdsWithin_le_nhds`.

Establish `hc0 : ‖p m (fun _ => y0)‖ ≤ 0` using `ge_of_tendsto hlim hbd`. Conclude with `norm_le_zero_iff.mp hc0`. Use `⟨p d, ?_⟩` and prove the remaining obligations. Establish `hA` using `hp.isBigO_sub_partialSum_pow (d + 1)`. Establish `hps : ∀ y : V n, p.partialSum (d + 1) y = p d (fun _ => y)`.

Introduce `y`. Simplify using `only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]`. Rewrite using `[Finset.sum_eq_zero (fun j hj => hvan j (Finset.mem_range.mp hj) y), zero_add]`. Simplify using `only [zero_add, hps] at hA`. Conclude with `hA`.
-/
theorem taylor_step {n d : ℕ} {G : V n → ℂ} (hG : AnalyticAt ℂ G 0)
    (hO : G =O[𝓝 0] fun z => ‖z‖ ^ d) :
    ∃ q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ,
      (fun z => G z - q (fun _ => z)) =O[𝓝 0] fun z => ‖z‖ ^ (d + 1) := by
  obtain ⟨p, hp⟩ := hG
  have hvan : ∀ m, m < d → ∀ y : V n, p m (fun _ => y) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm y0
      have hps : ∀ y : V n, p.partialSum (m + 1) y = p m (fun _ => y) := by
        intro y
        simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
        rw [Finset.sum_eq_zero (fun j hj => ih j (Finset.mem_range.mp hj)
          (by have := Finset.mem_range.mp hj; omega) y), zero_add]
      have hA := hp.isBigO_sub_partialSum_pow (m + 1)
      simp only [zero_add, hps] at hA
      have hB : G =O[𝓝 0] fun z => ‖z‖ ^ (m + 1) := hO.trans (isBigO_norm_pow_of_le (by omega))
      have h : (fun y : V n => p m (fun _ => y)) =O[𝓝 0] fun y => ‖y‖ ^ (m + 1) :=
        (hB.sub hA).congr_left (fun y => by ring)
      have htend : Tendsto (fun t : ℂ => t • y0) (𝓝 0) (𝓝 0) := by
        have hc : Continuous fun t : ℂ => t • y0 := continuous_id.smul continuous_const
        have := hc.tendsto 0
        simpa using this
      have h2 := h.comp_tendsto htend
      obtain ⟨C, hC⟩ := h2.bound
      have hhom : ∀ t : ℂ, p m (fun _ => t • y0) = t ^ m * p m (fun _ => y0) := by
        intro t
        have := (p m).map_smul_univ (fun _ => t) (fun _ => y0)
        rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hbd : ∀ᶠ t in 𝓝[≠] (0 : ℂ), ‖p m (fun _ => y0)‖ ≤ C * ‖y0‖ ^ (m + 1) * ‖t‖ := by
        filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with t ht ht0
        simp only [Function.comp_apply, hhom, norm_mul, norm_pow, norm_smul, mul_pow, norm_norm] at ht
        have htpos : 0 < ‖t‖ ^ m := pow_pos (norm_pos_iff.mpr (by simpa using ht0)) m
        refine le_of_mul_le_mul_left ?_ htpos
        calc ‖t‖ ^ m * ‖p m (fun _ => y0)‖ ≤ C * (‖t‖ ^ (m + 1) * ‖y0‖ ^ (m + 1)) := by
              linarith [ht]
          _ = ‖t‖ ^ m * (C * ‖y0‖ ^ (m + 1) * ‖t‖) := by ring
      have hlim : Tendsto (fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖) (𝓝[≠] 0) (𝓝 0) := by
        have hc : Continuous fun t : ℂ => C * ‖y0‖ ^ (m + 1) * ‖t‖ :=
          continuous_const.mul continuous_norm
        have := hc.tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      have hc0 : ‖p m (fun _ => y0)‖ ≤ 0 := ge_of_tendsto hlim hbd
      exact norm_le_zero_iff.mp hc0
  refine ⟨p d, ?_⟩
  have hA := hp.isBigO_sub_partialSum_pow (d + 1)
  have hps : ∀ y : V n, p.partialSum (d + 1) y = p d (fun _ => y) := by
    intro y
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun j hj => hvan j (Finset.mem_range.mp hj) y), zero_add]
  simp only [zero_add, hps] at hA
  exact hA

/- English proof (translation)
Set `b : Fin n → V n` to `fun k => L.symm (EuclideanSpace.basisFun (Fin n) ℂ k)`. Set `cnt : (Fin d → Fin n) → (Fin n → ℕ)` to `fun f k => (Finset.univ.filter fun i => f i = k).card`. Establish `hcnt : ∀ f, cnt f ∈ Finset.Nat.antidiagonalTuple n d`. Introduce `f`. Rewrite using `[Finset.Nat.mem_antidiagonalTuple]`.

Use `Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin d))) (t := (Finset.univ : Finset (Fin n))) (f := f) (fun i _ => Finset.mem_univ (f i))` as an intermediate fact. Rewrite `this` using `[Finset.card_univ, Fintype.card_fin]`. Conclude with `this.symm`. Establish `hprod : ∀ (f : Fin d → Fin n) (c : Fin n → ℂ), ∏ i, c (f i) = ∏ k, c k ^ cnt f k`. Introduce `f c`.

Rewrite using `[← Finset.prod_fiberwise Finset.univ f (fun i => c (f i))]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_congr rfl (fun i hi => congrArg c (Finset.mem_filter.mp hi).2), Finset.prod_const]`. Use `⟨fun α => ∑ f ∈ Finset.univ.filter (fun f => cnt f = α), q (fun i => b (f i)), fun z => ?_⟩` and prove the remaining obligations. Establish `hz : z = ∑ k, (L z) k • b k`.

Establish `h1` using `(EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (L z)`. Simplify using `only [EuclideanSpace.basisFun_repr] at h1`. Combine the equalities or inequalities in the displayed calculation. Establish `hL : q (fun _ => z) = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k` using `by conv_lhs => rw [hz]`. Rewrite using `[ContinuousMultilinearMap.map_sum]`.

Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]`. Use `congr 1`. Use `hprod f (fun k => (L z) k)` as an intermediate fact. Simplify using `using this`.

Rewrite using `[hL]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun f hf => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.mp hf).2]`. Use `_ = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k := Finset.sum_fiberwise_of_maps_to (fun f _ => hcnt f) _`.
-/
theorem multilinear_expand {n d : ℕ} (q : ContinuousMultilinearMap ℂ (fun _ : Fin d => V n) ℂ)
    (L : V n ≃L[ℂ] V n) :
    ∃ a : (Fin n → ℕ) → ℂ, ∀ z, q (fun _ => z) =
      ∑ α ∈ Finset.Nat.antidiagonalTuple n d, a α * ∏ k, (L z) k ^ α k := by
  classical
  let b : Fin n → V n := fun k => L.symm (EuclideanSpace.basisFun (Fin n) ℂ k)
  let cnt : (Fin d → Fin n) → (Fin n → ℕ) := fun f k => (Finset.univ.filter fun i => f i = k).card
  have hcnt : ∀ f, cnt f ∈ Finset.Nat.antidiagonalTuple n d := by
    intro f
    rw [Finset.Nat.mem_antidiagonalTuple]
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin d)))
      (t := (Finset.univ : Finset (Fin n))) (f := f) (fun i _ => Finset.mem_univ (f i))
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have hprod : ∀ (f : Fin d → Fin n) (c : Fin n → ℂ), ∏ i, c (f i) = ∏ k, c k ^ cnt f k := by
    intro f c
    rw [← Finset.prod_fiberwise Finset.univ f (fun i => c (f i))]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Finset.prod_congr rfl (fun i hi => congrArg c (Finset.mem_filter.mp hi).2), Finset.prod_const]
  refine ⟨fun α => ∑ f ∈ Finset.univ.filter (fun f => cnt f = α), q (fun i => b (f i)), fun z => ?_⟩
  have hz : z = ∑ k, (L z) k • b k := by
    have h1 := (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr (L z)
    simp only [EuclideanSpace.basisFun_repr] at h1
    calc z = L.symm (L z) := (L.symm_apply_apply z).symm
      _ = L.symm (∑ k, (L z) k • EuclideanSpace.basisFun (Fin n) ℂ k) := by rw [h1]
      _ = ∑ k, (L z) k • b k := by simp only [map_sum, map_smul, b]
  have hL : q (fun _ => z) = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k := by
    conv_lhs => rw [hz]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ, smul_eq_mul, mul_comm]
    congr 1
    have := hprod f (fun k => (L z) k)
    simpa using this
  rw [hL]
  symm
  calc ∑ α ∈ Finset.Nat.antidiagonalTuple n d,
        (∑ f ∈ Finset.univ.filter (fun f => cnt f = α), q (fun i => b (f i))) * ∏ k, (L z) k ^ α k
      = ∑ α ∈ Finset.Nat.antidiagonalTuple n d, ∑ f ∈ Finset.univ.filter (fun f => cnt f = α),
          q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun f hf => ?_
        rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f : Fin d → Fin n, q (fun i => b (f i)) * ∏ k, (L z) k ^ cnt f k :=
        Finset.sum_fiberwise_of_maps_to (fun f _ => hcnt f) _

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA
