import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PullStmt

open UpperTheory.V.Lit.Geo

/- English proof (translation)
Establish `hp1 : HasFDerivAt W (fderiv ℝ W p) ((1 : ℝ) • p)`. Rewrite using `[one_smul]`. Conclude with `hd.hasFDerivAt`. Establish `hr : HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) 1` using `(hasDerivAt_id (1 : ℝ)).smul_const p`. Establish `h1 : HasDerivAt (fun s : ℝ => W (s • p)) (fderiv ℝ W p ((1 : ℝ) • p)) 1` using `hp1.comp_hasDerivAt (1 : ℝ) hr`.

Establish `h2 : HasDerivAt (fun s : ℝ => W (s • p)) (W p) 1`. Establish `hl : HasDerivAt (fun s : ℝ => s • W p) ((1 : ℝ) • W p) 1` using `(hasDerivAt_id (1 : ℝ)).smul_const (W p)`. Rewrite `hl` using `[one_smul]`. Use `hl.congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with s hs`.

Conclude with `hh s hs`. Establish `heul : fderiv ℝ W p p = W p`. Use `h1.unique h2` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis. Establish `hf : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p` using `(hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)`.

Rewrite using `[hf.fderiv]`. Simplify using `[flow, heul]`.
-/
private theorem UpperTheory.V.Lit.Geo.euler_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (hd : DifferentiableAt ℝ W p) (hh : ∀ t : ℝ, 0 < t → W (t • p) = t • W p) (t : ℝ) :
    fderiv ℝ (flow W t) p p = flow W t p := by
  have hp1 : HasFDerivAt W (fderiv ℝ W p) ((1 : ℝ) • p) := by
    rw [one_smul]
    exact hd.hasFDerivAt
  have hr : HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun s : ℝ => W (s • p)) (fderiv ℝ W p ((1 : ℝ) • p)) 1 :=
    hp1.comp_hasDerivAt (1 : ℝ) hr
  have h2 : HasDerivAt (fun s : ℝ => W (s • p)) (W p) 1 := by
    have hl : HasDerivAt (fun s : ℝ => s • W p) ((1 : ℝ) • W p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const (W p)
    rw [one_smul] at hl
    refine hl.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with s hs
    exact hh s hs
  have heul : fderiv ℝ W p p = W p := by
    have := h1.unique h2
    rwa [one_smul] at this
  have hf : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)
  rw [hf.fderiv]
  simp [flow, heul]

/- English proof (translation)
Introduce `V F _ _ _ _ _ _ Y hY W hW hh q`. Establish `hdiff : ∀ p ∈ Y, DifferentiableAt ℝ W p` using `fun p hp => (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)`. Establish `he : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p p = flow W t p` using `fun p hp t => euler_flow (hdiff p hp) (fun s hs => hh s hs p hp) t`. Use `⟨fun w hw => ?_, fun w _ hw => ?_⟩` and prove the remaining obligations. Introduce `p hp v i hi`.

Rewrite using `[pb_apply]`. Apply `hw (flow W 1 p) (hW.2 p hp 1 ⟨zero_le_one, le_rfl⟩) _ i` to reduce the goal to its premises. Simplify using `[hi, he p hp]`. Introduce `p hp v i hi`. Establish `hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, hk W t w p v = 0`.

Introduce `t ht`. Rewrite using `[hk_apply]`. Apply `hw (flow W t p) (hW.2 p hp t ht) _ i.succ` to reduce the goal to its premises. Simplify using `[hi, he p hp]`. Use `show (∫ t in (0 : ℝ)..1, hk W t w p) v = 0`.

Distinguish the cases in `hint : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1`. Establish `hc` using `(ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm hint`. Simplify using `only [ContinuousAlternatingMap.apply_apply] at hc`. Rewrite using `[← hc, intervalIntegral.integral_congr (g := fun _ => (0 : F))]`. Simplify using the standard rewrite rules.

Introduce `t ht`. Rewrite `ht` using `[Set.uIcc_of_le zero_le_one]`. Conclude with `hz t ht`. Rewrite using `[intervalIntegral.integral_undef hint]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Lit.Geo.pbBasic :
    PbBasic := by
  intro V F _ _ _ _ _ _ Y hY W hW hh q
  have hdiff : ∀ p ∈ Y, DifferentiableAt ℝ W p := fun p hp =>
    (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have he : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p p = flow W t p := fun p hp t =>
    euler_flow (hdiff p hp) (fun s hs => hh s hs p hp) t
  refine ⟨fun w hw => ?_, fun w _ hw => ?_⟩
  · intro p hp v i hi
    rw [pb_apply]
    apply hw (flow W 1 p) (hW.2 p hp 1 ⟨zero_le_one, le_rfl⟩) _ i
    simp [hi, he p hp]
  · intro p hp v i hi
    have hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, hk W t w p v = 0 := by
      intro t ht
      rw [hk_apply]
      apply hw (flow W t p) (hW.2 p hp t ht) _ i.succ
      simp [hi, he p hp]
    show (∫ t in (0 : ℝ)..1, hk W t w p) v = 0
    by_cases hint : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1
    · have hc := (ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm hint
      simp only [ContinuousAlternatingMap.apply_apply] at hc
      rw [← hc, intervalIntegral.integral_congr (g := fun _ => (0 : F))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact hz t ht
    · rw [intervalIntegral.integral_undef hint]
      rfl
