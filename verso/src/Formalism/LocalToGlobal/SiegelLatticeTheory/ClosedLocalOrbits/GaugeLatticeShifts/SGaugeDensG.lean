import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SGaugeDensB

open MeasureTheory Filter Topology Set Function
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Gauge

variable {n : ℕ}

section Glue

variable {ε : Fin n → Bool}

/- English proof (translation)
The claim follows from `(continuous_expG ε).comp (obG ε).repr.symm.continuous`.
-/
theorem continuous_expCG (ε : Fin n → Bool) : Continuous (expC ε) :=
  (continuous_expG ε).comp (obG ε).repr.symm.continuous

/- English proof (translation)
The claim follows from `(continuous_expCG ε).measurable`.
-/
theorem measurable_expCG (ε : Fin n → Bool) : Measurable (expC ε) := (continuous_expCG ε).measurable

def nuG (ε : Fin n → Bool) (s : ℝ) (xs : ℕ → Formalism.REAL.UJ ε) (D : ℕ → Set (Formalism.REAL.UJ ε)) : Measure (Formalism.REAL.UJ ε) :=
  Measure.sum fun i => ((lamM ε s).map (fun h => xs i * h)).restrict (D i)

/- English proof (translation)
Rewrite using `[Measure.map_apply (measurable_const_mul x) hB, Measure.map_apply (measurable_const_mul y) hB]`. Use `set A' := (fun h => x * h) ⁻¹' B with hA'`. Establish `himg : (fun h => (y⁻¹ * x) * h) '' A' = (fun h => y * h) ⁻¹' B`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a, ha, rfl⟩ show y * (y⁻¹ * x * a) ∈ B`. Rewrite using `[← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]`. Conclude with `ha`. Introduce `hg`. Use `⟨x⁻¹ * y * g, ?_, ?_⟩` and prove the remaining obligations.

Use `show x * (x⁻¹ * y * g) ∈ B`. Rewrite using `[← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]`. Conclude with `hg`. Use `show y⁻¹ * x * (x⁻¹ * y * g) = g`. Simplify using `[mul_assoc]`.

Rewrite using `[← himg]`. Use `(hL (y⁻¹ * x) A' (hB.preimage (measurable_const_mul x)) ?_ ?_).symm` and prove the remaining obligations. Introduce `a ha`. Take `⟨w, hw, hwa⟩` from `hBx ha`. Establish `: w = a` using `mul_left_cancel hwa`.

Rewrite using `[← this]`. Conclude with `hw`. Rewrite using `[himg]`. Introduce `g hg`. Take `⟨w, hw, hwg⟩` from `hBy hg`.

Establish `: w = g` using `mul_left_cancel hwg`. Rewrite using `[← this]`. Conclude with `hw`.
-/
theorem lamM_map_agree {s : ℝ} (hL : LocInv ε s) (x y : Formalism.REAL.UJ ε) {B : Set (Formalism.REAL.UJ ε)} (hB : MeasurableSet B)
    (hBx : B ⊆ (fun h => x * h) '' (expC ε '' Metric.ball 0 s)) (hBy : B ⊆ (fun h => y * h) '' (expC ε '' Metric.ball 0 s)) :
    (lamM ε s).map (fun h => x * h) B = (lamM ε s).map (fun h => y * h) B := by
  rw [Measure.map_apply (measurable_const_mul x) hB, Measure.map_apply (measurable_const_mul y) hB]
  set A' := (fun h => x * h) ⁻¹' B with hA'
  have himg : (fun h => (y⁻¹ * x) * h) '' A' = (fun h => y * h) ⁻¹' B := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      show y * (y⁻¹ * x * a) ∈ B
      rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]; exact ha
    · intro hg
      refine ⟨x⁻¹ * y * g, ?_, ?_⟩
      · show x * (x⁻¹ * y * g) ∈ B
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]; exact hg
      · show y⁻¹ * x * (x⁻¹ * y * g) = g
        simp [mul_assoc]
  rw [← himg]
  refine (hL (y⁻¹ * x) A' (hB.preimage (measurable_const_mul x)) ?_ ?_).symm
  · intro a ha
    obtain ⟨w, hw, hwa⟩ := hBx ha
    have : w = a := mul_left_cancel hwa
    rw [← this]; exact hw
  · rw [himg]
    intro g hg
    obtain ⟨w, hw, hwg⟩ := hBy hg
    have : w = g := mul_left_cancel hwg
    rw [← this]; exact hw

section Cover

variable {s : ℝ} {xs : ℕ → Formalism.REAL.UJ ε} {D : ℕ → Set (Formalism.REAL.UJ ε)} {V : Set (Formalism.REAL.UJ ε)}

/- English proof (translation)
Rewrite using `[nuG, Measure.sum_apply _ hA]`. Simplify using `only [Measure.restrict_apply hA]`. Establish `e : ∀ i, (lamM ε s).map (fun h => xs i * h) (A ∩ D i) = (lamM ε s).map (fun h => y * h) (A ∩ D i)` using `fun i => lamM_map_agree hL (xs i) y (hA.inter (hD i)) ((inter_subset_right.trans (hDV i)).trans (image_mono hVW)) (inter_subset_left.trans hAy)`. Rewrite using `[tsum_congr e, ← measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right) (fun i => hA.inter (hD i)), ← inter_iUnion, hcov, inter_univ]`.
-/
theorem nuG_eq (hL : LocInv ε s) (hVW : V ⊆ expC ε '' Metric.ball 0 s)
    (hD : ∀ i, MeasurableSet (D i)) (hdisj : Pairwise (Disjoint on D)) (hcov : ⋃ i, D i = univ)
    (hDV : ∀ i, D i ⊆ (fun h => xs i * h) '' V) (y : Formalism.REAL.UJ ε) {A : Set (Formalism.REAL.UJ ε)} (hA : MeasurableSet A)
    (hAy : A ⊆ (fun h => y * h) '' (expC ε '' Metric.ball 0 s)) :
    nuG ε s xs D A = (lamM ε s).map (fun h => y * h) A := by
  rw [nuG, Measure.sum_apply _ hA]
  simp only [Measure.restrict_apply hA]
  have e : ∀ i, (lamM ε s).map (fun h => xs i * h) (A ∩ D i) = (lamM ε s).map (fun h => y * h) (A ∩ D i) := fun i =>
    lamM_map_agree hL (xs i) y (hA.inter (hD i)) ((inter_subset_right.trans (hDV i)).trans (image_mono hVW))
      (inter_subset_left.trans hAy)
  rw [tsum_congr e, ← measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right)
    (fun i => hA.inter (hD i)), ← inter_iUnion, hcov, inter_univ]

/- English proof (translation)
Use extensionality with `A hA`. Rewrite using `[Measure.map_apply (measurable_const_mul g) hA]`. Use `set B := (fun h => g * h) ⁻¹' A with hBdef`. Establish `hB : MeasurableSet B` using `hA.preimage (measurable_const_mul g)`. Establish `hmB : ∀ i, MeasurableSet (B ∩ D i)` using `fun i => hB.inter (hD i)`.

Establish `hUB : ⋃ i, B ∩ D i = B` using `by rw [← inter_iUnion, hcov, inter_univ]`. Establish `hUA : ⋃ i, (fun h => g⁻¹ * h) ⁻¹' (B ∩ D i) = A`. Rewrite using `[← preimage_iUnion, hUB, hBdef, ← preimage_comp]`. Use extensionality with `h`. Simplify using the standard rewrite rules.

Establish `hWsub : ∀ i, B ∩ D i ⊆ (fun h => xs i * h) '' (expC ε '' Metric.ball 0 s)` using `fun i => (inter_subset_right.trans (hDV i)).trans (image_mono hVW)`. Establish `e : ∀ i, nuG ε s xs D ((fun h => g⁻¹ * h) ⁻¹' (B ∩ D i)) = nuG ε s xs D (B ∩ D i)`. Introduce `i`. Establish `hm : MeasurableSet ((fun h => g⁻¹ * h) ⁻¹' (B ∩ D i))` using `(hmB i).preimage (measurable_const_mul _)`. Establish `hsub : (fun h => g⁻¹ * h) ⁻¹' (B ∩ D i) ⊆ (fun h => (g * xs i) * h) '' (expC ε '' Metric.ball 0 s)`.

Introduce `h hh`. Take `⟨w, hw, hwe⟩` from `hWsub i hh`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Use `show g * xs i * w = h`. Establish `hwe' : xs i * w = g⁻¹ * h` using `hwe`.

Rewrite using `[mul_assoc, hwe']`. Simplify using the standard rewrite rules. Rewrite using `[nuG_eq hL hVW hD hdisj hcov hDV (g * xs i) hm hsub, nuG_eq hL hVW hD hdisj hcov hDV (xs i) (hmB i) (hWsub i), Measure.map_apply (measurable_const_mul _) hm, Measure.map_apply (measurable_const_mul _) (hmB i), ← preimage_comp]`. Use `congr 1`. Use extensionality with `h`.

Simplify using `[mul_assoc]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nuG_leftInv (hL : LocInv ε s) (hVW : V ⊆ expC ε '' Metric.ball 0 s)
    (hD : ∀ i, MeasurableSet (D i)) (hdisj : Pairwise (Disjoint on D)) (hcov : ⋃ i, D i = univ)
    (hDV : ∀ i, D i ⊆ (fun h => xs i * h) '' V) (g : Formalism.REAL.UJ ε) :
    (nuG ε s xs D).map (fun h => g * h) = nuG ε s xs D := by
  ext A hA
  rw [Measure.map_apply (measurable_const_mul g) hA]
  set B := (fun h => g * h) ⁻¹' A with hBdef
  have hB : MeasurableSet B := hA.preimage (measurable_const_mul g)
  have hmB : ∀ i, MeasurableSet (B ∩ D i) := fun i => hB.inter (hD i)
  have hUB : ⋃ i, B ∩ D i = B := by rw [← inter_iUnion, hcov, inter_univ]
  have hUA : ⋃ i, (fun h => g⁻¹ * h) ⁻¹' (B ∩ D i) = A := by
    rw [← preimage_iUnion, hUB, hBdef, ← preimage_comp]
    ext h; simp
  have hWsub : ∀ i, B ∩ D i ⊆ (fun h => xs i * h) '' (expC ε '' Metric.ball 0 s) := fun i =>
    (inter_subset_right.trans (hDV i)).trans (image_mono hVW)
  have e : ∀ i, nuG ε s xs D ((fun h => g⁻¹ * h) ⁻¹' (B ∩ D i)) = nuG ε s xs D (B ∩ D i) := by
    intro i
    have hm : MeasurableSet ((fun h => g⁻¹ * h) ⁻¹' (B ∩ D i)) := (hmB i).preimage (measurable_const_mul _)
    have hsub : (fun h => g⁻¹ * h) ⁻¹' (B ∩ D i) ⊆ (fun h => (g * xs i) * h) '' (expC ε '' Metric.ball 0 s) := by
      intro h hh
      obtain ⟨w, hw, hwe⟩ := hWsub i hh
      refine ⟨w, hw, ?_⟩
      show g * xs i * w = h
      have hwe' : xs i * w = g⁻¹ * h := hwe
      rw [mul_assoc, hwe']; simp
    rw [nuG_eq hL hVW hD hdisj hcov hDV (g * xs i) hm hsub, nuG_eq hL hVW hD hdisj hcov hDV (xs i) (hmB i) (hWsub i),
      Measure.map_apply (measurable_const_mul _) hm, Measure.map_apply (measurable_const_mul _) (hmB i), ← preimage_comp]
    congr 1
    ext h; simp [mul_assoc]
  calc nuG ε s xs D B = nuG ε s xs D (⋃ i, B ∩ D i) := by rw [hUB]
    _ = ∑' i, nuG ε s xs D (B ∩ D i) :=
        measure_iUnion (fun i j hij => (hdisj hij).mono inter_subset_right inter_subset_right) hmB
    _ = ∑' i, nuG ε s xs D ((fun h => g⁻¹ * h) ⁻¹' (B ∩ D i)) := (tsum_congr e).symm
    _ = nuG ε s xs D (⋃ i, (fun h => g⁻¹ * h) ⁻¹' (B ∩ D i)) :=
        (measure_iUnion (fun i j hij => ((hdisj hij).mono inter_subset_right inter_subset_right).preimage _)
          (fun i => (hmB i).preimage (measurable_const_mul _))).symm
    _ = nuG ε s xs D A := by rw [hUA]

end Cover

/- English proof (translation)
Rewrite using `[lamM, Measure.map_apply (measurable_expCG ε) hA, withDensity_apply _ (hA.preimage (measurable_expCG ε)), Measure.restrict_restrict (hA.preimage (measurable_expCG ε))]`.
-/
theorem lamM_applyG (ε : Fin n → Bool) (s : ℝ) {A : Set (Formalism.REAL.UJ ε)} (hA : MeasurableSet A) :
    lamM ε s A = ∫⁻ t in expC ε ⁻¹' A ∩ Metric.ball 0 s, jd ε t := by
  rw [lamM, Measure.map_apply (measurable_expCG ε) hA, withDensity_apply _ (hA.preimage (measurable_expCG ε)),
    Measure.restrict_restrict (hA.preimage (measurable_expCG ε))]

/- English proof (translation)
Rewrite using `[lamM_applyG ε s MeasurableSet.univ, preimage_univ, univ_inter]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lamM_univ_lt_top (ε : Fin n → Bool) (s : ℝ) : lamM ε s univ < ∞ := by
  rw [lamM_applyG ε s MeasurableSet.univ, preimage_univ, univ_inter]
  calc ∫⁻ t in Metric.ball (0 : EL ε) s, jd ε t ≤ ∫⁻ t in Metric.closedBall (0 : EL ε) s, jd ε t :=
        lintegral_mono_set Metric.ball_subset_closedBall
    _ = ∫⁻ t in Metric.closedBall (0 : EL ε) s, ((Real.toNNReal (chartJac (thetaExp ε) t) : NNReal) : ℝ≥0∞) := rfl
    _ < ∞ := setLIntegral_lt_top_of_isCompact (measure_closedBall_lt_top).ne (isCompact_closedBall 0 s)
        (continuous_real_toNNReal.comp (continuous_chartJac_thetaExp ε))

/- English proof (translation)
Rewrite using `[← expSet_ball_eq]`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, e⟩`. Conclude with `⟨t, ht, uMat_inj (by rw [uMat_expC, e]; rfl)⟩`.

Introduce and unpack `⟨t, ht, rfl⟩`. Conclude with `⟨t, ht, (uMat_expC ε t).symm⟩`.
-/
theorem expSet_ball_eq_image (ε : Fin n → Bool) (ρ : ℝ) :
    expSet ε (Metric.ball (0 : gLie ε) ρ) = expC ε '' Metric.ball 0 ρ := by
  rw [← expSet_ball_eq]
  ext g
  constructor
  · rintro ⟨t, ht, e⟩
    exact ⟨t, ht, uMat_inj (by rw [uMat_expC, e]; rfl)⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (uMat_expC ε t).symm⟩

/- English proof (translation)
Introduce and unpack `hN ⟨s₀, hs₀, hL⟩`. Take `⟨ρ₀, hρ₀, hinj⟩` from `injOn_thetaExp ε`. Establish `hs : 0 < min s₀ ρ₀` using `lt_min hs₀ hρ₀`. Use `set s := min s₀ ρ₀ with hsdef`. Establish `hLs : LocInv ε s` using `hL s hs (min_le_left _ _)`.

Establish `hinjs : Set.InjOn (expC ε) (Metric.ball 0 s)`. Introduce `a ha b hb e`. Apply `hinj (Metric.ball_subset_ball (min_le_right _ _) ha) (Metric.ball_subset_ball (min_le_right _ _) hb)` to reduce the goal to its premises. Use `congrArg uMat e` as an intermediate fact. Rewrite `this` using `[uMat_expC, uMat_expC]`.

Conclude with `Matrix.of.injective this`. Establish `hVo : IsOpen (interior (expC ε '' Metric.ball (0 : EL ε) s))` using `isOpen_interior`. Establish `hVW : interior (expC ε '' Metric.ball (0 : EL ε) s) ⊆ expC ε '' Metric.ball (0 : EL ε) s` using `interior_subset`. Establish `hV1 : (1 : Formalism.REAL.UJ ε) ∈ interior (expC ε '' Metric.ball (0 : EL ε) s)` using `mem_interior_iff_mem_nhds.2 (hN s hs)`. Use `set V := interior (expC ε '' Metric.ball (0 : EL ε) s) with hVdef`.

Establish `hcovN : ∀ x : Formalism.REAL.UJ ε, (fun h => x * h) '' V ∈ 𝓝 x` using `fun x => ((isOpenMap_mul_left x) V hVo).mem_nhds ⟨1, hV1, mul_one x⟩`. Establish `hOm' : ∀ y : Formalism.REAL.UJ ε, MeasurableSet ((fun h => y * h) '' V)` using `fun y => ((isOpenMap_mul_left y) V hVo).measurableSet`. Take `⟨S, hSc, hSU⟩` from `TopologicalSpace.countable_cover_nhds hcovN`. Establish `hSne : S.Nonempty`. Assume the negation of the conclusion as `h`.

Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Establish `: (1 : Formalism.REAL.UJ ε) ∈ ⋃ x ∈ S, (fun h => x * h) '' V` using `by rw [hSU]; trivial`. Rewrite `this` using `[h]`. Simplify using `at this`. Take `⟨xs, hxs⟩` from `hSc.exists_eq_range hSne`.

Set `O : ℕ → Set (Formalism.REAL.UJ ε)` to `fun i => (fun h => xs i * h) '' V`. Establish `hOU : ⋃ i, O i = univ` using `by rw [← hSU, hxs, Set.biUnion_range]`. Establish `hD : ∀ i, MeasurableSet (disjointed O i)` using `MeasurableSet.disjointed fun i => hOm' (xs i)`. Establish `hdisj : Pairwise (Disjoint on disjointed O)` using `disjoint_disjointed O`. Establish `hcov : ⋃ i, disjointed O i = univ` using `by rw [iUnion_disjointed, hOU]`.

Establish `hDV : ∀ i, disjointed O i ⊆ (fun h => xs i * h) '' V` using `fun i => disjointed_subset O i`. Use `haveI : Measure.IsMulLeftInvariant (nuG ε s xs (disjointed O)) := ⟨fun g => nuG_leftInv hLs hVW hD hdisj hcov hDV g⟩`. Use `haveI : IsLocallyFiniteMeasure (nuG ε s xs (disjointed O)) := ⟨fun y => ⟨(fun h => y * h) '' V, hcovN y, by`. Rewrite using `[nuG_eq hLs hVW hD hdisj hcov hDV y (hOm' y) (image_mono hVW)]`. Combine the equalities or inequalities in the displayed calculation.

Use `haveI : Measure.IsHaarMeasure (Formalism.REAL.muG ε) := by unfold Formalism.REAL.muG; infer_instance`. Establish `hνμ` using `Measure.isMulLeftInvariant_eq_smul (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε)`. Use `set κ := Measure.haarScalarFactor (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε) with hκdef`. Establish `hform : ∀ ρ, 0 < ρ → ρ ≤ s → nuG ε s xs (disjointed O) (expC ε '' Metric.ball 0 ρ) = ∫⁻ t in Metric.ball (0 : EL ε) ρ, jd ε t`. Introduce `ρ hρ hρs`.

Establish `hsub : Metric.ball (0 : EL ε) ρ ⊆ Metric.ball 0 s` using `Metric.ball_subset_ball hρs`. Establish `hm : MeasurableSet (expC ε '' Metric.ball 0 ρ)` using `measurableSet_ball.image_of_continuousOn_injOn (continuous_expCG ε).continuousOn (hinjs.mono hsub)`. Establish `hsubW : expC ε '' Metric.ball 0 ρ ⊆ (fun h => (1 : Formalism.REAL.UJ ε) * h) '' (expC ε '' Metric.ball 0 s)`. Simplify using `only [one_mul, image_id']`. Conclude with `image_mono hsub`.

Rewrite using `[nuG_eq hLs hVW hD hdisj hcov hDV 1 hm hsubW]`. Establish `hmap : (lamM ε s).map (fun h => (1 : Formalism.REAL.UJ ε) * h) = lamM ε s`. Simplify using `only [one_mul]`. Conclude with `Measure.map_id`. Rewrite using `[hmap, lamM_applyG ε s hm]`.

Rewrite using `[show expC ε ⁻¹' (expC ε '' Metric.ball 0 ρ) ∩ Metric.ball 0 s = Metric.ball 0 ρ from ?_]`. Use extensionality with `t`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨t', ht', e⟩, ht⟩`. Rewrite using `[← hinjs (hsub ht') ht e]`.

Conclude with `ht'`. Introduce `ht`. Conclude with `⟨⟨t, ht, rfl⟩, hsub ht⟩`. Take `⟨η, hη, hcont⟩` from `Metric.continuousAt_iff.1 ((continuous_chartJac_thetaExp ε).continuousAt (x := 0)) (1 / 2) (by norm_num)`. Establish `hρ1 : 0 < min s η` using `lt_min hs hη`.

Establish `hpos : ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t ≠ 0`. Establish `hle : ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : EL ε) (min s η)) ≤ ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t`. Rewrite using `[← setLIntegral_const]`. Use `lintegral_mono_ae ?_` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem measurableSet_ball] with t ht`.

Use `hcont (lt_of_lt_of_le ht (min_le_right _ _))` as an intermediate fact. Rewrite `this` using `[chartJac_thetaExp_zero, Real.dist_eq]`. Conclude with `ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 this).1])`. Use `(lt_of_lt_of_le ?_ hle).ne'` and prove the remaining obligations. Conclude with `ENNReal.mul_pos (by simp) (Metric.measure_ball_pos _ _ hρ1).ne'`.

Establish `hκ : κ ≠ 0`. Introduce `h0`. Apply `hpos` to reduce the goal to its premises. Rewrite using `[← hform _ hρ1 (min_le_left _ _), hνμ, h0, zero_smul]`. Both sides reduce to the same expression.

Establish `hκpos : (0 : ℝ) < (κ : ℝ)` using `NNReal.coe_pos.2 (pos_iff_ne_zero.2 hκ)`. Use `⟨((κ : ℝ))⁻¹, inv_pos.2 hκpos, s, hs, fun ρ hρ hρs => ?_⟩` and prove the remaining obligations. Rewrite using `[expSet_ball_eq_image]`. Establish `h1` using `hform ρ hρ hρs`. Rewrite `h1` using `[hνμ]`.

Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1`. Rewrite using `[← h1, ← mul_assoc, ENNReal.ofReal_inv_of_pos hκpos, ENNReal.ofReal_coe_nnreal, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hκ) ENNReal.coe_ne_top, one_mul]`.
-/
theorem ballFormOf (ε : Fin n → Bool) : BallFormOf ε := by
  rintro hN ⟨s₀, hs₀, hL⟩
  obtain ⟨ρ₀, hρ₀, hinj⟩ := injOn_thetaExp ε
  have hs : 0 < min s₀ ρ₀ := lt_min hs₀ hρ₀
  set s := min s₀ ρ₀ with hsdef
  have hLs : LocInv ε s := hL s hs (min_le_left _ _)
  have hinjs : Set.InjOn (expC ε) (Metric.ball 0 s) := by
    intro a ha b hb e
    apply hinj (Metric.ball_subset_ball (min_le_right _ _) ha) (Metric.ball_subset_ball (min_le_right _ _) hb)
    have := congrArg uMat e
    rw [uMat_expC, uMat_expC] at this
    exact Matrix.of.injective this
  have hVo : IsOpen (interior (expC ε '' Metric.ball (0 : EL ε) s)) := isOpen_interior
  have hVW : interior (expC ε '' Metric.ball (0 : EL ε) s) ⊆ expC ε '' Metric.ball (0 : EL ε) s := interior_subset
  have hV1 : (1 : Formalism.REAL.UJ ε) ∈ interior (expC ε '' Metric.ball (0 : EL ε) s) :=
    mem_interior_iff_mem_nhds.2 (hN s hs)
  set V := interior (expC ε '' Metric.ball (0 : EL ε) s) with hVdef
  have hcovN : ∀ x : Formalism.REAL.UJ ε, (fun h => x * h) '' V ∈ 𝓝 x := fun x =>
    ((isOpenMap_mul_left x) V hVo).mem_nhds ⟨1, hV1, mul_one x⟩
  have hOm' : ∀ y : Formalism.REAL.UJ ε, MeasurableSet ((fun h => y * h) '' V) := fun y =>
    ((isOpenMap_mul_left y) V hVo).measurableSet
  obtain ⟨S, hSc, hSU⟩ := TopologicalSpace.countable_cover_nhds hcovN
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : (1 : Formalism.REAL.UJ ε) ∈ ⋃ x ∈ S, (fun h => x * h) '' V := by rw [hSU]; trivial
    rw [h] at this; simp at this
  obtain ⟨xs, hxs⟩ := hSc.exists_eq_range hSne
  let O : ℕ → Set (Formalism.REAL.UJ ε) := fun i => (fun h => xs i * h) '' V
  have hOU : ⋃ i, O i = univ := by rw [← hSU, hxs, Set.biUnion_range]
  have hD : ∀ i, MeasurableSet (disjointed O i) := MeasurableSet.disjointed fun i => hOm' (xs i)
  have hdisj : Pairwise (Disjoint on disjointed O) := disjoint_disjointed O
  have hcov : ⋃ i, disjointed O i = univ := by rw [iUnion_disjointed, hOU]
  have hDV : ∀ i, disjointed O i ⊆ (fun h => xs i * h) '' V := fun i => disjointed_subset O i
  haveI : Measure.IsMulLeftInvariant (nuG ε s xs (disjointed O)) := ⟨fun g => nuG_leftInv hLs hVW hD hdisj hcov hDV g⟩
  haveI : IsLocallyFiniteMeasure (nuG ε s xs (disjointed O)) := ⟨fun y => ⟨(fun h => y * h) '' V, hcovN y, by
      rw [nuG_eq hLs hVW hD hdisj hcov hDV y (hOm' y) (image_mono hVW)]
      calc (lamM ε s).map (fun h => y * h) ((fun h => y * h) '' V) ≤ (lamM ε s).map (fun h => y * h) univ :=
            measure_mono (subset_univ _)
        _ = lamM ε s univ := by rw [Measure.map_apply (measurable_const_mul y) MeasurableSet.univ, preimage_univ]
        _ < ∞ := lamM_univ_lt_top ε s⟩⟩
  haveI : Measure.IsHaarMeasure (Formalism.REAL.muG ε) := by unfold Formalism.REAL.muG; infer_instance
  have hνμ := Measure.isMulLeftInvariant_eq_smul (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε)
  set κ := Measure.haarScalarFactor (nuG ε s xs (disjointed O)) (Formalism.REAL.muG ε) with hκdef
  have hform : ∀ ρ, 0 < ρ → ρ ≤ s →
      nuG ε s xs (disjointed O) (expC ε '' Metric.ball 0 ρ) = ∫⁻ t in Metric.ball (0 : EL ε) ρ, jd ε t := by
    intro ρ hρ hρs
    have hsub : Metric.ball (0 : EL ε) ρ ⊆ Metric.ball 0 s := Metric.ball_subset_ball hρs
    have hm : MeasurableSet (expC ε '' Metric.ball 0 ρ) :=
      measurableSet_ball.image_of_continuousOn_injOn (continuous_expCG ε).continuousOn (hinjs.mono hsub)
    have hsubW : expC ε '' Metric.ball 0 ρ ⊆ (fun h => (1 : Formalism.REAL.UJ ε) * h) '' (expC ε '' Metric.ball 0 s) := by
      simp only [one_mul, image_id']; exact image_mono hsub
    rw [nuG_eq hLs hVW hD hdisj hcov hDV 1 hm hsubW]
    have hmap : (lamM ε s).map (fun h => (1 : Formalism.REAL.UJ ε) * h) = lamM ε s := by
      simp only [one_mul]; exact Measure.map_id
    rw [hmap, lamM_applyG ε s hm]
    rw [show expC ε ⁻¹' (expC ε '' Metric.ball 0 ρ) ∩ Metric.ball 0 s = Metric.ball 0 ρ from ?_]
    ext t
    constructor
    · rintro ⟨⟨t', ht', e⟩, ht⟩
      rw [← hinjs (hsub ht') ht e]; exact ht'
    · intro ht; exact ⟨⟨t, ht, rfl⟩, hsub ht⟩
  obtain ⟨η, hη, hcont⟩ := Metric.continuousAt_iff.1 ((continuous_chartJac_thetaExp ε).continuousAt (x := 0)) (1 / 2)
    (by norm_num)
  have hρ1 : 0 < min s η := lt_min hs hη
  have hpos : ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t ≠ 0 := by
    have hle : ENNReal.ofReal (1 / 2) * volume (Metric.ball (0 : EL ε) (min s η)) ≤
        ∫⁻ t in Metric.ball (0 : EL ε) (min s η), jd ε t := by
      rw [← setLIntegral_const]
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with t ht
      have := hcont (lt_of_lt_of_le ht (min_le_right _ _))
      rw [chartJac_thetaExp_zero, Real.dist_eq] at this
      exact ENNReal.ofReal_le_ofReal (by linarith [(abs_lt.1 this).1])
    refine (lt_of_lt_of_le ?_ hle).ne'
    exact ENNReal.mul_pos (by simp) (Metric.measure_ball_pos _ _ hρ1).ne'
  have hκ : κ ≠ 0 := by
    intro h0
    apply hpos
    rw [← hform _ hρ1 (min_le_left _ _), hνμ, h0, zero_smul]
    rfl
  have hκpos : (0 : ℝ) < (κ : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hκ)
  refine ⟨((κ : ℝ))⁻¹, inv_pos.2 hκpos, s, hs, fun ρ hρ hρs => ?_⟩
  rw [expSet_ball_eq_image]
  have h1 := hform ρ hρ hρs
  rw [hνμ] at h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
  rw [← h1, ← mul_assoc, ENNReal.ofReal_inv_of_pos hκpos, ENNReal.ofReal_coe_nnreal,
    ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hκ) ENNReal.coe_ne_top, one_mul]

end Glue

end Formalism.MainNotions.S.Gauge
