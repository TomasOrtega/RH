import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClassAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.DixmierMalliavin
import GroundTheory.AutomorphicForms.L2LocalComponents.ArchBump

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ContDiff

/- English proof (translation)
Simplify using `only [frobSq, Matrix.mul_diagonal, norm_mul, mul_pow, he, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _`.
-/
private theorem frob_diag {𝕜 : Type*} [RCLike 𝕜] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) (e : 𝕜) (r : ℝ)
    (he : ‖e‖ = r) : frobSq (M * Matrix.diagonal fun _ => e) = r ^ 2 * frobSq M := by
  simp only [frobSq, Matrix.mul_diagonal, norm_mul, mul_pow, he, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _

private noncomputable def lam (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : ℝ :=
  ((rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s : {r : ℝ // 0 < r}) : ℝ)

/- English proof (translation)
The claim follows from `(rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s).2`.
-/
private theorem lam_pos (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r}) : 0 < lam K n s :=
  (rpowHom ((n * Module.finrank ℚ K : ℝ))⁻¹ s).2

/- English proof (translation)
Use `⟨(GroundTheory.Global.IdeleGroup.infiniteProj w (posIdele (K := K) (lam K n s) (lam_pos K n s)) : (w.Completion)ˣ), ?_, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[GroundTheory.Global.IdeleGroup.coe_infiniteProj]`. Conclude with `norm_posIdele_infinite _ _ w`. Establish `e : centralSection K n s = diagUnits n fun _ => posIdele (K` using `K) (lam K n s) (lam_pos K n s) := rfl`. Rewrite using `[infEmb_zInf, e, infAt_diagUnits, coe_diagUnits, Matrix.diagonal_apply]`.
-/
private theorem infAt_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (s : {r : ℝ // 0 < r})
    (w : InfinitePlace K) : ∃ u : w.Completion, ‖u‖ = lam K n s ∧ ∀ a b : Fin n,
      Reduction.infAt w (infEmb K n (zInf K n s)) a b = if a = b then u else 0 := by
  refine ⟨(GroundTheory.Global.IdeleGroup.infiniteProj w (posIdele (K := K) (lam K n s) (lam_pos K n s)) : (w.Completion)ˣ), ?_, fun a b => ?_⟩
  · rw [GroundTheory.Global.IdeleGroup.coe_infiniteProj]
    exact norm_posIdele_infinite _ _ w
  · have e : centralSection K n s = diagUnits n fun _ => posIdele (K := K) (lam K n s) (lam_pos K n s) := rfl
    rw [infEmb_zInf, e, infAt_diagUnits, coe_diagUnits, Matrix.diagonal_apply]

/- English proof (translation)
Establish `hr : ∀ v : {w : InfinitePlace K // InfinitePlace.IsReal w}, ∃ e : ℝ, ‖e‖ = lam K n s ∧ realCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e`. Introduce and unpack `⟨w, hw⟩`. Take `⟨u, hu, hab⟩` from `infAt_zInf K n s w`. Use `⟨InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu]`.

Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) u`. Use extensionality with `a b`. Establish `h1` using `congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) (hab a b)`. Rewrite `h1` using `[infAt_infEmb_apply, extensionEmbeddingOfIsReal_symm]`. Simplify using `only [realCompM_apply, Matrix.map_apply, realComp_apply, Matrix.diagonal_apply]`.

Rewrite using `[h1]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hc : ∀ v : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ∃ e : ℂ, ‖e‖ = lam K n s ∧ complexCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e`. Introduce and unpack `⟨w, hw⟩`. Take `⟨u, hu, hab⟩` from `infAt_zInf K n s w`.

Use `⟨InfinitePlace.Completion.extensionEmbedding w u, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu]`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) u`. Use extensionality with `a b`. Establish `h1` using `congrArg (InfinitePlace.Completion.extensionEmbedding w) (hab a b)`.

Rewrite `h1` using `[infAt_infEmb_apply, extensionEmbedding_symm _ hw]`. Simplify using `only [complexCompM_apply, Matrix.map_apply, complexComp_apply, Matrix.diagonal_apply]`. Rewrite using `[h1]`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [archQuad, mul_add, Finset.mul_sum, map_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Take `⟨e, he, hv⟩` from `hr v`. Rewrite using `[hv, frob_diag _ e _ he]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Take `⟨e, he, hv⟩` from `hc v`. Rewrite using `[hv, frob_diag _ e _ he]`.
-/
private theorem quad_mul_zInf (K : Type) [Field K] [NumberField K] (n : ℕ) (A : ArchMatrix K n)
    (s : {r : ℝ // 0 < r}) : archQuad (A * archVal (zInf K n s)) = lam K n s ^ 2 * archQuad A := by
  have hr : ∀ v : {w : InfinitePlace K // InfinitePlace.IsReal w}, ∃ e : ℝ, ‖e‖ = lam K n s ∧
      realCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbeddingOfIsReal hw u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbeddingOfIsReal_symm] at h1
      simp only [realCompM_apply, Matrix.map_apply, realComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  have hc : ∀ v : {w : InfinitePlace K // InfinitePlace.IsComplex w}, ∃ e : ℂ, ‖e‖ = lam K n s ∧
      complexCompM v (archVal (zInf K n s)) = Matrix.diagonal fun _ => e := by
    rintro ⟨w, hw⟩
    obtain ⟨u, hu, hab⟩ := infAt_zInf K n s w
    refine ⟨InfinitePlace.Completion.extensionEmbedding w u, ?_, ?_⟩
    · rw [← hu]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) u
    · ext a b
      have h1 := congrArg (InfinitePlace.Completion.extensionEmbedding w) (hab a b)
      rw [infAt_infEmb_apply, extensionEmbedding_symm _ hw] at h1
      simp only [complexCompM_apply, Matrix.map_apply, complexComp_apply, Matrix.diagonal_apply]
      rw [h1]
      split_ifs <;> simp
  simp only [archQuad, mul_add, Finset.mul_sum, map_mul]
  congr 1
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hr v
    rw [hv, frob_diag _ e _ he]
  · refine Finset.sum_congr rfl fun v _ => ?_
    obtain ⟨e, he, hv⟩ := hc v
    rw [hv, frob_diag _ e _ he]

/- English proof (translation)
Introduce `h`. Establish `h0` using `archQuad_eq_zero h`. Establish `h1 : archVal a * archVal a⁻¹ = 1`. Rewrite using `[archVal, archVal, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]`. Rewrite `h1` using `[h0, zero_mul]`.

Establish `h2 : (0 : mixedEmbedding.mixedSpace K) = 1`. Establish `h3` using `congrFun (congrFun (congrArg mat h1) ⟨0, hn⟩) ⟨0, hn⟩`. Rewrite `h3` using `[mat_zero, mat_one, Matrix.one_apply_eq]`. Conclude with `h3`. Take `⟨w⟩ : Nonempty (InfinitePlace K)` from `inferInstance`.

Distinguish the cases in `hw : InfinitePlace.IsReal w`. Establish `h3` using `congrArg (fun p : mixedEmbedding.mixedSpace K => p.1 ⟨w, hw⟩) h2`. Conclude with `zero_ne_one (α := ℝ) h3`. Establish `hw'` using `InfinitePlace.not_isReal_iff_isComplex.1 hw`. Establish `h3` using `congrArg (fun p : mixedEmbedding.mixedSpace K => p.2 ⟨w, hw'⟩) h2`.

Conclude with `zero_ne_one (α := ℂ) h3`.
-/
private theorem quad_ne (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) :
    archQuad (archVal a) ≠ 0 := by
  intro h
  have h0 := archQuad_eq_zero h
  have h1 : archVal a * archVal a⁻¹ = 1 := by
    rw [archVal, archVal, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  rw [h0, zero_mul] at h1
  have h2 : (0 : mixedEmbedding.mixedSpace K) = 1 := by
    have h3 := congrFun (congrFun (congrArg mat h1) ⟨0, hn⟩) ⟨0, hn⟩
    rw [mat_zero, mat_one, Matrix.one_apply_eq] at h3
    exact h3
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  by_cases hw : InfinitePlace.IsReal w
  · have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.1 ⟨w, hw⟩) h2
    exact zero_ne_one (α := ℝ) h3
  · have hw' := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have h3 := congrArg (fun p : mixedEmbedding.mixedSpace K => p.2 ⟨w, hw'⟩) h2
    exact zero_ne_one (α := ℂ) h3

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Real.exp t) ^ ((n * Module.finrank ℚ K : ℝ))⁻¹ = _`. Rewrite using `[← Real.exp_mul]`.
-/
private theorem lam_exp (K : Type) [Field K] [NumberField K] (n : ℕ) (t : ℝ) :
    lam K n (GroundTheory.Global.expPos t) = Real.exp (t * (n * Module.finrank ℚ K : ℝ)⁻¹) := by
  change (Real.exp t) ^ ((n * Module.finrank ℚ K : ℝ))⁻¹ = _
  rw [← Real.exp_mul]

private noncomputable def lq (K : Type) [Field K] [NumberField K] (n : ℕ) (a : archGroup K n) : ℝ :=
  Real.log (archQuad (archVal a))

/- English proof (translation)
Establish `e : archVal (a * zInf K n (GroundTheory.Global.expPos t)) = archVal a * archVal (zInf K n (GroundTheory.Global.expPos t))` using `rfl`. Rewrite using `[lq, e, quad_mul_zInf, lam_exp, Real.log_mul (by positivity) (quad_ne K n hn a), Real.log_pow, Real.log_exp, lq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem lq_mul (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) (a : archGroup K n) (t : ℝ) :
    lq K n (a * zInf K n (GroundTheory.Global.expPos t)) = lq K n a + 2 * (n * Module.finrank ℚ K : ℝ)⁻¹ * t := by
  have e : archVal (a * zInf K n (GroundTheory.Global.expPos t)) = archVal a * archVal (zInf K n (GroundTheory.Global.expPos t)) := rfl
  rw [lq, e, quad_mul_zInf, lam_exp, Real.log_mul (by positivity) (quad_ne K n hn a), Real.log_pow, Real.log_exp, lq]
  push_cast
  ring

/- English proof (translation)
The claim follows from `Continuous.log ((contDiff_archQuad (K := K) (n := n)).continuous.comp continuous_archVal) (quad_ne K n hn)`.
-/
private theorem continuous_lq (K : Type) [Field K] [NumberField K] (n : ℕ) (hn : 0 < n) :
    Continuous (lq K n) :=
  Continuous.log ((contDiff_archQuad (K := K) (n := n)).continuous.comp continuous_archVal) (quad_ne K n hn)

/- English proof (translation)
Introduce `K _ _ n hn`. Use `set d : ℝ := (n * Module.finrank ℚ K : ℝ) with hd`. Establish `hd0 : 0 < d`. Establish `: 0 < Module.finrank ℚ K` using `Module.finrank_pos`. Establish `h2 : (0 : ℝ) < n` using `Nat.cast_pos.2 hn`.

Establish `h3 : (0 : ℝ) < Module.finrank ℚ K` using `Nat.cast_pos.2 this`. Check the signs of the components of the expression. Use `set β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hβ`. Use `set h : ℝ → ℝ := β.normed volume with hh`. Use `set c : ℝ := 2 * d⁻¹ with hc`.

Establish `hc0 : 0 < c` using `by positivity`. Use `⟨fun A => c * h (lq K n A), ?_, fun A => ?_, fun C hC => ?_⟩` and prove the remaining obligations. Rewrite using `[IsExpLieAlgebra.isSmoothFun_iff]`. Introduce `g`. Establish `hY : ContDiff ℝ ∞ (fun Y : archLie K n => (Y : ArchMatrix K n))` using `(Submodule.subtypeL (archLie K n)).contDiff`.

Establish `hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n)` using `contDiff_exp ℝ _`. Establish `hq : ContDiff ℝ ∞ (archQuad : ArchMatrix K n → ℝ)` using `contDiff_archQuad.of_le le_top`. Establish `e : (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) = fun Y : archLie K n => Real.log (archQuad (archVal g * NormedSpace.exp (Y : ArchMatrix K n)))`. Use function extensionality and compare the values at `Y`. Simplify using `only [lq, archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]`.

Establish `hl : ContDiff ℝ ∞ (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y))`. Rewrite using `[e]`. Use `ContDiff.log (hq.comp (contDiff_const.mul (hexp.comp hY))) fun Y => ?_` and prove the remaining obligations. Use `quad_ne K n hn (g * (isExpLieAlgebra K n).expG Y)` as an intermediate fact. Simplify `this` using `only [archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]`.

Conclude with `Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (β.contDiff_normed.comp hl))`. Establish `hemb : MeasurableEmbedding GroundTheory.Global.expPos` using `GroundTheory.Global.expPosHomeomorph.measurableEmbedding`. Rewrite using `[kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos, hemb.integral_map]`. Establish `e1 : ∀ t : ℝ, ((c * h (lq K n (A * zInf K n (GroundTheory.Global.expPos t))) : ℝ) : ℂ) = ((c * h (lq K n A + c * t) : ℝ) : ℂ)` using `fun t => by`. Rewrite using `[lq_mul K n hn]`.

Simplify using `only [e1]`. Rewrite using `[integral_complex_ofReal, integral_const_mul]`. Establish `e2 : ∫ t, h (lq K n A + c * t) = |c⁻¹| • ∫ y, h (lq K n A + y)` using `Measure.integral_comp_mul_left (fun y => h (lq K n A + y)) c`. Rewrite using `[e2, integral_add_left_eq_self h (lq K n A), hh, β.integral_normed, abs_of_pos (inv_pos.2 hc0), smul_eq_mul, mul_one, mul_inv_cancel₀ hc0.ne']`. Simplify using the standard rewrite rules.

Use `set C' : Set (archGroup K n) := (fun x : G1 K n => infPart K n (x : AdelicGLn.AdelicGL K n)) '' C with hC'`. Establish `hC'c : IsCompact C'` using `hC.image (continuous_infPart.comp continuous_subtype_val)`. Take `⟨M, hM⟩` from `hC'c.exists_bound_of_continuousOn (continuous_lq K n hn).continuousOn`. Use `set R : ℝ := (2 + M) / c with hR`. Use `⟨(fun p : archGroup K n × ℝ => p.1 * zInf K n (GroundTheory.Global.expPos p.2)) '' (C' ×ˢ Set.Icc (-R) R), (hC'c.prod isCompact_Icc).image (continuous_fst.mul (continuous_zInf.comp (GroundTheory.Global.expPosHomeomorph.continuous.comp continuous_snd))), fun A hA hAC => ?_⟩` and prove the remaining obligations.

Use `set r := detA K n A with hr`. Use `set a := infPart K n (archP K n A : AdelicGLn.AdelicGL K n) with ha`. Establish `haC : a ∈ C'` using `⟨_, hAC, rfl⟩`. Establish `hr' : GroundTheory.Global.expPos (Real.log r) = r` using `Subtype.ext (Real.exp_log r.2)`. Establish `hAa : A = a * zInf K n (GroundTheory.Global.expPos (Real.log r))`.

Rewrite using `[hr', ha, infPart_archP, inv_mul_cancel_right]`. Establish `hsup : lq K n A ∈ Metric.ball (0 : ℝ) 2`. Establish `h1 : h (lq K n A) ≠ 0` using `right_ne_zero_of_mul hA`. Establish `h2 : lq K n A ∈ Function.support h` using `h1`. Rewrite `h2` using `[hh, β.support_normed_eq]`.

Conclude with `h2`. Rewrite `hsup` using `[Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]`. Establish `hl` using `lq_mul K n hn a (Real.log r)`. Rewrite `hl` using `[← hAa]`. Establish `hMa` using `hM a haC`.

Rewrite `hMa` using `[Real.norm_eq_abs]`. Establish `hct : |c * Real.log r| ≤ 2 + M`. Establish `e3 : c * Real.log r = lq K n A - lq K n a` using `by rw [hl, hc, hd]; ring`. Rewrite using `[e3]`. Conclude with `(abs_sub _ _).trans (by linarith)`.

Establish `ht : |Real.log r| ≤ R`. Rewrite using `[hR, le_div_iff₀ hc0]`. Rewrite `hct` using `[abs_mul, abs_of_pos hc0, mul_comm]`. Then use the resulting hypothesis. Conclude with `⟨(a, Real.log r), ⟨haC, abs_le.1 ht⟩, hAa.symm⟩`.
-/
theorem UpperTheory.exists_smooth_archCutoff_kbar_eq_one :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n →
        ∃ χ : archGroup K n → ℝ, (isExpLieAlgebra K n).IsSmoothFun (fun A => (χ A : ℂ)) ∧
          (∀ A, kbar (fun g => (χ g : ℂ)) A = 1) ∧
          ∀ C : Set (G1 K n), IsCompact C → ∃ D : Set (archGroup K n), IsCompact D ∧
            ∀ A, χ A ≠ 0 → archP K n A ∈ C → A ∈ D := by
  intro K _ _ n hn
  set d : ℝ := (n * Module.finrank ℚ K : ℝ) with hd
  have hd0 : 0 < d := by
    have : 0 < Module.finrank ℚ K := Module.finrank_pos
    have h2 : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have h3 : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.2 this
    positivity
  set β : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩ with hβ
  set h : ℝ → ℝ := β.normed volume with hh
  set c : ℝ := 2 * d⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨fun A => c * h (lq K n A), ?_, fun A => ?_, fun C hC => ?_⟩
  · rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have hY : ContDiff ℝ ∞ (fun Y : archLie K n => (Y : ArchMatrix K n)) :=
      (Submodule.subtypeL (archLie K n)).contDiff
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : ArchMatrix K n → ArchMatrix K n) :=
      contDiff_exp ℝ _
    have hq : ContDiff ℝ ∞ (archQuad : ArchMatrix K n → ℝ) := contDiff_archQuad.of_le le_top
    have e : (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) = fun Y : archLie K n =>
        Real.log (archQuad (archVal g * NormedSpace.exp (Y : ArchMatrix K n))) := by
      funext Y
      simp only [lq, archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG]
    have hl : ContDiff ℝ ∞ (fun Y : archLie K n => lq K n (g * (isExpLieAlgebra K n).expG Y)) := by
      rw [e]
      refine ContDiff.log (hq.comp (contDiff_const.mul (hexp.comp hY))) fun Y => ?_
      have := quad_ne K n hn (g * (isExpLieAlgebra K n).expG Y)
      simpa only [archVal, Subgroup.coe_mul, Units.val_mul, IsExpLieAlgebra.coe_expG] using this
    exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (β.contDiff_normed.comp hl))
  · have hemb : MeasurableEmbedding GroundTheory.Global.expPos :=
      GroundTheory.Global.expPosHomeomorph.measurableEmbedding
    rw [kbar, GroundTheory.Global.posRealMeasure_eq_map_expPos, hemb.integral_map]
    have e1 : ∀ t : ℝ, ((c * h (lq K n (A * zInf K n (GroundTheory.Global.expPos t))) : ℝ) : ℂ) =
        ((c * h (lq K n A + c * t) : ℝ) : ℂ) := fun t => by
      rw [lq_mul K n hn]
    simp only [e1]
    rw [integral_complex_ofReal, integral_const_mul]
    have e2 : ∫ t, h (lq K n A + c * t) = |c⁻¹| • ∫ y, h (lq K n A + y) :=
      Measure.integral_comp_mul_left (fun y => h (lq K n A + y)) c
    rw [e2, integral_add_left_eq_self h (lq K n A), hh, β.integral_normed, abs_of_pos (inv_pos.2 hc0),
      smul_eq_mul, mul_one, mul_inv_cancel₀ hc0.ne']
    simp
  · set C' : Set (archGroup K n) := (fun x : G1 K n => infPart K n (x : AdelicGLn.AdelicGL K n)) '' C with hC'
    have hC'c : IsCompact C' := hC.image (continuous_infPart.comp continuous_subtype_val)
    obtain ⟨M, hM⟩ := hC'c.exists_bound_of_continuousOn (continuous_lq K n hn).continuousOn
    set R : ℝ := (2 + M) / c with hR
    refine ⟨(fun p : archGroup K n × ℝ => p.1 * zInf K n (GroundTheory.Global.expPos p.2)) '' (C' ×ˢ Set.Icc (-R) R),
      (hC'c.prod isCompact_Icc).image
        (continuous_fst.mul (continuous_zInf.comp (GroundTheory.Global.expPosHomeomorph.continuous.comp continuous_snd))),
      fun A hA hAC => ?_⟩
    set r := detA K n A with hr
    set a := infPart K n (archP K n A : AdelicGLn.AdelicGL K n) with ha
    have haC : a ∈ C' := ⟨_, hAC, rfl⟩
    have hr' : GroundTheory.Global.expPos (Real.log r) = r := Subtype.ext (Real.exp_log r.2)
    have hAa : A = a * zInf K n (GroundTheory.Global.expPos (Real.log r)) := by
      rw [hr', ha, infPart_archP, inv_mul_cancel_right]
    have hsup : lq K n A ∈ Metric.ball (0 : ℝ) 2 := by
      have h1 : h (lq K n A) ≠ 0 := right_ne_zero_of_mul hA
      have h2 : lq K n A ∈ Function.support h := h1
      rw [hh, β.support_normed_eq] at h2
      exact h2
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hsup
    have hl := lq_mul K n hn a (Real.log r)
    rw [← hAa] at hl
    have hMa := hM a haC
    rw [Real.norm_eq_abs] at hMa
    have hct : |c * Real.log r| ≤ 2 + M := by
      have e3 : c * Real.log r = lq K n A - lq K n a := by rw [hl, hc, hd]; ring
      rw [e3]
      exact (abs_sub _ _).trans (by linarith)
    have ht : |Real.log r| ≤ R := by
      rw [hR, le_div_iff₀ hc0]
      rwa [abs_mul, abs_of_pos hc0, mul_comm] at hct
    exact ⟨(a, Real.log r), ⟨haC, abs_le.1 ht⟩, hAa.symm⟩
