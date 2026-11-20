import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.StarInvMulVecDotProductMulVecInvMulVec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NormDetDenomLeRankOne
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFourierExpansionHolomorphicTubeStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsIntegralBasisHermitianMatricesDualStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.TracePairingGeDetImPowHermitianHalfSpaceStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SummableExpNegTraceTotallyPositiveHermitianStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.Decay

open MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {N : ℕ}

def pr (T : Matrix (Fin N) (Fin N) E) (Z : CM Ψ N N) : ℂ := ∑ τ : Ψ, (T.map τ.1 * Z τ).trace

def cube (m : ℕ) : Set (Fin m → ℝ) := Set.pi Set.univ (fun _ : Fin m => Set.Ico (0 : ℝ) 1)

/- English proof (translation)
Simplify using `[cube, volume_pi_pi]`.
-/
theorem volume_cube (m : ℕ) : volume (cube m) = 1 := by
  simp [cube, volume_pi_pi]

/- English proof (translation)
Rewrite using `[Matrix.IsHermitian, ← Base.ccT_map, h]`.
-/
theorem herm_map {T : Matrix (Fin N) (Fin N) E} (h : ccT T = T) (τ : E →+* ℂ) :
    (T.map τ).IsHermitian := by
  rw [Matrix.IsHermitian, ← Base.ccT_map, h]

/- English proof (translation)
Rewrite using `[← Complex.conj_eq_iff_im]`. Use `Matrix.trace_conjTranspose (A * B)` as an intermediate fact. Rewrite `this` using `[conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]`. Conclude with `this.symm`.
-/
theorem trace_im {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have := Matrix.trace_conjTranspose (A * B)
  rw [conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm] at this
  exact this.symm

/- English proof (translation)
Rewrite using `[imH, h.eq, sub_self, smul_zero]`.
-/
theorem imH_of_herm {X : Matrix (Fin N) (Fin N) ℂ} (h : X.IsHermitian) : imH X = 0 := by
  rw [imH, h.eq, sub_self, smul_zero]

/- English proof (translation)
Rewrite using `[imH_add_I_smul _ _ hY, imH_of_herm hX, zero_add]`.
-/
theorem imH_xy {X Y : Matrix (Fin N) (Fin N) ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) :
    imH (X + I • Y) = Y := by
  rw [imH_add_I_smul _ _ hY, imH_of_herm hX, zero_add]

/- English proof (translation)
Establish `: Z - I • imH Z = (2 : ℂ)⁻¹ • (Z + Zᴴ)`. Use extensionality with `a b`. Simplify using `only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, Matrix.IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose, add_comm]`. Simplify using the standard rewrite rules.
-/
theorem re_herm (Z : Matrix (Fin N) (Fin N) ℂ) : (Z - I • imH Z).IsHermitian := by
  have : Z - I • imH Z = (2 : ℂ)⁻¹ • (Z + Zᴴ) := by
    ext a b
    simp only [imH, Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, smul_eq_mul]
    field_simp
    ring
  rw [this, Matrix.IsHermitian, conjTranspose_smul, conjTranspose_add, conjTranspose_conjTranspose,
    add_comm]
  simp

/- English proof (translation)
Establish `h : A * Z = A * (Z - I • imH Z) + I • (A * imH Z)`. Rewrite using `[← Matrix.mul_smul, ← Matrix.mul_add, sub_add_cancel]`. Use `conv_lhs => rw [h]`. Rewrite using `[trace_add, trace_smul, add_im, trace_im hA (re_herm Z)]`. Simplify using the standard rewrite rules.
-/
theorem trace_mul_im {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (Z : Matrix (Fin N) (Fin N) ℂ) : (A * Z).trace.im = (A * imH Z).trace.re := by
  have h : A * Z = A * (Z - I • imH Z) + I • (A * imH Z) := by
    rw [← Matrix.mul_smul, ← Matrix.mul_add, sub_add_cancel]
  conv_lhs => rw [h]
  rw [trace_add, trace_smul, add_im, trace_im hA (re_herm Z)]
  simp

/- English proof (translation)
Rewrite using `[pr, im_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => trace_mul_im (herm_map h _) _`.
-/
theorem pr_im {T : Matrix (Fin N) (Fin N) E} (h : ccT T = T) (Z : CM Ψ N N) :
    (pr T Z).im = ∑ τ : Ψ, (T.map τ.1 * imH (Z τ)).trace.re := by
  rw [pr, im_sum]
  exact Finset.sum_congr rfl fun τ _ => trace_mul_im (herm_map h _) _

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.
-/
theorem norm_e (w : ℂ) : ‖cexp (2 * π * I * w)‖ = Real.exp (-(2 * π * w.im)) := by
  rw [Complex.norm_exp]; simp

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Simplify using the standard rewrite rules.
-/
theorem norm_e' (w : ℂ) : ‖cexp (-(2 * π * I * w))‖ = Real.exp (2 * π * w.im) := by
  rw [Complex.norm_exp]; simp

/- English proof (translation)
Establish `h1 : ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef` using `Matrix.PosDef.one.smul (by exact_mod_cast hη)`. Simplify using `using h1.add_posSemidef h`.
-/
theorem posDef_of_ge {Y : Matrix (Fin N) (Fin N) ℂ} {η : ℝ} (hη : 0 < η)
    (h : (Y - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) : Y.PosDef := by
  have h1 : ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (by exact_mod_cast hη)
  simpa using h1.add_posSemidef h

def IsCoef {m : ℕ} (X : (Fin m → ℝ) → CM Ψ N N) (f : CM Ψ N N → ℂ) (T : Matrix (Fin N) (Fin N) E)
    (a : ℂ) : Prop :=
  ∀ Y : CM Ψ N N, (∀ τ, (Y τ).PosDef) → a = ∫ x in cube m,
    f (fun τ => X x τ + I • Y τ) * cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y τ)))

section coef
variable {m : ℕ} {X : (Fin m → ℝ) → CM Ψ N N} {f : CM Ψ N N → ℂ} {T : Matrix (Fin N) (Fin N) E}
  {a : ℂ} {η B : ℝ}

/- English proof (translation)
Establish `hi : ∀ τ, imH (X x τ + I • Y τ) = Y τ` using `fun τ => imH_xy (hX x τ) (posDef_of_ge hη (hY τ)).1`. Rewrite using `[norm_mul, norm_e', pr_im hT]`. Simplify using `only [hi]`. Use `gcongr`. Conclude with `hB _ fun τ => by simpa only [hi] using hY τ`.
-/
theorem norm_integrand_le (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) {Y : CM Ψ N N}
    (hY : ∀ τ, (Y τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) (x : Fin m → ℝ) :
    ‖f (fun τ => X x τ + I • Y τ) * cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y τ)))‖ ≤
      B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y τ).trace.re) := by
  have hi : ∀ τ, imH (X x τ + I • Y τ) = Y τ := fun τ =>
    imH_xy (hX x τ) (posDef_of_ge hη (hY τ)).1
  rw [norm_mul, norm_e', pr_im hT]
  simp only [hi]
  gcongr
  exact hB _ fun τ => by simpa only [hi] using hY τ

/- English proof (translation)
Rewrite using `[ha Y fun τ => posDef_of_ge hη (hY τ)]`. Use `norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cube m) (by rw [volume_cube]; exact ENNReal.one_lt_top) (fun x _ => norm_integrand_le hX hT hη hB hY x)` as an intermediate fact. Simplify `this` using `[Measure.real, volume_cube]`.
-/
theorem coef_bound (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) {Y : CM Ψ N N}
    (hY : ∀ τ, (Y τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef) :
    ‖a‖ ≤ B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y τ).trace.re) := by
  rw [ha Y fun τ => posDef_of_ge hη (hY τ)]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := cube m)
    (by rw [volume_cube]; exact ENNReal.one_lt_top)
    (fun x _ => norm_integrand_le hX hT hη hB hY x)
  simpa [Measure.real, volume_cube] using this

/- English proof (translation)
Simplify using `only [Matrix.trace, diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem trace_vecMulVec (A : Matrix (Fin N) (Fin N) ℂ) (u : Fin N → ℂ) :
    (A * vecMulVec u (star u)).trace = star u ⬝ᵥ A *ᵥ u := by
  simp only [Matrix.trace, diag, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `posSemidef_iff_dotProduct_mulVec.2 ⟨herm_map hT _, fun u => ?_⟩` and prove the remaining obligations. Rewrite using `[Complex.le_def]`. Use `⟨?_, (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.quad_im (herm_map hT _) u).symm⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hneg`. Simplify using `only [zero_re, not_le] at hneg`.

Use `set q := (star u ⬝ᵥ T.map τ.1 *ᵥ u).re with hq`. Use `set c := ∑ σ : Ψ, (T.map σ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re with hc`. Establish `key : ∀ t : ℝ, 0 ≤ t → ‖a‖ ≤ B * Real.exp (2 * π * (c + q * t))`. Introduce `t ht`. Use `coef_bound hX hT hη hB ha (Y := fun σ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + if σ = τ then (t : ℂ) • vecMulVec u (star u) else 0) (fun σ => by` as an intermediate fact.

Rewrite using `[add_sub_cancel_left]`. Use `split_ifs`. Conclude with `(posSemidef_vecMulVec_self_star u).smul (by exact_mod_cast ht)`. Conclude with `PosSemidef.zero)`. Use `this using 4` and compare the differences between its conclusion and the goal.

Simplify using `only [Matrix.mul_add, trace_add, add_re, Finset.sum_add_distrib]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single τ]`. Rewrite using `[if_pos rfl, Matrix.mul_smul, trace_smul, trace_vecMulVec, smul_eq_mul, re_ofReal_mul, mul_comm]`. Introduce `σ _ h`.

Simplify using `[h]`. Simplify using the standard rewrite rules. Establish `lim : Tendsto (fun t : ℝ => B * Real.exp (2 * π * (c + q * t))) atTop (𝓝 (B * 0))`. Use `Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)` and prove the remaining obligations. Conclude with `Tendsto.const_mul_atBot (by positivity) (tendsto_atBot_add_const_left _ _ (tendsto_id.const_mul_atTop_of_neg hneg))`.

Use `ge_of_tendsto lim ((eventually_ge_atTop 0).mono key)` as an intermediate fact. Conclude with `h0 (norm_le_zero_iff.1 (by simpa using this))`.
-/
theorem coef_psd (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T) (hη : 0 < η)
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) (h0 : a ≠ 0) (τ : Ψ) :
    (T.map τ.1).PosSemidef := by
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨herm_map hT _, fun u => ?_⟩
  rw [Complex.le_def]
  refine ⟨?_, (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.quad_im (herm_map hT _) u).symm⟩
  by_contra hneg
  simp only [zero_re, not_le] at hneg
  set q := (star u ⬝ᵥ T.map τ.1 *ᵥ u).re with hq
  set c := ∑ σ : Ψ, (T.map σ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re with hc
  have key : ∀ t : ℝ, 0 ≤ t → ‖a‖ ≤ B * Real.exp (2 * π * (c + q * t)) := by
    intro t ht
    have := coef_bound hX hT hη hB ha (Y := fun σ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) +
      if σ = τ then (t : ℂ) • vecMulVec u (star u) else 0) (fun σ => by
        rw [add_sub_cancel_left]
        split_ifs
        · exact (posSemidef_vecMulVec_self_star u).smul (by exact_mod_cast ht)
        · exact PosSemidef.zero)
    convert this using 4
    simp only [Matrix.mul_add, trace_add, add_re, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single τ]
    · rw [if_pos rfl, Matrix.mul_smul, trace_smul, trace_vecMulVec, smul_eq_mul, re_ofReal_mul,
        mul_comm]
    · intro σ _ h; simp [h]
    · simp
  have lim : Tendsto (fun t : ℝ => B * Real.exp (2 * π * (c + q * t))) atTop (𝓝 (B * 0)) := by
    refine Tendsto.const_mul _ (Real.tendsto_exp_atBot.comp ?_)
    exact Tendsto.const_mul_atBot (by positivity)
      (tendsto_atBot_add_const_left _ _ (tendsto_id.const_mul_atTop_of_neg hneg))
  have := ge_of_tendsto lim ((eventually_ge_atTop 0).mono key)
  exact h0 (norm_le_zero_iff.1 (by simpa using this))

/- English proof (translation)
Use `set P : CM Ψ N N := fun τ => vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) with hP`. Use `set Y : ℝ → CM Ψ N N := fun t τ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (t : ℂ) • P τ with hYdef`. Establish `hY : ∀ t, 0 ≤ t → ∀ τ, (Y t τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef`. Introduce `t ht τ`. Simplify using `only [hYdef, add_sub_cancel_left]`.

Conclude with `(posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)`. Establish `hTP : ∀ τ : Ψ, (T.map τ.1 * P τ).trace = 0`. Introduce `τ`. Rewrite using `[hP, trace_vecMulVec]`. Establish `: T.map τ.1 *ᵥ (fun a => τ.1 (v a)) = 0`.

Use extensionality with `i`. Use `congrArg τ.1 (congrFun hTv i)` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct]`. Rewrite using `[this, dotProduct_zero]`. Establish `hpush : ∀ x t, (fun τ => X x τ + I • Y t τ) = pushZ Ψ (fun τ => X x τ + I • Y 0 τ) v t`.

Introduce `x t`. Use function extensionality and compare the values at `τ`. Simplify using `only [hYdef, pushZ, hP, smul_add, smul_smul, ofReal_zero, mul_zero, zero_smul, add_zero, add_assoc]`. Both sides reduce to the same expression. Establish `hpr : ∀ x t, pr T (fun τ => X x τ + I • Y t τ) = pr T (fun τ => X x τ + I • Y 0 τ)`.

Introduce `x t`. Simplify using `[pr, hYdef, Matrix.mul_add, hTP]`. Establish `htr : ∀ t, ∑ τ : Ψ, (T.map τ.1 * Y t τ).trace.re = ∑ τ : Ψ, (T.map τ.1 * Y 0 τ).trace.re`. Introduce `t`. Simplify using `[hYdef, Matrix.mul_add, hTP]`.

Establish `hH : ∀ t, 0 ≤ t → ∀ x, (fun τ => X x τ + I • Y t τ) ∈ Hn Ψ N` using `fun t ht x τ => by`. Use `posDef_of_ge hη (hY t ht τ)` as an intermediate fact. Simplify `this` using `only [imH_xy (hX x τ) this.1]`. Use `haveI : IsFiniteMeasure (volume.restrict (cube m)) := isFiniteMeasure_restrict.2 (by rw [volume_cube]; exact ENNReal.one_ne_top)`. Establish `lim` using `tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (cube m)) (l := atTop) (F := fun (t : ℝ) x => f (fun τ => X x τ + I • Y t τ) * cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y t τ)))) (f := fun _ => 0) (fun _ => B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y …`.

Establish `hc : Continuous fun x => (fun τ => X x τ + I • Y t τ : CM Ψ N N)` using `hXc.add continuous_const`. Use `(Continuous.mul (hf.continuousOn.comp_continuous hc (hH t ht)) ?_).aestronglyMeasurable` and prove the remaining obligations. Use `Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul ?_))` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun τ _ => (continuous_const.matrix_mul ((continuous_apply τ).comp hc)).matrix_trace)`. Use the proof step `((eventually_ge_atTop 0).mono fun t ht => ae_of_all _ fun x => by`.

Rewrite using `[← htr t]`. Conclude with `norm_integrand_le hX hT hη hB (hY t ht) x)`. Use the proof step `(integrable_const _)`. Use the proof step `(ae_of_all _ fun x => by`. Use `(hv _ (hH 0 le_rfl x)).mul_const (cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y 0 τ))))` as an intermediate fact.

Rewrite `this` using `[zero_mul]`. Conclude with `this.congr fun t => by rw [hpr x t, hpush x t])`. Rewrite `lim` using `[integral_zero]`. Use `tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) lim` and prove the remaining obligations. Conclude with `(eventually_ge_atTop 0).mono fun t ht => ha _ fun τ => posDef_of_ge hη (hY t ht τ)`.
-/
theorem coef_sing (hXc : Continuous X) (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T)
    (hη : 0 < η)
    (hf : DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N})
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a) {v : Fin N → E}
    (hv : ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0))
    (hTv : T *ᵥ v = 0) : a = 0 := by
  set P : CM Ψ N N := fun τ => vecMulVec (fun a => τ.1 (v a)) (star fun a => τ.1 (v a)) with hP
  set Y : ℝ → CM Ψ N N := fun t τ => (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) + (t : ℂ) • P τ
    with hYdef
  have hY : ∀ t, 0 ≤ t → ∀ τ, (Y t τ - (η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef := by
    intro t ht τ
    simp only [hYdef, add_sub_cancel_left]
    exact (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast ht)
  have hTP : ∀ τ : Ψ, (T.map τ.1 * P τ).trace = 0 := by
    intro τ
    rw [hP, trace_vecMulVec]
    have : T.map τ.1 *ᵥ (fun a => τ.1 (v a)) = 0 := by
      ext i
      have := congrArg τ.1 (congrFun hTv i)
      simpa [mulVec, dotProduct] using this
    rw [this, dotProduct_zero]
  have hpush : ∀ x t, (fun τ => X x τ + I • Y t τ) = pushZ Ψ (fun τ => X x τ + I • Y 0 τ) v t := by
    intro x t
    funext τ
    simp only [hYdef, pushZ, hP, smul_add, smul_smul, ofReal_zero, mul_zero, zero_smul, add_zero,
      add_assoc]
    rfl
  have hpr : ∀ x t, pr T (fun τ => X x τ + I • Y t τ) = pr T (fun τ => X x τ + I • Y 0 τ) := by
    intro x t
    simp [pr, hYdef, Matrix.mul_add, hTP]
  have htr : ∀ t, ∑ τ : Ψ, (T.map τ.1 * Y t τ).trace.re = ∑ τ : Ψ, (T.map τ.1 * Y 0 τ).trace.re := by
    intro t
    simp [hYdef, Matrix.mul_add, hTP]
  have hH : ∀ t, 0 ≤ t → ∀ x, (fun τ => X x τ + I • Y t τ) ∈ Hn Ψ N := fun t ht x τ => by
    have := posDef_of_ge hη (hY t ht τ)
    simpa only [imH_xy (hX x τ) this.1] using this
  haveI : IsFiniteMeasure (volume.restrict (cube m)) :=
    isFiniteMeasure_restrict.2 (by rw [volume_cube]; exact ENNReal.one_ne_top)
  have lim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (cube m))
    (l := atTop) (F := fun (t : ℝ) x => f (fun τ => X x τ + I • Y t τ) *
      cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y t τ)))) (f := fun _ => 0)
    (fun _ => B * Real.exp (2 * π * ∑ τ : Ψ, (T.map τ.1 * Y 0 τ).trace.re))
    ((eventually_ge_atTop 0).mono fun t ht => by
      have hc : Continuous fun x => (fun τ => X x τ + I • Y t τ : CM Ψ N N) :=
        hXc.add continuous_const
      refine (Continuous.mul (hf.continuousOn.comp_continuous hc (hH t ht)) ?_).aestronglyMeasurable
      refine Complex.continuous_exp.comp (Continuous.neg (continuous_const.mul ?_))
      exact continuous_finset_sum _ fun τ _ =>
        (continuous_const.matrix_mul ((continuous_apply τ).comp hc)).matrix_trace)
    ((eventually_ge_atTop 0).mono fun t ht => ae_of_all _ fun x => by
      rw [← htr t]; exact norm_integrand_le hX hT hη hB (hY t ht) x)
    (integrable_const _)
    (ae_of_all _ fun x => by
      have := (hv _ (hH 0 le_rfl x)).mul_const
        (cexp (-(2 * π * I * pr T (fun τ => X x τ + I • Y 0 τ))))
      rw [zero_mul] at this
      exact this.congr fun t => by rw [hpr x t, hpush x t])
  rw [integral_zero] at lim
  refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) lim
  exact (eventually_ge_atTop 0).mono fun t ht => ha _ fun τ => posDef_of_ge hη (hY t ht τ)

/- English proof (translation)
Use `(coef_psd hX hT hη hB ha h0 τ).posDef_iff_det_ne_zero.2 fun h => h0 ?_` and prove the remaining obligations. Establish `: T.det = 0`. Establish `e` using `τ.1.map_det T`. Rewrite `e` using `[RingHom.mapMatrix_apply, h]`. Conclude with `(map_eq_zero _).1 e`.

Take `⟨v, hv0, hTv⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 this`. Conclude with `coef_sing hXc hX hT hη hf hB ha (hv v hv0) hTv`.
-/
theorem coef_posDef (hXc : Continuous X) (hX : ∀ x τ, (X x τ).IsHermitian) (hT : ccT T = T)
    (hη : 0 < η)
    (hf : DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N})
    (hB : ∀ Z ∈ HnGe Ψ N η, ‖f Z‖ ≤ B) (ha : IsCoef X f T a)
    (hv : ∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N,
      Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0))
    (h0 : a ≠ 0) (τ : Ψ) : (T.map τ.1).PosDef := by
  refine (coef_psd hX hT hη hB ha h0 τ).posDef_iff_det_ne_zero.2 fun h => h0 ?_
  have : T.det = 0 := by
    have e := τ.1.map_det T
    rw [RingHom.mapMatrix_apply, h] at e
    exact (map_eq_zero _).1 e
  obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 this
  exact coef_sing hXc hX hT hη hf hB ha (hv v hv0) hTv

end coef

/- English proof (translation)
Take `⟨m, β, T, c, hc, h1, hd, hZ⟩` from `GlobalTheory.T.exists_integral_basis_hermitian_matrices_dual E Ψ hΨ N R hR`. Use `choose hβ hT hD y hy hyc hβy using h1`. Use `set Φ : (Fin m → ℂ) → CM Ψ N N := fun z τ => ∑ j, z j • (β j).map τ.1 with hΦ`. Use `set co : CM Ψ N N → Fin m → ℂ := fun Z j => pr (T j) Z with hco`. Establish `hΦco : ∀ Z, Φ (co Z) = Z` using `fun Z => (hZ Z).symm`.

Establish `hcoΦ : ∀ z, co (Φ z) = z`. Introduce `z`. Use function extensionality and compare the values at `i`. Simplify using `only [hco, hΦ, pr, Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`.

Establish `: ∀ j, ∑ τ : Ψ, z j * ((T i).map τ.1 * (β j).map τ.1).trace = z j * if i = j then 1 else 0`. Introduce `j`. Rewrite using `[← hd i j, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Matrix.map_mul, AddMonoidHom.map_trace]`.

Simplify using `only [this]`. Simplify using the standard rewrite rules. Use `set TT : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E := fun ν => ∑ i, (ν i : E) • T i with hTT`. Establish `hpr : ∀ ν Z, pr (TT ν) Z = ∑ i, (ν i : ℂ) * co Z i`. Introduce `ν Z`.

Establish `: ∀ τ : Ψ, (TT ν).map τ.1 = ∑ i, (ν i : ℂ) • (T i).map τ.1`. Introduce `τ`. Use extensionality with `a b`. Simplify using `[hTT, Matrix.sum_apply]`. Simplify using `only [pr, this, hco, Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul, Finset.mul_sum]`.

Conclude with `Finset.sum_comm`. Establish `hherm : ∀ (x : Fin m → ℝ) τ, (Φ (fun i => (x i : ℂ)) τ).IsHermitian`. Introduce `x τ`. Simplify using `only [hΦ, Matrix.IsHermitian, conjTranspose_sum, conjTranspose_smul, (herm_map (hβ _) _).eq, star_def, conj_ofReal]`. Establish `hadd : ∀ z w, Φ (z + w) = fun τ => Φ z τ + Φ w τ`.

Introduce `z w`. Use function extensionality and compare the values at `τ`. Simplify using `[hΦ, add_smul, Finset.sum_add_distrib]`. Establish `hxy : ∀ x y : Fin m → ℝ, Φ (fun i => (x i : ℂ) + I * y i) = fun τ => Φ (fun i => (x i : ℂ)) τ + I • Φ (fun i => (y i : ℂ)) τ`. Introduce `x y`.

Use function extensionality and compare the values at `τ`. Simplify using `only [hΦ, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]`. Establish `him : ∀ z τ, imH (Φ z τ) = Φ (fun i => ((z i).im : ℂ)) τ`. Introduce `z τ`. Establish `: z = fun i => ((z i).re : ℂ) + I * (z i).im`.

Use function extensionality and compare the values at `i`. Rewrite using `[mul_comm, re_add_im]`. Use `conv_lhs => rw [this, hxy]`. Conclude with `imH_xy (hherm _ τ) (hherm _ τ)`. Establish `hΦd : Differentiable ℂ (fun (z : Fin m → ℂ) (τ : Ψ) (a b : Fin N) => Φ z τ a b)`.

Use `differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_` and prove the remaining obligations. Simplify using `only [hΦ, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]`. Use `fun_prop`. Establish `hXc : Continuous fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ))` using `hΦd.continuous.comp (continuous_pi fun i => continuous_ofReal.comp (continuous_apply i))`. Establish `hint : ∀ k : ℤ, IsIntegral ℤ (k : E)` using `fun k => by`.

Simplify using `using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)`. Establish `hccT : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, ccT (S i) = S i) → ccT (∑ i, (ν i : E) • S i) = ∑ i, (ν i : E) • S i`. Introduce `S ν hS`. Use extensionality with `a b`. Establish `: ∀ i, cc (S i b a) = S i a b` using `fun i => congrFun (congrFun (hS i) a) b`.

Simplify using `only [cc] at this`. Simplify using `[ccT, cc, Matrix.sum_apply, this]`. Establish `hIntM : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, IntM (S i)) → IntM (∑ i, (ν i : E) • S i)`. Introduce `S ν hS a b`. Rewrite using `[Matrix.sum_apply]`.

Conclude with `IsIntegral.sum _ fun i _ => (hint _).mul (hS i a b)`. Use `⟨m, c, TT, fun x => Φ (fun i => (x i : ℂ)), hc, ?_, fun ν => ⟨hccT T ν hT, ?_⟩, hXc, hherm, fun f hf hper => ?_⟩` and prove the remaining obligations. Introduce `ν μ h`. Use function extensionality and compare the values at `j`. Establish `h1` using `hpr ν (Φ (Pi.single j 1))`.

Rewrite `h1` using `[h, hpr, hcoΦ]`. Simplify using `only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`. Conclude with `h1.symm` after adjusting the coercions. Use `hIntM (fun i => (c : E) • T i) ν hD` as an intermediate fact. Simplify `this` using `only [Den, hTT, Finset.smul_sum, smul_comm (c : E)]`.

Use `set Ω : Set (Fin m → ℝ) := {y | ∀ τ, (Φ (fun i => (y i : ℂ)) τ).PosDef} with hΩ`. Establish `hmem : ∀ z : Fin m → ℂ, (fun i => (z i).im) ∈ Ω ↔ Φ z ∈ Hn Ψ N`. Introduce `z`. Simplify using `only [hΩ, Hn, Set.mem_setOf_eq, him]`. Establish `hopen : IsOpen Ω`.

Use `isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_` and prove the remaining obligations. Conclude with `Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually (fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ)) τ) (fun a b => (((continuous_apply τ).comp hXc).matrix_elem a b)) (fun x => hherm x τ) x0 (hx0 τ)`. Establish `hconv : Convex ℝ Ω`. Introduce `x hx y hy s t hs ht hst τ`. Establish `e : Φ (fun i => (((s • x + t • y) i : ℝ) : ℂ)) τ = (s : ℂ) • Φ (fun i => (x i : ℂ)) τ + (t : ℂ) • Φ (fun i => (y i : ℂ)) τ`.

Simplify using `only [hΦ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_add, ofReal_mul, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]`. Rewrite using `[e]`. Break down `hs.eq_or_lt with h0 | h0` into its components or cases. Establish `: t = 1` using `by linarith`. Substitute `this h0` using the available equality.

Simplify using `using hy τ`. Conclude with `((hx τ).smul (by exact_mod_cast h0)).add_posSemidef ((hy τ).posSemidef.smul (by exact_mod_cast ht))`. Take `⟨a, ha1, ha2⟩` from `GlobalTheory.T.exists_fourier_expansion_holomorphic_tube (Fin m) Ω (fun z => f (Φ z)) hopen hconv (hf.comp hΦd.differentiableOn fun z hz => (hmem z).1 hz) (by`. Introduce `z hz k`. Use `hper _ (hIntM y k hy) (hccT y k hyc) _ ((hmem z).1 hz)` as an intermediate fact.

Rewrite using `[← this]`. Express the relevant statement in the definitionally equal form `f (Φ _) = _`. Rewrite using `[hadd]`. Use `congr 1`. Use function extensionality and compare the values at `τ`.

Use `congr 1`. Use extensionality with `a b`. Simplify using `only [hΦ, hβy, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_sum, map_natCast, map_intCast, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring)`. Use `⟨a, fun ν Y hY => ?_, fun Z hZ' => ?_⟩` and prove the remaining obligations.

Establish `hre : (fun i => (((co Y i).re : ℝ) : ℂ)) = co Y`. Use function extensionality and compare the values at `i`. Use `Complex.ext (by simp) ?_` and prove the remaining obligations. Simplify using `[hco, pr_im (hT i), imH_of_herm (hY _).1]`. Establish `hYe : Φ (fun i => (((co Y i).re : ℝ) : ℂ)) = Y` using `by rw [hre, hΦco]`.

Rewrite using `[ha2 (fun i => (co Y i).re) (fun τ => by rw [hYe]; exact hY τ) ν]`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Establish `e` using `hxy x (fun i => (co Y i).re)`. Rewrite `e` using `[hYe]`. Simplify using `only []`.

Rewrite using `[← e, hpr, hcoΦ]`. Use `ha1 (co Z) ((hmem _).2 (by rwa [hΦco]))` as an intermediate fact. Simplify `this` using `only [hΦco, hpr]`.
-/
theorem exists_fourier (hΨ : IsType Ψ) (N R : ℕ) (hR : 0 < R) :
    ∃ (m c : ℕ) (T : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E) (X : (Fin m → ℝ) → CM Ψ N N),
      0 < c ∧ Function.Injective T ∧ (∀ ν, ccT (T ν) = T ν ∧ Den c (T ν)) ∧ Continuous X ∧
      (∀ x τ, (X x τ).IsHermitian) ∧ ∀ f : CM Ψ N N → ℂ,
        DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} →
        (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N,
          f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) →
        ∃ a : (Fin m → ℤ) → ℂ, (∀ ν, IsCoef X f (T ν) (a ν)) ∧
          ∀ Z ∈ Hn Ψ N, HasSum (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) (f Z) := by
  obtain ⟨m, β, T, c, hc, h1, hd, hZ⟩ := GlobalTheory.T.exists_integral_basis_hermitian_matrices_dual E Ψ hΨ N R hR
  choose hβ hT hD y hy hyc hβy using h1
  set Φ : (Fin m → ℂ) → CM Ψ N N := fun z τ => ∑ j, z j • (β j).map τ.1 with hΦ
  set co : CM Ψ N N → Fin m → ℂ := fun Z j => pr (T j) Z with hco
  have hΦco : ∀ Z, Φ (co Z) = Z := fun Z => (hZ Z).symm
  have hcoΦ : ∀ z, co (Φ z) = z := by
    intro z
    funext i
    simp only [hco, hΦ, pr, Matrix.mul_sum, Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul]
    rw [Finset.sum_comm]
    have : ∀ j, ∑ τ : Ψ, z j * ((T i).map τ.1 * (β j).map τ.1).trace =
        z j * if i = j then 1 else 0 := by
      intro j
      rw [← hd i j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Matrix.map_mul, AddMonoidHom.map_trace]
    simp only [this]
    simp
  set TT : (Fin m → ℤ) → Matrix (Fin N) (Fin N) E := fun ν => ∑ i, (ν i : E) • T i with hTT
  have hpr : ∀ ν Z, pr (TT ν) Z = ∑ i, (ν i : ℂ) * co Z i := by
    intro ν Z
    have : ∀ τ : Ψ, (TT ν).map τ.1 = ∑ i, (ν i : ℂ) • (T i).map τ.1 := by
      intro τ; ext a b; simp [hTT, Matrix.sum_apply]
    simp only [pr, this, hco, Matrix.sum_mul, Matrix.smul_mul, trace_sum, trace_smul, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_comm
  have hherm : ∀ (x : Fin m → ℝ) τ, (Φ (fun i => (x i : ℂ)) τ).IsHermitian := by
    intro x τ
    simp only [hΦ, Matrix.IsHermitian, conjTranspose_sum, conjTranspose_smul,
      (herm_map (hβ _) _).eq, star_def, conj_ofReal]
  have hadd : ∀ z w, Φ (z + w) = fun τ => Φ z τ + Φ w τ := by
    intro z w; funext τ; simp [hΦ, add_smul, Finset.sum_add_distrib]
  have hxy : ∀ x y : Fin m → ℝ, Φ (fun i => (x i : ℂ) + I * y i) =
      fun τ => Φ (fun i => (x i : ℂ)) τ + I • Φ (fun i => (y i : ℂ)) τ := by
    intro x y; funext τ
    simp only [hΦ, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
  have him : ∀ z τ, imH (Φ z τ) = Φ (fun i => ((z i).im : ℂ)) τ := by
    intro z τ
    have : z = fun i => ((z i).re : ℂ) + I * (z i).im := by
      funext i; rw [mul_comm, re_add_im]
    conv_lhs => rw [this, hxy]
    exact imH_xy (hherm _ τ) (hherm _ τ)
  have hΦd : Differentiable ℂ (fun (z : Fin m → ℂ) (τ : Ψ) (a b : Fin N) => Φ z τ a b) := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [hΦ, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have hXc : Continuous fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ)) :=
    hΦd.continuous.comp (continuous_pi fun i => continuous_ofReal.comp (continuous_apply i))
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : E) := fun k => by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := k)
  have hccT : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, ccT (S i) = S i) →
      ccT (∑ i, (ν i : E) • S i) = ∑ i, (ν i : E) • S i := by
    intro S ν hS
    ext a b
    have : ∀ i, cc (S i b a) = S i a b := fun i => congrFun (congrFun (hS i) a) b
    simp only [cc] at this
    simp [ccT, cc, Matrix.sum_apply, this]
  have hIntM : ∀ (S : Fin m → Matrix (Fin N) (Fin N) E) (ν : Fin m → ℤ), (∀ i, IntM (S i)) →
      IntM (∑ i, (ν i : E) • S i) := by
    intro S ν hS a b
    rw [Matrix.sum_apply]
    exact IsIntegral.sum _ fun i _ => (hint _).mul (hS i a b)
  refine ⟨m, c, TT, fun x => Φ (fun i => (x i : ℂ)), hc, ?_, fun ν => ⟨hccT T ν hT, ?_⟩, hXc,
    hherm, fun f hf hper => ?_⟩
  · intro ν μ h
    funext j
    have h1 := hpr ν (Φ (Pi.single j 1))
    rw [h, hpr, hcoΦ] at h1
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h1
    exact_mod_cast h1.symm
  · have := hIntM (fun i => (c : E) • T i) ν hD
    simpa only [Den, hTT, Finset.smul_sum, smul_comm (c : E)] using this
  set Ω : Set (Fin m → ℝ) := {y | ∀ τ, (Φ (fun i => (y i : ℂ)) τ).PosDef} with hΩ
  have hmem : ∀ z : Fin m → ℂ, (fun i => (z i).im) ∈ Ω ↔ Φ z ∈ Hn Ψ N := by
    intro z; simp only [hΩ, Hn, Set.mem_setOf_eq, him]
  have hopen : IsOpen Ω := by
    refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
    exact Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
      (fun x : Fin m → ℝ => Φ (fun i => (x i : ℂ)) τ)
      (fun a b => (((continuous_apply τ).comp hXc).matrix_elem a b)) (fun x => hherm x τ) x0 (hx0 τ)
  have hconv : Convex ℝ Ω := by
    intro x hx y hy s t hs ht hst τ
    have e : Φ (fun i => (((s • x + t • y) i : ℝ) : ℂ)) τ =
        (s : ℂ) • Φ (fun i => (x i : ℂ)) τ + (t : ℂ) • Φ (fun i => (y i : ℂ)) τ := by
      simp only [hΦ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ofReal_add, ofReal_mul, add_smul,
        Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    rw [e]
    rcases hs.eq_or_lt with h0 | h0
    · have : t = 1 := by linarith
      subst this h0
      simpa using hy τ
    · exact ((hx τ).smul (by exact_mod_cast h0)).add_posSemidef
        ((hy τ).posSemidef.smul (by exact_mod_cast ht))
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.T.exists_fourier_expansion_holomorphic_tube (Fin m) Ω (fun z => f (Φ z)) hopen hconv
    (hf.comp hΦd.differentiableOn fun z hz => (hmem z).1 hz) (by
      intro z hz k
      have := hper _ (hIntM y k hy) (hccT y k hyc) _ ((hmem z).1 hz)
      rw [← this]
      change f (Φ _) = _
      rw [hadd]
      congr 1
      funext τ
      congr 1
      ext a b
      simp only [hΦ, hβy, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        map_mul, map_sum, map_natCast, map_intCast, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
  refine ⟨a, fun ν Y hY => ?_, fun Z hZ' => ?_⟩
  · have hre : (fun i => (((co Y i).re : ℝ) : ℂ)) = co Y := by
      funext i
      refine Complex.ext (by simp) ?_
      simp [hco, pr_im (hT i), imH_of_herm (hY _).1]
    have hYe : Φ (fun i => (((co Y i).re : ℝ) : ℂ)) = Y := by rw [hre, hΦco]
    rw [ha2 (fun i => (co Y i).re) (fun τ => by rw [hYe]; exact hY τ) ν]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have e := hxy x (fun i => (co Y i).re)
    rw [hYe] at e
    simp only []
    rw [← e, hpr, hcoΦ]
  · have := ha1 (co Z) ((hmem _).2 (by rwa [hΦco]))
    simpa only [hΦco, hpr] using this

/- English proof (translation)
Use `⟨Real.exp (-(p * Real.log (b / (p + 1)))), fun u hu => ?_⟩` and prove the remaining obligations. Establish `hε : 0 < b / (p + 1)` using `by positivity`. Rewrite using `[Real.rpow_def_of_pos hu, ← Real.exp_add, Real.exp_le_exp]`. Establish `h1` using `Real.log_le_sub_one_of_pos (mul_pos hε hu)`. Rewrite `h1` using `[Real.log_mul hε.ne' hu.ne']`.

Establish `h2 : p * (b / (p + 1) * u) ≤ b * u`. Rewrite using `[← mul_assoc]`. Use `gcongr`. Rewrite using `[← mul_div_assoc, div_le_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h1 hp]`.
-/
theorem rpow_mul_exp_le {b p : ℝ} (hb : 0 < b) (hp : 0 ≤ p) :
    ∃ C : ℝ, ∀ u : ℝ, 0 < u → u ^ p * Real.exp (-(b * u)) ≤ C := by
  refine ⟨Real.exp (-(p * Real.log (b / (p + 1)))), fun u hu => ?_⟩
  have hε : 0 < b / (p + 1) := by positivity
  rw [Real.rpow_def_of_pos hu, ← Real.exp_add, Real.exp_le_exp]
  have h1 := Real.log_le_sub_one_of_pos (mul_pos hε hu)
  rw [Real.log_mul hε.ne' hu.ne'] at h1
  have h2 : p * (b / (p + 1) * u) ≤ b * u := by
    rw [← mul_assoc]
    gcongr
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hp]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Rewrite using `[Finset.card_pos]`. Distinguish the cases in `h : τ ∈ Ψ`. Conclude with `⟨τ, h⟩`. Conclude with `⟨_, not_not.1 (mt (hΨ τ).2 h)⟩`.
-/
theorem card_pos (hΨ : IsType Ψ) : 0 < Ψ.card := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  rw [Finset.card_pos]
  by_cases h : τ ∈ Ψ
  · exact ⟨τ, h⟩
  · exact ⟨_, not_not.1 (mt (hΨ τ).2 h)⟩

end

end GlobalTheory.SW.Decay

open GlobalTheory.SW.Decay in

/- English proof (translation)
Introduce `E _ _ _ Ψ hΨ N R δ s hN hR hδ hs`. Take `⟨m, c, T, X, hc, hinj, hT, hXc, hX, hF⟩` from `exists_fourier hΨ N R hR`. Take `⟨k, hk, hk'⟩` from `GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace E Ψ hΨ N c hN hc`. Establish `hsum` using `GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian E Ψ hΨ N c (π * δ / 2) hc (by positivity)`. Use `set S : Set (Fin m → ℤ) := {ν | ∀ τ : Ψ, ((T ν).map τ.1).PosSemidef} with hS`.

Establish `hsum' : Summable fun ν : S => Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re))`. Establish `hi : Function.Injective fun ν : S => (⟨T ν.1, (hT _).1, (hT _).2, ν.2⟩ : {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧ ∀ τ : Ψ, (T.map τ.1).PosSemidef})` using `fun ν μ h => Subtype.ext (hinj (Subtype.mk.inj h))`. Use `hsum.comp_injective hi` as an intermediate fact. Simplify `this` using `only [Function.comp_def]`. Use `set σ := ∑' ν : S, Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re)) with hσ`.

Establish `hσ0 : 0 ≤ σ` using `tsum_nonneg fun _ => (Real.exp_pos _).le`. Establish `hd : (0 : ℝ) < ((Ψ.card * N : ℕ) : ℝ)` using `by exact_mod_cast Nat.mul_pos (card_pos hΨ) hN`. Use `set d : ℝ := ((Ψ.card * N : ℕ) : ℝ)`. Take `⟨C, hC⟩` from `rpow_mul_exp_le (b := π * k) (p := d * s) (by positivity) (by positivity)`. Use `⟨C * σ, fun f B hf hper hB hv Z hZ => ?_⟩` and prove the remaining obligations.

Take `⟨a, ha, hfa⟩` from `hF f hf hper`. Establish `hη : 0 < δ / 4` using `by positivity`. Establish `hZ' : Z ∈ Hn Ψ N` using `fun τ => posDef_of_ge hδ (hZ τ)`. Establish `hB0 : 0 ≤ B`. Use `(norm_nonneg _).trans (hB (fun _ => 0 + I • (((δ / 4 : ℝ) : ℂ) • 1)) fun τ => ?_)` and prove the remaining obligations.

Rewrite using `[imH_xy isHermitian_zero (posDef_of_ge hη (by simpa using PosSemidef.zero)).1]`. Simplify using `using PosSemidef.zero`. Establish `hD : 0 < detIm Z` using `Finset.prod_pos fun τ _ => (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.det_re_pos_im (hZ' τ)).1`. Use `set u := detIm Z ^ (1 / d) with hu`. Establish `hu0 : 0 < u` using `Real.rpow_pos_of_pos hD _`.

Establish `hus : detIm Z ^ s = u ^ (d * s)`. Rewrite using `[hu, ← Real.rpow_mul hD.le]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `h1 : HasSum (fun ν : S => a ν.1 * cexp (2 * π * I * pr (T ν.1) Z)) (f Z)`.

Establish `hsupp : Function.support (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) ⊆ S` using `fun ν hν τ => coef_psd hX (hT ν).1 hη hB (ha ν) (left_ne_zero_of_mul hν) τ`. Use `(hasSum_subtype_iff_of_support_subset hsupp).2 (hfa Z hZ')` as an intermediate fact. Simplify `this` using `only [Function.comp_def]`. Establish `h2 : ‖f Z‖ ≤ B * Real.exp (-(π * k * u)) * σ`. Use `h1.norm_le_of_bounded (hsum'.hasSum.mul_left _) fun ν => ?_` and prove the remaining obligations.

Distinguish the cases in `h0 : a ν.1 = 0`. Rewrite using `[h0, zero_mul, norm_zero]`. Check the signs of the components of the expression. Establish `hpd` using `coef_posDef hXc hX (hT ν.1).1 hη hf hB (ha ν.1) hv h0`. Establish `b1` using `coef_bound hX (hT ν.1).1 hη hB (ha ν.1) (Y := fun _ => ((δ / 4 : ℝ) : ℂ) • 1) (fun _ => by simpa using PosSemidef.zero)`.

Establish `b2` using `hk' _ (hT ν.1).1 (hT ν.1).2 hpd Z hZ'`. Establish `tr : ∀ η : ℝ, ∑ τ : Ψ, ((T ν.1).map τ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re = η * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re`. Introduce `η`. Simplify using `only [Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, re_ofReal_mul, Finset.mul_sum]`. Establish `b3 : δ * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re ≤ ∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re`.

Rewrite using `[← tr]`. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Use `GlobalTheory.re_trace_mul_nonneg_of_posSemidef (ν.2 τ) (hZ τ)` as an intermediate fact. Rewrite `this` using `[Matrix.mul_sub, trace_sub, map_sub, sub_nonneg]`. Conclude with `this`.

Rewrite `b1` using `[tr]`. Rewrite using `[norm_mul, norm_e, pr_im (hT ν.1).1]`. Use `(mul_le_mul_of_nonneg_right b1 (Real.exp_pos _).le).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc B, mul_assoc B, ← Real.exp_add, ← Real.exp_add]`. Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0` and prove the remaining obligations.

Use `replace b2 : k * u ≤ _ := b2`. Generalize the expression as in `∑ τ : Ψ, ((T ν.1).map τ.1).trace.re = p at b3 ⊢`. Generalize the expression as in `∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re = q at b2 b3 ⊢`. Use `add_le_add (mul_le_mul_of_nonneg_left b2 Real.pi_pos.le) (mul_le_mul_of_nonneg_left b3 Real.pi_pos.le)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hus]`. Use `gcongr`. Use `_ = u ^ (d * s) * Real.exp (-(π * k * u)) * σ * B := by ring`. Use `_ ≤ C * σ * B := by gcongr; exact hC u hu0`.
-/
theorem GlobalTheory.SW.decay_of_vanishing_at_cusps : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N R : ℕ) (δ s : ℝ), 0 < N → 0 < R → 0 < δ → 0 ≤ s → ∃ C : ℝ, ∀ (f : CM Ψ N N → ℂ) (B : ℝ), DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} → (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N, f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) → (∀ Z ∈ HnGe Ψ N (δ / 4), ‖f Z‖ ≤ B) → (∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0)) → ∀ Z ∈ HnGe Ψ N δ, ‖f Z‖ * detIm Z ^ s ≤ C * B := by
  intro E _ _ _ Ψ hΨ N R δ s hN hR hδ hs
  obtain ⟨m, c, T, X, hc, hinj, hT, hXc, hX, hF⟩ := exists_fourier hΨ N R hR
  obtain ⟨k, hk, hk'⟩ := GlobalTheory.T.trace_pairing_ge_detIm_pow_hermitianHalfSpace E Ψ hΨ N c hN hc
  have hsum := GlobalTheory.T.summable_exp_neg_trace_totallyPositive_hermitian E Ψ hΨ N c (π * δ / 2) hc (by positivity)
  set S : Set (Fin m → ℤ) := {ν | ∀ τ : Ψ, ((T ν).map τ.1).PosSemidef} with hS
  have hsum' : Summable fun ν : S =>
      Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re)) := by
    have hi : Function.Injective fun ν : S => (⟨T ν.1, (hT _).1, (hT _).2, ν.2⟩ :
        {T : Matrix (Fin N) (Fin N) E // ccT T = T ∧ Den c T ∧
          ∀ τ : Ψ, (T.map τ.1).PosSemidef}) :=
      fun ν μ h => Subtype.ext (hinj (Subtype.mk.inj h))
    have := hsum.comp_injective hi
    simpa only [Function.comp_def] using this
  set σ := ∑' ν : S, Real.exp (-(π * δ / 2 * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re)) with hσ
  have hσ0 : 0 ≤ σ := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hd : (0 : ℝ) < ((Ψ.card * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos (card_pos hΨ) hN
  set d : ℝ := ((Ψ.card * N : ℕ) : ℝ)
  obtain ⟨C, hC⟩ := rpow_mul_exp_le (b := π * k) (p := d * s) (by positivity) (by positivity)
  refine ⟨C * σ, fun f B hf hper hB hv Z hZ => ?_⟩
  obtain ⟨a, ha, hfa⟩ := hF f hf hper
  have hη : 0 < δ / 4 := by positivity
  have hZ' : Z ∈ Hn Ψ N := fun τ => posDef_of_ge hδ (hZ τ)
  have hB0 : 0 ≤ B := by
    refine (norm_nonneg _).trans (hB (fun _ => 0 + I • (((δ / 4 : ℝ) : ℂ) • 1)) fun τ => ?_)
    rw [imH_xy isHermitian_zero (posDef_of_ge hη (by simpa using PosSemidef.zero)).1]
    simpa using PosSemidef.zero
  have hD : 0 < detIm Z :=
    Finset.prod_pos fun τ _ => (ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA.det_re_pos_im (hZ' τ)).1
  set u := detIm Z ^ (1 / d) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hD _
  have hus : detIm Z ^ s = u ^ (d * s) := by
    rw [hu, ← Real.rpow_mul hD.le]; congr 1; field_simp
  have h1 : HasSum (fun ν : S => a ν.1 * cexp (2 * π * I * pr (T ν.1) Z)) (f Z) := by
    have hsupp : Function.support (fun ν => a ν * cexp (2 * π * I * pr (T ν) Z)) ⊆ S :=
      fun ν hν τ => coef_psd hX (hT ν).1 hη hB (ha ν) (left_ne_zero_of_mul hν) τ
    have := (hasSum_subtype_iff_of_support_subset hsupp).2 (hfa Z hZ')
    simpa only [Function.comp_def] using this
  have h2 : ‖f Z‖ ≤ B * Real.exp (-(π * k * u)) * σ := by
    refine h1.norm_le_of_bounded (hsum'.hasSum.mul_left _) fun ν => ?_
    by_cases h0 : a ν.1 = 0
    · rw [h0, zero_mul, norm_zero]; positivity
    have hpd := coef_posDef hXc hX (hT ν.1).1 hη hf hB (ha ν.1) hv h0
    have b1 := coef_bound hX (hT ν.1).1 hη hB (ha ν.1)
      (Y := fun _ => ((δ / 4 : ℝ) : ℂ) • 1) (fun _ => by simpa using PosSemidef.zero)
    have b2 := hk' _ (hT ν.1).1 (hT ν.1).2 hpd Z hZ'
    have tr : ∀ η : ℝ, ∑ τ : Ψ, ((T ν.1).map τ.1 * ((η : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ))).trace.re
        = η * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re := by
      intro η
      simp only [Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul, re_ofReal_mul,
        Finset.mul_sum]
    have b3 : δ * ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re ≤
        ∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re := by
      rw [← tr]
      refine Finset.sum_le_sum fun τ _ => ?_
      have := GlobalTheory.re_trace_mul_nonneg_of_posSemidef (ν.2 τ) (hZ τ)
      rw [Matrix.mul_sub, trace_sub, map_sub, sub_nonneg] at this
      exact this
    rw [tr] at b1
    rw [norm_mul, norm_e, pr_im (hT ν.1).1]
    refine (mul_le_mul_of_nonneg_right b1 (Real.exp_pos _).le).trans ?_
    rw [mul_assoc B, mul_assoc B, ← Real.exp_add, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hB0
    replace b2 : k * u ≤ _ := b2
    generalize ∑ τ : Ψ, ((T ν.1).map τ.1).trace.re = p at b3 ⊢
    generalize ∑ τ : Ψ, ((T ν.1).map τ.1 * imH (Z τ)).trace.re = q at b2 b3 ⊢
    have := add_le_add (mul_le_mul_of_nonneg_left b2 Real.pi_pos.le)
      (mul_le_mul_of_nonneg_left b3 Real.pi_pos.le)
    linarith
  calc ‖f Z‖ * detIm Z ^ s ≤ B * Real.exp (-(π * k * u)) * σ * u ^ (d * s) := by
        rw [hus]; gcongr
    _ = u ^ (d * s) * Real.exp (-(π * k * u)) * σ * B := by ring
    _ ≤ C * σ * B := by gcongr; exact hC u hu0
