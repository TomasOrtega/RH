import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.PartialCoeffDiagonalBlockGLEqVecCoeff

open NumberField NumberField.mixedEmbedding MeasureTheory Topology Set Filter IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

open AutomorphicForm

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

structure IsUSmooth (ϕ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  arch : IsArchSmooth ϕ
  fin : ∃ V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n),
    ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g
  left : IsLeftInvariant ϕ

/- English proof (translation)
Take `⟨U, hU⟩` from `hϕ.fin`. Use `continuous_iff_continuousAt.2 fun g₀ => ?_` and prove the remaining obligations. Set `e : AdelicGLn.AdelicGL K n → AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n` to `fun g => AdelicGLn.prodEquiv K n (g₀⁻¹ * g)`. Establish `he : Continuous e` using `(AdelicGLn.prodEquiv K n).continuous.comp (continuous_const.mul continuous_id)`. Set `F : AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n → ℂ` to `fun p => ϕ (g₀ * infEmb K n (archEquiv K n p.1) * finEmb K n p.2)`.

Establish `hφF : ϕ = F ∘ e`. Use function extensionality and compare the values at `g`. Simplify using `only [F, e, Function.comp_apply, mul_assoc]`. Rewrite using `[infEmb_mul_finEmb, mul_inv_cancel_left]`. Establish `hslice : Continuous (archSlice ϕ g₀)`.

Use `letI := (isExpLieAlgebra K n).chartedSpace`. Conclude with `(hϕ.arch g₀).continuous`. Establish `hF : ContinuousAt F (e g₀)`. Establish `hFeq : F =ᶠ[𝓝 (e g₀)] fun p => archSlice ϕ g₀ (archEquiv K n p.1)`. Establish `he1 : e g₀ = 1` using `by simp only [e, inv_mul_cancel, map_one]`.

Establish `hmem : (univ ×ˢ (U : Set (AdelicGLn.FiniteAdelicGL K n))) ∈ 𝓝 (e g₀)`. Rewrite using `[he1]`. Conclude with `prod_mem_nhds univ_mem (U.isOpen.mem_nhds (one_mem U))`. Use `filter_upwards [hmem] with p hp`. Conclude with `hU _ p.2 hp.2`.

Use `ContinuousAt.congr ?_ hFeq.symm` and prove the remaining obligations. Conclude with `(hslice.comp ((archEquiv K n).continuous.comp continuous_fst)).continuousAt`. Rewrite using `[hφF]`. Conclude with `hF.comp he.continuousAt`.
-/
theorem IsUSmooth.continuous {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) : Continuous ϕ := by
  obtain ⟨U, hU⟩ := hϕ.fin
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  let e : AdelicGLn.AdelicGL K n → AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n :=
    fun g => AdelicGLn.prodEquiv K n (g₀⁻¹ * g)
  have he : Continuous e :=
    (AdelicGLn.prodEquiv K n).continuous.comp (continuous_const.mul continuous_id)
  let F : AdelicGLn.InfiniteAdelicGL K n × AdelicGLn.FiniteAdelicGL K n → ℂ :=
    fun p => ϕ (g₀ * infEmb K n (archEquiv K n p.1) * finEmb K n p.2)
  have hφF : ϕ = F ∘ e := by
    funext g
    simp only [F, e, Function.comp_apply, mul_assoc]
    rw [infEmb_mul_finEmb, mul_inv_cancel_left]
  have hslice : Continuous (archSlice ϕ g₀) := by
    letI := (isExpLieAlgebra K n).chartedSpace
    exact (hϕ.arch g₀).continuous
  have hF : ContinuousAt F (e g₀) := by
    have hFeq : F =ᶠ[𝓝 (e g₀)] fun p => archSlice ϕ g₀ (archEquiv K n p.1) := by
      have he1 : e g₀ = 1 := by simp only [e, inv_mul_cancel, map_one]
      have hmem : (univ ×ˢ (U : Set (AdelicGLn.FiniteAdelicGL K n))) ∈ 𝓝 (e g₀) := by
        rw [he1]
        exact prod_mem_nhds univ_mem (U.isOpen.mem_nhds (one_mem U))
      filter_upwards [hmem] with p hp
      exact hU _ p.2 hp.2
    refine ContinuousAt.congr ?_ hFeq.symm
    exact (hslice.comp ((archEquiv K n).continuous.comp continuous_fst)).continuousAt
  rw [hφF]
  exact hF.comp he.continuousAt

def rDeriv (Y : archLie K n) (ϕ : AdelicGLn.AdelicGL K n → ℂ) : AdelicGLn.AdelicGL K n → ℂ :=
  fun g => (isExpLieAlgebra K n).rightDeriv Y (archSlice ϕ g) 1

/- English proof (translation)
Use function extensionality and compare the values at `g`. Rewrite using `[← coe_uAction, uAction_ι_apply]`. Both sides reduce to the same expression.
-/
theorem rDeriv_eq_uActFun (Y : archLie K n) {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hϕ : IsArchSmooth ϕ) :
    rDeriv Y ϕ = uActFun (UniversalEnvelopingAlgebra.ι ℝ ((isExpLieAlgebra K n).toLie Y))
      ⟨ϕ, hϕ⟩ := by
  funext g
  rw [← coe_uAction, uAction_ι_apply]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [archSlice_apply]`. Rewrite using `[mul_assoc, ← infEmb_mul_finEmb_comm, ← mul_assoc, hV _ v hv]`.
-/
theorem archSlice_mul_finEmb {ϕ : AdelicGLn.AdelicGL K n → ℂ} {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) (g : AdelicGLn.AdelicGL K n) {v} (hv : v ∈ V) :
    archSlice ϕ (g * finEmb K n v) = archSlice ϕ g := by
  funext x
  simp only [archSlice_apply]
  rw [mul_assoc, ← infEmb_mul_finEmb_comm, ← mul_assoc, hV _ v hv]

/- English proof (translation)
Rewrite using `[rDeriv_eq_uActFun Y hϕ.arch]`. Conclude with `uActFun_mem _ _`. Use `fin := by`. Take `⟨V, hV⟩` from `hϕ.fin`. Conclude with `⟨V, fun g v hv => by simp only [rDeriv, archSlice_mul_finEmb hV g hv]⟩`.

Use `left γ g := by`. Simplify using `only [rDeriv]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [archSlice_apply, mul_assoc, hϕ.left γ]`.
-/
theorem IsUSmooth.rDeriv_smooth {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ) (Y : archLie K n) :
    IsUSmooth (rDeriv Y ϕ) where
  arch := by
    rw [rDeriv_eq_uActFun Y hϕ.arch]
    exact uActFun_mem _ _
  fin := by
    obtain ⟨V, hV⟩ := hϕ.fin
    exact ⟨V, fun g v hv => by simp only [rDeriv, archSlice_mul_finEmb hV g hv]⟩
  left γ g := by
    simp only [rDeriv]
    congr 1
    funext x
    simp only [archSlice_apply, mul_assoc, hϕ.left γ]

def oneParam (Y : archLie K n) (s : ℝ) : AdelicGLn.AdelicGL K n :=
  infEmb K n ((isExpLieAlgebra K n).expG (s • Y))

/- English proof (translation)
Rewrite using `[oneParam, oneParam, oneParam, ← map_mul]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [IsExpLieAlgebra.coe_expG, Subgroup.coe_mul, Units.val_mul, add_smul, Submodule.coe_add, Submodule.coe_smul]`.

Conclude with `exp_add_of_commute' ℝ ((Commute.refl (Y : ArchMatrix K n)).smul_left s |>.smul_right r)`.
-/
theorem oneParam_add (Y : archLie K n) (s r : ℝ) :
    oneParam Y (s + r) = oneParam Y s * oneParam Y r := by
  rw [oneParam, oneParam, oneParam, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [IsExpLieAlgebra.coe_expG, Subgroup.coe_mul, Units.val_mul, add_smul,
    Submodule.coe_add, Submodule.coe_smul]
  exact exp_add_of_commute' ℝ ((Commute.refl (Y : ArchMatrix K n)).smul_left s |>.smul_right r)

/- English proof (translation)
Simplify using `[oneParam]`.
-/
theorem oneParam_zero (Y : archLie K n) : oneParam Y 0 = 1 := by
  simp [oneParam]

/- English proof (translation)
The claim follows from `continuous_infEmb.comp ((isExpLieAlgebra K n).continuous_expG.comp (continuous_id.smul continuous_const))`.
-/
theorem continuous_oneParam (Y : archLie K n) : Continuous (oneParam Y) :=
  continuous_infEmb.comp ((isExpLieAlgebra K n).continuous_expG.comp
    (continuous_id.smul continuous_const))

/- English proof (translation)
Use `(isExpLieAlgebra K n).hasDerivAt_rightDeriv (hϕ.arch g) Y 1` as an intermediate fact. Establish `h1 : (fun t : ℝ => archSlice ϕ g (1 * (isExpLieAlgebra K n).expG (t • Y))) = fun s => ϕ (g * oneParam Y s)`. Use function extensionality and compare the values at `s`. Simplify using `only [one_mul, archSlice_apply, oneParam]`. Rewrite `this` using `[h1]`.

Conclude with `this`.
-/
theorem IsUSmooth.hasDerivAt {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ)
    (Y : archLie K n) (g : AdelicGLn.AdelicGL K n) :
    HasDerivAt (fun s : ℝ => ϕ (g * oneParam Y s)) (rDeriv Y ϕ g) 0 := by
  have := (isExpLieAlgebra K n).hasDerivAt_rightDeriv (hϕ.arch g) Y 1
  have h1 : (fun t : ℝ => archSlice ϕ g (1 * (isExpLieAlgebra K n).expG (t • Y))) =
      fun s => ϕ (g * oneParam Y s) := by
    funext s; simp only [one_mul, archSlice_apply, oneParam]
  rw [h1] at this
  exact this

/- English proof (translation)
Use `set χ : (Fin k → 𝔸[K]) → ℂ := fun x => (GroundTheory.Global.adelicChar K (-pair (lastVec k) x) : ℂ)`. Establish `hχ : Continuous χ` using `continuous_adelicChar_neg_pair _`. Use `set μ := (vecMeasure K (Fin k)).restrict (vecDomain K (Fin k))`. Establish `: IsFiniteMeasure μ` using `⟨by`. Rewrite using `[Measure.restrict_apply_univ, vecMeasure_vecDomain]`.

Conclude with `ENNReal.one_lt_top⟩`. Establish `hcF' : Continuous fun q : (Fin k → 𝔸[K]) × ℝ => F' (colGL k q.1 * (g * e q.2))` using `hF'.comp (((continuous_colGL k).comp continuous_fst).mul (continuous_const.mul (he.comp continuous_snd)))`. Take `⟨M, hM⟩` from `((isCompact_closure_vecDomain (K := K) (ι := Fin k)).prod (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn hcF'.continuousOn`. Establish `hcs : ∀ s : ℝ, Continuous fun x : Fin k → 𝔸[K] => F (colGL k x * (g * e s)) * χ x` using `fun s => (hF.comp ((continuous_colGL k).mul continuous_const)).mul hχ`. Establish `hcs' : ∀ s : ℝ, Continuous fun x : Fin k → 𝔸[K] => F' (colGL k x * (g * e s)) * χ x` using `fun s => (hF'.comp ((continuous_colGL k).mul continuous_const)).mul hχ`.

Establish `hmain` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ)) (F := fun s x => F (colGL k x * (g * e s)) * χ x) (F' := fun s x => F' (colGL k x * (g * e s)) * χ x) (bound := fun _ => M) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos) (Eventually.of_forall fun …`. Simplify using `only [norm_mul, χ, Circle.norm_coe, mul_one]`. Conclude with `hM (x, s) ⟨subset_closure hx, Metric.ball_subset_closedBall hs⟩))`. Use the proof step `(integrable_const M)`. Use the proof step `(ae_of_all _ fun x s _ => by`.

Establish `h0` using `hd (colGL k x * (g * e s))`. Establish `h0' : HasDerivAt (fun r : ℝ => F (colGL k x * (g * e s) * e r)) (F' (colGL k x * (g * e s))) (s + -s)` using `by rw [add_neg_cancel]; exact h0`. Establish `h1` using `h0'.comp_add_const s (-s)`. Establish `h2 : (fun r : ℝ => F (colGL k x * (g * e s) * e (r + -s))) = fun r => F (colGL k x * (g * e r))`. Use function extensionality and compare the values at `r`.

Rewrite using `[mul_assoc, mul_assoc, ← hadd]`. Use `congr 4`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2]`. Conclude with `h1.mul_const (χ x))`.

Establish `h2` using `hmain.2`. Simplify using `only [he0, mul_one] at h2`. Conclude with `h2`.
-/
theorem hasDerivAt_stepCoeff (k : ℕ) {F F' : AdelicGLn.AdelicGL K n → ℂ} (hF : Continuous F)
    (hF' : Continuous F') {e : ℝ → AdelicGLn.AdelicGL K n} (he : Continuous e)
    (hadd : ∀ s r, e (s + r) = e s * e r) (he0 : e 0 = 1)
    (hd : ∀ g, HasDerivAt (fun s => F (g * e s)) (F' g) 0) (g : AdelicGLn.AdelicGL K n) :
    HasDerivAt (fun s => stepCoeff k F (g * e s)) (stepCoeff k F' g) 0 := by
  set χ : (Fin k → 𝔸[K]) → ℂ := fun x => (GroundTheory.Global.adelicChar K (-pair (lastVec k) x) : ℂ)
  have hχ : Continuous χ := continuous_adelicChar_neg_pair _
  set μ := (vecMeasure K (Fin k)).restrict (vecDomain K (Fin k))
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  have hcF' : Continuous fun q : (Fin k → 𝔸[K]) × ℝ => F' (colGL k q.1 * (g * e q.2)) :=
    hF'.comp (((continuous_colGL k).comp continuous_fst).mul
      (continuous_const.mul (he.comp continuous_snd)))
  obtain ⟨M, hM⟩ := ((isCompact_closure_vecDomain (K := K) (ι := Fin k)).prod
    (isCompact_closedBall (0 : ℝ) 1)).exists_bound_of_continuousOn hcF'.continuousOn
  have hcs : ∀ s : ℝ, Continuous fun x : Fin k → 𝔸[K] => F (colGL k x * (g * e s)) * χ x :=
    fun s => (hF.comp ((continuous_colGL k).mul continuous_const)).mul hχ
  have hcs' : ∀ s : ℝ, Continuous fun x : Fin k → 𝔸[K] => F' (colGL k x * (g * e s)) * χ x :=
    fun s => (hF'.comp ((continuous_colGL k).mul continuous_const)).mul hχ
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun s x => F (colGL k x * (g * e s)) * χ x)
    (F' := fun s x => F' (colGL k x * (g * e s)) * χ x)
    (bound := fun _ => M) (s := Metric.ball 0 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun s => (hcs s).aestronglyMeasurable)
    (((hcs 0).continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure)
    (hcs' 0).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_vecDomain).2 (ae_of_all _ fun x hx s hs => by
      simp only [norm_mul, χ, Circle.norm_coe, mul_one]
      exact hM (x, s) ⟨subset_closure hx, Metric.ball_subset_closedBall hs⟩))
    (integrable_const M)
    (ae_of_all _ fun x s _ => by
      have h0 := hd (colGL k x * (g * e s))
      have h0' : HasDerivAt (fun r : ℝ => F (colGL k x * (g * e s) * e r))
          (F' (colGL k x * (g * e s))) (s + -s) := by rw [add_neg_cancel]; exact h0
      have h1 := h0'.comp_add_const s (-s)
      have h2 : (fun r : ℝ => F (colGL k x * (g * e s) * e (r + -s))) =
          fun r => F (colGL k x * (g * e r)) := by
        funext r
        rw [mul_assoc, mul_assoc, ← hadd]
        congr 4
        ring
      rw [h2] at h1
      exact h1.mul_const (χ x))
  have h2 := hmain.2
  simp only [he0, mul_one] at h2
  exact h2

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact hϕ`. Consider the case `succ m ih => exact continuous_stepCoeff _ ih`.
-/
theorem partialWhittakerCoeff_continuous {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : Continuous ϕ) (m : ℕ) :
    Continuous (partialWhittakerCoeff ϕ m) := by
  induction m with
  | zero => exact hϕ
  | succ m ih => exact continuous_stepCoeff _ ih

/- English proof (translation)
Unfold `partialCoeff`. Proceed by induction on `n - k generalizing g with`. Consider the case `zero => exact hϕ.hasDerivAt Y g`. Consider the case `succ m ih`. Conclude with `hasDerivAt_stepCoeff _ (partialWhittakerCoeff_continuous hϕ.continuous m) (partialWhittakerCoeff_continuous (hϕ.rDeriv_smooth Y).continuous m) (continuous_oneParam Y) (oneParam_add Y) (oneParam_zero Y) ih g`.
-/
theorem hasDerivAt_partialCoeff {ϕ : AdelicGLn.AdelicGL K n → ℂ} (hϕ : IsUSmooth ϕ)
    (Y : archLie K n) (k : ℕ) (g : AdelicGLn.AdelicGL K n) :
    HasDerivAt (fun s => partialCoeff ϕ k (g * oneParam Y s)) (partialCoeff (rDeriv Y ϕ) k g) 0 := by
  unfold partialCoeff
  induction n - k generalizing g with
  | zero => exact hϕ.hasDerivAt Y g
  | succ m ih =>
    exact hasDerivAt_stepCoeff _ (partialWhittakerCoeff_continuous hϕ.continuous m)
      (partialWhittakerCoeff_continuous (hϕ.rDeriv_smooth Y).continuous m) (continuous_oneParam Y)
      (oneParam_add Y) (oneParam_zero Y) ih g

/- English proof (translation)
Rewrite using `[NormedSpace.exp_eq_tsum ℝ]`. Simplify using `only`. Rewrite using `[tsum_eq_sum (s := Finset.range 2) (fun m hm => ?_)]`. Simplify using `[Finset.sum_range_succ]`. Establish `h2 : 2 ≤ m` using `by simp at hm; omega`.

Take `⟨r, rfl⟩` from `Nat.exists_eq_add_of_le h2`. Rewrite using `[pow_add, sq, smul_mul_smul_comm, hE, smul_zero, zero_mul, smul_zero]`.
-/
theorem exp_smul_of_mul_self_eq_zero {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] {E : 𝔸} (hE : E * E = 0) (s : ℝ) :
    NormedSpace.exp (s • E) = 1 + s • E := by
  rw [NormedSpace.exp_eq_tsum ℝ]
  simp only
  rw [tsum_eq_sum (s := Finset.range 2) (fun m hm => ?_)]
  · simp [Finset.sum_range_succ]
  · have h2 : 2 ≤ m := by simp at hm; omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h2
    rw [pow_add, sq, smul_mul_smul_comm, hE, smul_zero, zero_mul, smul_zero]

def dirMat (k : ℕ) (p : Fin k × BIdx K) : ArchMatrix K n :=
  Matrix.of fun a b => if a.val = p.1.val ∧ b.val = k then latticeBasis K p.2 else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dirMat_apply (k : ℕ) (p : Fin k × BIdx K) (a b : Fin n) :
    (dirMat k p : Matrix (Fin n) (Fin n) (mixedSpace K)) a b =
      if a.val = p.1.val ∧ b.val = k then latticeBasis K p.2 else 0 := rfl

/- English proof (translation)
Set `M : Matrix (Fin n) (Fin n) (mixedSpace K)` to `Matrix.of fun a b => if a.val = p.1.val ∧ b.val = k then latticeBasis K p.2 else 0`. Establish `h : M * M = 0`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Simplify using `only [M, Matrix.of_apply]`. Apply the tactic sequence `split_ifs with h1 h2 <;> first | (exfalso; have := p.1.2; omega) | simp`. Conclude with `h`.
-/
theorem dirMat_mul_self (k : ℕ) (p : Fin k × BIdx K) :
    dirMat (n := n) k p * dirMat k p = 0 := by
  let M : Matrix (Fin n) (Fin n) (mixedSpace K) :=
    Matrix.of fun a b => if a.val = p.1.val ∧ b.val = k then latticeBasis K p.2 else 0
  have h : M * M = 0 := by
    refine Matrix.ext fun a b => ?_
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp only [M, Matrix.of_apply]
    split_ifs with h1 h2 <;> first | (exfalso; have := p.1.2; omega) | simp
  exact h

def archPt (g : AdelicGLn.AdelicGL K n) : archGroup K n :=
  archEquiv K n (AdelicGLn.prodEquiv K n g).1

def dirY (k : ℕ) (g : AdelicGLn.AdelicGL K n) (p : Fin k × BIdx K) : archLie K n :=
  ⟨(((((archPt g)⁻¹ : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) * dirMat k p *
    (((archPt g : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n)), Submodule.mem_top⟩

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [IsExpLieAlgebra.coe_expG, Submodule.coe_smul, dirY, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]`. Use `set u : (ArchMatrix K n)ˣ := ((archPt g : archGroup K n) : (ArchMatrix K n)ˣ)`. Use `set E := dirMat (n := n) k p`.

Establish `hE : E * E = 0` using `dirMat_mul_self k p`. Establish `hY : ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u * (((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u) = 0`. Rewrite using `[show ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u * (((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u) = ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * (E * (u * ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n)) * E) * u by noncomm_ring, Units.mul_inv, mul_one, hE, mul_z …`. Rewrite using `[exp_smul_of_mul_self_eq_zero hY, exp_smul_of_mul_self_eq_zero hE, mul_add, add_mul, mul_one, Units.inv_mul, mul_smul_comm, smul_mul_assoc]`.
-/
theorem expG_smul_dirY (k : ℕ) (g : AdelicGLn.AdelicGL K n) (p : Fin k × BIdx K) (s : ℝ) :
    (isExpLieAlgebra K n).expG (s • dirY k g p) =
      (archPt g)⁻¹ * (isExpLieAlgebra K n).expG (s • ⟨dirMat k p, Submodule.mem_top⟩) *
        archPt g := by
  apply Subtype.ext
  apply Units.ext
  simp only [IsExpLieAlgebra.coe_expG, Submodule.coe_smul, dirY, Subgroup.coe_mul, Units.val_mul,
    Subgroup.coe_inv]
  set u : (ArchMatrix K n)ˣ := ((archPt g : archGroup K n) : (ArchMatrix K n)ˣ)
  set E := dirMat (n := n) k p
  have hE : E * E = 0 := dirMat_mul_self k p
  have hY : ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u *
      (((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u) = 0 := by
    rw [show ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u *
        (((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * E * u) =
        ((u⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) * (E * (u * ((u⁻¹ : (ArchMatrix K n)ˣ) :
          ArchMatrix K n)) * E) * u by noncomm_ring, Units.mul_inv, mul_one, hE, mul_zero, zero_mul]
  rw [exp_smul_of_mul_self_eq_zero hY, exp_smul_of_mul_self_eq_zero hE, mul_add, add_mul, mul_one,
    Units.inv_mul, mul_smul_comm, smul_mul_assoc]

/- English proof (translation)
Establish `hg : infEmb K n (archPt g) * finEmb K n (AdelicGLn.prodEquiv K n g).2 = g` using `infEmb_mul_finEmb g`. Use `set a := archPt g`. Use `set f := (AdelicGLn.prodEquiv K n g).2`. Rewrite using `[← hg, mul_assoc (infEmb K n a) (finEmb K n f), ← infEmb_mul_finEmb_comm, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, show a * (a⁻¹ * X * a) = X * a by group]`.
-/
theorem infEmb_mul_eq (g : AdelicGLn.AdelicGL K n) (X : archGroup K n) :
    infEmb K n X * g = g * infEmb K n ((archPt g)⁻¹ * X * archPt g) := by
  have hg : infEmb K n (archPt g) * finEmb K n (AdelicGLn.prodEquiv K n g).2 = g :=
    infEmb_mul_finEmb g
  set a := archPt g
  set f := (AdelicGLn.prodEquiv K n g).2
  rw [← hg, mul_assoc (infEmb K n a) (finEmb K n f), ← infEmb_mul_finEmb_comm, ← mul_assoc,
    ← map_mul, ← mul_assoc, ← map_mul, show a * (a⁻¹ * X * a) = X * a by group]

/- English proof (translation)
Use `set v : Fin k → 𝔸[K] := torusPt (Pi.single p s)`. Establish `hv1 : ∀ i : Fin k, GroundTheory.Global.homeomorphMixedSpace K (v i).1 = if i = p.1 then s • latticeBasis K p.2 else 0`. Introduce `i`. Use `show GroundTheory.Global.homeomorphMixedSpace K (ofCoord fun j => (Pi.single p s : Fin k × BIdx K → ℝ) (i, j)) = _`. Rewrite using `[homeomorphMixedSpace_ofCoord]`.

Distinguish the cases in `hi : i = p.1`. Substitute `hi` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single p.2]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Rewrite using `[Pi.single_eq_of_ne (fun h => hj (by rw [← h])), zero_smul]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg hi]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne (fun h => hi (by rw [← h])), zero_smul]`.

Establish `hv2 : ∀ i : Fin k, (v i).2 = 0` using `fun i => rfl`. Establish `hfin : (AdelicGLn.prodEquiv K n (colGL k v)).2 = 1`. Apply `Units.ext` to reduce the goal to its premises. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Rewrite using `[AdelicGLn.prodEquiv_apply_snd]`.

Simplify using `only [colGL, coe_uGL, uMat_apply, colX_apply, Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | simp_all`. Establish `hinf : archEquiv K n (AdelicGLn.prodEquiv K n (colGL k v)).1 = (isExpLieAlgebra K n).expG (s • ⟨dirMat k p, Submodule.mem_top⟩)`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[IsExpLieAlgebra.coe_expG]`. Simplify using `only [Submodule.coe_smul]`. Rewrite using `[exp_smul_of_mul_self_eq_zero (dirMat_mul_self k p)]`. Apply the tactic sequence `have hentry : ∀ a b : Fin n, ((1 + s • dirMat k p : ArchMatrix K n) : Matrix (Fin n) (Fin n) (mixedSpace K)) a b = (if a = b then 1 else 0) + s • (dirMat k p : Matrix (Fin n) (Fin n) (mixedSpace K)) a b := fun a b => rfl`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Rewrite using `[hentry]`. Use `show archMatrixEquiv K n ((AdelicGLn.prodEquiv K n (colGL k v)).1 : Matrix (Fin n) (Fin n) _) a b = _`. Rewrite using `[archMatrixEquiv_apply, AdelicGLn.prodEquiv_apply_fst, dirMat_apply]`. Simplify using `only [colGL, coe_uGL, uMat_apply, colX_apply]`. Establish `hp` using `p.1.2`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, if_neg (by omega), smul_zero, add_zero]`. Conclude with `map_one _`. Rewrite using `[if_neg hab, if_neg hab, zero_add]`.

Distinguish the cases in `hlt : a < b`. Rewrite using `[dif_pos hlt]`. Distinguish the cases in `hbk : b.val = k`. Rewrite using `[dif_pos hbk, ← GroundTheory.Global.homeomorphMixedSpace_apply, hv1]`. Distinguish the cases in `ha : a.val = p.1.val`.

Rewrite using `[if_pos (Fin.ext ha), if_pos ⟨ha, hbk⟩]`. Rewrite using `[if_neg (fun h => ha (by rw [← h])), if_neg (fun h => ha h.1), smul_zero]`. Rewrite using `[dif_neg hbk, if_neg (fun h => hbk h.2), smul_zero]`. Conclude with `map_zero _`. Rewrite using `[dif_neg hlt, if_neg (fun h => hlt (by rw [Fin.lt_def]; omega)), smul_zero]`.

Conclude with `map_zero _`. Apply `(AdelicGLn.prodEquiv K n).injective` to reduce the goal to its premises. Rewrite using `[prodEquiv_infEmb, ← hinf, ContinuousMulEquiv.symm_apply_apply, ← hfin]`.
-/
theorem infEmb_expG_dirMat (k : ℕ) (hk : k < n) (p : Fin k × BIdx K) (s : ℝ) :
    infEmb K n ((isExpLieAlgebra K n).expG (s • ⟨dirMat k p, Submodule.mem_top⟩)) =
      colGL k (torusPt (Pi.single p s)) := by
  set v : Fin k → 𝔸[K] := torusPt (Pi.single p s)
  have hv1 : ∀ i : Fin k, GroundTheory.Global.homeomorphMixedSpace K (v i).1 =
      if i = p.1 then s • latticeBasis K p.2 else 0 := by
    intro i
    show GroundTheory.Global.homeomorphMixedSpace K (ofCoord fun j => (Pi.single p s : Fin k × BIdx K → ℝ) (i, j)) = _
    rw [homeomorphMixedSpace_ofCoord]
    by_cases hi : i = p.1
    · subst hi
      rw [if_pos rfl, Finset.sum_eq_single p.2]
      · simp
      · intro j _ hj
        rw [Pi.single_eq_of_ne (fun h => hj (by rw [← h])), zero_smul]
      · simp
    · rw [if_neg hi]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Pi.single_eq_of_ne (fun h => hi (by rw [← h])), zero_smul]
  have hv2 : ∀ i : Fin k, (v i).2 = 0 := fun i => rfl
  have hfin : (AdelicGLn.prodEquiv K n (colGL k v)).2 = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    rw [AdelicGLn.prodEquiv_apply_snd]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply, Units.val_one, Matrix.one_apply]
    split_ifs <;> first | rfl | simp_all
  have hinf : archEquiv K n (AdelicGLn.prodEquiv K n (colGL k v)).1 =
      (isExpLieAlgebra K n).expG (s • ⟨dirMat k p, Submodule.mem_top⟩) := by
    apply Subtype.ext
    apply Units.ext
    rw [IsExpLieAlgebra.coe_expG]
    simp only [Submodule.coe_smul]
    rw [exp_smul_of_mul_self_eq_zero (dirMat_mul_self k p)]
    have hentry : ∀ a b : Fin n, ((1 + s • dirMat k p : ArchMatrix K n) :
        Matrix (Fin n) (Fin n) (mixedSpace K)) a b =
        (if a = b then 1 else 0) + s • (dirMat k p : Matrix (Fin n) (Fin n) (mixedSpace K)) a b :=
      fun a b => rfl
    refine Matrix.ext fun a b => ?_
    rw [hentry]
    show archMatrixEquiv K n ((AdelicGLn.prodEquiv K n (colGL k v)).1 :
      Matrix (Fin n) (Fin n) _) a b = _
    rw [archMatrixEquiv_apply, AdelicGLn.prodEquiv_apply_fst, dirMat_apply]
    simp only [colGL, coe_uGL, uMat_apply, colX_apply]
    have hp := p.1.2
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl, if_neg (by omega), smul_zero, add_zero]
      exact map_one _
    · rw [if_neg hab, if_neg hab, zero_add]
      by_cases hlt : a < b
      · rw [dif_pos hlt]
        by_cases hbk : b.val = k
        · rw [dif_pos hbk, ← GroundTheory.Global.homeomorphMixedSpace_apply, hv1]
          by_cases ha : a.val = p.1.val
          · rw [if_pos (Fin.ext ha), if_pos ⟨ha, hbk⟩]
          · rw [if_neg (fun h => ha (by rw [← h])), if_neg (fun h => ha h.1), smul_zero]
        · rw [dif_neg hbk, if_neg (fun h => hbk h.2), smul_zero]
          exact map_zero _
      · rw [dif_neg hlt, if_neg (fun h => hlt (by rw [Fin.lt_def]; omega)), smul_zero]
        exact map_zero _
  apply (AdelicGLn.prodEquiv K n).injective
  rw [prodEquiv_infEmb, ← hinf, ContinuousMulEquiv.symm_apply_apply, ← hfin]

/- English proof (translation)
Rewrite using `[oneParam, expG_smul_dirY, ← infEmb_expG_dirMat k hk, infEmb_mul_eq]`.
-/
theorem colGL_torusPt_single_mul (k : ℕ) (hk : k < n) (g : AdelicGLn.AdelicGL K n)
    (p : Fin k × BIdx K) (s : ℝ) :
    colGL k (torusPt (Pi.single p s)) * g = g * oneParam (dirY k g p) s := by
  rw [oneParam, expG_smul_dirY, ← infEmb_expG_dirMat k hk, infEmb_mul_eq]

end FourierWhittaker

end

end GroundTheory.Automorphic
