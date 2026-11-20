import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.KernInvariantSymmPos

open Matrix Complex NumberField GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate Real Topology
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.SW.KernSum

section Tame

variable {ι : Type} {a : ι → ℝ}

def Tame (a x : ι → ℝ) : Prop := ∀ c : ℝ, 0 ≤ c → Summable fun i => a i * Real.exp (c * x i)

/- English proof (translation)
Introduce `c hc`. Use `((hx (c * k) (mul_nonneg hc hk)).add (hy (c * k) (mul_nonneg hc hk))).of_nonneg_of_le (fun i => mul_nonneg (ha i) (Real.exp_pos _).le) fun i => ?_` and prove the remaining obligations. Rewrite using `[← mul_add]`. Use `mul_le_mul_of_nonneg_left ?_ (ha i)` and prove the remaining obligations. Break down `h i with h | h` into its components or cases.

Use `le_add_of_le_of_nonneg (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left h hc`. Use `le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 ?_)` and prove the remaining obligations. Rewrite using `[mul_assoc]`.

Conclude with `mul_le_mul_of_nonneg_left h hc`.
-/
theorem Tame.of_le_max (ha : ∀ i, 0 ≤ a i) {x y z : ι → ℝ} (hx : Tame a x) (hy : Tame a y)
    {k : ℝ} (hk : 0 ≤ k) (h : ∀ i, z i ≤ k * x i ∨ z i ≤ k * y i) : Tame a z := by
  intro c hc
  refine ((hx (c * k) (mul_nonneg hc hk)).add (hy (c * k) (mul_nonneg hc hk))).of_nonneg_of_le
    (fun i => mul_nonneg (ha i) (Real.exp_pos _).le) fun i => ?_
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (ha i)
  rcases h i with h | h
  · refine le_add_of_le_of_nonneg (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h hc
  · refine le_add_of_nonneg_of_le (Real.exp_pos _).le (Real.exp_le_exp.2 ?_)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h hc

/- English proof (translation)
The claim follows from `hx.of_le_max ha hy zero_le_two fun i => by rcases le_total (x i) (y i) with h | h · right; linarith · left; linarith`.
-/
theorem Tame.add (ha : ∀ i, 0 ≤ a i) {x y : ι → ℝ} (hx : Tame a x) (hy : Tame a y) :
    Tame a fun i => x i + y i :=
  hx.of_le_max ha hy zero_le_two fun i => by
    rcases le_total (x i) (y i) with h | h
    · right; linarith
    · left; linarith

/- English proof (translation)
The claim follows from `hx.of_le_max ha hy zero_le_one fun i => by rcases abs_cases (x i) with h | h · left; linarith [h.1] · right; linarith [h.1]`.
-/
theorem Tame.abs (ha : ∀ i, 0 ≤ a i) {x : ι → ℝ} (hx : Tame a x) (hy : Tame a fun i => -x i) :
    Tame a fun i => |x i| :=
  hx.of_le_max ha hy zero_le_one fun i => by
    rcases abs_cases (x i) with h | h
    · left; linarith [h.1]
    · right; linarith [h.1]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro c _`. Simplify using `using h0`. Consider the case `insert k s hk ih`. Simplify using `only [Finset.sum_insert hk]`.

Conclude with `(hx k).add ha ih`.
-/
theorem Tame.sum (ha : ∀ i, 0 ≤ a i) (h0 : Summable a) {κ : Type} (s : Finset κ) {x : κ → ι → ℝ}
    (hx : ∀ k, Tame a (x k)) : Tame a fun i => ∑ k ∈ s, x k i := by
  classical
  induction s using Finset.induction_on with
  | empty => intro c _; simpa using h0
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact (hx k).add ha ih

end Tame

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

/- English proof (translation)
Establish `ha : ∀ i, 0 ≤ ‖A i‖` using `fun i => norm_nonneg _`. Establish `h0 : Summable fun i => ‖A i‖` using `by simpa using (h 0).norm`. Establish `h1 (ζ : ℂ) (t : W) : Tame (fun i => ‖A i‖) fun i => (ζ * B i t t).re`. Introduce `c _`. Take `⟨s, hs⟩` from `IsAlgClosed.exists_pow_nat_eq ((c : ℂ) * ζ) two_pos`.

Use `(h (s • t)).norm.congr fun i => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_exp]`. Use `congr 2`. Simplify using `only [map_smul, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, ← sq, hs, mul_assoc, re_ofReal_mul]`.

Establish `h2 (t : W) : Tame (fun i => ‖A i‖) fun i => ‖B i t t‖`. Establish `e1` using `Tame.abs ha (h1 1 t) (by simpa using h1 (-1) t)`. Establish `e2` using `Tame.abs ha (h1 I t) (by simpa using h1 (-I) t)`. Use `(e1.add ha e2).of_le_max ha e1 zero_le_one fun i => Or.inl ?_` and prove the remaining obligations. Simplify using `using norm_le_abs_re_add_abs_im (B i t t)`.

Set `b` to `Module.finBasis ℂ W`. Set `K : ℝ` to `‖b.equivFunL.toContinuousLinearMap‖ * |R|`. Establish `h3` using `Tame.sum ha h0 Finset.univ fun j => Tame.sum ha h0 Finset.univ fun k => (h2 (b j + b k)).add ha (h2 (b j - b k))`. Use `⟨_, h3 (K * K) (mul_self_nonneg K), fun i v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, norm_exp]`.

Use `mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((re_le_norm _).trans ?_)) (ha i)` and prove the remaining obligations. Establish `hK (j) : ‖b.repr v j‖ ≤ K` using `((norm_le_pi_norm (b.equivFunL v) j).trans (b.equivFunL.toContinuousLinearMap.le_opNorm v)).trans (mul_le_mul_of_nonneg_left (hv.trans (le_abs_self R)) (norm_nonneg _))`. Establish `e : B i v v = ∑ j, ∑ k, b.repr v j * b.repr v k * B i (b j) (b k)` using `by conv_lhs => rw [← b.sum_repr v]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`. Establish `e' : B i v v = ∑ j, ∑ k, b.repr v j * b.repr v k * ((B i (b j + b k) (b j + b k) - B i (b j - b k) (b j - b k)) / 4)`. Establish `e2` using `e`. Rewrite `e2` using `[Finset.sum_comm]`. Rewrite using `[← add_self_div_two (B i v v), congrArg₂ (· + ·) e e2, ← Finset.sum_add_distrib, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e', Finset.mul_sum]`. Use `norm_sum_le_of_le _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `norm_sum_le_of_le _ fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`.

Use `mul_le_mul (mul_le_mul (hK j) (hK k) (norm_nonneg _) ((norm_nonneg _).trans (hK j))) ?_ (norm_nonneg _) (mul_self_nonneg K)` and prove the remaining obligations. Rewrite using `[norm_div]`. Use `norm_sub_le (B i (b j + b k) (b j + b k)) (B i (b j - b k) (b j - b k))` as an intermediate fact. Establish `h4 : ‖(4 : ℂ)‖ = 4` using `by simp`. Rewrite using `[h4]`.

Combine the linear relations using `[norm_nonneg (B i (b j + b k) (b j + b k) - B i (b j - b k) (b j - b k))]`.
-/
theorem exists_majorant {ι : Type} (A : ι → ℂ) (B : ι → W →ₗ[ℂ] W →ₗ[ℂ] ℂ)
    (h : ∀ v, Summable fun i => A i * cexp (B i v v)) (R : ℝ) :
    ∃ u : ι → ℝ, Summable u ∧ ∀ i v, ‖v‖ ≤ R → ‖A i * cexp (B i v v)‖ ≤ u i := by
  have ha : ∀ i, 0 ≤ ‖A i‖ := fun i => norm_nonneg _
  have h0 : Summable fun i => ‖A i‖ := by simpa using (h 0).norm
  have h1 (ζ : ℂ) (t : W) : Tame (fun i => ‖A i‖) fun i => (ζ * B i t t).re := by
    intro c _
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((c : ℂ) * ζ) two_pos
    refine (h (s • t)).norm.congr fun i => ?_
    rw [norm_mul, norm_exp]
    congr 2
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← sq, hs, mul_assoc, re_ofReal_mul]
  have h2 (t : W) : Tame (fun i => ‖A i‖) fun i => ‖B i t t‖ := by
    have e1 := Tame.abs ha (h1 1 t) (by simpa using h1 (-1) t)
    have e2 := Tame.abs ha (h1 I t) (by simpa using h1 (-I) t)
    refine (e1.add ha e2).of_le_max ha e1 zero_le_one fun i => Or.inl ?_
    simpa using norm_le_abs_re_add_abs_im (B i t t)
  let b := Module.finBasis ℂ W
  let K : ℝ := ‖b.equivFunL.toContinuousLinearMap‖ * |R|
  have h3 := Tame.sum ha h0 Finset.univ fun j => Tame.sum ha h0 Finset.univ fun k =>
    (h2 (b j + b k)).add ha (h2 (b j - b k))
  refine ⟨_, h3 (K * K) (mul_self_nonneg K), fun i v hv => ?_⟩
  rw [norm_mul, norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ((re_le_norm _).trans ?_)) (ha i)
  have hK (j) : ‖b.repr v j‖ ≤ K :=
    ((norm_le_pi_norm (b.equivFunL v) j).trans (b.equivFunL.toContinuousLinearMap.le_opNorm v)).trans
      (mul_le_mul_of_nonneg_left (hv.trans (le_abs_self R)) (norm_nonneg _))
  have e : B i v v = ∑ j, ∑ k, b.repr v j * b.repr v k * B i (b j) (b k) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have e' : B i v v = ∑ j, ∑ k, b.repr v j * b.repr v k *
      ((B i (b j + b k) (b j + b k) - B i (b j - b k) (b j - b k)) / 4) := by
    have e2 := e
    rw [Finset.sum_comm] at e2
    rw [← add_self_div_two (B i v v), congrArg₂ (· + ·) e e2, ← Finset.sum_add_distrib,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
    ring
  rw [e', Finset.mul_sum]
  refine norm_sum_le_of_le _ fun j _ => ?_
  rw [Finset.mul_sum]
  refine norm_sum_le_of_le _ fun k _ => ?_
  rw [norm_mul, norm_mul]
  refine mul_le_mul (mul_le_mul (hK j) (hK k) (norm_nonneg _) ((norm_nonneg _).trans (hK j))) ?_
    (norm_nonneg _) (mul_self_nonneg K)
  rw [norm_div]
  have := norm_sub_le (B i (b j + b k) (b j + b k)) (B i (b j - b k) (b j - b k))
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  linarith [norm_nonneg (B i (b j + b k) (b j + b k) - B i (b j - b k) (b j - b k))]

variable {σ : Type}

noncomputable def bd (P Q : MvPolynomial σ ℂ) (u : σ → W) (F : W × W → ℂ) : ℂ :=
  polyDeriv P u (fun z => polyDeriv Q u (fun w => F (z, w)) 0) 0

/- English proof (translation)
Take `rfl : S = fun p => ∑' i, F i p` from `funext fun p => (hS p).tsum_eq.symm`. Establish `hd : ∀ i, DifferentiableOn ℂ (F i) Set.univ` using `fun i p _ => (hF i p).differentiableAt.differentiableWithinAt`. Establish `hle : ∀ x ∈ (Set.univ : Set (W × W)), ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i` using `fun x _ => by`. Take `⟨u, h1, h2⟩` from `hu (‖x‖ + 1)`. Conclude with `⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball.mem_nhds (by simp), u, h1, fun i z hz => h2 i z (mem_ball_zero_iff.1 hz).le⟩`.

Establish `ha : ∀ p, AnalyticAt ℂ (fun p => ∑' i, F i p) p` using `fun p => SCV.analyticOnNhd_of_differentiableOn isOpen_univ (SCV.differentiableOn_tsum_of_locally_normal isOpen_univ hd hle) p trivial`. Use `⟨ha, ?_⟩` and prove the remaining obligations. Simplify using `only [bd, KernSym.polyDeriv_polyDeriv P Q u ha, KernSym.polyDeriv_polyDeriv P Q u (hF _), lineDerivList_eq_iteratedFDeriv (ha _), lineDerivList_eq_iteratedFDeriv (hF _ _)]`. Use `hasSum_sum fun m _ => hasSum_sum fun m' _ => HasSum.mul_left _ ?_` and prove the remaining obligations. Conclude with `(ContinuousMultilinearMap.apply ℂ _ ℂ _).hasSum (SCV.hasSum_iteratedFDeriv_of_locally_normal isOpen_univ hd hle _ (Set.mem_univ 0))`.
-/
theorem bd_hasSum (P Q : MvPolynomial σ ℂ) (u : σ → W) {ι : Type} {F : ι → W × W → ℂ}
    {S : W × W → ℂ} (hF : ∀ i p, AnalyticAt ℂ (F i) p) (hS : ∀ p, HasSum (fun i => F i p) (S p))
    (hu : ∀ R : ℝ, ∃ u : ι → ℝ, Summable u ∧ ∀ i p, ‖p‖ ≤ R → ‖F i p‖ ≤ u i) :
    (∀ p, AnalyticAt ℂ S p) ∧ HasSum (fun i => bd P Q u (F i)) (bd P Q u S) := by
  obtain rfl : S = fun p => ∑' i, F i p := funext fun p => (hS p).tsum_eq.symm
  have hd : ∀ i, DifferentiableOn ℂ (F i) Set.univ := fun i p _ =>
    (hF i p).differentiableAt.differentiableWithinAt
  have hle : ∀ x ∈ (Set.univ : Set (W × W)), ∃ t ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧
      ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ u i := fun x _ => by
    obtain ⟨u, h1, h2⟩ := hu (‖x‖ + 1)
    exact ⟨Metric.ball 0 (‖x‖ + 1), Metric.isOpen_ball.mem_nhds (by simp), u, h1,
      fun i z hz => h2 i z (mem_ball_zero_iff.1 hz).le⟩
  have ha : ∀ p, AnalyticAt ℂ (fun p => ∑' i, F i p) p := fun p =>
    SCV.analyticOnNhd_of_differentiableOn isOpen_univ
      (SCV.differentiableOn_tsum_of_locally_normal isOpen_univ hd hle) p trivial
  refine ⟨ha, ?_⟩
  simp only [bd, KernSym.polyDeriv_polyDeriv P Q u ha, KernSym.polyDeriv_polyDeriv P Q u (hF _),
    lineDerivList_eq_iteratedFDeriv (ha _), lineDerivList_eq_iteratedFDeriv (hF _ _)]
  refine hasSum_sum fun m _ => hasSum_sum fun m' _ => HasSum.mul_left _ ?_
  exact (ContinuousMultilinearMap.apply ℂ _ ℂ _).hasSum
    (SCV.hasSum_iteratedFDeriv_of_locally_normal isOpen_univ hd hle _ (Set.mem_univ 0))

omit [FiniteDimensional ℂ W] in
/- English proof (translation)
Establish `h : ∀ p, AnalyticAt ℂ (fun p => F p + G p) p` using `fun p => (hF p).add (hG p)`. Rewrite using `[bd, bd, bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u hF, KernSym.polyDeriv_polyDeriv P Q u hG, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_add, ← lineDerivList_add (hF 0) (hG 0)]`.
-/
theorem bd_add (P Q : MvPolynomial σ ℂ) (u : σ → W) {F G : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) (hG : ∀ p, AnalyticAt ℂ G p) :
    bd P Q u (fun p => F p + G p) = bd P Q u F + bd P Q u G := by
  have h : ∀ p, AnalyticAt ℂ (fun p => F p + G p) p := fun p => (hF p).add (hG p)
  rw [bd, bd, bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u hF,
    KernSym.polyDeriv_polyDeriv P Q u hG, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [← mul_add, ← lineDerivList_add (hF 0) (hG 0)]

omit [FiniteDimensional ℂ W] in
/- English proof (translation)
Establish `h : ∀ p, AnalyticAt ℂ (fun p => ∑ k ∈ s, F k p) p` using `fun p => Finset.analyticAt_fun_sum _ fun k _ => hF k p`. Simplify using `only [bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u (hF _), lineDerivList_sum s fun k _ => hF k 0, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`.
-/
theorem bd_sum (P Q : MvPolynomial σ ℂ) (u : σ → W) {κ : Type} (s : Finset κ) {F : κ → W × W → ℂ}
    (hF : ∀ k p, AnalyticAt ℂ (F k) p) :
    bd P Q u (fun p => ∑ k ∈ s, F k p) = ∑ k ∈ s, bd P Q u (F k) := by
  have h : ∀ p, AnalyticAt ℂ (fun p => ∑ k ∈ s, F k p) p := fun p =>
    Finset.analyticAt_fun_sum _ fun k _ => hF k p
  simp only [bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u (hF _),
    lineDerivList_sum s fun k _ => hF k 0, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_comm]

omit [FiniteDimensional ℂ W] in
/- English proof (translation)
Establish `h : ∀ p, AnalyticAt ℂ (fun p => c * F p) p` using `fun p => analyticAt_const.mul (hF p)`. Rewrite using `[bd, bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u hF, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m' _ => ?_` and prove the remaining obligations.

Use `congrFun (lineDerivList_const_smul (List.map (fun s => (u s, 0)) (KernSym.lst m) ++ List.map (fun s => (0, u s)) (KernSym.lst m')) c F) 0` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bd_const_mul (P Q : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {F : W × W → ℂ}
    (hF : ∀ p, AnalyticAt ℂ F p) : bd P Q u (fun p => c * F p) = c * bd P Q u F := by
  have h : ∀ p, AnalyticAt ℂ (fun p => c * F p) p := fun p => analyticAt_const.mul (hF p)
  rw [bd, bd, KernSym.polyDeriv_polyDeriv P Q u h, KernSym.polyDeriv_polyDeriv P Q u hF,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m' _ => ?_
  have := congrFun (lineDerivList_const_smul (List.map (fun s => (u s, 0)) (KernSym.lst m) ++
    List.map (fun s => (0, u s)) (KernSym.lst m')) c F) 0
  simp only [smul_eq_mul] at this
  rw [this]; ring

omit [FiniteDimensional ℂ W] in
/- English proof (translation)
Rewrite using `[KernSym.polyDeriv_eq_sum_list _ _ hF, KernSym.polyDeriv_eq_sum_list _ _ (F := fun p => c * F p) (analyticAt_const.mul hF), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `congrFun (lineDerivList_const_smul (List.map u (KernSym.lst m)) c F) 0` as an intermediate fact. Simplify using `only [smul_eq_mul] at this`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem polyDeriv_const_mul (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {F : W → ℂ}
    (hF : AnalyticAt ℂ F 0) : polyDeriv P u (fun p => c * F p) 0 = c * polyDeriv P u F 0 := by
  rw [KernSym.polyDeriv_eq_sum_list _ _ hF,
    KernSym.polyDeriv_eq_sum_list _ _ (F := fun p => c * F p) (analyticAt_const.mul hF),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have := congrFun (lineDerivList_const_smul (List.map u (KernSym.lst m)) c F) 0
  simp only [smul_eq_mul] at this
  rw [this]; ring

variable [StarAddMonoid W] [StarModule ℂ W] [ContinuousStar W]

/- English proof (translation)
Use `SCV.analyticAt_iff_eventually_differentiableAt.2 (.of_forall fun q => ?_)` and prove the remaining obligations. Simplify `(hh (star q)).differentiableAt.star_star` using `[Function.comp_def]`.
-/
theorem analyticAt_conj {h : W → ℂ} (hh : ∀ p, AnalyticAt ℂ h p) (p : W) :
    AnalyticAt ℂ (fun w => conj (h (star w))) p := by
  refine SCV.analyticAt_iff_eventually_differentiableAt.2 (.of_forall fun q => ?_)
  simpa [Function.comp_def] using (hh (star q)).differentiableAt.star_star

/- English proof (translation)
Establish `h1 : polyDeriv (barP Q) u (fun w => conj (h (star w))) 0 = conj (polyDeriv Q u h 0)`. Rewrite using `[KernSym.polyDeriv_eq_sum_list _ _ (analyticAt_conj hh 0), KernSym.polyDeriv_eq_sum_list _ _ (hh 0), map_sum, barP, MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[KernSym.lineDerivList_conj _ (by`. Simplify using `only [List.mem_map]`.

Introduce and unpack `v ⟨s, -, rfl⟩`. Conclude with `hu s), MvPolynomial.coeff_map, map_mul]`. Simplify using `only [star_zero]`. Simplify using `only [bd, polyDeriv_const_mul _ _ _ (analyticAt_conj hh 0), h1]`. Simplify using `only [mul_comm (f _)]`.

Rewrite using `[polyDeriv_const_mul _ _ _ (hf 0), mul_comm]`.
-/
theorem bd_prod (P Q : MvPolynomial σ ℂ) (u : σ → W) (hu : ∀ s, star (u s) = u s) {f h : W → ℂ}
    (hf : ∀ p, AnalyticAt ℂ f p) (hh : ∀ p, AnalyticAt ℂ h p) :
    bd P (barP Q) u (fun p => f p.1 * conj (h (star p.2))) =
      polyDeriv P u f 0 * conj (polyDeriv Q u h 0) := by
  have h1 : polyDeriv (barP Q) u (fun w => conj (h (star w))) 0 = conj (polyDeriv Q u h 0) := by
    rw [KernSym.polyDeriv_eq_sum_list _ _ (analyticAt_conj hh 0),
      KernSym.polyDeriv_eq_sum_list _ _ (hh 0), map_sum, barP,
      MvPolynomial.support_map_of_injective _ (starRingEnd ℂ).injective]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [KernSym.lineDerivList_conj _ (by
      simp only [List.mem_map]
      rintro v ⟨s, -, rfl⟩
      exact hu s), MvPolynomial.coeff_map, map_mul]
    simp only [star_zero]
  simp only [bd, polyDeriv_const_mul _ _ _ (analyticAt_conj hh 0), h1]
  simp only [mul_comm (f _)]
  rw [polyDeriv_const_mul _ _ _ (hf 0), mul_comm]

/- English proof (translation)
Establish `ha (τ) (z w z' w' : Fin g → ℂ) : KernSym.mixV X idx τ (z + z') (w + w') = KernSym.mixV X idx τ z w + KernSym.mixV X idx τ z' w'`. Apply the tactic sequence `funext a; simp only [KernSym.mixV, Pi.add_apply]; split_ifs <;> rfl`. Establish `hs (τ) (c : ℂ) (z w : Fin g → ℂ) : KernSym.mixV X idx τ (c • z) (c • w) = c • KernSym.mixV X idx τ z w`. Apply the tactic sequence `funext a; simp only [KernSym.mixV, Pi.smul_apply]; split_ifs <;> rfl`. Use `⟨∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹, LinearMap.mk₂ ℂ (fun p q => ∑ τ : X.Ψ, Real.pi * ∑ k, KernSym.mixV X idx τ (p.2 k) (p.1 k) ⬝ᵥ KernSym.kM X x₁ x₂ τ *ᵥ KernSym.mixV X idx τ (q.1 k) (q.2 k)) ?_ ?_ ?_ ?_, fun p => ?_⟩` and prove the remaining obligations.

Use `rotate_right`. Rewrite using `[KernSym.kZero_eq, Finset.prod_mul_distrib, ← Complex.exp_sum]`. Both sides reduce to the same expression. Introduce `p p' q`. Simplify using `only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, add_dotProduct, Finset.sum_add_distrib, mul_add]`.

Introduce `c p q`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hs, smul_dotProduct, smul_eq_mul, Finset.mul_sum, mul_left_comm c]`. Introduce `p q q'`. Simplify using `only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, mulVec_add, dotProduct_add, Finset.sum_add_distrib, mul_add]`. Introduce `c p q`.

Simplify using `only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hs, mulVec_smul, dotProduct_smul, smul_eq_mul, Finset.mul_sum, mul_left_comm c]`.
-/
theorem kZero_quad {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} (X : Data E r)
    (idx : Fin g ≃ X.Ψ × Fin r) (x₁ x₂ : Frame X.Ψ r) :
    ∃ (A : ℂ) (B : ((Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ)) →ₗ[ℂ]
      ((Fin n → Fin g → ℂ) × (Fin n → Fin g → ℂ)) →ₗ[ℂ] ℂ),
      ∀ p, kZero X idx x₁ x₂ p.1 p.2 = A * cexp (B p p) := by
  have ha (τ) (z w z' w' : Fin g → ℂ) : KernSym.mixV X idx τ (z + z') (w + w') =
      KernSym.mixV X idx τ z w + KernSym.mixV X idx τ z' w' := by
    funext a; simp only [KernSym.mixV, Pi.add_apply]; split_ifs <;> rfl
  have hs (τ) (c : ℂ) (z w : Fin g → ℂ) : KernSym.mixV X idx τ (c • z) (c • w) =
      c • KernSym.mixV X idx τ z w := by
    funext a; simp only [KernSym.mixV, Pi.smul_apply]; split_ifs <;> rfl
  refine ⟨∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹,
    LinearMap.mk₂ ℂ (fun p q => ∑ τ : X.Ψ, Real.pi * ∑ k,
    KernSym.mixV X idx τ (p.2 k) (p.1 k) ⬝ᵥ KernSym.kM X x₁ x₂ τ *ᵥ
      KernSym.mixV X idx τ (q.1 k) (q.2 k)) ?_ ?_ ?_ ?_, fun p => ?_⟩
  rotate_right
  · rw [KernSym.kZero_eq, Finset.prod_mul_distrib, ← Complex.exp_sum]
    rfl
  · intro p p' q
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, add_dotProduct,
      Finset.sum_add_distrib, mul_add]
  · intro c p q
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hs, smul_dotProduct, smul_eq_mul,
      Finset.mul_sum, mul_left_comm c]
  · intro p q q'
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ha, mulVec_add, dotProduct_add,
      Finset.sum_add_distrib, mul_add]
  · intro c p q
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, hs, mulVec_smul, dotProduct_smul,
      smul_eq_mul, Finset.mul_sum, mul_left_comm c]

end GlobalTheory.SW.KernSum
