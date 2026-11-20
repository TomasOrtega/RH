import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

noncomputable section

/- English proof (translation)
Establish `hk : ContDiffAt ℝ 2 (fun t : ℝ => c * t + d) (f x)` using `((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)`. Establish `h` using `leviChain n (fun t : ℝ => c * t + d) f x ξ hf hk`. Establish `hd : deriv (fun t : ℝ => c * t + d) = fun _ => c`. Use function extensionality and compare the values at `t`. Rewrite using `[deriv_add_const, deriv_const_mul_field', deriv_id'']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, hd]`. Simplify using the standard rewrite rules.
-/
theorem leviV_const_mul {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (c d : ℝ)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y + d : ℝ) : ℂ)) x ξ = c * leviV n (fun y => ((f y : ℝ) : ℂ)) x ξ := by
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => c * t + d) (f x) :=
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  have h := leviChain n (fun t : ℝ => c * t + d) f x ξ hf hk
  have hd : deriv (fun t : ℝ => c * t + d) = fun _ => c := by
    funext t; rw [deriv_add_const, deriv_const_mul_field', deriv_id'']; ring
  rw [h, hd]; simp

/- English proof (translation)
The claim follows from `((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hv)).of_le (by norm_cast)`.
-/
theorem contDiffAt_two_of_holo {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {v : V n} (hv : v ∈ U) : ContDiffAt ℂ 2 g v :=
  ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hv)).of_le (by norm_cast)

/- English proof (translation)
The claim follows from `(ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).restrict_scalars ℝ`.
-/
theorem contDiffOn_of_holo {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : ContDiffOn ℝ ∞ g U :=
  (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).restrict_scalars ℝ

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

def psD {N : ℕ} (L : La) (w : Fin N → ι → Y → ℂ) (s : Fin n → ι → Y → ℂ) (ps1 : Y → ℝ)
    (η δ : ℝ) (y : Y) : ℝ :=
  ps1 y + η * Real.log (A.sqn L w y) + n * Real.log (A.sqn L s y + δ)

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun k _ => by unfold nsq; positivity`.
-/
theorem aap_sqn_nonneg {N : ℕ} (la : La) (w : Fin N → ι → Y → ℂ) (y : Y) : 0 ≤ A.sqn la w y :=
  Finset.sum_nonneg fun k _ => by unfold nsq; positivity

/- English proof (translation)
Take `⟨k, hk⟩` from `hD.no_common_zero y`. Use `Finset.sum_pos' (fun j _ => by unfold nsq; positivity) ⟨k, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Unfold `nsq`. Use `norm_pos_iff.2 hk` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem aap_sqn_pos {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (y : Y) : 0 < A.sqn L w y := by
  obtain ⟨k, hk⟩ := hD.no_common_zero y
  refine Finset.sum_pos' (fun j _ => by unfold nsq; positivity) ⟨k, Finset.mem_univ _, ?_⟩
  unfold nsq; have := norm_pos_iff.2 hk; positivity

/- English proof (translation)
Establish `h` using `hs.1 i`. Simplify using `using h`.
-/
theorem holo_chart {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s) (i : ι) :
    DifferentiableOn ℂ (s i ∘ (A.chart i).symm) (A.chart i).target := by
  have h := hs.1 i; simpa using h

/- English proof (translation)
Introduce `i`. Use `set φ := A.chart i`. Establish `hb : ContDiffOn ℝ ∞ (fun v => A.ph L i (φ.symm v)) φ.target` using `A.smooth_ph L i`. Establish `hn2 : ∀ {m : ℕ} (u : Fin m → ι → Y → ℂ), (∀ k, A.IsSec L (u k)) → ContDiffOn ℝ ∞ (fun v => (∑ k, ‖u k i (φ.symm v)‖ ^ 2) * Real.exp (-A.ph L i (φ.symm v))) φ.target` using `fun u hu => (ContDiffOn.sum fun k _ => (contDiff_norm_sq ℝ).comp_contDiffOn (contDiffOn_of_holo φ.open_target (A.holo_chart (hu k) i))).mul (Real.contDiff_exp.comp_contDiffOn hb.neg)`. Establish `heq : ∀ v ∈ φ.target, (A.psD L w s ps1 η δ ∘ φ.symm) v = ps1 (φ.symm v) + η * Real.log ((∑ k, ‖w k i (φ.symm v)‖ ^ 2) * Real.exp (-A.ph L i (φ.symm v))) + n * Real.log ((∑ k, ‖s k i (φ.symm v)‖ ^ 2) * Real.exp (-A.ph L i (φ.symm v)) + δ)`.

Introduce `v hv`. Establish `hx` using `φ.map_target hv`. Simplify using `only [Function.comp, psD, A.sqn_chart L w hD.sec_w i hx, A.sqn_chart L s hD.sec_s i hx]`. Use `ContDiffOn.congr ?_ heq` and prove the remaining obligations. Use `((hps1 i).add (contDiffOn_const.mul ((hn2 w hD.sec_w).log ?_))).add (contDiffOn_const.mul (((hn2 s hD.sec_s).add contDiffOn_const).log ?_))` and prove the remaining obligations.

Introduce `v hv`. Establish `hx` using `φ.map_target hv`. Rewrite using `[← A.sqn_chart L w hD.sec_w i hx]`. Conclude with `(A.aap_sqn_pos hD _).ne'`. Introduce `v hv`.

Establish `hx` using `φ.map_target hv`. Rewrite using `[← A.sqn_chart L s hD.sec_s i hx]`. Use `A.aap_sqn_nonneg L s (φ.symm v)` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem psD_smooth {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) {ps1 : Y → ℝ} (hps1 : A.SmoothFn ps1)
    (η : ℝ) {δ : ℝ} (hδ : 0 < δ) : A.SmoothFn (A.psD L w s ps1 η δ) := by
  intro i
  set φ := A.chart i
  have hb : ContDiffOn ℝ ∞ (fun v => A.ph L i (φ.symm v)) φ.target := A.smooth_ph L i
  have hn2 : ∀ {m : ℕ} (u : Fin m → ι → Y → ℂ), (∀ k, A.IsSec L (u k)) →
      ContDiffOn ℝ ∞ (fun v => (∑ k, ‖u k i (φ.symm v)‖ ^ 2) * Real.exp (-A.ph L i (φ.symm v)))
        φ.target := fun u hu =>
    (ContDiffOn.sum fun k _ => (contDiff_norm_sq ℝ).comp_contDiffOn
      (contDiffOn_of_holo φ.open_target (A.holo_chart (hu k) i))).mul
      (Real.contDiff_exp.comp_contDiffOn hb.neg)
  have heq : ∀ v ∈ φ.target, (A.psD L w s ps1 η δ ∘ φ.symm) v =
      ps1 (φ.symm v) + η * Real.log ((∑ k, ‖w k i (φ.symm v)‖ ^ 2) *
        Real.exp (-A.ph L i (φ.symm v))) + n * Real.log ((∑ k, ‖s k i (φ.symm v)‖ ^ 2) *
        Real.exp (-A.ph L i (φ.symm v)) + δ) := by
    intro v hv
    have hx := φ.map_target hv
    simp only [Function.comp, psD, A.sqn_chart L w hD.sec_w i hx, A.sqn_chart L s hD.sec_s i hx]
  refine ContDiffOn.congr ?_ heq
  refine ((hps1 i).add (contDiffOn_const.mul ((hn2 w hD.sec_w).log ?_))).add
    (contDiffOn_const.mul (((hn2 s hD.sec_s).add contDiffOn_const).log ?_))
  · intro v hv
    have hx := φ.map_target hv
    rw [← A.sqn_chart L w hD.sec_w i hx]; exact (A.aap_sqn_pos hD _).ne'
  · intro v hv
    have hx := φ.map_target hv
    rw [← A.sqn_chart L s hD.sec_s i hx]; have := A.aap_sqn_nonneg L s (φ.symm v); positivity

/- English proof (translation)
Establish `h1` using `A.aap_sqn_pos hD y`. Establish `h2 : 0 < A.sqn L s y + δ` using `by have := A.aap_sqn_nonneg L s y; linarith`. Rewrite using `[Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`. Unfold `psD`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_neg_psD {N : ℕ} {L : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (ps1 : Y → ℝ) (η : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (y : Y) : Real.exp (-A.psD L w s ps1 η δ y) =
      Real.exp (-ps1 y) * A.sqn L w y ^ (-η) * (A.sqn L s y + δ) ^ (-(n : ℝ)) := by
  have h1 := A.aap_sqn_pos hD y
  have h2 : 0 < A.sqn L s y + δ := by have := A.aap_sqn_nonneg L s y; linarith
  rw [Real.rpow_def_of_pos h1, Real.rpow_def_of_pos h2, ← Real.exp_add, ← Real.exp_add]
  congr 1; unfold psD; ring

/- English proof (translation)
Use `set φ := A.chart i`. Use `set v0 := φ y`. Establish `hv0 : v0 ∈ φ.target` using `φ.map_source hy`. Establish `hT : φ.target ∈ 𝓝 v0` using `φ.open_target.mem_nhds hv0`. Establish `hsy : φ.symm v0 = y` using `φ.left_inv hy`.

Use `set a : V n → ℝ := fun v => A.ph (la - n • L) i (φ.symm v) + ps1 (φ.symm v)`. Use `set b : V n → ℝ := fun v => A.ph L i (φ.symm v)`. Use `set W : V n → ℝ := fun v => ∑ k, Complex.normSq (w k i (φ.symm v))`. Use `set Sv : V n → ℝ := fun v => Real.exp (b v + Real.log δ) + ∑ k, Complex.normSq (s k i (φ.symm v))`. Establish `hwC : ∀ k, ContDiffAt ℂ 2 (w k i ∘ φ.symm) v0` using `fun k => contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_w k) i) hv0`.

Establish `hsC : ∀ k, ContDiffAt ℂ 2 (s k i ∘ φ.symm) v0` using `fun k => contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_s k) i) hv0`. Establish `ha : ContDiffAt ℝ 2 a v0` using `(((A.smooth_ph (la - n • L) i).add (hps1 i)).contDiffAt hT).of_le (by norm_cast)`. Establish `hb : ContDiffAt ℝ 2 b v0` using `((A.smooth_ph L i).contDiffAt hT).of_le (by norm_cast)`. Establish `hW0 : 0 < W v0`. Establish `h` using `A.aap_sqn_pos hD y`.

Rewrite `h` using `[A.sqn_chart L w hD.sec_w i hy]`. Establish `h2 : 0 < ∑ k, ‖w k i y‖ ^ 2` using `pos_of_mul_pos_left h (Real.exp_pos _).le`. Simplify `h2` using `[W, hsy, Complex.normSq_eq_norm_sq]`. Establish `hS0 : 0 < Sv v0`. Use `Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v0))` as an intermediate fact.

Use `Real.exp_pos (b v0 + Real.log δ)` as an intermediate fact. Simplify using `only [Sv]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hWC : ContDiffAt ℝ 2 W v0` using `ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hwC k)`. Establish `hbd : ContDiffAt ℝ 2 (fun v => b v + Real.log δ) v0` using `hb.add contDiffAt_const`.

Establish `hSC : ContDiffAt ℝ 2 Sv v0` using `(Real.contDiff_exp.contDiffAt.comp v0 hbd).add (ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hsC k))`. Establish `hlW : ContDiffAt ℝ 2 (fun v => Real.log (W v)) v0` using `hWC.log hW0.ne'`. Establish `hlS : ContDiffAt ℝ 2 (fun v => Real.log (Sv v)) v0` using `hSC.log hS0.ne'`. Establish `hLW : 0 ≤ (leviV n (fun v => ((Real.log (W v) : ℝ) : ℂ)) v0 ξ).re` using `leviV_log_sum_nonneg (u := fun k v => Complex.normSq (w k i (φ.symm v))) (fun k => contDiffAt_normSq_comp (hwC k)) (fun k => logPshAt_normSq (hwC k)) hW0 ξ`. Establish `hPb : ∀ ζ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((b v + Real.log δ : ℝ) : ℂ)) v0 ζ).re`.

Introduce `ζ`. Establish `h1 : (fun v => ((b v + Real.log δ : ℝ) : ℂ)) = fun v => ((1 * b v + Real.log δ : ℝ) : ℂ)`. Simplify using the standard rewrite rules. Rewrite using `[h1, leviV_const_mul hb, Complex.ofReal_one, one_mul]`. Establish `h2` using `hPosL i y hy ζ`.

Simplify `h2` using `[leviAt]`. Establish `hLS : 0 ≤ (leviV n (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) v0 ξ).re` using `by set u : Fin (n + 1) → V n → ℝ := Fin.cons (fun v => Real.exp (b v + Real.log δ)) (fun k v => Complex.normSq (s k i (φ.symm v)))`. Establish `hsum : (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) = fun v => ((Real.log (∑ j, u j v) : ℝ) : ℂ)`. Use function extensionality and compare the values at `v`. Simplify using `[u, Sv, Fin.sum_univ_succ]`.

Rewrite using `[hsum]`. Use `leviV_log_sum_nonneg (fun j => ?_) (fun j => ?_) ?_ ξ` and prove the remaining obligations. Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact Real.contDiff_exp.contDiffAt.comp v0 hbd`. Consider the case `succ k => exact contDiffAt_normSq_comp (hsC k)`.

Consider the cases of `j using Fin.cases with`. Consider the case `zero => exact logPshAt_exp hbd hPb`. Consider the case `succ k => exact logPshAt_normSq (hsC k)`. Establish `: (∑ j, u j v0) = Sv v0` using `by simp [u, Sv, Fin.sum_univ_succ]`. Rewrite using `[this]`.

Conclude with `hS0`. Establish `hev : (fun v => ((A.ph la i (φ.symm v) + A.psD L w s ps1 η δ (φ.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0] fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) + (n * Real.log (Sv v) + 0) : ℝ) : ℂ)` using `by filter_upwards [hT] with v hv`. Establish `hx` using `φ.map_target hv`. Establish `hWv : A.sqn L w (φ.symm v) = W v * Real.exp (-b v)`. Rewrite using `[A.sqn_chart L w hD.sec_w i hx]`.

Simplify using `[W, b, Complex.normSq_eq_norm_sq]`. Establish `hSv : A.sqn L s (φ.symm v) + δ = Real.exp (-b v) * Sv v`. Rewrite using `[A.sqn_chart L s hD.sec_s i hx]`. Simplify using `only [Sv, b, Complex.normSq_eq_norm_sq, mul_add, Real.exp_add, Real.exp_log hδ]`. Rewrite using `[← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hWp : 0 < W v`. Establish `h` using `A.aap_sqn_pos hD (φ.symm v)`. Rewrite `h` using `[hWv]`. Conclude with `pos_of_mul_pos_left h (Real.exp_pos _).le`.

Establish `hSp : 0 < Sv v`. Use `Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v))` as an intermediate fact. Use `Real.exp_pos (b v + Real.log δ)` as an intermediate fact. Simplify using `only [Sv]`. Combine the linear equalities and inequalities to obtain the conclusion.

Unfold `psD`. Rewrite using `[hWv, hSv, Real.log_mul hWp.ne' (Real.exp_pos _).ne', Real.log_mul (Real.exp_pos _).ne' hSp.ne', Real.log_exp, A.ph_eq_sub_nsmul la L n i hx]`. Simplify using `only [a, b]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `set u4 : Fin 4 → V n → ℝ := ![a, fun v => (-η) * b v + 0, fun v => η * Real.log (W v) + 0, fun v => n * Real.log (Sv v) + 0]`. Establish `hu4 : ∀ j, ContDiffAt ℝ 2 (u4 j) v0`. Introduce `j`. Use `fin_cases j`. Conclude with `ha`.

Conclude with `(contDiffAt_const.mul hb).add contDiffAt_const`. Conclude with `(contDiffAt_const.mul hlW).add contDiffAt_const`. Conclude with `(contDiffAt_const.mul hlS).add contDiffAt_const`. Establish `hfun : (fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) + (n * Real.log (Sv v) + 0) : ℝ) : ℂ)) = fun v => ((∑ j, u4 j v : ℝ) : ℂ)`. Use function extensionality and compare the values at `v`.

Simplify using `[u4, Fin.sum_univ_four]`. Establish `hL` using `hLevi i y hy ξ`. Unfold `leviAt at hL ⊢`. Rewrite using `[leviV_congr hev, hfun, leviV_ofReal_sum hu4, Fin.sum_univ_four]`. Establish `e1 : u4 0 = a` using `rfl`.

Establish `e2 : u4 1 = fun v => (-η) * b v + 0` using `rfl`. Establish `e3 : u4 2 = fun v => η * Real.log (W v) + 0` using `rfl`. Establish `e4 : u4 3 = fun v => n * Real.log (Sv v) + 0` using `rfl`. Rewrite using `[e1, e2, e3, e4, leviV_const_mul hb, leviV_const_mul hlW, leviV_const_mul hlS]`. Simplify using `only [Complex.add_re, Complex.re_ofReal_mul]`.

Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Use `mul_nonneg hη.le hLW` as an intermediate fact. Use `mul_nonneg hn0 hLS` as an intermediate fact. Express the relevant statement in the definitionally equal form `η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ _`. Express the relevant statement in the definitionally equal form `2 * η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ (leviV n (fun v => ((a v : ℝ) : ℂ)) v0 ξ).re at hL`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem levi_psD {N : ℕ} {L la : La} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ}
    {s : Fin n → ι → Y → ℂ} (hD : A.D0 L w w0 s) (hPosL : A.Pos L fun _ => 0)
    {ps1 : Y → ℝ} (hps1 : A.SmoothFn ps1) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ)
    (hLevi : ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      2 * η * A.leviAt i (A.ph L i) y ξ ≤
        A.leviAt i (fun x => A.ph (la - n • L) i x + ps1 x) y ξ)
    (i : ι) {y : Y} (hy : y ∈ (A.chart i).source) (ξ : Fin n → ℂ) :
    η * A.leviAt i (A.ph L i) y ξ ≤
      A.leviAt i (fun x => A.ph la i x + A.psD L w s ps1 η δ x) y ξ := by
  set φ := A.chart i
  set v0 := φ y
  have hv0 : v0 ∈ φ.target := φ.map_source hy
  have hT : φ.target ∈ 𝓝 v0 := φ.open_target.mem_nhds hv0
  have hsy : φ.symm v0 = y := φ.left_inv hy
  set a : V n → ℝ := fun v => A.ph (la - n • L) i (φ.symm v) + ps1 (φ.symm v)
  set b : V n → ℝ := fun v => A.ph L i (φ.symm v)
  set W : V n → ℝ := fun v => ∑ k, Complex.normSq (w k i (φ.symm v))
  set Sv : V n → ℝ := fun v => Real.exp (b v + Real.log δ) + ∑ k, Complex.normSq (s k i (φ.symm v))
  have hwC : ∀ k, ContDiffAt ℂ 2 (w k i ∘ φ.symm) v0 := fun k =>
    contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_w k) i) hv0
  have hsC : ∀ k, ContDiffAt ℂ 2 (s k i ∘ φ.symm) v0 := fun k =>
    contDiffAt_two_of_holo φ.open_target (A.holo_chart (hD.sec_s k) i) hv0
  have ha : ContDiffAt ℝ 2 a v0 :=
    (((A.smooth_ph (la - n • L) i).add (hps1 i)).contDiffAt hT).of_le (by norm_cast)
  have hb : ContDiffAt ℝ 2 b v0 := ((A.smooth_ph L i).contDiffAt hT).of_le (by norm_cast)
  have hW0 : 0 < W v0 := by
    have h := A.aap_sqn_pos hD y
    rw [A.sqn_chart L w hD.sec_w i hy] at h
    have h2 : 0 < ∑ k, ‖w k i y‖ ^ 2 := pos_of_mul_pos_left h (Real.exp_pos _).le
    simpa [W, hsy, Complex.normSq_eq_norm_sq] using h2
  have hS0 : 0 < Sv v0 := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v0))
    have := Real.exp_pos (b v0 + Real.log δ); simp only [Sv]; linarith
  have hWC : ContDiffAt ℝ 2 W v0 := ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hwC k)
  have hbd : ContDiffAt ℝ 2 (fun v => b v + Real.log δ) v0 := hb.add contDiffAt_const
  have hSC : ContDiffAt ℝ 2 Sv v0 :=
    (Real.contDiff_exp.contDiffAt.comp v0 hbd).add
      (ContDiffAt.sum fun k _ => contDiffAt_normSq_comp (hsC k))
  have hlW : ContDiffAt ℝ 2 (fun v => Real.log (W v)) v0 := hWC.log hW0.ne'
  have hlS : ContDiffAt ℝ 2 (fun v => Real.log (Sv v)) v0 := hSC.log hS0.ne'

  have hLW : 0 ≤ (leviV n (fun v => ((Real.log (W v) : ℝ) : ℂ)) v0 ξ).re :=
    leviV_log_sum_nonneg (u := fun k v => Complex.normSq (w k i (φ.symm v)))
      (fun k => contDiffAt_normSq_comp (hwC k)) (fun k => logPshAt_normSq (hwC k)) hW0 ξ
  have hPb : ∀ ζ : Fin n → ℂ, 0 ≤ (leviV n (fun v => ((b v + Real.log δ : ℝ) : ℂ)) v0 ζ).re := by
    intro ζ
    have h1 : (fun v => ((b v + Real.log δ : ℝ) : ℂ)) = fun v => ((1 * b v + Real.log δ : ℝ) : ℂ) := by
      simp
    rw [h1, leviV_const_mul hb, Complex.ofReal_one, one_mul]
    have h2 := hPosL i y hy ζ
    simpa [leviAt] using h2
  have hLS : 0 ≤ (leviV n (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) v0 ξ).re := by
    set u : Fin (n + 1) → V n → ℝ :=
      Fin.cons (fun v => Real.exp (b v + Real.log δ)) (fun k v => Complex.normSq (s k i (φ.symm v)))
    have hsum : (fun v => ((Real.log (Sv v) : ℝ) : ℂ)) = fun v => ((Real.log (∑ j, u j v) : ℝ) : ℂ) := by
      funext v; simp [u, Sv, Fin.sum_univ_succ]
    rw [hsum]
    refine leviV_log_sum_nonneg (fun j => ?_) (fun j => ?_) ?_ ξ
    · cases j using Fin.cases with
      | zero => exact Real.contDiff_exp.contDiffAt.comp v0 hbd
      | succ k => exact contDiffAt_normSq_comp (hsC k)
    · cases j using Fin.cases with
      | zero => exact logPshAt_exp hbd hPb
      | succ k => exact logPshAt_normSq (hsC k)
    · have : (∑ j, u j v0) = Sv v0 := by simp [u, Sv, Fin.sum_univ_succ]
      rw [this]; exact hS0

  have hev : (fun v => ((A.ph la i (φ.symm v) + A.psD L w s ps1 η δ (φ.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 v0]
      fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) + (n * Real.log (Sv v) + 0) : ℝ) : ℂ) := by
    filter_upwards [hT] with v hv
    have hx := φ.map_target hv
    have hWv : A.sqn L w (φ.symm v) = W v * Real.exp (-b v) := by
      rw [A.sqn_chart L w hD.sec_w i hx]; simp [W, b, Complex.normSq_eq_norm_sq]
    have hSv : A.sqn L s (φ.symm v) + δ = Real.exp (-b v) * Sv v := by
      rw [A.sqn_chart L s hD.sec_s i hx]
      simp only [Sv, b, Complex.normSq_eq_norm_sq, mul_add, Real.exp_add, Real.exp_log hδ]
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]; ring
    have hWp : 0 < W v := by
      have h := A.aap_sqn_pos hD (φ.symm v); rw [hWv] at h
      exact pos_of_mul_pos_left h (Real.exp_pos _).le
    have hSp : 0 < Sv v := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => Complex.normSq_nonneg (s k i (φ.symm v))
      have := Real.exp_pos (b v + Real.log δ); simp only [Sv]; linarith
    unfold psD
    rw [hWv, hSv, Real.log_mul hWp.ne' (Real.exp_pos _).ne', Real.log_mul (Real.exp_pos _).ne' hSp.ne',
      Real.log_exp, A.ph_eq_sub_nsmul la L n i hx]
    simp only [a, b]; push_cast; ring
  set u4 : Fin 4 → V n → ℝ := ![a, fun v => (-η) * b v + 0,
      fun v => η * Real.log (W v) + 0, fun v => n * Real.log (Sv v) + 0]
  have hu4 : ∀ j, ContDiffAt ℝ 2 (u4 j) v0 := by
    intro j
    fin_cases j
    · exact ha
    · exact (contDiffAt_const.mul hb).add contDiffAt_const
    · exact (contDiffAt_const.mul hlW).add contDiffAt_const
    · exact (contDiffAt_const.mul hlS).add contDiffAt_const
  have hfun : (fun v => ((a v + ((-η) * b v + 0) + (η * Real.log (W v) + 0) +
      (n * Real.log (Sv v) + 0) : ℝ) : ℂ)) = fun v => ((∑ j, u4 j v : ℝ) : ℂ) := by
    funext v; simp [u4, Fin.sum_univ_four]
  have hL := hLevi i y hy ξ
  unfold leviAt at hL ⊢
  rw [leviV_congr hev, hfun, leviV_ofReal_sum hu4, Fin.sum_univ_four]
  have e1 : u4 0 = a := rfl
  have e2 : u4 1 = fun v => (-η) * b v + 0 := rfl
  have e3 : u4 2 = fun v => η * Real.log (W v) + 0 := rfl
  have e4 : u4 3 = fun v => n * Real.log (Sv v) + 0 := rfl
  rw [e1, e2, e3, e4, leviV_const_mul hb, leviV_const_mul hlW, leviV_const_mul hlS]
  simp only [Complex.add_re, Complex.re_ofReal_mul]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have := mul_nonneg hη.le hLW
  have := mul_nonneg hn0 hLS
  change η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ _
  change 2 * η * (leviV n (fun v => ((b v : ℝ) : ℂ)) v0 ξ).re ≤ (leviV n (fun v => ((a v : ℝ) : ℂ)) v0 ξ).re at hL
  linarith

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
