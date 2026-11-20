import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

noncomputable section

open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton Filter Topology
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.FSCrofton

variable {n : ℕ}

/- English proof (translation)
Establish `hv1 : DifferentiableAt ℝ v x` using `hv.differentiableAt (by simp)`. Establish `hk1 : DifferentiableAt ℝ (deriv k) (v x)` using `differentiableAt_deriv_of_contDiffAt hk`. Establish `hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x` using `Complex.ofRealCLM.contDiff.contDiffAt.comp x hv`. Establish `hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y` using `eventually_differentiableAt_of_contDiffAt hv`. Establish `hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y)` using `hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)`.

Establish `hE : wdb n c (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x] fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n c (fun y => ((v y : ℝ) : ℂ)) y` using `by filter_upwards [hvd, hkd] with y hy1 hy2`. Conclude with `wdb_ofReal_comp hy2 hy1`. Establish `hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x` using `differentiableAt_ofReal (hk1.comp x hv1)`. Rewrite using `[wd_congr hE, wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n c (fun y => ((v y : ℝ) : ℂ))) hD1 (differentiableAt_wdb hv'), wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]`.
-/
theorem hessLog_chain {k : ℝ → ℝ} {v : V n → ℝ} {x : V n} (hv : ContDiffAt ℝ 2 v x)
    (hk : ContDiffAt ℝ 2 k (v x)) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((k (v y) : ℝ) : ℂ))) x =
      ((deriv (deriv k) (v x) : ℝ) : ℂ) * wd n j (fun y => ((v y : ℝ) : ℂ)) x *
          conj (wd n c (fun y => ((v y : ℝ) : ℂ)) x) +
        ((deriv k (v x) : ℝ) : ℂ) * wd n j (wdb n c (fun y => ((v y : ℝ) : ℂ))) x := by
  have hv1 : DifferentiableAt ℝ v x := hv.differentiableAt (by simp)
  have hk1 : DifferentiableAt ℝ (deriv k) (v x) := differentiableAt_deriv_of_contDiffAt hk
  have hv' : ContDiffAt ℝ 2 (fun y => ((v y : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hv
  have hvd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ v y := eventually_differentiableAt_of_contDiffAt hv
  have hkd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ k (v y) :=
    hv1.continuousAt.tendsto.eventually (eventually_differentiableAt_of_contDiffAt hk)
  have hE : wdb n c (fun y => ((k (v y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => ((deriv k (v y) : ℝ) : ℂ) * wdb n c (fun y => ((v y : ℝ) : ℂ)) y := by
    filter_upwards [hvd, hkd] with y hy1 hy2
    exact wdb_ofReal_comp hy2 hy1
  have hD1 : DifferentiableAt ℝ (fun y => ((deriv k (v y) : ℝ) : ℂ)) x :=
    differentiableAt_ofReal (hk1.comp x hv1)
  rw [wd_congr hE,
    wd_mul (f := fun y => ((deriv k (v y) : ℝ) : ℂ)) (g := wdb n c (fun y => ((v y : ℝ) : ℂ)))
      hD1 (differentiableAt_wdb hv'),
    wd_ofReal_comp hk1 hv1, wdb_ofReal hv1]

/- English proof (translation)
Establish `hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y` using `(hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)`. Establish `hgx : DifferentiableAt ℂ g x` using `hg.differentiableAt (by simp)`. Establish `hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y)`. Use function extensionality and compare the values at `y`. Rewrite using `[Complex.mul_conj]`.

Establish `h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x` using `hg.fderiv_right (by norm_num)`. Establish `hh : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n c)) x` using `(h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)`. Establish `hE : wdb n c (fun y => g y * conj (g y)) =ᶠ[𝓝 x] fun y => g y * conj (fderiv ℂ g y (bas n c))` using `by filter_upwards [hgd] with y hy`. Rewrite using `[wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)), wdb_of_differentiableAt hy, wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hf, wd_congr hE, wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n c))) (hgx.restrictScalars ℝ) (differentiableAt_conj (hh.restrictScalars ℝ)), wd_conj (hh.restrictScalars ℝ), wdb_of_differentiableAt hh]`. Simplify using `[wd_of_differentiableAt hgx]`.
-/
theorem hessLog_normSq {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (j c : Fin n) :
    wd n j (wdb n c (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n c g x) := by
  have hgd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    (hg.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by simp)
  have hgx : DifferentiableAt ℂ g x := hg.differentiableAt (by simp)
  have hf : (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) := by
    funext y; rw [Complex.mul_conj]
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
  have hh : DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n c)) x :=
    (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
  have hE : wdb n c (fun y => g y * conj (g y)) =ᶠ[𝓝 x]
      fun y => g y * conj (fderiv ℂ g y (bas n c)) := by
    filter_upwards [hgd] with y hy
    rw [wdb_mul (hy.restrictScalars ℝ) (differentiableAt_conj (hy.restrictScalars ℝ)),
      wdb_of_differentiableAt hy, wdb_conj (hy.restrictScalars ℝ), wd_of_differentiableAt hy]
    ring
  rw [hf, wd_congr hE, wd_mul (f := g) (g := fun y => conj (fderiv ℂ g y (bas n c)))
    (hgx.restrictScalars ℝ) (differentiableAt_conj (hh.restrictScalars ℝ)),
    wd_conj (hh.restrictScalars ℝ), wdb_of_differentiableAt hh]
  simp [wd_of_differentiableAt hgx]

/- English proof (translation)
Introduce `d β _ U f hU hf z hz`. Establish `hC : ∀ j, ContDiffAt ℂ 2 (f j) z` using `fun j => ((contDiffOn_of_differentiableOn d (f j) U hU (hf j)).contDiffAt (hU.mem_nhds hz)).of_le ENat.LEInfty.out`. Establish `hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (f j y)) z` using `fun j => H.contDiffAt_normSq_comp (hC j)`. Establish `hu' : ∀ j, ContDiffAt ℝ 2 (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z` using `fun j => Complex.ofRealCLM.contDiff.contDiffAt.comp z (hu j)`. Establish `hnorm : ∀ v, (1 + ∑ j, ‖f j v‖ ^ 2 : ℝ) = 1 + ∑ j, Complex.normSq (f j v)` using `fun v => by`.

Simplify using `only [Complex.normSq_eq_norm_sq]`. Use `set S : V d → ℝ := fun y => 1 + ∑ j, Complex.normSq (f j y) with hSdef`. Establish `hSpos : 0 < S z` using `add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)`. Establish `hS : ContDiffAt ℝ 2 S z` using `contDiffAt_const.add (ContDiffAt.sum fun j _ => hu j)`. Establish `hlog : ContDiffAt ℝ 2 Real.log (S z)` using `Real.contDiffAt_log.2 hSpos.ne'`.

Establish `hSc : (fun y => ((S y : ℝ) : ℂ)) = fun y => 1 + ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ)`. Use function extensionality and compare the values at `y`. Simplify using `[hSdef]`. Establish `hTd : ∀ {y}, (∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y) → DifferentiableAt ℝ (fun y => ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ)) y` using `fun h => DifferentiableAt.fun_sum fun j _ => h j`. Establish `hwd : ∀ a, wd d a (fun y => ((S y : ℝ) : ℂ)) z = ∑ j, wd d a (f j) z * conj (f j z)` using `fun a => by`.

Establish `h1 : ∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z` using `fun j => (hu' j).differentiableAt (by simp)`. Rewrite using `[hSc, wd_add (differentiableAt_const _) (hTd h1), wd_sum Finset.univ fun j _ => h1 j]`. Simplify using `only [fun j => H.wd_normSq_comp (j := a) (hC j)]`. Simplify using `[wd]`. Establish `hhess : ∀ a c, wd d a (wdb d c (fun y => ((S y : ℝ) : ℂ))) z = ∑ j, wd d a (f j) z * conj (wd d c (f j) z)` using `fun a c => by`.

Establish `hev : wdb d c (fun y => ((S y : ℝ) : ℂ)) =ᶠ[𝓝 z] fun y => ∑ j, wdb d c (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y`. Establish `: ∀ᶠ y in 𝓝 z, ∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y`. Rewrite using `[Filter.eventually_all]`. Conclude with `fun j => eventually_differentiableAt_of_contDiffAt (hu' j)`. Use `filter_upwards [this] with y hy`.

Rewrite using `[hSc, wdb_add (differentiableAt_const _) (hTd hy), wdb_sum Finset.univ fun j _ => hy j]`. Simplify using `[wdb]`. Rewrite using `[wd_congr hev, wd_sum Finset.univ fun j _ => differentiableAt_wdb (hu' j)]`. Conclude with `Finset.sum_congr rfl fun j _ => hessLog_normSq (hC j) a c`. Establish `hd1 : deriv Real.log (S z) = (S z)⁻¹` using `by rw [Real.deriv_log']`.

Establish `hd2 : deriv (deriv Real.log) (S z) = -((S z) ^ 2)⁻¹`. Rewrite using `[Real.deriv_log']`. Conclude with `deriv_inv`. Establish `hS0 : ((S z : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hSpos.ne'`. Use extensionality with `a c`.

Establish `hfun : (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) = fun v => ((Real.log (S v) : ℝ) : ℂ)`. Use function extensionality and compare the values at `v`. Rewrite using `[hnorm]`. Establish `hF : ∀ (j : β) (a : Fin d), fderiv ℂ (f j) z (EuclideanSpace.single a 1) = wd d a (f j) z` using `fun j a => (wd_of_differentiableAt ((hC j).differentiableAt (by simp))).symm`. Establish `hval : ((1 + ∑ j, ‖f j z‖ ^ 2 : ℝ) : ℂ) = ((S z : ℝ) : ℂ)` using `by rw [hnorm]`.

Simplify using `only [cHess, fsLevi, Matrix.of_apply, hF, hfun, hval]`. Rewrite using `[hessLog_chain hS hlog a c, hd1, hd2, hwd a, hwd c, hhess a c, map_sum]`. Establish `hconj : ∑ j, conj (wd d c (f j) z * conj (f j z)) = ∑ j, f j z * conj (wd d c (f j) z)` using `Finset.sum_congr rfl fun j _ => by rw [map_mul, Complex.conj_conj, mul_comm]`. Rewrite using `[hconj]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cHess_log_one_add_sum : ∀ (d : ℕ) (β : Type) [Fintype β] (U : Set (V d)) (f : β → V d → ℂ),
    IsOpen U → (∀ j, DifferentiableOn ℂ (f j) U) → ∀ z ∈ U,
    cHess d (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) z =
      fsLevi (fun j => f j z) (Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)) := by
  intro d β _ U f hU hf z hz
  have hC : ∀ j, ContDiffAt ℂ 2 (f j) z := fun j =>
    ((contDiffOn_of_differentiableOn d (f j) U hU (hf j)).contDiffAt (hU.mem_nhds hz)).of_le
      ENat.LEInfty.out
  have hu : ∀ j, ContDiffAt ℝ 2 (fun y => Complex.normSq (f j y)) z := fun j =>
    H.contDiffAt_normSq_comp (hC j)
  have hu' : ∀ j, ContDiffAt ℝ 2 (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (hu j)
  have hnorm : ∀ v, (1 + ∑ j, ‖f j v‖ ^ 2 : ℝ) = 1 + ∑ j, Complex.normSq (f j v) := fun v => by
    simp only [Complex.normSq_eq_norm_sq]
  set S : V d → ℝ := fun y => 1 + ∑ j, Complex.normSq (f j y) with hSdef
  have hSpos : 0 < S z :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _)
  have hS : ContDiffAt ℝ 2 S z := contDiffAt_const.add (ContDiffAt.sum fun j _ => hu j)
  have hlog : ContDiffAt ℝ 2 Real.log (S z) := Real.contDiffAt_log.2 hSpos.ne'
  have hSc : (fun y => ((S y : ℝ) : ℂ)) =
      fun y => 1 + ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ) := by
    funext y; simp [hSdef]
  have hTd : ∀ {y}, (∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y) →
      DifferentiableAt ℝ (fun y => ∑ j, ((Complex.normSq (f j y) : ℝ) : ℂ)) y := fun h =>
    DifferentiableAt.fun_sum fun j _ => h j
  have hwd : ∀ a, wd d a (fun y => ((S y : ℝ) : ℂ)) z =
      ∑ j, wd d a (f j) z * conj (f j z) := fun a => by
    have h1 : ∀ j, DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) z := fun j =>
      (hu' j).differentiableAt (by simp)
    rw [hSc, wd_add (differentiableAt_const _) (hTd h1), wd_sum Finset.univ fun j _ => h1 j]
    simp only [fun j => H.wd_normSq_comp (j := a) (hC j)]
    simp [wd]
  have hhess : ∀ a c, wd d a (wdb d c (fun y => ((S y : ℝ) : ℂ))) z =
      ∑ j, wd d a (f j) z * conj (wd d c (f j) z) := fun a c => by
    have hev : wdb d c (fun y => ((S y : ℝ) : ℂ)) =ᶠ[𝓝 z]
        fun y => ∑ j, wdb d c (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
      have : ∀ᶠ y in 𝓝 z, ∀ j,
          DifferentiableAt ℝ (fun y => ((Complex.normSq (f j y) : ℝ) : ℂ)) y := by
        rw [Filter.eventually_all]
        exact fun j => eventually_differentiableAt_of_contDiffAt (hu' j)
      filter_upwards [this] with y hy
      rw [hSc, wdb_add (differentiableAt_const _) (hTd hy), wdb_sum Finset.univ fun j _ => hy j]
      simp [wdb]
    rw [wd_congr hev, wd_sum Finset.univ fun j _ => differentiableAt_wdb (hu' j)]
    exact Finset.sum_congr rfl fun j _ => hessLog_normSq (hC j) a c
  have hd1 : deriv Real.log (S z) = (S z)⁻¹ := by rw [Real.deriv_log']
  have hd2 : deriv (deriv Real.log) (S z) = -((S z) ^ 2)⁻¹ := by
    rw [Real.deriv_log']; exact deriv_inv
  have hS0 : ((S z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hSpos.ne'
  ext a c
  have hfun : (fun v => ((Real.log (1 + ∑ j, ‖f j v‖ ^ 2) : ℝ) : ℂ)) =
      fun v => ((Real.log (S v) : ℝ) : ℂ) := by
    funext v; rw [hnorm]
  have hF : ∀ (j : β) (a : Fin d), fderiv ℂ (f j) z (EuclideanSpace.single a 1) = wd d a (f j) z :=
    fun j a => (wd_of_differentiableAt ((hC j).differentiableAt (by simp))).symm
  have hval : ((1 + ∑ j, ‖f j z‖ ^ 2 : ℝ) : ℂ) = ((S z : ℝ) : ℂ) := by rw [hnorm]
  simp only [cHess, fsLevi, Matrix.of_apply, hF, hfun, hval]
  rw [hessLog_chain hS hlog a c, hd1, hd2, hwd a, hwd c, hhess a c, map_sum]
  have hconj : ∑ j, conj (wd d c (f j) z * conj (f j z)) = ∑ j, f j z * conj (wd d c (f j) z) :=
    Finset.sum_congr rfl fun j _ => by rw [map_mul, Complex.conj_conj, mul_comm]
  rw [hconj]
  push_cast
  field_simp
  ring

end GlobalTheory.CompanionTheory.FSCrofton
