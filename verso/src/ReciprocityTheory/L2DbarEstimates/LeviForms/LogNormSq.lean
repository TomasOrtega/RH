import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul

open Complex ComplexConjugate Filter Topology Matrix

namespace ReciprocityTheory.L2DbarEstimates

noncomputable def wJac (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) : Matrix (Fin p) (Fin n) ℂ :=
  fun i k => wd n k (g i) x

def LeviLogNormSqStatement : Prop :=
  ∀ (n p : ℕ) (g : Fin p → V n → ℂ) (x : V n) (ξ : Fin n → ℂ),
    (∀ i, ContDiffAt ℂ 2 (g i) x) → (fun i => g i x) ≠ 0 →
    leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((sqNorm (projPerp (fun i => g i x) *ᵥ (wJac n p g x *ᵥ ξ)) / sqNorm (fun i => g i x) : ℝ) : ℂ)

variable {n : ℕ}

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ 2 g x` using `hg.restrict_scalars ℝ`. Establish `h2 : (fun y => Complex.normSq (g y)) = fun y => ‖g y‖ ^ 2`. Use function extensionality and compare the values at `fun y => Complex.normSq_eq_norm_sq _`. Rewrite using `[h2]`. Conclude with `h1.norm_sq ℝ`.
-/
theorem contDiffAt_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    ContDiffAt ℝ 2 (fun y => Complex.normSq (g y)) x := by
  have h1 : ContDiffAt ℝ 2 g x := hg.restrict_scalars ℝ
  have h2 : (fun y => Complex.normSq (g y)) = fun y => ‖g y‖ ^ 2 :=
    funext fun y => Complex.normSq_eq_norm_sq _
  rw [h2]
  exact h1.norm_sq ℝ

/- English proof (translation)
Establish `hgC : DifferentiableAt ℂ g x` using `hg.differentiableAt (by norm_num)`. Establish `hgR : DifferentiableAt ℝ g x` using `hgC.restrictScalars ℝ`. Establish `hc : DifferentiableAt ℝ (fun y => conj (g y)) x` using `Complex.conjCLE.differentiableAt.comp x hgR`. Rewrite using `[show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from`. Use function extensionality and compare the values at `fun y => (Complex.mul_conj (g y)).symm, wd_mul hgR hc, wd_conj hgR,`.

Use `wdb_of_differentiableAt hgC, map_zero, mul_zero, add_zero]`.
-/
theorem wd_normSq_comp {j : Fin n} {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) :
    wd n j (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x = wd n j g x * conj (g x) := by
  have hgC : DifferentiableAt ℂ g x := hg.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := hgC.restrictScalars ℝ
  have hc : DifferentiableAt ℝ (fun y => conj (g y)) x := Complex.conjCLE.differentiableAt.comp x hgR
  rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
    funext fun y => (Complex.mul_conj (g y)).symm, wd_mul hgR hc, wd_conj hgR,
    wdb_of_differentiableAt hgC, map_zero, mul_zero, add_zero]

/- English proof (translation)
Establish `hcd : ∀ {f : V n → ℂ} {y : V n}, DifferentiableAt ℝ f y → DifferentiableAt ℝ (fun z => conj (f z)) y` using `fun h => Complex.conjCLE.differentiableAt.comp _ h`. Establish `hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ 2 g y` using `hg.eventually (by simp)`. Establish `hdC : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y` using `hev.mono fun y hy => hy.differentiableAt (by norm_num)`. Establish `hgR : DifferentiableAt ℝ g x` using `(hg.differentiableAt (by norm_num)).restrictScalars ℝ`. Establish `hwdk : ∀ k, wd n k g =ᶠ[𝓝 x] fun y => fderiv ℂ g y (bas n k)` using `fun k => hdC.mono fun y hy => wd_of_differentiableAt hy`.

Establish `hfd : ∀ k, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x`. Introduce `k`. Establish `h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x` using `hg.fderiv_right (by norm_num)`. Conclude with `(h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)`. Establish `hwdbwd : ∀ j k, wdb n j (wd n k g) x = 0` using `fun j k => (wdb_congr (hwdk k)).trans (wdb_of_differentiableAt (hfd k))`.

Establish `hwdR : ∀ k, DifferentiableAt ℝ (wd n k g) x` using `fun k => ((hfd k).restrictScalars ℝ).congr_of_eventuallyEq (hwdk k)`. Establish `hwdbf : ∀ k, wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x] fun y => g y * conj (wd n k g y)`. Introduce `k`. Use `filter_upwards [hev] with y hy`. Establish `hyC : DifferentiableAt ℂ g y` using `hy.differentiableAt (by norm_num)`.

Establish `hyR : DifferentiableAt ℝ g y` using `hyC.restrictScalars ℝ`. Rewrite using `[show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from`. Use function extensionality and compare the values at `fun y => (Complex.mul_conj (g y)).symm, wdb_mul hyR (hcd hyR), wdb_conj hyR,`. Use `wdb_of_differentiableAt hyC, zero_mul, zero_add]`. Establish `hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x = wd n j g x * conj (wd n k g x)`.

Introduce `j k`. Rewrite using `[wd_congr (hwdbf k), wd_mul hgR (hcd (hwdR k)), wd_conj (hwdR k), hwdbwd j k, map_zero, mul_zero, add_zero]`. Unfold `leviV`. Repeatedly rewrite using `[hterm]`. Rewrite using `[← Complex.mul_conj, map_sum, Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviV_normSq_comp {g : V n → ℂ} {x : V n} (hg : ContDiffAt ℂ 2 g x) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) x ξ =
      ((Complex.normSq (∑ j, wd n j g x * ξ j) : ℝ) : ℂ) := by
  have hcd : ∀ {f : V n → ℂ} {y : V n}, DifferentiableAt ℝ f y →
      DifferentiableAt ℝ (fun z => conj (f z)) y :=
    fun h => Complex.conjCLE.differentiableAt.comp _ h
  have hev : ∀ᶠ y in 𝓝 x, ContDiffAt ℂ 2 g y := hg.eventually (by simp)
  have hdC : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ g y :=
    hev.mono fun y hy => hy.differentiableAt (by norm_num)
  have hgR : DifferentiableAt ℝ g x := (hg.differentiableAt (by norm_num)).restrictScalars ℝ

  have hwdk : ∀ k, wd n k g =ᶠ[𝓝 x] fun y => fderiv ℂ g y (bas n k) :=
    fun k => hdC.mono fun y hy => wd_of_differentiableAt hy
  have hfd : ∀ k, DifferentiableAt ℂ (fun y => fderiv ℂ g y (bas n k)) x := by
    intro k
    have h1 : ContDiffAt ℂ 1 (fderiv ℂ g) x := hg.fderiv_right (by norm_num)
    exact (h1.differentiableAt (by norm_num)).clm_apply (differentiableAt_const _)
  have hwdbwd : ∀ j k, wdb n j (wd n k g) x = 0 :=
    fun j k => (wdb_congr (hwdk k)).trans (wdb_of_differentiableAt (hfd k))
  have hwdR : ∀ k, DifferentiableAt ℝ (wd n k g) x :=
    fun k => ((hfd k).restrictScalars ℝ).congr_of_eventuallyEq (hwdk k)
  have hwdbf : ∀ k, wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) =ᶠ[𝓝 x]
      fun y => g y * conj (wd n k g y) := by
    intro k
    filter_upwards [hev] with y hy
    have hyC : DifferentiableAt ℂ g y := hy.differentiableAt (by norm_num)
    have hyR : DifferentiableAt ℝ g y := hyC.restrictScalars ℝ
    rw [show (fun y => ((Complex.normSq (g y) : ℝ) : ℂ)) = fun y => g y * conj (g y) from
      funext fun y => (Complex.mul_conj (g y)).symm, wdb_mul hyR (hcd hyR), wdb_conj hyR,
      wdb_of_differentiableAt hyC, zero_mul, zero_add]
  have hterm : ∀ j k, wd n j (wdb n k (fun y => ((Complex.normSq (g y) : ℝ) : ℂ))) x =
      wd n j g x * conj (wd n k g x) := by
    intro j k
    rw [wd_congr (hwdbf k), wd_mul hgR (hcd (hwdR k)), wd_conj (hwdR k), hwdbwd j k, map_zero,
      mul_zero, add_zero]
  unfold leviV
  simp_rw [hterm]
  rw [← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul]
  ring

/- English proof (translation)
Introduce `n p g x ξ hg hG`. Use `set G : Fin p → ℂ := fun i => g i x with hGdef`. Establish `hpos : 0 < sqNorm G` using `sqNorm_pos hG`. Establish `hne : ((sqNorm G : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hpos.ne'`. Establish `hv : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x`.

Unfold `sqNorm`. Conclude with `ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hg i)`. Establish `hk : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x))` using `Real.contDiffAt_log.mpr hpos.ne'`. Establish `hc : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ = ((deriv Real.log (sqNorm G) : ℝ) : ℂ) * leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ + ((deriv (deriv Real.log) (sqNorm G) : ℝ) : ℂ) * ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun …` using `leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hv hk`. Establish `hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ = ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ)`.

Establish `h1 : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ = ∑ i, leviV n (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x ξ` using `leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y)) (fun i => contDiffAt_normSq_comp (hg i)) ξ`. Rewrite using `[h1, sqNorm, Complex.ofReal_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ`. Establish `hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x = ∑ i, wd n j (g i) x * conj (g i x)`. Introduce `j`.

Establish `h1 : wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x` using `wd_ofReal_sum (u := fun i y => Complex.normSq (g i y)) (fun i => (contDiffAt_normSq_comp (hg i)).differentiableAt (by norm_num))`. Rewrite using `[h1]`. Conclude with `Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)`. Establish `hS : ∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j = star G ⬝ᵥ (wJac n p g x *ᵥ ξ)`. Simplify using `only [hwd, dotProduct, Matrix.mulVec, wJac, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hGdef, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, hlv, hS, projPerp_sqNorm p G _ hG, Real.deriv_log, Real.deriv_log', deriv_inv]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviLogNormSq : LeviLogNormSqStatement := by
  intro n p g x ξ hg hG
  set G : Fin p → ℂ := fun i => g i x with hGdef
  have hpos : 0 < sqNorm G := sqNorm_pos hG
  have hne : ((sqNorm G : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hv : ContDiffAt ℝ 2 (fun y => sqNorm (fun i => g i y)) x := by
    unfold sqNorm
    exact ContDiffAt.sum fun i _ => contDiffAt_normSq_comp (hg i)
  have hk : ContDiffAt ℝ 2 Real.log (sqNorm (fun i => g i x)) := Real.contDiffAt_log.mpr hpos.ne'
  have hc : leviV n (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) x ξ =
      ((deriv Real.log (sqNorm G) : ℝ) : ℂ) *
          leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ +
        ((deriv (deriv Real.log) (sqNorm G) : ℝ) : ℂ) *
          ((Complex.normSq (∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j) :
            ℝ) : ℂ) :=
    leviChain n Real.log (fun y => sqNorm (fun i => g i y)) x ξ hv hk
  have hlv : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
      ((sqNorm (wJac n p g x *ᵥ ξ) : ℝ) : ℂ) := by
    have h1 : leviV n (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x ξ =
        ∑ i, leviV n (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x ξ :=
      leviV_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => contDiffAt_normSq_comp (hg i)) ξ
    rw [h1, sqNorm, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => leviV_normSq_comp (hg i) ξ
  have hwd : ∀ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
      ∑ i, wd n j (g i) x * conj (g i x) := by
    intro j
    have h1 : wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x =
        ∑ i, wd n j (fun y => ((Complex.normSq (g i y) : ℝ) : ℂ)) x :=
      wd_ofReal_sum (u := fun i y => Complex.normSq (g i y))
        (fun i => (contDiffAt_normSq_comp (hg i)).differentiableAt (by norm_num))
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => wd_normSq_comp (hg i)
  have hS : ∑ j, wd n j (fun y => ((sqNorm (fun i => g i y) : ℝ) : ℂ)) x * ξ j =
      star G ⬝ᵥ (wJac n p g x *ᵥ ξ) := by
    simp only [hwd, dotProduct, Matrix.mulVec, wJac, Pi.star_apply, Finset.sum_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hGdef, Complex.star_def]
    ring
  rw [hc, hlv, hS, projPerp_sqNorm p G _ hG, Real.deriv_log, Real.deriv_log', deriv_inv]
  push_cast
  field_simp
  ring

end ReciprocityTheory.L2DbarEstimates
