import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ContinuousHerm
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.IteratedDerivZeroOfBound
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DifferentiableClassFunctionParam

noncomputable section

open MeasureTheory Matrix Filter Topology Metric

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z PositivityTheory.Rg.Sw.WR.T

/- English proof (translation)
Introduce `hBr hCD n m s hs hmn t ht β hβ`. Take `⟨-, hint⟩` from `hI n`. Take `⟨N₁, hN₁⟩` from `hCD n m s hs hmn`. Establish `hGN` using `fun N => hGain n s hs m 0 N 1`. Use `choose J a G hGc hGb hGeq using hGN`.

Use `choose CG hCG using hGb`. Establish `hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((m + 0 + N : ℕ) : ℝ) / 2))` using `fun N j y => by`. Use `hCG N j y` as an intermediate fact. Rewrite `this` using `[neg_div]`. Then use the resulting hypothesis. Use `set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK`.

Set `Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ` to `fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y`. Set `WN : ℕ → ℂ → ℂ` to `fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z`. Set `U : ℕ → Set ℂ` to `fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2}`. Set `orig : ℂ → ℂ` to `fun z => ∫ y, cls s z m 0 1 y * chr t β y`. Establish `hUopen : ∀ N, IsOpen (U N)` using `fun N => isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)`.

Establish `hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N)`. Introduce `N`. Use `DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _` and prove the remaining obligations. Conclude with `(a N j).differentiable.differentiableOn.mul (holo hI t β (hGc N j) (((m + 0 + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))`. Establish `hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2 → ∫ y, (Delta^[N] (cls s z m 0 1)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z`.

Introduce `N z hz`. Establish `e : (fun y => (Delta^[N] (cls s z m 0 1)) y * chr t β y) = fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y)`. Use function extensionality and compare the values at `y`. Rewrite using `[hGeq N z y, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.

Rewrite using `[e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[integral_const_mul]`. Establish `hgood : ∀ z : ℂ, (n : ℝ) ^ 2 / 2 < z.re → Good (cls (n` using `n) s z m 0 1) := by`. Introduce `z hz`.

Establish `hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2` using `by positivity`. Use `⟨(hB n s hs m 0 1 z).1, fun L => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `(hB n s hs m 0 1 z).2 L`. Conclude with `⟨fun y => C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2)), (hint _ (by linarith)).const_mul C, hC⟩`. Establish `hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z`.

Introduce `N z hz`. Establish `hz' : (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2`. Establish `: (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `show KK ^ N * _ = ∫ y, cls s z m 0 1 y * chr t β y`.

Rewrite using `[ibp_iter hIBP (hgood z hz) t β ht hβ N, hsum N z hz']`. Establish `agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N)`. Introduce `N N' hNN'`. Establish `hsub : U N ⊆ U N'` using `fun z hz => by`. Simplify using `only [U, Set.mem_ofPred_eq] at hz ⊢`.

Establish `: ((m + 0 + N : ℕ) : ℝ) ≤ ((m + 0 + N' : ℕ) : ℝ)` using `by exact_mod_cast (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA : AnalyticOnNhd ℂ (WN N) (U N)` using `(hWdiff N).analyticOnNhd (hUopen N)`. Establish `hA' : AnalyticOnNhd ℂ (WN N') (U N)` using `((hWdiff N').mono hsub).analyticOnNhd (hUopen N)`. Establish `hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((m + 0 + N : ℕ) : ℝ) / 2 < z.re}`.

Use extensionality with `z`. Simplify using `only [U, Set.mem_ofPred_eq]`. Apply the tactic sequence `constructor <;> intro h <;> linarith`. Establish `hpre : IsPreconnected (U N)`. Rewrite using `[hU]`.

Conclude with `(convex_halfSpace_re_gt _).isPreconnected`. Use `set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1`. Establish `hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1` using `by rw [hz1, Complex.ofReal_re]`. Establish `hz1U : z1 ∈ U N`. Simplify using `only [U, Set.mem_ofPred_eq, hz1re]`.

Establish `: (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re}`. Simplify using `only [Set.mem_ofPred_eq, hz1re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hev : WN N =ᶠ[𝓝 z1] WN N'` using `Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm`. Conclude with `hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev`. Establish `agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z`. Introduce `N N' z hz hz'`.

Break down `le_total N N' with h | h` into its components or cases. Conclude with `agree N N' h hz`. Conclude with `(agree N' N h hz').symm`. Take `⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1` from `⟨_, fun _ => rfl⟩`. Establish `hNf : ∀ z, z ∈ U (Nf z)`.

Introduce `z`. Use `show (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + Nf z : ℕ) : ℝ) / 2`. Rewrite using `[hNfdef z]`. Establish `h1` using `Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)`. Use `push_cast`.

Establish `: (0 : ℝ) ≤ (m : ℝ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set Ns : ℕ := max (n ^ 2 + 3) N₁ with hNs`. Establish `hdiv : DivZ (n - m) ((cayF (n` using `n) s m)^[Ns] 1) := hN₁ Ns (le_max_right _ _)`. Establish `hNs3 : ((n ^ 2 + 3 : ℕ) : ℝ) ≤ (Ns : ℝ)` using `by exact_mod_cast le_max_left _ _`.

Use `set κ : ℝ := ((m + 0 + Ns : ℕ) : ℝ) / 2 with hκ`. Establish `hκ1 : (n : ℝ) ^ 2 / 2 + 1 < κ`. Rewrite using `[hκ]`. Move the coercions through the operations in `at hNs3 ⊢`. Establish `: (0 : ℝ) ≤ (m : ℝ)` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hball : ball (0 : ℂ) 1 ⊆ U Ns`. Introduce `z hz`. Rewrite `hz` using `[mem_ball_zero_iff]`. Use `show (n : ℝ) ^ 2 / 2 < z.re + κ`.

Use `Complex.abs_re_le_norm z` as an intermediate fact. Use `neg_abs_le z.re` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨A, hA⟩ : ∃ A : ℝ, ∀ w ∈ closedBall (0 : ℂ) 1, ‖∑ j, ‖(a Ns j).eval w‖‖ ≤ A` from `(isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn (continuous_finsetSum _ fun j _ => (Polynomial.continuous _).norm).continuousOn`. Use `set CGp : ℝ := max (CG Ns) 0 with hCGp`.

Use `set M : E n → ℝ := fun y => A * CGp * (dP y ^ (1 - κ) + dP y ^ (-1 - κ)) with hM`. Establish `hMint : Integrable M`. Establish `h1` using `hint (κ - 1) (by linarith)`. Establish `h2` using `hint (κ + 1) (by linarith)`. Use `((h1.add h2).const_mul (A * CGp)).congr (ae_of_all _ fun y => ?_)` and prove the remaining obligations.

Simplify using `only [hM, Pi.add_apply]`. Apply the tactic sequence `congr 2 <;> congr 1 <;> ring`. Establish `hpt : ∀ (y : E n) (z : ℂ), ‖z‖ ≤ 1 → ‖(Delta^[Ns] (cls s z m 0 1)) y‖ ≤ ‖z‖ ^ (n - m) * M y`. Introduce `y z hz`. Take `⟨q, hqd, hq⟩` from `factor hE hCh hBr hs m Ns (n - m) hdiv y`.

Establish `hp` using `dP_pos hI y`. Establish `hcircle : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ (n - m) * q w‖ ≤ M y`. Introduce `w hw`. Rewrite using `[← hq w, hGeq Ns w y, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]`. Establish `hre : |w.re - 0| ≤ 1` using `by rw [sub_zero]; exact (Complex.abs_re_le_norm w).trans hw.le`.

Establish `r1` using `rpow_neg_le_add (dP y) w.re 0 1 hp hre`. Establish `hs1 : ‖∑ j, (a Ns j).eval w * G Ns j y‖ ≤ A * (CGp * dP y ^ (-κ))`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Establish `hb1 : ∀ j, ‖(a Ns j).eval w * G Ns j y‖ ≤ ‖(a Ns j).eval w‖ * (CGp * dP y ^ (-κ))`. Introduce `j`.

Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_left ((hCG' Ns j y).trans ?_) (norm_nonneg _)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _)`. Use `(Finset.sum_le_sum fun j _ => hb1 j).trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`.

Use `mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hp.le _))` and prove the remaining obligations. Use `hA w (by rw [mem_closedBall_zero_iff]; exact hw.le)` as an intermediate fact. Rewrite `this` using `[Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hM]`.

Establish `e1 : dP y ^ (-(0 - 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (1 - κ)`. Rewrite using `[← Real.rpow_add hp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : dP y ^ (-(0 + 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (-1 - κ)`.

Rewrite using `[← Real.rpow_add hp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only []`. Combine the equalities or inequalities in the displayed calculation.

Establish `hqz` using `norm_le_of_circle hqd hcircle hz`. Rewrite using `[hq z, norm_mul, norm_pow]`. Conclude with `mul_le_mul_of_nonneg_left hqz (by positivity)`. Establish `hWbound : ∀ z ∈ ball (0 : ℂ) 1, ‖WN Ns z‖ ≤ (‖KK‖ ^ Ns * ∫ y, M y) * ‖z‖ ^ (n - m)`. Introduce `z hz`.

Establish `hzU` using `hball hz`. Establish `hz1 : ‖z‖ ≤ 1` using `(mem_ball_zero_iff.1 hz).le`. Establish `e : WN Ns z = KK ^ Ns * ∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y` using `by show KK ^ Ns * _ = _`. Rewrite using `[hsum Ns z hzU]`. Rewrite using `[e, norm_mul, norm_pow]`.

Establish `hi : ‖∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y‖ ≤ ∫ y, ‖z‖ ^ (n - m) * M y`. Use `norm_integral_le_of_norm_le (hMint.const_mul _) (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_chr, mul_one]`. Conclude with `hpt y z hz1`. Rewrite `hi` using `[integral_const_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Introduce `z0`. Establish `hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0)` using `Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz`. Conclude with `(((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev`.

Take `⟨C, hC⟩` from `(hB n s hs m 0 1 z).2 []`. Establish `hC0 : ∀ y : E n, ‖cls s z m 0 1 y‖ ≤ C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2))`. Introduce `y`. Use `hC y` as an intermediate fact. Simplify using `using this`.

Establish `hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2` using `by positivity`. Use `Integrable.mono' ((hint (z.re + ((m : ℝ) + (0 : ℕ)) / 2) (by linarith)).const_mul C) (((hB n s hs m 0 1 z).1.continuous.mul (continuous_chr t β)).aestronglyMeasurable) (ae_of_all _ fun y => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_chr, mul_one]`. Conclude with `hC0 y`. Conclude with `hbig (Nf z) z hz`.

Introduce `j hj`. Establish `hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 0] WN Ns` using `Filter.eventuallyEq_of_mem ((hUopen Ns).mem_nhds (hball (mem_ball_self one_pos))) fun z hz => agree' _ _ z (hNf z) hz`. Rewrite using `[hev.iteratedDeriv_eq]`. Conclude with `iteratedDeriv_zero_of_bound one_pos ((hWdiff Ns).mono hball) hWbound hj`.
-/
theorem sPrime_of' (hB : ClsBound) (hGain : ClsGain) (hIBP : IBP) (hI : Integr) (hCh : Chain) (hE : Ext) :
    SPrimeOf := by
  intro hBr hCD n m s hs hmn t ht β hβ
  obtain ⟨-, hint⟩ := hI n
  obtain ⟨N₁, hN₁⟩ := hCD n m s hs hmn
  have hGN := fun N => hGain n s hs m 0 N 1
  choose J a G hGc hGb hGeq using hGN
  choose CG hCG using hGb
  have hCG' : ∀ N j y, ‖G N j y‖ ≤ CG N * dP y ^ (-(((m + 0 + N : ℕ) : ℝ) / 2)) := fun N j y => by
    have := hCG N j y
    rwa [neg_div] at this
  set KK : ℂ := (-1) ^ n * ((-(Complex.I * t)) ^ n * (herm β).det)⁻¹ with hKK
  let Fj : (N : ℕ) → Fin (J N) → ℂ → ℂ := fun N j z => ∫ y, ((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y
  let WN : ℕ → ℂ → ℂ := fun N z => KK ^ N * ∑ j, (a N j).eval z * Fj N j z
  let U : ℕ → Set ℂ := fun N => {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2}
  let orig : ℂ → ℂ := fun z => ∫ y, cls s z m 0 1 y * chr t β y
  have hUopen : ∀ N, IsOpen (U N) := fun N =>
    isOpen_lt continuous_const (Complex.continuous_re.add continuous_const)
  have hWdiff : ∀ N, DifferentiableOn ℂ (WN N) (U N) := by
    intro N
    refine DifferentiableOn.const_mul (DifferentiableOn.fun_sum fun j _ => ?_) _
    exact (a N j).differentiable.differentiableOn.mul
      (holo hI t β (hGc N j) (((m + 0 + N : ℕ) : ℝ) / 2) (CG N) (hCG' N j))
  have hsum : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2 →
      ∫ y, (Delta^[N] (cls s z m 0 1)) y * chr t β y = ∑ j, (a N j).eval z * Fj N j z := by
    intro N z hz
    have e : (fun y => (Delta^[N] (cls s z m 0 1)) y * chr t β y) =
        fun y => ∑ j, (a N j).eval z * (((dP y : ℝ) : ℂ) ^ (-z) * G N j y * chr t β y) := by
      funext y
      rw [hGeq N z y, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (integ_term hI t β (hGc N j) (hCG' N j) hz).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  have hgood : ∀ z : ℂ, (n : ℝ) ^ 2 / 2 < z.re → Good (cls (n := n) s z m 0 1) := by
    intro z hz
    have hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2 := by positivity
    refine ⟨(hB n s hs m 0 1 z).1, fun L => ?_⟩
    obtain ⟨C, hC⟩ := (hB n s hs m 0 1 z).2 L
    exact ⟨fun y => C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2)), (hint _ (by linarith)).const_mul C, hC⟩
  have hbig : ∀ N z, (n : ℝ) ^ 2 / 2 < z.re → WN N z = orig z := by
    intro N z hz
    have hz' : (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + N : ℕ) : ℝ) / 2 := by
      have : (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    show KK ^ N * _ = ∫ y, cls s z m 0 1 y * chr t β y
    rw [ibp_iter hIBP (hgood z hz) t β ht hβ N, hsum N z hz']
  have agree : ∀ N N', N ≤ N' → Set.EqOn (WN N) (WN N') (U N) := by
    intro N N' hNN'
    have hsub : U N ⊆ U N' := fun z hz => by
      simp only [U, Set.mem_ofPred_eq] at hz ⊢
      have : ((m + 0 + N : ℕ) : ℝ) ≤ ((m + 0 + N' : ℕ) : ℝ) := by exact_mod_cast (by omega)
      linarith
    have hA : AnalyticOnNhd ℂ (WN N) (U N) := (hWdiff N).analyticOnNhd (hUopen N)
    have hA' : AnalyticOnNhd ℂ (WN N') (U N) := ((hWdiff N').mono hsub).analyticOnNhd (hUopen N)
    have hU : U N = {z : ℂ | (n : ℝ) ^ 2 / 2 - ((m + 0 + N : ℕ) : ℝ) / 2 < z.re} := by
      ext z
      simp only [U, Set.mem_ofPred_eq]
      constructor <;> intro h <;> linarith
    have hpre : IsPreconnected (U N) := by
      rw [hU]; exact (convex_halfSpace_re_gt _).isPreconnected
    set z1 : ℂ := (((n : ℝ) ^ 2 / 2 + 1 : ℝ) : ℂ) with hz1
    have hz1re : z1.re = (n : ℝ) ^ 2 / 2 + 1 := by rw [hz1, Complex.ofReal_re]
    have hz1U : z1 ∈ U N := by
      simp only [U, Set.mem_ofPred_eq, hz1re]
      have : (0 : ℝ) ≤ ((m + 0 + N : ℕ) : ℝ) / 2 := by positivity
      linarith
    have hO : IsOpen {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hz1O : z1 ∈ {z : ℂ | (n : ℝ) ^ 2 / 2 < z.re} := by
      simp only [Set.mem_ofPred_eq, hz1re]; linarith
    have hev : WN N =ᶠ[𝓝 z1] WN N' :=
      Filter.eventuallyEq_of_mem (hO.mem_nhds hz1O) fun z hz => (hbig N z hz).trans (hbig N' z hz).symm
    exact hA.eqOn_of_preconnected_of_eventuallyEq hA' hpre hz1U hev
  have agree' : ∀ N N' z, z ∈ U N → z ∈ U N' → WN N z = WN N' z := by
    intro N N' z hz hz'
    rcases le_total N N' with h | h
    · exact agree N N' h hz
    · exact (agree N' N h hz').symm
  obtain ⟨Nf, hNfdef⟩ : ∃ Nf : ℂ → ℕ, ∀ z, Nf z = ⌈(n : ℝ) ^ 2 - 2 * z.re⌉₊ + 1 := ⟨_, fun _ => rfl⟩
  have hNf : ∀ z, z ∈ U (Nf z) := by
    intro z
    show (n : ℝ) ^ 2 / 2 < z.re + ((m + 0 + Nf z : ℕ) : ℝ) / 2
    rw [hNfdef z]
    have h1 := Nat.le_ceil ((n : ℝ) ^ 2 - 2 * z.re)
    push_cast
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith

  set Ns : ℕ := max (n ^ 2 + 3) N₁ with hNs
  have hdiv : DivZ (n - m) ((cayF (n := n) s m)^[Ns] 1) := hN₁ Ns (le_max_right _ _)
  have hNs3 : ((n ^ 2 + 3 : ℕ) : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast le_max_left _ _
  set κ : ℝ := ((m + 0 + Ns : ℕ) : ℝ) / 2 with hκ
  have hκ1 : (n : ℝ) ^ 2 / 2 + 1 < κ := by
    rw [hκ]; push_cast at hNs3 ⊢
    have : (0 : ℝ) ≤ (m : ℝ) := by positivity
    linarith
  have hball : ball (0 : ℂ) 1 ⊆ U Ns := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    show (n : ℝ) ^ 2 / 2 < z.re + κ
    have := Complex.abs_re_le_norm z
    have := neg_abs_le z.re
    linarith

  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ w ∈ closedBall (0 : ℂ) 1, ‖∑ j, ‖(a Ns j).eval w‖‖ ≤ A :=
    (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      (continuous_finsetSum _ fun j _ => (Polynomial.continuous _).norm).continuousOn
  set CGp : ℝ := max (CG Ns) 0 with hCGp
  set M : E n → ℝ := fun y => A * CGp * (dP y ^ (1 - κ) + dP y ^ (-1 - κ)) with hM
  have hMint : Integrable M := by
    have h1 := hint (κ - 1) (by linarith)
    have h2 := hint (κ + 1) (by linarith)
    refine ((h1.add h2).const_mul (A * CGp)).congr (ae_of_all _ fun y => ?_)
    simp only [hM, Pi.add_apply]
    congr 2 <;> congr 1 <;> ring
  have hpt : ∀ (y : E n) (z : ℂ), ‖z‖ ≤ 1 → ‖(Delta^[Ns] (cls s z m 0 1)) y‖ ≤ ‖z‖ ^ (n - m) * M y := by
    intro y z hz
    obtain ⟨q, hqd, hq⟩ := factor hE hCh hBr hs m Ns (n - m) hdiv y
    have hp := dP_pos hI y
    have hcircle : ∀ w : ℂ, ‖w‖ = 1 → ‖w ^ (n - m) * q w‖ ≤ M y := by
      intro w hw
      rw [← hq w, hGeq Ns w y, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.neg_re]
      have hre : |w.re - 0| ≤ 1 := by rw [sub_zero]; exact (Complex.abs_re_le_norm w).trans hw.le
      have r1 := rpow_neg_le_add (dP y) w.re 0 1 hp hre
      have hs1 : ‖∑ j, (a Ns j).eval w * G Ns j y‖ ≤ A * (CGp * dP y ^ (-κ)) := by
        refine (norm_sum_le _ _).trans ?_
        have hb1 : ∀ j, ‖(a Ns j).eval w * G Ns j y‖ ≤ ‖(a Ns j).eval w‖ * (CGp * dP y ^ (-κ)) := by
          intro j
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((hCG' Ns j y).trans ?_) (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _)
        refine (Finset.sum_le_sum fun j _ => hb1 j).trans ?_
        rw [← Finset.sum_mul]
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hp.le _))
        have := hA w (by rw [mem_closedBall_zero_iff]; exact hw.le)
        rwa [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at this
      calc dP y ^ (-w.re) * ‖∑ j, (a Ns j).eval w * G Ns j y‖
          ≤ (dP y ^ (-(0 - 1)) + dP y ^ (-(0 + 1))) * (A * (CGp * dP y ^ (-κ))) :=
            mul_le_mul r1 hs1 (norm_nonneg _) (by positivity)
        _ = M y := by
            rw [hM]
            have e1 : dP y ^ (-(0 - 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (1 - κ) := by
              rw [← Real.rpow_add hp]; congr 1; ring
            have e2 : dP y ^ (-(0 + 1 : ℝ)) * dP y ^ (-κ) = dP y ^ (-1 - κ) := by
              rw [← Real.rpow_add hp]; congr 1; ring
            simp only []
            calc (dP y ^ (-(0 - 1 : ℝ)) + dP y ^ (-(0 + 1 : ℝ))) * (A * (CGp * dP y ^ (-κ)))
                = A * CGp * (dP y ^ (-(0 - 1 : ℝ)) * dP y ^ (-κ) + dP y ^ (-(0 + 1 : ℝ)) * dP y ^ (-κ)) := by ring
              _ = _ := by rw [e1, e2]
    have hqz := norm_le_of_circle hqd hcircle hz
    rw [hq z, norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hqz (by positivity)
  have hWbound : ∀ z ∈ ball (0 : ℂ) 1, ‖WN Ns z‖ ≤ (‖KK‖ ^ Ns * ∫ y, M y) * ‖z‖ ^ (n - m) := by
    intro z hz
    have hzU := hball hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le
    have e : WN Ns z = KK ^ Ns * ∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y := by
      show KK ^ Ns * _ = _
      rw [hsum Ns z hzU]
    rw [e, norm_mul, norm_pow]
    have hi : ‖∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y‖ ≤ ∫ y, ‖z‖ ^ (n - m) * M y := by
      refine norm_integral_le_of_norm_le (hMint.const_mul _) (ae_of_all _ fun y => ?_)
      rw [norm_mul, norm_chr, mul_one]
      exact hpt y z hz1
    rw [integral_const_mul] at hi
    calc ‖KK‖ ^ Ns * ‖∫ y, (Delta^[Ns] (cls s z m 0 1)) y * chr t β y‖ ≤ ‖KK‖ ^ Ns * (‖z‖ ^ (n - m) * ∫ y, M y) :=
          mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by ring
  refine ⟨fun z => WN (Nf z) z, ?_, ⟨(n : ℝ) ^ 2 / 2, fun z hz => ⟨?_, ?_⟩⟩, ?_⟩
  · intro z0
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 z0] WN (Nf z0) :=
      Filter.eventuallyEq_of_mem ((hUopen (Nf z0)).mem_nhds (hNf z0)) fun z hz => agree' _ _ z (hNf z) hz
    exact (((hWdiff (Nf z0)).differentiableAt ((hUopen (Nf z0)).mem_nhds (hNf z0)))).congr_of_eventuallyEq hev
  · obtain ⟨C, hC⟩ := (hB n s hs m 0 1 z).2 []
    have hC0 : ∀ y : E n, ‖cls s z m 0 1 y‖ ≤ C * dP y ^ (-(z.re + ((m : ℝ) + (0 : ℕ)) / 2)) := by
      intro y
      have := hC y
      simpa using this
    have hm : (0 : ℝ) ≤ ((m : ℝ) + (0 : ℕ)) / 2 := by positivity
    refine Integrable.mono' ((hint (z.re + ((m : ℝ) + (0 : ℕ)) / 2) (by linarith)).const_mul C)
      (((hB n s hs m 0 1 z).1.continuous.mul (continuous_chr t β)).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, norm_chr, mul_one]
    exact hC0 y
  · exact hbig (Nf z) z hz
  · intro j hj
    have hev : (fun z => WN (Nf z) z) =ᶠ[𝓝 0] WN Ns :=
      Filter.eventuallyEq_of_mem ((hUopen Ns).mem_nhds (hball (mem_ball_self one_pos))) fun z hz =>
        agree' _ _ z (hNf z) hz
    rw [hev.iteratedDeriv_eq]
    exact iteratedDeriv_zero_of_bound one_pos ((hWdiff Ns).mono hball) hWbound hj

end PositivityTheory.Rg.Sw.SP
