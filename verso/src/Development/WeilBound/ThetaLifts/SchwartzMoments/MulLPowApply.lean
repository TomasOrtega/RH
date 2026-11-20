import Mathlib
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.NormIteratedFDerivCexpCompLe

noncomputable section

namespace PositivityTheory.ThKOwn

open Filter Topology Complex GlobalTheory.CompanionTheory.OM.SchDiff GlobalTheory.CompanionTheory.OM.GaussSch
open scoped SchwartzMap ContDiff

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def expo (L : V →L[ℝ] ℝ) (Q : V → ℂ) (q : ℂ × V) : ℂ := q.1 * (L q.2 : ℂ) + Q q.2

def mulL (L : V →L[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ fun x => ((L x : ℝ) : ℂ)

/- English proof (translation)
Establish `hT : (fun x => ((L x : ℝ) : ℂ)).HasTemperateGrowth` using `(Complex.ofRealCLM ∘L L).hasTemperateGrowth`. Rewrite using `[mulL, SchwartzMap.smulLeftCLM_apply_apply hT, smul_eq_mul]`.
-/
theorem mulL_apply (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) : mulL L f x = (L x : ℂ) * f x := by
  have hT : (fun x => ((L x : ℝ) : ℂ)).HasTemperateGrowth := (Complex.ofRealCLM ∘L L).hasTemperateGrowth
  rw [mulL, SchwartzMap.smulLeftCLM_apply_apply hT, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ', ContinuousLinearMap.mul_apply, mulL_apply, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulL_pow_apply (L : V →L[ℝ] ℝ) (m : ℕ) (f : 𝓢(V, ℂ)) (x : V) : (mulL L ^ m) f x = (L x : ℂ) ^ m * f x := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', ContinuousLinearMap.mul_apply, mulL_apply, ih]; ring

variable (L : V →L[ℝ] ℝ) {Q : V → ℂ} {w : ℝ}

/- English proof (translation)
The claim follows from `((ContinuousLinearMap.fst ℝ ℂ V).hasTemperateGrowth.mul (Complex.ofRealCLM ∘L L ∘L ContinuousLinearMap.snd ℝ ℂ V).hasTemperateGrowth).add (hQ.comp (ContinuousLinearMap.snd ℝ ℂ V).hasTemperateGrowth)`.
-/
theorem expo_tg (hQ : Q.HasTemperateGrowth) : (expo L Q).HasTemperateGrowth :=
  ((ContinuousLinearMap.fst ℝ ℂ V).hasTemperateGrowth.mul
    (Complex.ofRealCLM ∘L L ∘L ContinuousLinearMap.snd ℝ ℂ V).hasTemperateGrowth).add
    (hQ.comp (ContinuousLinearMap.snd ℝ ℂ V).hasTemperateGrowth)

/- English proof (translation)
Establish `h1 : (p * (L x : ℂ)).re ≤ R * ‖L‖ * ‖x‖`. Use `(Complex.re_le_norm _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, mul_assoc]`. Use `L.le_opNorm x` as an intermediate fact. Establish `h0` using `(norm_nonneg p).trans hp`.

Use `gcongr`. Establish `h2 : R * ‖L‖ * ‖x‖ ≤ (R * ‖L‖) ^ 2 / (2 * w) + w / 2 * ‖x‖ ^ 2`. Establish `: (R * ‖L‖) ^ 2 / (2 * w) + w / 2 * ‖x‖ ^ 2 - R * ‖L‖ * ‖x‖ = (R * ‖L‖ - w * ‖x‖) ^ 2 / (2 * w)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : 0 ≤ (R * ‖L‖ - w * ‖x‖) ^ 2 / (2 * w)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h3` using `hre x`. Simplify using `only [expo, Complex.add_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem expo_re (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) {R : ℝ} {p : ℂ} (hp : ‖p‖ ≤ R) (x : V) :
    (expo L Q (p, x)).re ≤ (R * ‖L‖) ^ 2 / (2 * w) + -(w / 2) * ‖x‖ ^ 2 := by
  have h1 : (p * (L x : ℂ)).re ≤ R * ‖L‖ * ‖x‖ := by
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, mul_assoc]
    have := L.le_opNorm x
    have h0 := (norm_nonneg p).trans hp
    gcongr
  have h2 : R * ‖L‖ * ‖x‖ ≤ (R * ‖L‖) ^ 2 / (2 * w) + w / 2 * ‖x‖ ^ 2 := by
    have : (R * ‖L‖) ^ 2 / (2 * w) + w / 2 * ‖x‖ ^ 2 - R * ‖L‖ * ‖x‖ = (R * ‖L‖ - w * ‖x‖) ^ 2 / (2 * w) := by
      field_simp
      ring
    have h3 : 0 ≤ (R * ‖L‖ - w * ‖x‖) ^ 2 / (2 * w) := by positivity
    linarith
  have h3 := hre x
  simp only [expo, Complex.add_re]
  linarith

/- English proof (translation)
Use `set B : ℝ := (‖z‖ * ‖L‖) ^ 2 / (2 * w)`. Establish `hq : (fun x => z * (L x : ℂ) + Q x + -(B : ℂ)).HasTemperateGrowth` using `(((Function.HasTemperateGrowth.const z).mul (Complex.ofRealCLM ∘L L).hasTemperateGrowth).add hQ).add (Function.HasTemperateGrowth.const _)`. Use `⟨cexp B • cexpSchwartz hq (half_pos hw) fun x => ?_, ?_⟩` and prove the remaining obligations. Use `expo_re L hw hre (le_refl ‖z‖) x` as an intermediate fact. Simplify using `only [expo] at this`.

Rewrite using `[Complex.add_re, Complex.neg_re, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `cexp B * cexp (z * (L x : ℂ) + Q x + -(B : ℂ)) = cexp (z * (L x : ℂ) + Q x)`. Rewrite using `[← Complex.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_family (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) (z : ℂ) :
    ∃ G : 𝓢(V, ℂ), ⇑G = fun x => (cexp ∘ expo L Q) (z, x) := by
  set B : ℝ := (‖z‖ * ‖L‖) ^ 2 / (2 * w)
  have hq : (fun x => z * (L x : ℂ) + Q x + -(B : ℂ)).HasTemperateGrowth :=
    (((Function.HasTemperateGrowth.const z).mul (Complex.ofRealCLM ∘L L).hasTemperateGrowth).add hQ).add
      (Function.HasTemperateGrowth.const _)
  refine ⟨cexp B • cexpSchwartz hq (half_pos hw) fun x => ?_, ?_⟩
  · have := expo_re L hw hre (le_refl ‖z‖) x
    simp only [expo] at this
    rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
    linarith
  · funext x
    change cexp B * cexp (z * (L x : ℂ) + Q x + -(B : ℂ)) = cexp (z * (L x : ℂ) + Q x)
    rw [← Complex.exp_add]
    congr 1
    ring

/- English proof (translation)
Take `⟨C, j, hC, hb⟩` from `norm_iteratedFDeriv_cexp_comp_le (expo_tg L hQ) n`. Use `set R : ℝ := ‖z‖ + 1`. Use `set B : ℝ := (R * ‖L‖) ^ 2 / (2 * w)`. Use `⟨C * (1 + R) ^ j * Real.exp B * Real.exp ((k + j : ℕ) ^ 2 / (4 * (w / 2))), fun p hp x => ?_⟩` and prove the remaining obligations. Establish `hp' : ‖p‖ ≤ R`.

Use `norm_add_le z (p - z)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR : 0 ≤ R` using `(norm_nonneg p).trans hp'`. Establish `h1 : 1 + ‖(p, x)‖ ≤ (1 + R) * (1 + ‖x‖)`.

Establish `: ‖(p, x)‖ ≤ ‖p‖ + ‖x‖`. Rewrite using `[Prod.norm_def]`. Conclude with `max_le (by simp) (by simp)`. Use polynomial arithmetic with `[mul_nonneg hR (norm_nonneg x)]`. Establish `h2` using `Real.exp_le_exp.2 (expo_re L hw hre hp' x)`.

Establish `h3` using `one_add_pow_mul_exp_le (half_pos hw) (norm_nonneg x) (k + j)`. Establish `h4 : ‖x‖ ≤ 1 + ‖x‖` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(hb _).trans (by gcongr)`. Use `_ = C * (1 + R) ^ j * Real.exp B * ((1 + ‖x‖) ^ (k + j) * Real.exp (-(w / 2) * ‖x‖ ^ 2)) := by`.

Rewrite using `[Real.exp_add, mul_pow, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by gcongr`.
-/
theorem family_bound (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2) (z : ℂ) (k n : ℕ) :
    ∃ C, ∀ p, ‖p - z‖ ≤ 1 → ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (cexp ∘ expo L Q) (p, x)‖ ≤ C := by
  obtain ⟨C, j, hC, hb⟩ := norm_iteratedFDeriv_cexp_comp_le (expo_tg L hQ) n
  set R : ℝ := ‖z‖ + 1
  set B : ℝ := (R * ‖L‖) ^ 2 / (2 * w)
  refine ⟨C * (1 + R) ^ j * Real.exp B * Real.exp ((k + j : ℕ) ^ 2 / (4 * (w / 2))), fun p hp x => ?_⟩
  have hp' : ‖p‖ ≤ R := by
    have := norm_add_le z (p - z)
    rw [add_sub_cancel] at this
    linarith
  have hR : 0 ≤ R := (norm_nonneg p).trans hp'
  have h1 : 1 + ‖(p, x)‖ ≤ (1 + R) * (1 + ‖x‖) := by
    have : ‖(p, x)‖ ≤ ‖p‖ + ‖x‖ := by
      rw [Prod.norm_def]
      exact max_le (by simp) (by simp)
    nlinarith [mul_nonneg hR (norm_nonneg x)]
  have h2 := Real.exp_le_exp.2 (expo_re L hw hre hp' x)
  have h3 := one_add_pow_mul_exp_le (half_pos hw) (norm_nonneg x) (k + j)
  have h4 : ‖x‖ ≤ 1 + ‖x‖ := by linarith
  calc _ ≤ (1 + ‖x‖) ^ k * (C * ((1 + R) * (1 + ‖x‖)) ^ j * Real.exp (B + -(w / 2) * ‖x‖ ^ 2)) := by
        gcongr
        exact (hb _).trans (by gcongr)
    _ = C * (1 + R) ^ j * Real.exp B * ((1 + ‖x‖) ^ (k + j) * Real.exp (-(w / 2) * ‖x‖ ^ 2)) := by
        rw [Real.exp_add, mul_pow, pow_add]; ring
    _ ≤ _ := by gcongr

/- English proof (translation)
Establish `hF : ContDiff ℝ ∞ (cexp ∘ expo L Q)` using `Complex.contDiff_exp.comp (expo_tg L hQ).1`. Establish `h` using `hasFDerivAt_family hF z (family_bound L hQ hw hre z) G (fun v => v • mulL L (G z)) hG (fun v => by`. Use function extensionality and compare the values at `x`. Establish `h1` using `(hF.differentiable (by simp) (z, x)).hasFDerivAt.hasLineDerivAt (v, 0)`. Establish `h2 : HasLineDerivAt ℝ (cexp ∘ expo L Q) (cexp (expo L Q (z, x)) * (v * L x)) (z, x) (v, 0)`.

Establish `a1 : HasDerivAt (fun t : ℝ => (z + (t : ℂ) * v) * (L x : ℂ) + Q x) (v * L x) 0`. Simplify using `using ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v).const_add z).mul_const (L x : ℂ)).add_const (Q x)`. Establish `a2` using `a1.cexp`. Simplify using `only [Complex.ofReal_zero, zero_mul, add_zero] at a2`. Use `a2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)` and prove the remaining obligations.

Simplify using `[expo]`. Rewrite using `[h1.unique h2, SchwartzMap.smul_apply, mulL_apply, hG]`. Simplify using `only [Function.comp, smul_eq_mul]`. Use the proof step `ring)`. Use `T ((ContinuousLinearMap.toSpanSingleton ℂ (T (mulL L (G z)))).restrictScalars ℝ) (fun v => by simp)`.

Conclude with `(hasFDerivAt_of_restrictScalars ℝ h rfl).hasDerivAt.congr_deriv (by simp)`.
-/
theorem family_deriv (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2)
    {G : ℂ → 𝓢(V, ℂ)} (hG : ∀ z, ⇑(G z) = fun x => (cexp ∘ expo L Q) (z, x)) (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (z : ℂ) :
    HasDerivAt (fun p => T (G p)) (T (mulL L (G z))) z := by
  have hF : ContDiff ℝ ∞ (cexp ∘ expo L Q) := Complex.contDiff_exp.comp (expo_tg L hQ).1
  have h := hasFDerivAt_family hF z (family_bound L hQ hw hre z) G (fun v => v • mulL L (G z)) hG
    (fun v => by
      funext x
      have h1 := (hF.differentiable (by simp) (z, x)).hasFDerivAt.hasLineDerivAt (v, 0)
      have h2 : HasLineDerivAt ℝ (cexp ∘ expo L Q) (cexp (expo L Q (z, x)) * (v * L x)) (z, x) (v, 0) := by
        have a1 : HasDerivAt (fun t : ℝ => (z + (t : ℂ) * v) * (L x : ℂ) + Q x) (v * L x) 0 := by
          simpa using ((((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const v).const_add z).mul_const (L x : ℂ)).add_const (Q x)
        have a2 := a1.cexp
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at a2
        refine a2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
        simp [expo]
      rw [h1.unique h2, SchwartzMap.smul_apply, mulL_apply, hG]
      simp only [Function.comp, smul_eq_mul]
      ring)
    T ((ContinuousLinearMap.toSpanSingleton ℂ (T (mulL L (G z)))).restrictScalars ℝ) (fun v => by simp)
  exact (hasFDerivAt_of_restrictScalars ℝ h rfl).hasDerivAt.congr_deriv (by simp)

/- English proof (translation)
Use `choose G hG using exists_family L hQ hw hre`. Establish `hd : ∀ (m : ℕ) p, HasDerivAt (fun p => T ((mulL L ^ m) (G p))) (T ((mulL L ^ (m + 1)) (G p))) p` using `fun m p => by`. Use `family_deriv L hQ hw hre hG (T ∘L mulL L ^ m) p` as an intermediate fact. Rewrite using `[pow_succ]`. Conclude with `this`.

Establish `hi : ∀ m : ℕ, iteratedDeriv m (fun p => T (G p)) = fun p => T ((mulL L ^ m) (G p))` using `fun m => by`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Use function extensionality and compare the values at `p`.

Rewrite using `[iteratedDeriv_succ, ih, (hd m p).deriv]`. Establish `h0 : G 0 = g`. Use extensionality with `x`. Simplify using `[hG, hg, expo]`. Establish `hz : G z = f`.

Use extensionality with `x`. Simplify using `[hG, hg, hf, expo, Complex.exp_add]`. Establish `hdiff : Differentiable ℂ fun p => T (G p)` using `fun p => by simpa using (hd 0 p).differentiableAt`. Use `Complex.taylorSeries_eq_of_entire' 0 z hdiff` as an intermediate fact. Simplify using `only [hi, h0, hT, mul_zero, zero_mul, tsum_zero, hz] at this`.

Conclude with `this.symm`.
-/
theorem kill_exp (hQ : Q.HasTemperateGrowth) (hw : 0 < w) (hre : ∀ x, (Q x).re ≤ -w * ‖x‖ ^ 2)
    {g : 𝓢(V, ℂ)} (hg : ∀ x, g x = cexp (Q x)) (T : 𝓢(V, ℂ) →L[ℂ] ℂ) (hT : ∀ m : ℕ, T ((mulL L ^ m) g) = 0)
    (z : ℂ) {f : 𝓢(V, ℂ)} (hf : ∀ x, f x = cexp (z * (L x : ℂ)) * g x) : T f = 0 := by
  choose G hG using exists_family L hQ hw hre
  have hd : ∀ (m : ℕ) p, HasDerivAt (fun p => T ((mulL L ^ m) (G p))) (T ((mulL L ^ (m + 1)) (G p))) p := fun m p => by
    have := family_deriv L hQ hw hre hG (T ∘L mulL L ^ m) p
    rw [pow_succ]
    exact this
  have hi : ∀ m : ℕ, iteratedDeriv m (fun p => T (G p)) = fun p => T ((mulL L ^ m) (G p)) := fun m => by
    induction m with
    | zero => simp
    | succ m ih =>
      funext p
      rw [iteratedDeriv_succ, ih, (hd m p).deriv]
  have h0 : G 0 = g := by
    ext x
    simp [hG, hg, expo]
  have hz : G z = f := by
    ext x
    simp [hG, hg, hf, expo, Complex.exp_add]
  have hdiff : Differentiable ℂ fun p => T (G p) := fun p => by simpa using (hd 0 p).differentiableAt
  have := Complex.taylorSeries_eq_of_entire' 0 z hdiff
  simp only [hi, h0, hT, mul_zero, zero_mul, tsum_zero, hz] at this
  exact this.symm

end PositivityTheory.ThKOwn

end
