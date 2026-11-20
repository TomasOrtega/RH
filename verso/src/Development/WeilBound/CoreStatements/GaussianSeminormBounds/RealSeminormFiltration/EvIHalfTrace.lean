import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.WeilBound.ThetaLifts.SchwartzMoments.SchwartzDqTendsto
import Development.WeilBound.ThetaLifts.SchwartzMoments.NormIterComp

noncomputable section

open scoped TensorProduct Matrix SchwartzMap LineDeriv
open NumberField Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace PositivityTheory.RL.Der

section Line
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def hl (a : V) (L : V →L[ℝ] ℝ) (t : ℝ) (f : V → ℂ) (x : V) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * (L a / 2) : ℝ) : ℂ)) * f (x + t • a)

def dop (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ L f

/- English proof (translation)
Establish `hT` using `L.hasTemperateGrowth`. Simplify using `only [dop, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT, SchwartzMap.lineDerivOp_apply_eq_fderiv]`. Simplify using `only [Complex.real_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dop_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    dop a L f x = fderiv ℝ f x a + (-(2 * Real.pi * Complex.I) * (L x : ℂ)) * f x := by
  have hT := L.hasTemperateGrowth
  simp only [dop, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t : ℝ => t * L x + t ^ 2 * (L a / 2)) (L x) 0`. Establish `a1 : HasDerivAt (fun t : ℝ => t * L x) (L x) 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (L x)`. Establish `a2 : HasDerivAt (fun t : ℝ => t ^ 2 * (L a / 2)) 0 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (L a / 2)`. Simplify using `using a1.fun_add a2`.

Establish `h2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * (L a / 2) : ℝ) : ℂ))) (-(2 * Real.pi * Complex.I) * (L x : ℂ)) 0`. Use `((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp` as an intermediate fact. Simplify using `using this`. Establish `h3 : HasDerivAt (fun t : ℝ => x + t • a) a 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x`.

Establish `h4 : HasDerivAt (fun t : ℝ => f (x + t • a)) (fderiv ℝ f x a) 0`. Establish `hf : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • a)`. Simplify using `using f.hasFDerivAt x`. Conclude with `hf.comp_hasDerivAt (0 : ℝ) h3`. Use `(h2.fun_mul h4).congr_deriv ?_` and prove the remaining obligations.

Rewrite using `[dop_apply]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hasDerivAt_hl (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (x : V) :
    HasDerivAt (fun t : ℝ => hl a L t f x) (dop a L f x) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * L x + t ^ 2 * (L a / 2)) (L x) 0 := by
    have a1 : HasDerivAt (fun t : ℝ => t * L x) (L x) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (L x)
    have a2 : HasDerivAt (fun t : ℝ => t ^ 2 * (L a / 2)) 0 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (L a / 2)
    simpa using a1.fun_add a2
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * ((t * L x + t ^ 2 * (L a / 2) : ℝ) : ℂ)))
      (-(2 * Real.pi * Complex.I) * (L x : ℂ)) 0 := by
    have := ((h1.ofReal_comp).const_mul (-(2 * Real.pi * Complex.I))).cexp
    simpa using this
  have h3 : HasDerivAt (fun t : ℝ => x + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x
  have h4 : HasDerivAt (fun t : ℝ => f (x + t • a)) (fderiv ℝ f x a) 0 := by
    have hf : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • a) := by
      simpa using f.hasFDerivAt x
    exact hf.comp_hasDerivAt (0 : ℝ) h3
  refine (h2.fun_mul h4).congr_deriv ?_
  rw [dop_apply]
  simp
  ring
end Line

open Complex in

/- English proof (translation)
Establish `hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use function extensionality and compare the values at `t`. Rewrite using `[iteratedDeriv_succ, ih]`. Establish `: HasDerivAt (fun t : ℝ => I ^ n * cexp (I * t)) (I ^ n * (cexp (I * t) * (I * 1))) t` using `(((hasDerivAt_id (t : ℂ)).const_mul I).cexp.const_mul _).comp_ofReal`. Rewrite using `[this.deriv]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff), fun n => ⟨0, 1, fun t => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]`. Simplify using the standard rewrite rules.
-/
theorem temperate_exp : Function.HasTemperateGrowth (fun t : ℝ => cexp (I * t)) := by
  have hd : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => cexp (I * t)) = fun t : ℝ => I ^ n * cexp (I * t) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have : HasDerivAt (fun t : ℝ => I ^ n * cexp (I * t)) (I ^ n * (cexp (I * t) * (I * 1))) t :=
        (((hasDerivAt_id (t : ℂ)).const_mul I).cexp.const_mul _).comp_ofReal
      rw [this.deriv]; ring
  refine ⟨Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff),
    fun n => ⟨0, 1, fun t => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hd, norm_mul, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_exp_I_mul_ofReal]
  simp

section LineProof
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def chirp (c : ℝ) (q : V → ℝ) (x : V) : ℂ := Complex.exp (Complex.I * ((-(2 * Real.pi) * c * q x : ℝ) : ℂ))

/- English proof (translation)
Establish `h1 : (fun x => -(2 * Real.pi) * c * q x).HasTemperateGrowth` using `(Function.HasTemperateGrowth.const _).mul hq`. Conclude with `temperate_exp.comp h1`.
-/
theorem chirp_tg (c : ℝ) {q : V → ℝ} (hq : q.HasTemperateGrowth) : (chirp c q).HasTemperateGrowth := by
  have h1 : (fun x => -(2 * Real.pi) * c * q x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hq
  exact temperate_exp.comp h1

/- English proof (translation)
Rewrite using `[chirp, chirp, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chirp_mul (q : V → ℝ) (x y : V) :
    chirp 1 q y * chirp (-1) q x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((q y - q x : ℝ) : ℂ)) := by
  rw [chirp, chirp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/- English proof (translation)
Rewrite using `[mul_comm, chirp_mul]`. Simplify using the standard rewrite rules.
-/
theorem chirp_one (q : V → ℝ) (x : V) : chirp (-1) q x * chirp 1 q x = 1 := by
  rw [mul_comm, chirp_mul]
  simp

/- English proof (translation)
Establish `hq : (fun x => t * L x + t ^ 2 * (L a / 2)).HasTemperateGrowth` using `((Function.HasTemperateGrowth.const t).mul L.hasTemperateGrowth).add (Function.HasTemperateGrowth.const _)`. Use `⟨SchwartzMap.smulLeftCLM ℂ (chirp 1 fun x => t * L x + t ^ 2 * (L a / 2)) (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f), fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (chirp_tg 1 hq), SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hl, chirp]`. Simplify using `only [smul_eq_mul]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hl_schwartz (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (t : ℝ) : ∃ G : 𝓢(V, ℂ), ∀ x, G x = hl a L t f x := by
  have hq : (fun x => t * L x + t ^ 2 * (L a / 2)).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const t).mul L.hasTemperateGrowth).add (Function.HasTemperateGrowth.const _)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (chirp 1 fun x => t * L x + t ^ 2 * (L a / 2))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f), fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (chirp_tg 1 hq), SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hl, chirp]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

/- English proof (translation)
Use `choose G hG using hl_schwartz a L f`. Use `⟨G, hG, fun ha T => ?_⟩` and prove the remaining obligations. Establish `hna : ‖a‖ ≠ 0` using `norm_ne_zero_iff.2 ha`. Take `⟨g₀, -, hg₀⟩` from `exists_dual_vector ℝ a hna`. Use `set lam : V →L[ℝ] ℝ := ‖a‖⁻¹ • g₀ with hlam`.

Establish `hla : lam a = 1`. Simplify using `only [hlam, ContinuousLinearMap.smul_apply, hg₀, smul_eq_mul]`. Simplify using `using inv_mul_cancel₀ hna`. Use `set q : V → ℝ := fun x => lam x * L x + (-(L a / 2)) * (lam x * lam x) with hq`. Establish `hqt : q.HasTemperateGrowth` using `(lam.hasTemperateGrowth.mul L.hasTemperateGrowth).add ((Function.HasTemperateGrowth.const _).mul (lam.hasTemperateGrowth.mul lam.hasTemperateGrowth))`.

Establish `hdiff : ∀ (x : V) (t : ℝ), q (x + t • a) - q x = t * L x + t ^ 2 * (L a / 2)` using `fun x t => by`. Simplify using `only [hq, map_add, map_smul, hla, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `t1` using `chirp_tg 1 hqt`. Establish `t2` using `chirp_tg (-1) hqt`.

Use `set P := SchwartzMap.smulLeftCLM ℂ (chirp 1 q) with hP`. Use `set Pi := SchwartzMap.smulLeftCLM ℂ (chirp (-1) q) with hPi`. Use `set g : 𝓢(V, ℂ) := P f with hg`. Establish `hGe : ∀ t, G t = Pi (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g)` using `fun t => by`. Use extensionality with `x`.

Rewrite using `[hG, hPi, SchwartzMap.smulLeftCLM_apply_apply t2, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hg, hP, SchwartzMap.smulLeftCLM_apply_apply t1, hl, ← hdiff]`. Simplify using `only [smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_comm (chirp (-1) q x), chirp_mul]`. Establish `hf : Pi g = f`. Use extensionality with `x`.

Rewrite using `[hPi, SchwartzMap.smulLeftCLM_apply_apply t2, hg, hP, SchwartzMap.smulLeftCLM_apply_apply t1]`. Simplify using `only [smul_eq_mul]`. Rewrite using `[← mul_assoc, chirp_one, one_mul]`. Establish `hG0 : G 0 = f`. Use extensionality with `x`.

Rewrite using `[hG]`. Simplify using `[hl]`. Establish `hder : ∀ T₁ : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T₁ (G t)) (T₁ (Pi (∂_{a} g))) 0` using `fun T₁ => by`. Rewrite using `[hasDerivAt_iff_tendsto_slope_zero]`. Establish `h` using `PositivityTheory.ThKOwn.schwartz_dq_tendsto g a`.

Establish `h2` using `(((T₁.comp Pi).restrictScalars ℝ).continuous.tendsto _).comp h`. Use `h2.congr fun t => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, map_smul, map_sub, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply, zero_add, hG0, hGe, hf]`. Establish `hid : Pi (∂_{a} g) = dop a L f`. Use extensionality with `x`.

Establish `h1` using `hder (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)`. Establish `e : (fun t => (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ) (G t)) = fun t => hl a L t f x`. Use function extensionality and compare the values at `t`. Conclude with `hG t x`. Rewrite `h1` using `[e]`.

Conclude with `h1.unique (hasDerivAt_hl a L f x)`. Rewrite using `[← hid]`. Conclude with `hder T`.
-/
theorem hl_line_deriv (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    ∃ G : ℝ → 𝓢(V, ℂ), (∀ t x, G t x = hl a L t f x) ∧
      (a ≠ 0 → ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T (G t)) (T (dop a L f)) 0) := by
  choose G hG using hl_schwartz a L f
  refine ⟨G, hG, fun ha T => ?_⟩
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  obtain ⟨g₀, -, hg₀⟩ := exists_dual_vector ℝ a hna
  set lam : V →L[ℝ] ℝ := ‖a‖⁻¹ • g₀ with hlam
  have hla : lam a = 1 := by
    simp only [hlam, ContinuousLinearMap.smul_apply, hg₀, smul_eq_mul]
    simpa using inv_mul_cancel₀ hna
  set q : V → ℝ := fun x => lam x * L x + (-(L a / 2)) * (lam x * lam x) with hq
  have hqt : q.HasTemperateGrowth :=
    (lam.hasTemperateGrowth.mul L.hasTemperateGrowth).add
      ((Function.HasTemperateGrowth.const _).mul (lam.hasTemperateGrowth.mul lam.hasTemperateGrowth))
  have hdiff : ∀ (x : V) (t : ℝ), q (x + t • a) - q x = t * L x + t ^ 2 * (L a / 2) := fun x t => by
    simp only [hq, map_add, map_smul, hla, smul_eq_mul]
    ring
  have t1 := chirp_tg 1 hqt
  have t2 := chirp_tg (-1) hqt
  set P := SchwartzMap.smulLeftCLM ℂ (chirp 1 q) with hP
  set Pi := SchwartzMap.smulLeftCLM ℂ (chirp (-1) q) with hPi
  set g : 𝓢(V, ℂ) := P f with hg
  have hGe : ∀ t, G t = Pi (SchwartzMap.compSubConstCLM ℂ (-(t • a)) g) := fun t => by
    ext x
    rw [hG, hPi, SchwartzMap.smulLeftCLM_apply_apply t2, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hg, hP,
      SchwartzMap.smulLeftCLM_apply_apply t1, hl, ← hdiff]
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_comm (chirp (-1) q x), chirp_mul]
  have hf : Pi g = f := by
    ext x
    rw [hPi, SchwartzMap.smulLeftCLM_apply_apply t2, hg, hP, SchwartzMap.smulLeftCLM_apply_apply t1]
    simp only [smul_eq_mul]
    rw [← mul_assoc, chirp_one, one_mul]
  have hG0 : G 0 = f := by
    ext x
    rw [hG]
    simp [hl]
  have hder : ∀ T₁ : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T₁ (G t)) (T₁ (Pi (∂_{a} g))) 0 := fun T₁ => by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have h := PositivityTheory.ThKOwn.schwartz_dq_tendsto g a
    have h2 := (((T₁.comp Pi).restrictScalars ℝ).continuous.tendsto _).comp h
    refine h2.congr fun t => ?_
    simp only [Function.comp, map_smul, map_sub, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply,
      zero_add, hG0, hGe, hf]
  have hid : Pi (∂_{a} g) = dop a L f := by
    ext x
    have h1 := hder (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)
    have e : (fun t => (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ) (G t)) =
        fun t => hl a L t f x := by
      funext t
      exact hG t x
    rw [e] at h1
    exact h1.unique (hasDerivAt_hl a L f x)
  rw [← hid]
  exact hder T

/- English proof (translation)
Set `b : ContDiffBump (0 : ℝ)` to `default`. Establish `h1 : HasCompactSupport (fun t => ((b t : ℝ) : ℂ))` using `b.hasCompactSupport.comp_left Complex.ofReal_zero`. Establish `h2 : ContDiff ℝ (⊤ : ℕ∞) (fun t => ((b t : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp b.contDiff`. Use `⟨h1.toSchwartzMap h2, b.eventuallyEq_one.mono fun t ht => ?_⟩` and prove the remaining obligations. Use `show ((b t : ℝ) : ℂ) = 1`.

Rewrite using `[ht]`. Simplify using the standard rewrite rules.
-/
theorem exists_bump : ∃ φ : 𝓢(ℝ, ℂ), ∀ᶠ t in 𝓝 (0 : ℝ), φ t = 1 := by
  let b : ContDiffBump (0 : ℝ) := default
  have h1 : HasCompactSupport (fun t => ((b t : ℝ) : ℂ)) := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun t => ((b t : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  refine ⟨h1.toSchwartzMap h2, b.eventuallyEq_one.mono fun t ht => ?_⟩
  show ((b t : ℝ) : ℂ) = 1
  rw [ht]
  simp

/- English proof (translation)
Use `choose G hG using hl_schwartz a L f`. Use `⟨G, hG, ?_⟩` and prove the remaining obligations. Take `⟨φ, hφ⟩` from `exists_bump`. Set `ι : V →L[ℝ] WithLp 2 (ℝ × V)` to `(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inr ℝ ℝ V`. Establish `hι : ∀ x, ι x = WithLp.toLp 2 (0, x)` using `fun x => rfl`.

Establish `hanti : AntilipschitzWith ‖WithLp.sndL 2 ℝ ℝ V‖₊ ι` using `(WithLp.sndL 2 ℝ ℝ V).lipschitz.to_rightInverse fun x => rfl`. Set `R : 𝓢(WithLp 2 (ℝ × V), ℂ) →L[ℂ] 𝓢(V, ℂ)` to `SchwartzMap.compCLMOfAntilipschitz ℂ ι.hasTemperateGrowth hanti`. Establish `hR : ∀ g x, R g x = g (WithLp.toLp 2 (0, x))` using `fun g x => rfl`. Take `⟨G', hG', hD⟩` from `hl_line_deriv (WithLp.toLp 2 ((1 : ℝ), a)) (L ∘L WithLp.sndL 2 ℝ ℝ V) (PositivityTheory.ThKOwn.tens φ f)`. Establish `hne : WithLp.toLp 2 ((1 : ℝ), a) ≠ 0` using `fun h => by`.

Use `congrArg (WithLp.fstL 2 ℝ ℝ V) h` as an intermediate fact. Simplify using `at this`. Establish `hev : ∀ᶠ t in 𝓝 (0 : ℝ), G t = R (G' t)` using `hφ.mono fun t ht => by`. Use extensionality with `x`. Rewrite using `[hR, hG, hG', hl, hl]`.

Establish `e : WithLp.toLp 2 ((0 : ℝ), x) + t • WithLp.toLp 2 ((1 : ℝ), a) = WithLp.toLp 2 (t, x + t • a)`. Rewrite using `[← WithLp.toLp_smul, ← WithLp.toLp_add]`. Simplify using the standard rewrite rules. Rewrite using `[e, PositivityTheory.ThKOwn.tens_apply, ht, one_mul]`. Both sides reduce to the same expression.

Use `set g₁ := R (dop (WithLp.toLp 2 ((1 : ℝ), a)) (L ∘L WithLp.sndL 2 ℝ ℝ V) (PositivityTheory.ThKOwn.tens φ f))`. Establish `hder : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T (G t)) (T g₁) 0` using `fun T => (hD hne (T ∘L R)).congr_of_eventuallyEq (hev.mono fun t ht => by simp only [ht]; rfl)`. Establish `hid : g₁ = dop a L f`. Use extensionality with `x`. Establish `h1` using `hder (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)`.

Establish `e : (fun t => (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ) (G t)) = fun t => hl a L t f x`. Use function extensionality and compare the values at `t`. Conclude with `hG t x`. Rewrite `h1` using `[e]`. Conclude with `h1.unique (hasDerivAt_hl a L f x)`.

Rewrite using `[← hid]`. Conclude with `hder`.
-/
theorem hl_deriv (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    ∃ G : ℝ → 𝓢(V, ℂ), (∀ t x, G t x = hl a L t f x) ∧
      ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T (G t)) (T (dop a L f)) 0 := by
  choose G hG using hl_schwartz a L f
  refine ⟨G, hG, ?_⟩
  obtain ⟨φ, hφ⟩ := exists_bump
  let ι : V →L[ℝ] WithLp 2 (ℝ × V) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ V).symm.toContinuousLinearMap ∘L ContinuousLinearMap.inr ℝ ℝ V
  have hι : ∀ x, ι x = WithLp.toLp 2 (0, x) := fun x => rfl
  have hanti : AntilipschitzWith ‖WithLp.sndL 2 ℝ ℝ V‖₊ ι :=
    (WithLp.sndL 2 ℝ ℝ V).lipschitz.to_rightInverse fun x => rfl
  let R : 𝓢(WithLp 2 (ℝ × V), ℂ) →L[ℂ] 𝓢(V, ℂ) := SchwartzMap.compCLMOfAntilipschitz ℂ ι.hasTemperateGrowth hanti
  have hR : ∀ g x, R g x = g (WithLp.toLp 2 (0, x)) := fun g x => rfl
  obtain ⟨G', hG', hD⟩ := hl_line_deriv (WithLp.toLp 2 ((1 : ℝ), a)) (L ∘L WithLp.sndL 2 ℝ ℝ V)
    (PositivityTheory.ThKOwn.tens φ f)
  have hne : WithLp.toLp 2 ((1 : ℝ), a) ≠ 0 := fun h => by
    have := congrArg (WithLp.fstL 2 ℝ ℝ V) h
    simp at this
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), G t = R (G' t) := hφ.mono fun t ht => by
    ext x
    rw [hR, hG, hG', hl, hl]
    have e : WithLp.toLp 2 ((0 : ℝ), x) + t • WithLp.toLp 2 ((1 : ℝ), a) = WithLp.toLp 2 (t, x + t • a) := by
      rw [← WithLp.toLp_smul, ← WithLp.toLp_add]
      simp
    rw [e, PositivityTheory.ThKOwn.tens_apply, ht, one_mul]
    rfl
  set g₁ := R (dop (WithLp.toLp 2 ((1 : ℝ), a)) (L ∘L WithLp.sndL 2 ℝ ℝ V) (PositivityTheory.ThKOwn.tens φ f))
  have hder : ∀ T : 𝓢(V, ℂ) →L[ℂ] ℂ, HasDerivAt (fun t => T (G t)) (T g₁) 0 := fun T =>
    (hD hne (T ∘L R)).congr_of_eventuallyEq (hev.mono fun t ht => by simp only [ht]; rfl)
  have hid : g₁ = dop a L f := by
    ext x
    have h1 := hder (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)
    have e : (fun t => (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ) (G t)) =
        fun t => hl a L t f x := by
      funext t
      exact hG t x
    rw [e] at h1
    exact h1.unique (hasDerivAt_hl a L f x)
  rw [← hid]
  exact hder

def dopL (a : V) (L : V →L[ℝ] ℝ) : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ) :=
  LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a +
    (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (fun x => ((L x : ℝ) : ℂ))

/- English proof (translation)
Use extensionality with `x`. Establish `hT : (fun x => ((L x : ℝ) : ℂ)).HasTemperateGrowth` using `(Complex.ofRealCLM ∘L L).hasTemperateGrowth`. Rewrite using `[dop_apply]`. Simplify using `only [dopL, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dopL_apply (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : dopL a L f = dop a L f := by
  ext x
  have hT : (fun x => ((L x : ℝ) : ℂ)).HasTemperateGrowth := (Complex.ofRealCLM ∘L L).hasTemperateGrowth
  rw [dop_apply]
  simp only [dopL, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT, LineDeriv.lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul]
  ring

end LineProof

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

/- English proof (translation)
The claim follows from `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
The claim follows from `map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1`.
-/
theorem evI_mul (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

/- English proof (translation)
The claim follows from `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.
-/
theorem evI_zero : evI F 0 = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using evI_zero`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]`.
-/
theorem evI_sum {ι : Type} (s : Finset ι) (g : ι → AF F) : evI F (∑ i ∈ s, g i) = ∑ i ∈ s, evI F (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evI_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, evI_add, ih]

/- English proof (translation)
Simplify using `[evI, realAd]`.
-/
theorem evI_realAd (t : ℝ) : evI F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  simp [evI, realAd]

def linForm (B : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (∑ i, (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) ∘ₗ (LinearMap.mulRight ℝ (B i)) ∘ₗ
      (LinearMap.proj i : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] mixedEmbedding.mixedSpace F))

/- English proof (translation)
Simplify using `[linForm, map_sum, LinearMap.sum_apply]`.
-/
theorem linForm_apply (B y : κ → mixedEmbedding.mixedSpace F) :
    linForm B y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, y i * B i) := by
  simp [linForm, map_sum, LinearMap.sum_apply]

open scoped Classical in

/- English proof (translation)
Establish `hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b)))`. Introduce `s hs`. Establish `hsb : ∀ i, s * b i = 0` using `fun i => by simpa using congrFun (hb s hs) i`. Establish `e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i)` using `fun i => by ring`. Establish `e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) = ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i)` using `fun i => by ring`.

Simplify using `only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero, add_zero]`. Rewrite using `[hψ.2.2 _ hz]`. Use `congr 3`. Establish `ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) = t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i))`. Simplify using `only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow, Finset.mul_sum]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[ev, map_add, map_smul, map_smul, linForm_apply]`. Simplify using `[smul_eq_mul]`.
-/
theorem phase_line (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (a b x : κ → AF F) (hb : At (evI F) b) (t : ℝ) :
    ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * linForm (fun i => evI F (b i)) (fun i => evI F (x i)) +
        t ^ 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) : ℝ) : ℂ)) := by
  have hz : At (evI F) (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) := by
    intro s hs
    have hsb : ∀ i, s * b i = 0 := fun i => by simpa using congrFun (hb s hs) i
    have e1 : ∀ i, s * (x i * (realAd F t * b i)) = x i * realAd F t * (s * b i) := fun i => by ring
    have e2 : ∀ i, s * (⅟(2 : AF F) * (realAd F t * a i * (realAd F t * b i))) =
        ⅟(2 : AF F) * (realAd F t * a i * realAd F t) * (s * b i) := fun i => by ring
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, e1, e2, hsb, mul_zero, Finset.sum_const_zero,
      add_zero]
  rw [hψ.2.2 _ hz]
  congr 3
  have ev : evI F (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) =
      t • (∑ i, evI F (x i) * evI F (b i)) + (t ^ 2) • (evI F ⅟(2 : AF F) * ∑ i, evI F (a i) * evI F (b i)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, evI_sum, evI_realAd, Algebra.smul_def, map_pow,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · exact Finset.sum_congr rfl fun i _ => by ring
  rw [ev, map_add, map_smul, map_smul, linForm_apply]
  simp [smul_eq_mul]

/- English proof (translation)
Establish `h1 : evI F ⅟(2 : AF F) + evI F ⅟(2 : AF F) = 1`. Rewrite using `[← evI_add, invOf_two_add_invOf_two]`. Conclude with `map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Establish `h2 : S = evI F ⅟(2 : AF F) * S + evI F ⅟(2 : AF F) * S`. Rewrite using `[← add_mul, h1, one_mul]`.

Establish `h3` using `congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h2`. Rewrite `h3` using `[map_add]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem evI_half_trace (S : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F ⅟(2 : AF F) * S) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) S / 2 := by
  have h1 : evI F ⅟(2 : AF F) + evI F ⅟(2 : AF F) = 1 := by
    rw [← evI_add, invOf_two_add_invOf_two]
    exact map_one (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h2 : S = evI F ⅟(2 : AF F) * S + evI F ⅟(2 : AF F) * S := by
    rw [← add_mul, h1, one_mul]
  have h3 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h2
  rw [map_add] at h3
  linarith

/- English proof (translation)
Set `u : AF F` to `(0, 1)`. Establish `h0 : evI F u = 0` using `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Establish `h : u * z i = 0` using `congrFun (hz u h0) i`. Establish `h' : (1 : Af F) * (z i).2 = 0` using `congrArg Prod.snd h`. Rewrite `h'` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem snd_eq_zero {z : κ → AF F} (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (0, 1)
  have h0 : evI F u = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  have h : u * z i = 0 := congrFun (hz u h0) i
  have h' : (1 : Af F) * (z i).2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h'

open scoped Classical in

/- English proof (translation)
Establish `hat : At (evI F) (realAd F t • a)` using `fun s hs => by`. Rewrite using `[smul_comm, ha s hs, smul_zero]`. Use function extensionality and compare the values at `x`. Establish `e : (fun i => evI F ((x + realAd F t • a) i)) = (fun i => evI F (x i)) + t • fun i => evI F (a i)`. Use function extensionality and compare the values at `i`.

Simplify using `[evI_add, evI_mul, evI_realAd, Algebra.smul_def]`. Establish `e2 : (fun i => ((x + realAd F t • a) i).2) = fun i => (x i).2`. Use function extensionality and compare the values at `i`. Use `show (x i).2 + ((realAd F t • a) i).2 = _`. Rewrite using `[snd_eq_zero hat, add_zero]`.

Use `show ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) * (f (fun i => evI F ((x + realAd F t • a) i)) * g (fun i => ((x + realAd F t • a) i).2)) = hl (fun i => evI F (a i)) (linForm fun i => evI F (b i)) t f (fun i => evI F (x i)) * g fun i => (x i) …`. Rewrite using `[phase_line ψ hψ _ _ x hb t, e, e2, evI_half_trace]`. Simplify using `only [hl, linForm_apply, mul_assoc]`.
-/
theorem schr_pure {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {a b : κ → AF F} (ha : At (evI F) a) (hb : At (evI F) b)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) (t : ℝ) :
    schr ψ (realAd F t • a, realAd F t • b) (pureA F f g) =
      pureA F (hl (fun i => evI F (a i)) (linForm fun i => evI F (b i)) t f) g := by
  have hat : At (evI F) (realAd F t • a) := fun s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  funext x
  have e : (fun i => evI F ((x + realAd F t • a) i)) = (fun i => evI F (x i)) + t • fun i => evI F (a i) := by
    funext i
    simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
  have e2 : (fun i => ((x + realAd F t • a) i).2) = fun i => (x i).2 := by
    funext i
    show (x i).2 + ((realAd F t • a) i).2 = _
    rw [snd_eq_zero hat, add_zero]
  show ψ (x ⬝ᵥ (realAd F t • b) + ⅟(2 : AF F) * ((realAd F t • a) ⬝ᵥ (realAd F t • b))) *
      (f (fun i => evI F ((x + realAd F t • a) i)) * g (fun i => ((x + realAd F t • a) i).2)) =
    hl (fun i => evI F (a i)) (linForm fun i => evI F (b i)) t f (fun i => evI F (x i)) * g fun i => (x i).2
  rw [phase_line ψ hψ _ _ x hb t, e, e2, evI_half_trace]
  simp only [hl, linForm_apply, mul_assoc]

end PositivityTheory.RL.Der

namespace PositivityTheory.RL

open Der

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ`. Use `⟨fun u => dopL (fun i => evI F ((d.e u).1 i)) (linForm fun i => evI F ((d.e u).2 i)), fun u hu f => ⟨?_, fun x => ?_⟩⟩` and prove the remaining obligations. Establish `hab : ∀ s, evI F s = 0 → s • d.e u = 0` using `fun s hs => by`. Rewrite using `[← map_smul, hu s hs, map_zero]`. Establish `ha : At (evI F) (d.e u).1` using `fun s hs => congrArg Prod.fst (hab s hs)`.

Establish `hb : At (evI F) (d.e u).2` using `fun s hs => congrArg Prod.snd (hab s hs)`. Introduce `g hg l hl'`. Take `⟨T, hT⟩` from `hl' g hg`. Take `⟨G, hG, hD⟩` from `hl_deriv (fun i => evI F ((d.e u).1 i)) (linForm fun i => evI F ((d.e u).2 i)) f`. Establish `e : (fun t => l (d.rho ψ (realAd F t • u) (pureA F f g))) = fun t => T (G t)`.

Use function extensionality and compare the values at `t`. Rewrite using `[← hT]`. Use `congr 1`. Use `show schr ψ (d.e (realAd F t • u)) _ = _`. Rewrite using `[map_smul]`.

Use `(schr_pure hψ ha hb f g t).trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `x`. Conclude with `(hG t x).symm`. Rewrite using `[e, hT, dopL_apply]`.

Conclude with `hD T`. Rewrite using `[dopL_apply, dop_apply, linForm_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem derEx : GlobalTheory.RealLift.DerEx := by
  classical
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ
  refine ⟨fun u => dopL (fun i => evI F ((d.e u).1 i)) (linForm fun i => evI F ((d.e u).2 i)), fun u hu f => ⟨?_, fun x => ?_⟩⟩
  · have hab : ∀ s, evI F s = 0 → s • d.e u = 0 := fun s hs => by
      rw [← map_smul, hu s hs, map_zero]
    have ha : At (evI F) (d.e u).1 := fun s hs => congrArg Prod.fst (hab s hs)
    have hb : At (evI F) (d.e u).2 := fun s hs => congrArg Prod.snd (hab s hs)
    intro g hg l hl'
    obtain ⟨T, hT⟩ := hl' g hg
    obtain ⟨G, hG, hD⟩ := hl_deriv (fun i => evI F ((d.e u).1 i)) (linForm fun i => evI F ((d.e u).2 i)) f
    have e : (fun t => l (d.rho ψ (realAd F t • u) (pureA F f g))) = fun t => T (G t) := by
      funext t
      rw [← hT]
      congr 1
      show schr ψ (d.e (realAd F t • u)) _ = _
      rw [map_smul]
      refine (schr_pure hψ ha hb f g t).trans ?_
      congr 1
      funext x
      exact (hG t x).symm
    rw [e, hT, dopL_apply]
    exact hD T
  · rw [dopL_apply, dop_apply, linForm_apply]
    ring

end PositivityTheory.RL

end
