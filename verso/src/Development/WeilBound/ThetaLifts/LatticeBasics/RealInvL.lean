import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsRealStructure
import Development.WeilBound.ThetaLifts.SchwartzMoments.SchwartzDqTendsto

noncomputable section

namespace GlobalTheory.ThK.Dbl.Dense

open scoped TensorProduct NNReal ENNReal Matrix SchwartzMap LineDeriv
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

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
Use extensionality with `x`. Simplify using `only [SchwartzMap.add_apply, dop_apply, map_add, ContinuousLinearMap.add_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dop_add (a b : V) (L M : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) :
    dop (a + b) (L + M) f = dop a L f + dop b M f := by
  ext x
  simp only [SchwartzMap.add_apply, dop_apply, map_add, ContinuousLinearMap.add_apply]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `x`. Establish `ha : a = 0` using `Subsingleton.elim _ _`. Establish `hx : x = 0` using `Subsingleton.elim _ _`. Simplify using `[dop_apply, ha, hx]`.
-/
theorem dop_subsingleton [Subsingleton V] (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) : dop a L f = 0 := by
  ext x
  have ha : a = 0 := Subsingleton.elim _ _
  have hx : x = 0 := Subsingleton.elim _ _
  simp [dop_apply, ha, hx]

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

variable {κ : Type} [Fintype κ]

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
end LineProof

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, pf_mem good_std, by rw [pf_eq_prod ∅ 0 fun u _ => ⟨rfl, fun i => by simp⟩, Finset.prod_empty]⟩`.
-/
theorem exists_sb_one {κ : Type} [Fintype κ] : ∃ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), g 0 = 1 :=
  ⟨_, pf_mem good_std, by rw [pf_eq_prod ∅ 0 fun u _ => ⟨rfl, fun i => by simp⟩, Finset.prod_empty]⟩

section Coord
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def aOf (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) : Fin n × Fin d → mixedEmbedding.mixedSpace F :=
  fun i => evI F ((M.co.e u).1 i)

def lOf (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  linForm fun i => evI F ((M.co.e u).2 i)

end Coord

section Coord2
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[aOf, map_add, evI_add]`.
-/
theorem aOf_add (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    aOf M (u + v) = aOf M u + aOf M v := by
  funext i
  simp [aOf, map_add, evI_add]

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [lOf, ContinuousLinearMap.add_apply, linForm_apply, ← map_add, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[map_add, evI_add, mul_add]`.
-/
theorem lOf_add (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    lOf M (u + v) = lOf M u + lOf M v := by
  ext y
  simp only [lOf, ContinuousLinearMap.add_apply, linForm_apply, ← map_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [map_add, evI_add, mul_add]

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

open scoped Classical in
/- English proof (translation)
Establish `hab : ∀ s, evI F s = 0 → s • M.co.e u = 0` using `fun s hs => by`. Rewrite using `[← map_smul, hu s hs, map_zero]`. Establish `ha : At (evI F) (M.co.e u).1` using `fun s hs => congrArg Prod.fst (hab s hs)`. Establish `hb : At (evI F) (M.co.e u).2` using `fun s hs => congrArg Prod.snd (hab s hs)`. Establish `hat : At (evI F) (realAd F t • (M.co.e u).1)` using `fun s hs => by`.

Rewrite using `[smul_comm, ha s hs, smul_zero]`. Use function extensionality and compare the values at `x`. Use `show schr ψ (M.co.e (realAd F t • u)) _ x = _`. Rewrite using `[map_smul]`. Use `show schr ψ (realAd F t • (M.co.e u).1, realAd F t • (M.co.e u).2) _ x = _`.

Establish `e : (fun i => evI F ((x + realAd F t • (M.co.e u).1) i)) = (fun i => evI F (x i)) + t • fun i => evI F ((M.co.e u).1 i)`. Use function extensionality and compare the values at `i`. Simplify using `[evI_add, evI_mul, evI_realAd, Algebra.smul_def]`. Simplify using `only [schr, tens]`. Rewrite using `[phase_line ψ hψ _ _ x hb t, e, hr x _ hat, evI_half_trace]`.

Simplify using `only [hl, aOf, lOf, linForm_apply, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem heisLine_tens (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d))
    {r : (Fin n × Fin d → AF F) → ℂ} (hr : ∀ x z, At (evI F) z → r (x + z) = r x) (t : ℝ) :
    M.heisLine ψ u t (tens (evI F) f r) = tens (evI F) (hl (aOf M u) (lOf M u) t f) r := by
  have hab : ∀ s, evI F s = 0 → s • M.co.e u = 0 := fun s hs => by
    rw [← map_smul, hu s hs, map_zero]
  have ha : At (evI F) (M.co.e u).1 := fun s hs => congrArg Prod.fst (hab s hs)
  have hb : At (evI F) (M.co.e u).2 := fun s hs => congrArg Prod.snd (hab s hs)
  have hat : At (evI F) (realAd F t • (M.co.e u).1) := fun s hs => by
    rw [smul_comm, ha s hs, smul_zero]
  funext x
  show schr ψ (M.co.e (realAd F t • u)) _ x = _
  rw [map_smul]
  show schr ψ (realAd F t • (M.co.e u).1, realAd F t • (M.co.e u).2) _ x = _
  have e : (fun i => evI F ((x + realAd F t • (M.co.e u).1) i)) =
      (fun i => evI F (x i)) + t • fun i => evI F ((M.co.e u).1 i) := by
    funext i
    simp [evI_add, evI_mul, evI_realAd, Algebra.smul_def]
  simp only [schr, tens]
  rw [phase_line ψ hψ _ _ x hb t, e, hr x _ hat, evI_half_trace]
  simp only [hl, aOf, lOf, linForm_apply, mul_assoc]
  rfl

open scoped Classical in
/- English proof (translation)
Introduce `r hr x`. Establish `e : (fun t => M.heisLine ψ u t (tens (evI F) f r) x) = fun t => hl (aOf M u) (lOf M u) t f (fun i => evI F (x i)) * r x`. Use function extensionality and compare the values at `t`. Rewrite using `[heisLine_tens M hψ hu f hr.1 t]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(hasDerivAt_hl _ _ f _).mul_const (r x)`.
-/
theorem actsD_dop (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f (dop (aOf M u) (lOf M u) f) := by
  intro r hr x
  have e : (fun t => M.heisLine ψ u t (tens (evI F) f r) x) =
      fun t => hl (aOf M u) (lOf M u) t f (fun i => evI F (x i)) * r x := by
    funext t
    rw [heisLine_tens M hψ hu f hr.1 t]
    rfl
  rw [e]
  exact (hasDerivAt_hl _ _ f _).mul_const (r x)

open scoped Classical in
/- English proof (translation)
Take `⟨g, hg, h0⟩` from `exists_sb_one (F := F) (κ := Fin n × Fin d)`. Use extensionality with `x`. Establish `hr : Rest (evI F) f (rOf g)` using `⟨fun x z hz => rOf_add g x z hz, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩`. Establish `h1` using `h _ hr (pt x 0)`. Establish `h2` using `actsD_dop M hψ hu f _ hr (pt x 0)`.

Use `h1.unique h2` as an intermediate fact. Simplify `this` using `[tens_rOf, pureA_pt, h0]`.
-/
theorem actsD_unique' (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)}
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ = dop (aOf M u) (lOf M u) f := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  ext x
  have hr : Rest (evI F) f (rOf g) := ⟨fun x z hz => rOf_add g x z hz, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  have h1 := h _ hr (pt x 0)
  have h2 := actsD_dop M hψ hu f _ hr (pt x 0)
  have := h1.unique h2
  simpa [tens_rOf, pureA_pt, h0] using this

end Coord2

section Inter
variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}
variable {M : Model σ Y W} {ψ : AddChar (AF F) ℂ} {om : Rep σ Y W} {k : UA σ Y.J × UA σ W.J}

/- English proof (translation)
Introduce `s hs` and use `by rw [actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu s hs, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem at_act (k : UA σ Y.J × UA σ W.J) {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) :
    At (evI F) (actAB (cA σ) k u) := fun s hs => by
  rw [actAB, ← Matrix.smul_mul, ← Matrix.mul_smul, hu s hs, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Rewrite using `[actAB, Matrix.mul_add, Matrix.add_mul]`. Both sides reduce to the same expression.
-/
theorem act_add (k : UA σ Y.J × UA σ W.J) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    actAB (cA σ) k (u + v) = actAB (cA σ) k u + actAB (cA σ) k v := by
  rw [actAB, Matrix.mul_add, Matrix.add_mul]; rfl

open scoped Classical in

def Impl (om : Rep σ Y W) (k : UA σ Y.J × UA σ W.J) (A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) : Prop :=
  ∀ f : SInf F (Fin n × Fin d), ∀ g ∈ SB (Fin n × Fin d → Af F), om k (pureA F f g) = pureA F (A f) g

open scoped Classical in
/- English proof (translation)
Take `⟨g, hg, h0⟩` from `exists_sb_one (F := F) (κ := Fin n × Fin d)`. Establish `hr : ∀ x z, At (evI F) z → rOf g (x + z) = rOf g x` using `fun x z hz => rOf_add g x z hz`. Establish `hΦ : pureA F f g ∈ schA F (Fin n × Fin d)` using `Submodule.subset_span ⟨f, g, hg, rfl⟩`. Establish `e1 : M.heisLine ψ u t (pureA F f g) = pureA F G g`. Rewrite using `[← tens_rOf, heisLine_tens M hψ hu f hr t, tens_rOf]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Conclude with `(hG x).symm`. Establish `e2 : om k (M.heisLine ψ u t (pureA F f g)) = M.heisLine ψ (actAB (cA σ) k u) t (om k (pureA F f g))`. Use `hs.impl k (realAd F t • u) _ hΦ` as an intermediate fact.

Rewrite `this` using `[actAB, Matrix.mul_smul, Matrix.smul_mul]`. Conclude with `this`. Rewrite `e2` using `[e1, hA G g hg, hA f g hg, ← tens_rOf, ← tens_rOf, heisLine_tens M hψ (at_act k hu) (A f) hr t]`. Use `congrFun e2 (pt x 0)` as an intermediate fact. Simplify `this` using `[tens_rOf, pureA_pt, h0]`.
-/
theorem line_hl (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f G : SInf F (Fin n × Fin d)) (t : ℝ)
    (hG : ∀ x, G x = hl (aOf M u) (lOf M u) t f x) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    A G x = hl (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) t (A f) x := by
  obtain ⟨g, hg, h0⟩ := exists_sb_one (F := F) (κ := Fin n × Fin d)
  have hr : ∀ x z, At (evI F) z → rOf g (x + z) = rOf g x := fun x z hz => rOf_add g x z hz
  have hΦ : pureA F f g ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : M.heisLine ψ u t (pureA F f g) = pureA F G g := by
    rw [← tens_rOf, heisLine_tens M hψ hu f hr t, tens_rOf]
    congr 1
    funext x
    exact (hG x).symm
  have e2 : om k (M.heisLine ψ u t (pureA F f g)) =
      M.heisLine ψ (actAB (cA σ) k u) t (om k (pureA F f g)) := by
    have := hs.impl k (realAd F t • u) _ hΦ
    rw [actAB, Matrix.mul_smul, Matrix.smul_mul] at this
    exact this
  rw [e1, hA G g hg, hA f g hg, ← tens_rOf, ← tens_rOf, heisLine_tens M hψ (at_act k hu) (A f) hr t] at e2
  have := congrFun e2 (pt x 0)
  simpa [tens_rOf, pureA_pt, h0] using this

open scoped Classical in
/- English proof (translation)
Take `⟨G, hG, hD⟩` from `hl_line_deriv (aOf M u) (lOf M u) f`. Use extensionality with `x`. Set `T` to `(BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ) ∘L A`. Establish `hT : ∀ f, A f x = T f` using `fun _ => rfl`. Establish `h1` using `hD ha T`.

Establish `e : (fun t => T (G t)) = fun t => hl (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) t (A f) x`. Use function extensionality and compare the values at `t`. Rewrite using `[← hT]`. Conclude with `line_hl hψ hs hA hu f (G t) t (hG t) x`. Rewrite `h1` using `[e]`.

Rewrite using `[hT]`. Conclude with `h1.unique (hasDerivAt_hl _ _ (A f) x)`.
-/
theorem inter_of_ne (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (ha : aOf M u ≠ 0) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) (A f) := by
  obtain ⟨G, hG, hD⟩ := hl_line_deriv (aOf M u) (lOf M u) f
  ext x
  let T := (BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ) ∘L A
  have hT : ∀ f, A f x = T f := fun _ => rfl
  have h1 := hD ha T
  have e : (fun t => T (G t)) = fun t => hl (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) t (A f) x := by
    funext t
    rw [← hT]
    exact line_hl hψ hs hA hu f (G t) t (hG t) x
  rw [e] at h1
  rw [hT]
  exact h1.unique (hasDerivAt_hl _ _ (A f) x)

open scoped Classical in
/- English proof (translation)
Use `⟨M.co.e.symm (pt ξ 0, 0), fun s hs => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : s.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs`. Rewrite using `[← map_smul, LinearEquiv.map_eq_zero_iff]`. Use `Prod.ext ?_ (by simp)` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show s.1 * _ = 0`. Rewrite using `[h1, zero_mul]`. Use `show s.2 * 0 = 0`. Rewrite using `[mul_zero]`.

Establish `: M.co.e (M.co.e.symm (pt ξ 0, 0)) = (pt ξ 0, 0)` using `LinearEquiv.apply_symm_apply _ _ show (fun i => evI F ((M.co.e (M.co.e.symm (pt ξ 0, 0))).1 i)) = ξ`. Rewrite using `[this]`. Conclude with `evI_pt ξ 0`.
-/
theorem exists_at (M : Model σ Y W) (ξ : Fin n × Fin d → mixedEmbedding.mixedSpace F) :
    ∃ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v ∧ aOf M v = ξ := by
  refine ⟨M.co.e.symm (pt ξ 0, 0), fun s hs => ?_, ?_⟩
  · have h1 : s.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.1 hs
    rw [← map_smul, LinearEquiv.map_eq_zero_iff]
    refine Prod.ext ?_ (by simp)
    funext i
    refine Prod.ext ?_ ?_
    · show s.1 * _ = 0
      rw [h1, zero_mul]
    · show s.2 * 0 = 0
      rw [mul_zero]
  · have : M.co.e (M.co.e.symm (pt ξ 0, 0)) = (pt ξ 0, 0) := LinearEquiv.apply_symm_apply _ _
    show (fun i => evI F ((M.co.e (M.co.e.symm (pt ξ 0, 0))).1 i)) = ξ
    rw [this]
    exact evI_pt ξ 0

open scoped Classical in
/- English proof (translation)
Distinguish the cases in `ha : aOf M u = 0`. Break down `subsingleton_or_nontrivial (Fin n × Fin d → mixedEmbedding.mixedSpace F) with hV | hV` into its components or cases. Rewrite using `[dop_subsingleton, dop_subsingleton, map_zero]`. Take `⟨ξ, hξ⟩` from `exists_ne (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)`. Take `⟨v, hv, rfl⟩` from `exists_at M ξ`.

Establish `huv : At (evI F) (u + v)` using `fun s hs => by rw [smul_add, hu s hs, hv s hs, add_zero]`. Establish `h1` using `inter_of_ne hψ hs hA huv (by rw [aOf_add, ha, zero_add]; exact hξ) f`. Establish `h2` using `inter_of_ne hψ hs hA hv hξ f`. Rewrite `h1` using `[aOf_add, lOf_add, dop_add, map_add, act_add, aOf_add, lOf_add, dop_add, h2]`. Conclude with `add_right_cancel h1`.

Conclude with `inter_of_ne hψ hs hA hu ha f`.
-/
theorem inter (hψ : IsStd ψ) (hs : IsSplitting (adeleClass F) ψ M.co (actAB (cA σ)) om)
    {A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)} (hA : Impl om k A)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) (f : SInf F (Fin n × Fin d)) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M (actAB (cA σ) k u)) (lOf M (actAB (cA σ) k u)) (A f) := by
  by_cases ha : aOf M u = 0
  · rcases subsingleton_or_nontrivial (Fin n × Fin d → mixedEmbedding.mixedSpace F) with hV | hV
    · rw [dop_subsingleton, dop_subsingleton, map_zero]
    · obtain ⟨ξ, hξ⟩ := exists_ne (0 : Fin n × Fin d → mixedEmbedding.mixedSpace F)
      obtain ⟨v, hv, rfl⟩ := exists_at M ξ
      have huv : At (evI F) (u + v) := fun s hs => by rw [smul_add, hu s hs, hv s hs, add_zero]
      have h1 := inter_of_ne hψ hs hA huv (by rw [aOf_add, ha, zero_add]; exact hξ) f
      have h2 := inter_of_ne hψ hs hA hv hξ f
      rw [aOf_add, lOf_add, dop_add, map_add, act_add, aOf_add, lOf_add, dop_add, h2] at h1
      exact add_right_cancel h1
  · exact inter_of_ne hψ hs hA hu ha f

end Inter

section Unit

/- English proof (translation)
Use `continuous_pi fun v => ?_` and prove the remaining obligations. Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]`. Conclude with `((continuous_apply _).comp continuous_fst).congr fun y => (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]`.

Conclude with `((continuous_apply _).comp continuous_snd).congr fun y => (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`.
-/
theorem cont_mixS : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

variable (F) (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem splitE_apply (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    splitE F κ p = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) := rfl

/- English proof (translation)
Rewrite using `[show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) => fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]`. Conclude with `continuous_pi fun i => (cont_mixS.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)`.
-/
theorem continuous_splitE : Continuous (splitE F κ) := by
  rw [show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]
  exact continuous_pi fun i => (cont_mixS.comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

variable {F} in
/- English proof (translation)
The claim follows from `(continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp ((continuous_apply w.1).comp continuous_fst)).prodMk (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp ((continuous_apply w. …`.
-/
theorem cont_evI : Continuous (evI F) :=
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal w.2).continuous.comp
    ((continuous_apply w.1).comp continuous_fst)).prodMk
  (continuous_pi fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w.1).continuous.comp
    ((continuous_apply w.1).comp continuous_fst))

/- English proof (translation)
Rewrite using `[show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F => ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]`. Conclude with `(continuous_pi fun i => cont_evI.comp (continuous_apply i)).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))`.
-/
theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  rw [show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) :
      (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]
  exact (continuous_pi fun i => cont_evI.comp (continuous_apply i)).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]`.
-/
theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  simp only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]

open scoped Classical in
/- English proof (translation)
Use `haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd`. Conclude with `Measure.pi.isAddHaarMeasure _`.
-/
theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  exact Measure.pi.isAddHaarMeasure _

variable {F κ} [Fintype κ]

open scoped Classical in
/- English proof (translation)
Take `⟨g, hg, h₁⟩` from `exists_sb_one (F := F) (κ := κ)`. Use `haveI := volume_isAddHaar F κ`. Use `haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance`. Use `haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`.

Use `haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F`. Use `letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _`. Use `haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩`. Use `letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _`. Use `haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩`.

Use `haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable`. Use `set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν`. Use `haveI : SFinite ν := inferInstance`. Use `haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd`. Use `haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd`.

Use `haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance`. Use `haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν`. Establish `hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ))` using `(splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)`. Set `em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F)` to `(Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv`. Establish `hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞, ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν)` using `fun h => lintegral_map_equiv h em`.

Establish `hgc : Continuous g` using `hg.1.continuous`. Establish `hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤`. Establish `h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤` using `((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2`. Use `ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)` and prove the remaining obligations. Rewrite using `[enorm_mul, sq]`.

Establish `hC0 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ 0` using `fun h0 => by`. Rewrite `h0` using `[lintegral_eq_zero_iff (hgc.measurable.enorm.pow_const 2)]`. Establish `h2 : g =ᵐ[ν] 0` using `h0.mono fun y hy => by simpa using hy`. Use `congrFun ((hgc.ae_eq_iff_eq ν continuous_zero).1 h2) 0` as an intermediate fact. Simplify using `[h₁] at this`.

Establish `hp : ∀ a : SInf F κ, ∫⁻ x, ‖pureA F a g x‖ₑ ^ 2 ∂((volume.prod ν).map (splitE F κ)) = (∫⁻ x, ‖a x‖ₑ ^ 2) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν` using `fun a => by`. Rewrite using `[hint]`. Establish `e1 : ∀ p, ‖pureA F a g (splitE F κ p)‖ₑ ^ 2 = ‖a p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2`. Introduce `p`. Rewrite using `[pureA_splitE, enorm_mul, mul_pow]`.

Repeatedly rewrite using `[e1]`. Rewrite using `[lintegral_prod_mul (a.continuous.measurable.enorm.pow_const 2).aemeasurable (hgc.measurable.enorm.pow_const 2).aemeasurable]`. Use `hU _ hμH _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)` as an intermediate fact. Rewrite `this` using `[h g hg, hp, hp]`. Conclude with `(ENNReal.mul_left_inj hC0 hC).1 this`.
-/
theorem lintegral_eq {S : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hU : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) {f f' : SInf F κ}
    (h : ∀ g ∈ SB (κ → Af F), S (pureA F f g) = pureA F f' g) : ∫⁻ x, ‖f' x‖ₑ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 := by
  obtain ⟨g, hg, h₁⟩ := exists_sb_one (F := F) (κ := κ)
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ)
      (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em
  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]
  have hC0 : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ 0 := fun h0 => by
    rw [lintegral_eq_zero_iff (hgc.measurable.enorm.pow_const 2)] at h0
    have h2 : g =ᵐ[ν] 0 := h0.mono fun y hy => by simpa using hy
    have := congrFun ((hgc.ae_eq_iff_eq ν continuous_zero).1 h2) 0
    simp [h₁] at this
  have hp : ∀ a : SInf F κ, ∫⁻ x, ‖pureA F a g x‖ₑ ^ 2 ∂((volume.prod ν).map (splitE F κ)) =
      (∫⁻ x, ‖a x‖ₑ ^ 2) * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν := fun a => by
    rw [hint]
    have e1 : ∀ p, ‖pureA F a g (splitE F κ p)‖ₑ ^ 2 = ‖a p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (a.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable]
  have := hU _ hμH _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)
  rw [h g hg, hp, hp] at this
  exact (ENNReal.mul_left_inj hC0 hC).1 this

end Unit

end GlobalTheory.ThK.Dbl.Dense

end
