import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.StrongApp
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPosNatMemOpenAdeleSubgroup

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep Filter Topology
open scoped Matrix

namespace UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F]

private def rotA (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
  val := !![fun v => Real.cos (θ v), fun v => Real.sin (θ v); fun v => -Real.sin (θ v), fun v => Real.cos (θ v)]
  inv := !![fun v => Real.cos (θ v), fun v => -Real.sin (θ v); fun v => Real.sin (θ v), fun v => Real.cos (θ v)]
  val_inv := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith
  inv_val := by
    ext i j v
    have := Real.sin_sq_add_cos_sq (θ v)
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> nlinarith

omit [NumberField F] in
/- English proof (translation)
Use extensionality with `i j v`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring`.
-/
private theorem rotA_add (θ η : TR.Rinf F) : rotA (θ + η) = rotA θ * rotA η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
/- English proof (translation)
Use extensionality with `i j v`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rotA]`.
-/
private theorem rotA_zero : rotA (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA]

/- English proof (translation)
Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_` and prove the remaining obligations. Establish `h : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `h.cos` using `[rotA]`. Simplify `h.sin` using `[rotA]`.

Simplify `h.sin.fun_neg` using `[rotA]`. Simplify `h.cos` using `[rotA]`.
-/
private theorem rotA_deriv (θ : TR.Rinf F) :
    HasDerivAt (fun t : ℝ => TR.toL (rotA (t • θ)).val) (TR.toL !![0, θ; -θ, 0]) 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  have h : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0 := by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)
  fin_cases i <;> fin_cases j
  · simpa [rotA] using h.cos
  · simpa [rotA] using h.sin
  · simpa [rotA] using h.sin.fun_neg
  · simpa [rotA] using h.cos

variable [IsTotallyReal F]

/- English proof (translation)
Establish `e : (TR.toL !![0, θ; -θ, 0] : TR.Lie F 2) = ∑ v, θ v • ((TR.toL (Matrix.single 0 1 (Pi.single v 1)) : TR.Lie F 2) - TR.toL (Matrix.single 1 0 (Pi.single v 1)))`. Use extensionality with `i j w`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Finset.sum_apply, Matrix.single, Pi.single_apply]`. Rewrite using `[e, map_sum, LinearMap.sum_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, ← hw v]`. Simplify using `only [TR.Eop]`. Use `congr!`.
-/
private theorem lie_rot {k : ℕ} {φ : TR.Sm F 2} (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ)
    (θ : TR.Rinf F) : TR.lie F 2 (TR.toL !![0, θ; -θ, 0]) φ = (Complex.I * k * ((∑ v, θ v : ℝ) : ℂ)) • φ := by
  classical
  have e : (TR.toL !![0, θ; -θ, 0] : TR.Lie F 2) = ∑ v, θ v • ((TR.toL (Matrix.single 0 1 (Pi.single v 1)) : TR.Lie F 2) -
      TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [Finset.sum_apply, Matrix.single, Pi.single_apply]
  rw [e, map_sum, LinearMap.sum_apply, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, ← hw v]
  simp only [TR.Eop]
  congr!

/- English proof (translation)
Use `set s : ℂ := Complex.I * k * ((∑ v, θ v : ℝ) : ℂ) with hs`. Use `set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rotA (t • θ))) with hf`. Establish `hd : ∀ t, HasDerivAt f (s * f t) t` using `fun t => by`. Establish `h1` using `TR.hasDerivAt_curve φ (g * TR.infGL F 2 (rotA (t • θ))) (fun u : ℝ => rotA (u • θ)) _ (by simp [rotA_zero]) (rotA_deriv θ)`. Rewrite `h1` using `[← TR.lie_apply, lie_rot hw]`.

Establish `h2 : HasDerivAt (fun u : ℝ => f (t + u)) (s * f t) 0`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [hf, add_smul, rotA_add, map_mul, mul_assoc]`. Both sides reduce to the same expression. Establish `h3` using `HasDerivAt.comp_add_const t (-t) (f := fun u : ℝ => f (t + u)) (by simpa using h2)`.

Simplify using `using h3`. Establish `he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-s * t)) (Complex.exp (-s * t) * -s) t` using `fun t => by`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp`. Establish `hz : ∀ t, HasDerivAt (fun t : ℝ => f t * Complex.exp (-s * t)) 0 t` using `fun t => by`. Use `(hd t).fun_mul (he t)` as an intermediate fact.

Rewrite `this` using `[show s * f t * Complex.exp (-s * t) + f t * (Complex.exp (-s * t) * -s) = 0 by ring]`. Then use the resulting hypothesis. Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0`. Establish `hn : ‖Complex.exp (-s)‖ = 1`. Rewrite using `[Complex.norm_exp, hs]`. Simplify using the standard rewrite rules.

Use `congrArg norm hc` as an intermediate fact. Simplify `this` using `[hf, hn, rotA_zero]`.
-/
private theorem norm_rot {k : ℕ} {φ : TR.Sm F 2} (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k) • φ)
    (θ : TR.Rinf F) (g : GA F 2) : ‖φ.1 (g * TR.infGL F 2 (rotA θ))‖ = ‖φ.1 g‖ := by
  set s : ℂ := Complex.I * k * ((∑ v, θ v : ℝ) : ℂ) with hs
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rotA (t • θ))) with hf
  have hd : ∀ t, HasDerivAt f (s * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (rotA (t • θ))) (fun u : ℝ => rotA (u • θ)) _
      (by simp [rotA_zero]) (rotA_deriv θ)
    rw [← TR.lie_apply, lie_rot hw] at h1
    have h2 : HasDerivAt (fun u : ℝ => f (t + u)) (s * f t) 0 := by
      convert h1 using 2
      · simp only [hf, add_smul, rotA_add, map_mul, mul_assoc]
      · rfl
    have h3 := HasDerivAt.comp_add_const t (-t) (f := fun u : ℝ => f (t + u)) (by simpa using h2)
    simpa using h3
  have he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-s * t)) (Complex.exp (-s * t) * -s) t := fun t => by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp
  have hz : ∀ t, HasDerivAt (fun t : ℝ => f t * Complex.exp (-s * t)) 0 t := fun t => by
    have := (hd t).fun_mul (he t)
    rwa [show s * f t * Complex.exp (-s * t) + f t * (Complex.exp (-s * t) * -s) = 0 by ring] at this
  have hc := is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0
  have hn : ‖Complex.exp (-s)‖ = 1 := by
    rw [Complex.norm_exp, hs]
    simp
  have := congrArg norm hc
  simpa [hf, hn, rotA_zero] using this

omit [NumberField F] [IsTotallyReal F] in
/- English proof (translation)
Set `z : InfinitePlace F → ℂ` to `fun v => ⟨h 1 1 v, -h 1 0 v⟩`. Establish `hdet : ∀ v, (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v = h 0 0 v * h 1 1 v - h 0 1 v * h 1 0 v` using `fun v => by`. Rewrite using `[Matrix.det_fin_two]`. Both sides reduce to the same expression. Establish `hz : ∀ v, z v ≠ 0` using `fun v h0 => by`.

Establish `h1 : h 1 1 v = 0` using `congrArg Complex.re h0`. Establish `h2 : -h 1 0 v = 0` using `congrArg Complex.im h0`. Use `hd v` as an intermediate fact. Rewrite `this` using `[hdet, h1, neg_eq_zero.1 h2]`. Simplify using `at this`.

Establish `hr : ∀ v, 0 < ‖z v‖` using `fun v => norm_pos_iff.2 (hz v)`. Establish `hsq : ∀ v, h 1 0 v ^ 2 + h 1 1 v ^ 2 = ‖z v‖ ^ 2` using `fun v => by`. Rewrite using `[Complex.sq_norm, Complex.normSq_apply]`. Simplify using `only [z]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hy : ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v / (h 1 0 v ^ 2 + h 1 1 v ^ 2)` using `fun v => div_pos (hd v) (by rw [hsq]; exact pow_pos (hr v) 2)`. Set `U : (f : TR.Rinf F) → (∀ v, 0 < f v) → (TR.Rinf F)ˣ` to `fun f hf => ⟨f, fun v => (f v)⁻¹, funext fun v => mul_inv_cancel₀ (hf v).ne', funext fun v => inv_mul_cancel₀ (hf v).ne'⟩`. Use `⟨U _ hr, U _ hy, fun v => (h 0 0 v * h 1 0 v + h 0 1 v * h 1 1 v) / (h 1 0 v ^ 2 + h 1 1 v ^ 2), fun v => Complex.arg (z v), ?_, hy, fun v => rfl⟩` and prove the remaining obligations. Use extensionality with `i j v`. Establish `hc : Real.cos (Complex.arg (z v)) = h 1 1 v / ‖z v‖` using `Complex.cos_arg (hz v)`.

Establish `hs : Real.sin (Complex.arg (z v)) = -h 1 0 v / ‖z v‖` using `Complex.sin_arg _`. Establish `h0` using `(hr v).ne'`. Establish `h1` using `hsq v`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [U, rotA, aff, Matrix.mul_apply, Fin.sum_univ_succ, hc, hs, hdet, h1, Matrix.GeneralLinearGroup.scalar] <;>`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(h.val 0 0 v)) * h1`. Take the linear combination `(-(h.val 0 1 v)) * h1`.
-/
private theorem iwasawa (h : GL (Fin 2) (TR.Rinf F)) (hd : ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v) :
    ∃ (ρ y : (TR.Rinf F)ˣ) (x θ : TR.Rinf F), h = Matrix.GeneralLinearGroup.scalar (Fin 2) ρ * (aff y x * rotA θ) ∧
      (∀ v, 0 < y.val v) ∧ ∀ v, y.val v = (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v / (h 1 0 v ^ 2 + h 1 1 v ^ 2) := by
  let z : InfinitePlace F → ℂ := fun v => ⟨h 1 1 v, -h 1 0 v⟩
  have hdet : ∀ v, (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v = h 0 0 v * h 1 1 v - h 0 1 v * h 1 0 v := fun v => by
    rw [Matrix.det_fin_two]; rfl
  have hz : ∀ v, z v ≠ 0 := fun v h0 => by
    have h1 : h 1 1 v = 0 := congrArg Complex.re h0
    have h2 : -h 1 0 v = 0 := congrArg Complex.im h0
    have := hd v
    rw [hdet, h1, neg_eq_zero.1 h2] at this
    simp at this
  have hr : ∀ v, 0 < ‖z v‖ := fun v => norm_pos_iff.2 (hz v)
  have hsq : ∀ v, h 1 0 v ^ 2 + h 1 1 v ^ 2 = ‖z v‖ ^ 2 := fun v => by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp only [z]; ring
  have hy : ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v / (h 1 0 v ^ 2 + h 1 1 v ^ 2) := fun v =>
    div_pos (hd v) (by rw [hsq]; exact pow_pos (hr v) 2)
  let U : (f : TR.Rinf F) → (∀ v, 0 < f v) → (TR.Rinf F)ˣ := fun f hf =>
    ⟨f, fun v => (f v)⁻¹, funext fun v => mul_inv_cancel₀ (hf v).ne', funext fun v => inv_mul_cancel₀ (hf v).ne'⟩
  refine ⟨U _ hr, U _ hy, fun v => (h 0 0 v * h 1 0 v + h 0 1 v * h 1 1 v) / (h 1 0 v ^ 2 + h 1 1 v ^ 2),
    fun v => Complex.arg (z v), ?_, hy, fun v => rfl⟩
  ext i j v
  have hc : Real.cos (Complex.arg (z v)) = h 1 1 v / ‖z v‖ := Complex.cos_arg (hz v)
  have hs : Real.sin (Complex.arg (z v)) = -h 1 0 v / ‖z v‖ := Complex.sin_arg _
  have h0 := (hr v).ne'
  have h1 := hsq v
  fin_cases i <;> fin_cases j <;>
    simp [U, rotA, aff, Matrix.mul_apply, Fin.sum_univ_succ, hc, hs, hdet, h1, Matrix.GeneralLinearGroup.scalar] <;>
    field_simp
  · linear_combination (-(h.val 0 0 v)) * h1
  · linear_combination (-(h.val 0 1 v)) * h1

omit [IsTotallyReal F] in
/- English proof (translation)
Use `finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 ?_` and prove the remaining obligations. Conclude with `(y.isUnit.map (pLoc F w)).ne_zero`.
-/
private theorem absF_pos (y : (Af F)ˣ) : 0 < absF y := by
  refine finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 ?_
  exact (y.isUnit.map (pLoc F w)).ne_zero

/- English proof (translation)
Establish `h1 : TR.pInf F (TR.infId F ρ).val = ρ.val`. Express the relevant statement in the definitionally equal form `TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _`. Establish `h : ∀ x, TR.pInf F (TR.sInf F x) = x` using `fun x => (TR.infEq F).symm_apply_apply x`. Simplify using `[h]`. Establish `h2 : pFin F (TR.infId F ρ).val = 1`.

Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Use `TR.ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[TR.pInf_infGL]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h1]`. Rewrite using `[TR.pFin_infGL]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h2]`.
-/
private theorem infGL_scalar (ρ : (TR.Rinf F)ˣ) :
    TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) ρ) = Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.infId F ρ) := by
  have h1 : TR.pInf F (TR.infId F ρ).val = ρ.val := by
    change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _
    have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
    simp [h]
  have h2 : pFin F (TR.infId F ρ).val = 1 := by
    change (1 : Af F) - 0 + 0 = 1
    simp
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h1]
  · rw [TR.pFin_infGL]
    refine Units.ext (Matrix.ext fun i j => ?_)
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h2]

/- English proof (translation)
Take `⟨ρ, y, x, θ, e, hy, hy'⟩` from `iwasawa h hd`. Establish `hc : ∀ t, coefAt a t = 0` using `fun t => by`. Unfold `coefAt`. Use `split_ifs with h`. Conclude with `ha _ h.choose_spec.1`.

Both sides reduce to the same expression. Establish `h1` using `he x y hy yf`. Simplify using `only [hc, zero_mul] at h1`. Establish `h2` using `sub_eq_zero.1 (h1.unique hasSum_zero)`. Establish `hp : 0 < ((∏ v, y.val v) * absF yf) ^ ((k : ℝ) / 2)` using `Real.rpow_pos_of_pos (mul_pos (Finset.prod_pos fun v _ => hy v) (absF_pos yf)) _`.

Rewrite `h2` using `[div_eq_iff (by exact_mod_cast hp.ne')]`. Establish `hn : ‖((ω.1 (TR.infId F ρ) : ℂˣ) : ℂ)‖ = 1`. Take `⟨n, hn, e⟩` from `isOfFinOrder_iff_pow_eq_one.1 hω`. Establish `: (ω.1 (TR.infId F ρ)) ^ n = 1` using `congrArg (fun χ : HChar F => χ.1 (TR.infId F ρ)) e`. Establish `h3 : ((ω.1 (TR.infId F ρ) : ℂˣ) : ℂ) ^ n = 1`.

Rewrite using `[← Units.val_pow_eq_pow_val, this, Units.val_one]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one h3 hn.ne'`. Simplify using `only [← hy']`. Rewrite using `[e, map_mul, map_mul, infGL_scalar, mul_assoc, hφ.cent, mul_assoc, TR.infGL_comm (rotA θ), ← mul_assoc, norm_mul, hn, one_mul, norm_rot hφ.wt, h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le, mul_comm]`.
-/
private theorem norm_inf {k : ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2} (hφ : IsHol k c ω φ)
    {c₀ a} (he : HasExp φ.1 k c₀ a) (ha : ∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = 0) (yf : (Af F)ˣ) (h : GL (Fin 2) (TR.Rinf F))
    (hd : ∀ v, 0 < (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v) :
    ‖φ.1 (TR.infGL F 2 h * finGL F 2 (aff yf 0))‖ =
      ((∏ v, (h : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v / (h 1 0 v ^ 2 + h 1 1 v ^ 2)) * absF yf) ^ ((k : ℝ) / 2) *
        ‖c₀ yf‖ := by
  obtain ⟨ρ, y, x, θ, e, hy, hy'⟩ := iwasawa h hd
  have hc : ∀ t, coefAt a t = 0 := fun t => by
    unfold coefAt
    split_ifs with h
    · exact ha _ h.choose_spec.1
    · rfl
  have h1 := he x y hy yf
  simp only [hc, zero_mul] at h1
  have h2 := sub_eq_zero.1 (h1.unique hasSum_zero)
  have hp : 0 < ((∏ v, y.val v) * absF yf) ^ ((k : ℝ) / 2) :=
    Real.rpow_pos_of_pos (mul_pos (Finset.prod_pos fun v _ => hy v) (absF_pos yf)) _
  rw [div_eq_iff (by exact_mod_cast hp.ne')] at h2
  have hn : ‖((ω.1 (TR.infId F ρ) : ℂˣ) : ℂ)‖ = 1 := by
    obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hω
    have : (ω.1 (TR.infId F ρ)) ^ n = 1 := congrArg (fun χ : HChar F => χ.1 (TR.infId F ρ)) e
    have h3 : ((ω.1 (TR.infId F ρ) : ℂˣ) : ℂ) ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    exact Complex.norm_eq_one_of_pow_eq_one h3 hn.ne'
  simp only [← hy']
  rw [e, map_mul, map_mul, infGL_scalar, mul_assoc, hφ.cent, mul_assoc, TR.infGL_comm (rotA θ), ← mul_assoc, norm_mul, hn,
    one_mul, norm_rot hφ.wt, h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hp.le, mul_comm]

private def lowA {R : Type} [CommRing R] (x : R) : GL (Fin 2) R where
  val := !![1, 0; x, 1]
  inv := !![1, 0; -x, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [lowA, Matrix.GeneralLinearGroup.map]`.
-/
private theorem map_lowA {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map p (lowA x) = lowA (p x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [lowA, Matrix.GeneralLinearGroup.map]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [lowA] <;> fun_prop`. Express the relevant statement in the definitionally equal form `Continuous fun x : R => (!![1, 0; -x, 1] : Matrix (Fin 2) (Fin 2) R)`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp <;> fun_prop`.
-/
private theorem continuous_lowA {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (lowA : R → GL (Fin 2) R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [lowA] <;> fun_prop
  · change Continuous fun x : R => (!![1, 0; -x, 1] : Matrix (Fin 2) (Fin 2) R)
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

/- English proof (translation)
Use `set t : GL (Fin 2) (Af F) := aff yf 0 with ht`. Establish `hc : Continuous fun x : Af F => t⁻¹ * lowA x * t` using `(continuous_const.mul continuous_lowA).mul continuous_const`. Establish `h0 : t⁻¹ * lowA (0 : Af F) * t ∈ {u | TR.finRep F 2 u φ = φ}`. Establish `: lowA (0 : Af F) = 1`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [lowA]`. Simplify using `[this]`. Take `⟨n, hn⟩` from `(((hc.tendsto 0).comp (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F)).eventually (hφ.aut.level.mem_nhds h0)).exists`. Use `set N : ℕ := n.factorial with hN`. Establish `hN0 : (0 : ℝ) < N` using `by exact_mod_cast n.factorial_pos`.

Establish `hn' : ∀ g, φ.1 (g * finGL F 2 (t⁻¹ * lowA (N : Af F) * t)) = φ.1 g` using `fun g => congrFun (congrArg Subtype.val hn) g`. Establish `e : ratGL F 2 (lowA (N : F)) = TR.infGL F 2 (lowA (N : TR.Rinf F)) * finGL F 2 (lowA (N : Af F))`. Rewrite using `[← TR.infGL_mul_finGL (ratGL F 2 (lowA (N : F))), ratGL, map_lowA, map_lowA, map_lowA]`. Simplify using `only [map_natCast]`. Establish `e2 : φ.1 (TR.infGL F 2 (lowA (N : TR.Rinf F)) * finGL F 2 t) = φ.1 (TR.infGL F 2 1 * finGL F 2 t)`.

Rewrite using `[← hφ.aut.left (lowA (N : F)) (TR.infGL F 2 1 * finGL F 2 t), e, ← hn', map_one, one_mul, mul_assoc, mul_assoc, ← map_mul, mul_inv_cancel_left, map_mul, mul_assoc]`. Establish `d1 : ∀ v, ((lowA (N : TR.Rinf F) : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v = 1` using `fun v => by`. Simplify using `[lowA, Matrix.det_fin_two]`. Establish `n1` using `norm_inf hω hφ he ha yf (lowA (N : TR.Rinf F)) fun v => by rw [d1]; exact one_pos`. Establish `n2` using `norm_inf hω hφ he ha yf 1 fun v => by simp`.

Rewrite `n1` using `[e2, n2]`. Assume the negation of the conclusion as `hne`. Establish `n3` using `mul_right_cancel₀ (norm_ne_zero_iff.2 hne) n1`. Establish `hlt : (∏ v : InfinitePlace F, (1 : ℝ) / ((N : ℝ) ^ 2 + 1)) < 1`. Rewrite using `[Finset.prod_const]`.

Use `pow_lt_one₀ (by positivity) ?_ (Finset.card_ne_zero_of_mem (Finset.mem_univ (Classical.arbitrary _)))` and prove the remaining obligations. Rewrite using `[div_lt_one (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpos : 0 ≤ (∏ v : InfinitePlace F, (1 : ℝ) / ((N : ℝ) ^ 2 + 1))` using `by positivity`. Establish `hA` using `absF_pos yf`.

Establish `hk' : (0 : ℝ) < (k : ℝ) / 2`. Establish `: (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.rpow_lt_rpow (mul_nonneg hpos hA.le) (mul_lt_mul_of_pos_right hlt hA) hk'` as an intermediate fact. Simplify using `only [d1] at n3`.

Use `this.ne ?_` and prove the remaining obligations. Apply the tactic sequence `convert n3.symm using 4 <;> simp [lowA]`.
-/
private theorem const_zero {k : ℕ} (hk : 1 ≤ k) {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHol k c ω φ) {c₀ a} (he : HasExp φ.1 k c₀ a) (ha : ∀ 𝔪, 𝔪 ≠ ⊥ → a 𝔪 = 0) (yf : (Af F)ˣ) : c₀ yf = 0 := by
  set t : GL (Fin 2) (Af F) := aff yf 0 with ht
  have hc : Continuous fun x : Af F => t⁻¹ * lowA x * t := (continuous_const.mul continuous_lowA).mul continuous_const
  have h0 : t⁻¹ * lowA (0 : Af F) * t ∈ {u | TR.finRep F 2 u φ = φ} := by
    have : lowA (0 : Af F) = 1 := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      fin_cases i <;> fin_cases j <;> simp [lowA]
    simp [this]
  obtain ⟨n, hn⟩ := (((hc.tendsto 0).comp (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F)).eventually
    (hφ.aut.level.mem_nhds h0)).exists
  set N : ℕ := n.factorial with hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast n.factorial_pos
  have hn' : ∀ g, φ.1 (g * finGL F 2 (t⁻¹ * lowA (N : Af F) * t)) = φ.1 g := fun g => congrFun (congrArg Subtype.val hn) g
  have e : ratGL F 2 (lowA (N : F)) = TR.infGL F 2 (lowA (N : TR.Rinf F)) * finGL F 2 (lowA (N : Af F)) := by
    rw [← TR.infGL_mul_finGL (ratGL F 2 (lowA (N : F))), ratGL, map_lowA, map_lowA, map_lowA]
    simp only [map_natCast]
  have e2 : φ.1 (TR.infGL F 2 (lowA (N : TR.Rinf F)) * finGL F 2 t) = φ.1 (TR.infGL F 2 1 * finGL F 2 t) := by
    rw [← hφ.aut.left (lowA (N : F)) (TR.infGL F 2 1 * finGL F 2 t), e, ← hn', map_one, one_mul, mul_assoc, mul_assoc,
      ← map_mul, mul_inv_cancel_left, map_mul, mul_assoc]
  have d1 : ∀ v, ((lowA (N : TR.Rinf F) : GL (Fin 2) (TR.Rinf F)) : Matrix (Fin 2) (Fin 2) (TR.Rinf F)).det v = 1 := fun v => by
    simp [lowA, Matrix.det_fin_two]
  have n1 := norm_inf hω hφ he ha yf (lowA (N : TR.Rinf F)) fun v => by rw [d1]; exact one_pos
  have n2 := norm_inf hω hφ he ha yf 1 fun v => by simp
  rw [e2, n2] at n1
  by_contra hne
  have n3 := mul_right_cancel₀ (norm_ne_zero_iff.2 hne) n1
  have hlt : (∏ v : InfinitePlace F, (1 : ℝ) / ((N : ℝ) ^ 2 + 1)) < 1 := by
    rw [Finset.prod_const]
    refine pow_lt_one₀ (by positivity) ?_ (Finset.card_ne_zero_of_mem (Finset.mem_univ (Classical.arbitrary _)))
    rw [div_lt_one (by positivity)]
    nlinarith
  have hpos : 0 ≤ (∏ v : InfinitePlace F, (1 : ℝ) / ((N : ℝ) ^ 2 + 1)) := by positivity
  have hA := absF_pos yf
  have hk' : (0 : ℝ) < (k : ℝ) / 2 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have := Real.rpow_lt_rpow (mul_nonneg hpos hA.le) (mul_lt_mul_of_pos_right hlt hA) hk'
  simp only [d1] at n3
  refine this.ne ?_
  convert n3.symm using 4 <;> simp [lowA]

end UpperTheory.V.Sd

/- English proof (translation)
Introduce `F _ _ _ k hk c ω hω φ hφ c₀ a he ha`. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Take `⟨γ, h, y, u, hu, hd, rfl⟩` from `UpperTheory.V.Sd.strongApp F { carrier := {u | UpperTheory.V.TR.finRep F 2 u φ = φ} one_mem' := by simp mul_mem' := fun {x y} hx hy => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[map_mul, Module.End.mul_apply, hy, hx]`.

Use the proof step `inv_mem' := fun {x} hx => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `conv_lhs => rw [← hx]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] } hφ.aut.level g`. Establish `hu' : ∀ g, φ.1 (g * finGL F 2 u) = φ.1 g` using `fun g => congrFun (congrArg Subtype.val hu) g`.

Rewrite using `[hφ.aut.left, map_mul, ← mul_assoc, hu']`. Use `UpperTheory.V.Sd.norm_inf hω hφ he ha y h hd` as an intermediate fact. Rewrite `this` using `[UpperTheory.V.Sd.const_zero hk hω hφ he ha y, norm_zero, mul_zero]`. Conclude with `norm_eq_zero.1 this`.
-/
theorem UpperTheory.V.Sd.expInj :
    UpperTheory.V.Sd.ExpInj := by
  intro F _ _ _ k hk c ω hω φ hφ c₀ a he ha
  refine Subtype.ext (funext fun g => ?_)
  obtain ⟨γ, h, y, u, hu, hd, rfl⟩ := UpperTheory.V.Sd.strongApp F
    { carrier := {u | UpperTheory.V.TR.finRep F 2 u φ = φ}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] } hφ.aut.level g
  have hu' : ∀ g, φ.1 (g * finGL F 2 u) = φ.1 g := fun g => congrFun (congrArg Subtype.val hu) g
  rw [hφ.aut.left, map_mul, ← mul_assoc, hu']
  have := UpperTheory.V.Sd.norm_inf hω hφ he ha y h hd
  rw [UpperTheory.V.Sd.const_zero hk hω hφ he ha y, norm_zero, mul_zero] at this
  exact norm_eq_zero.1 this
