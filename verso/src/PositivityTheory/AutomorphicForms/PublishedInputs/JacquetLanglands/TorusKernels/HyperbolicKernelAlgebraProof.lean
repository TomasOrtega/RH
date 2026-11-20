import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.HyperbolicKernelAlgebraLemmas

variable {F : Type} [Field F] [NumberField F]

def rotA (θ : TR.Rinf F) : GL (Fin 2) (TR.Rinf F) where
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
theorem rotA_add (θ η : TR.Rinf F) : rotA (θ + η) = rotA θ * rotA η := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Real.cos_add, Real.sin_add] <;> ring

omit [NumberField F] in
/- English proof (translation)
Use extensionality with `i j v`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [rotA]`.
-/
theorem rotA_zero : rotA (0 : TR.Rinf F) = 1 := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rotA]

/- English proof (translation)
Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_` and prove the remaining obligations. Establish `h : HasDerivAt (fun t : ℝ => t * θ v) (θ v) 0` using `by simpa using (hasDerivAt_id (0 : ℝ)).mul_const (θ v)`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Simplify `h.cos` using `[rotA]`. Simplify `h.sin` using `[rotA]`.

Simplify `h.sin.fun_neg` using `[rotA]`. Simplify `h.cos` using `[rotA]`.
-/
theorem rotA_deriv (θ : TR.Rinf F) :
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
Establish `e : (TR.toL !![0, θ; -θ, 0] : TR.Lie F 2) = ∑ v, θ v • ((TR.toL (Matrix.single 0 1 (Pi.single v 1)) : TR.Lie F 2) - TR.toL (Matrix.single 1 0 (Pi.single v 1)))`. Use extensionality with `i j w`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Finset.sum_apply, Matrix.single, Pi.single_apply]`. Rewrite using `[e, map_sum, LinearMap.sum_apply, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, ← hw v]`. Simplify using `only [TR.Eop]`. Use `congr!`.
-/
theorem lie_rotV {k : InfinitePlace F → ℕ} {φ : TR.Sm F 2}
    (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ) (θ : TR.Rinf F) :
    TR.lie F 2 (TR.toL !![0, θ; -θ, 0]) φ = (∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ)) • φ := by
  classical
  have e : (TR.toL !![0, θ; -θ, 0] : TR.Lie F 2) = ∑ v, θ v • ((TR.toL (Matrix.single 0 1 (Pi.single v 1)) : TR.Lie F 2) -
      TR.toL (Matrix.single 1 0 (Pi.single v 1))) := by
    ext i j w
    fin_cases i <;> fin_cases j <;> simp [Finset.sum_apply, Matrix.single, Pi.single_apply]
  rw [e, map_sum, LinearMap.sum_apply, Finset.sum_smul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, map_sub, LinearMap.smul_apply, LinearMap.sub_apply, mul_comm, mul_smul, ← hw v]
  simp only [TR.Eop]
  congr!

/- English proof (translation)
Use `set s : ℂ := ∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ) with hs`. Use `set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rotA (t • θ))) with hf`. Establish `hd : ∀ t, HasDerivAt f (s * f t) t` using `fun t => by`. Establish `h1` using `TR.hasDerivAt_curve φ (g * TR.infGL F 2 (rotA (t • θ))) (fun u : ℝ => rotA (u • θ)) _ (by simp [rotA_zero]) (rotA_deriv θ)`. Rewrite `h1` using `[← TR.lie_apply, lie_rotV hw]`.

Establish `h2 : HasDerivAt (fun u : ℝ => f (t + u)) (s * f t) 0`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Simplify using `only [hf, add_smul, rotA_add, map_mul, mul_assoc]`. Both sides reduce to the same expression. Establish `h3` using `HasDerivAt.comp_add_const t (-t) (f := fun u : ℝ => f (t + u)) (by simpa using h2)`.

Simplify using `using h3`. Establish `he : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-s * t)) (Complex.exp (-s * t) * -s) t` using `fun t => by`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp`. Establish `hz : ∀ t, HasDerivAt (fun t : ℝ => f t * Complex.exp (-s * t)) 0 t` using `fun t => by`. Use `(hd t).fun_mul (he t)` as an intermediate fact.

Rewrite `this` using `[show s * f t * Complex.exp (-s * t) + f t * (Complex.exp (-s * t) * -s) = 0 by ring]`. Then use the resulting hypothesis. Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hz t).differentiableAt) (fun t => (hz t).deriv) 1 0`. Simplify `hc` using `[hf, rotA_zero]`.
-/
theorem rot_eq {k : InfinitePlace F → ℕ} {φ : TR.Sm F 2}
    (hw : ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = (Complex.I * k v) • φ) (θ : TR.Rinf F) (g : GA F 2) :
    φ.1 (g * TR.infGL F 2 (rotA θ)) * Complex.exp (-∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ)) = φ.1 g := by
  set s : ℂ := ∑ v, Complex.I * k v * ((θ v : ℝ) : ℂ) with hs
  set f : ℝ → ℂ := fun t => φ.1 (g * TR.infGL F 2 (rotA (t • θ))) with hf
  have hd : ∀ t, HasDerivAt f (s * f t) t := fun t => by
    have h1 := TR.hasDerivAt_curve φ (g * TR.infGL F 2 (rotA (t • θ))) (fun u : ℝ => rotA (u • θ)) _
      (by simp [rotA_zero]) (rotA_deriv θ)
    rw [← TR.lie_apply, lie_rotV hw] at h1
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
  simpa [hf, rotA_zero] using hc

/- English proof (translation)
Establish `h1 : TR.pInf F (TR.infId F ρ).val = ρ.val`. Express the relevant statement in the definitionally equal form `TR.pInf F (1 - TR.sInf F 1 + TR.sInf F _) = _`. Establish `h : ∀ x, TR.pInf F (TR.sInf F x) = x` using `fun x => (TR.infEq F).symm_apply_apply x`. Simplify using `[h]`. Establish `h2 : pFin F (TR.infId F ρ).val = 1`.

Express the relevant statement in the definitionally equal form `(1 : Af F) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Use `TR.ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[TR.pInf_infGL]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h1]`. Rewrite using `[TR.pFin_infGL]`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map, h2]`.
-/
theorem infGL_scalar (ρ : (TR.Rinf F)ˣ) :
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
Take `⟨n, hn, e⟩` from `isOfFinOrder_iff_pow_eq_one.1 h`. Establish `e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n`. Use `Units.ext (funext fun i => ?_)` and prove the remaining obligations. Establish `: (n : ℝ) ≠ 0` using `by positivity`. Simplify using `only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1, map_pow, map_pow]`. Establish `e2 : ω.1 ^ n = 1` using `congrArg Subtype.val e`. Conclude with `DFunLike.congr_fun e2 _`.
-/
theorem fin_expU {ω : HChar F} (h : IsOfFinOrder ω) (z : TR.Rinf F) : ω.1 (TR.infId F (TR.expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

/- English proof (translation)
Rewrite using `[infGL_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent, fin_expU hω]`. Simplify using the standard rewrite rules.
-/
theorem scal {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (z : TR.Rinf F) (h : GA F 2) :
    φ.1 (h * TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) (TR.expU z))) = φ.1 h := by
  rw [infGL_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent, fin_expU hω]
  simp

/- English proof (translation)
The claim follows from `TR.ga_ext (by simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, one_mul]) (by simp only [map_mul, TR.pFin_infGL, pFin_finGL, mul_one, one_mul])`.
-/
theorem inf_fin_comm (y : GL (Fin 2) (TR.Rinf F)) (x : GF F) :
    TR.infGL F 2 y * finGL F 2 x = finGL F 2 x * TR.infGL F 2 y :=
  TR.ga_ext (by simp only [map_mul, TR.pInf_infGL, TR.pInf_finGL, mul_one, one_mul])
    (by simp only [map_mul, TR.pFin_infGL, pFin_finGL, mul_one, one_mul])

/- English proof (translation)
Establish `hgv : ∀ v i j, (gv v r) i j = r i j v` using `fun v i j => rfl`. Establish `hE : ∀ v, r 1 1 v = r 0 0 v ∧ r 1 0 v = -r 0 1 v` using `fun v => by`. Establish `h1` using `congrArg Subtype.val (hr v)`. Rewrite `h1` using `[coe_smul, div_eq_iff (den_ne _ iP.2)]`. Establish `hre` using `congrArg Complex.re h1`.

Establish `him` using `congrArg Complex.im h1`. Simplify using `[num, den, iP, hgv] at hre him`. Apply the tactic sequence `constructor <;> linarith`. Use `set w : InfinitePlace F → ℂ := fun v => ⟨r 0 0 v, r 0 1 v⟩ with hw`. Establish `hw0 : ∀ v, w v ≠ 0` using `fun v h0 => by`.

Establish `ha : r 0 0 v = 0` using `congrArg Complex.re h0`. Establish `hb : r 0 1 v = 0` using `congrArg Complex.im h0`. Apply `(gv v r).det_ne_zero` to reduce the goal to its premises. Rewrite using `[det_eq]`. Simplify using `only [hgv, (hE v).1, (hE v).2, ha, hb]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hρ : ∀ v, 0 < ‖w v‖` using `fun v => norm_pos_iff.2 (hw0 v)`. Use `set θ : TR.Rinf F := fun v => Complex.arg (w v) with hθ`. Use `set u := TR.expU (fun v => Real.log ‖w v‖) with hu0`. Establish `hu : ∀ v, (u : TR.Rinf F) v = ‖w v‖` using `fun v => by`.

Rewrite using `[hu0, TR.expU_val, Real.exp_log (hρ v)]`. Establish `hc : ∀ v, Real.cos (θ v) = r 0 0 v / ‖w v‖` using `fun v => Complex.cos_arg (hw0 v)`. Establish `hs : ∀ v, Real.sin (θ v) = r 0 1 v / ‖w v‖` using `fun v => Complex.sin_arg _`. Establish `hdec : r = Matrix.GeneralLinearGroup.scalar (Fin 2) u * rotA θ`. Use extensionality with `i j v`.

Establish `h0` using `(hρ v).ne'`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, hu, hc, hs, (hE v).1, (hE v).2] <;>`. Clear the denominators using the available nonvanishing facts. Establish `hj : ∀ v, j1 (k v) (gv v r) iP = Complex.exp (-(Complex.I * k v * ((θ v : ℝ) : ℂ)))` using `fun v => by`.

Unfold `j1`. Establish `hden : den (gv v r) iP.1 = (‖w v‖ : ℂ) * Complex.exp (-((θ v : ℝ) : ℂ) * Complex.I)`. Rewrite using `[Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]`. Establish `h0` using `(hρ v).ne'`. Apply the tactic sequence `apply Complex.ext <;> simp [den, hgv, (hE v).1, (hE v).2, iP] <;> field_simp`.

Establish `hdet : |(gv v r).val.det| = ‖w v‖ ^ 2`. Rewrite using `[det_eq, Complex.sq_norm, Complex.normSq_apply]`. Simplify using `only [hgv, (hE v).1, (hE v).2, hw]`. Rewrite using `[abs_of_nonneg (by nlinarith [mul_self_nonneg (r 0 0 v), mul_self_nonneg (r 0 1 v)])]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hp : (‖w v‖ ^ 2) ^ (-(k v : ℝ) / 2) = (‖w v‖ ^ (k v))⁻¹`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast, ← Real.rpow_neg (norm_nonneg _)]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hden, hdet, hp, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_inv, Complex.ofReal_pow, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (hρ v).ne')), one_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hinf : h * TR.infGL F 2 r = (h * TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) * TR.infGL F 2 (rotA θ)`. Rewrite using `[mul_assoc, ← map_mul, ← hdec]`.

Rewrite using `[Finset.prod_congr rfl fun v _ => hj v, ← Complex.exp_sum, Finset.sum_neg_distrib, hinf, rot_eq hφ.wt θ, hu0, scal hω hφ]`.
-/
theorem stab {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (r : GL (Fin 2) (TR.Rinf F)) (hr : ∀ v, gv v r • iP = iP) (h : GA F 2) :
    φ.1 (h * TR.infGL F 2 r) * ∏ v, j1 (k v) (gv v r) iP = φ.1 h := by
  have hgv : ∀ v i j, (gv v r) i j = r i j v := fun v i j => rfl
  have hE : ∀ v, r 1 1 v = r 0 0 v ∧ r 1 0 v = -r 0 1 v := fun v => by
    have h1 := congrArg Subtype.val (hr v)
    rw [coe_smul, div_eq_iff (den_ne _ iP.2)] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [num, den, iP, hgv] at hre him
    constructor <;> linarith
  set w : InfinitePlace F → ℂ := fun v => ⟨r 0 0 v, r 0 1 v⟩ with hw
  have hw0 : ∀ v, w v ≠ 0 := fun v h0 => by
    have ha : r 0 0 v = 0 := congrArg Complex.re h0
    have hb : r 0 1 v = 0 := congrArg Complex.im h0
    apply (gv v r).det_ne_zero
    rw [det_eq]
    simp only [hgv, (hE v).1, (hE v).2, ha, hb]
    ring
  have hρ : ∀ v, 0 < ‖w v‖ := fun v => norm_pos_iff.2 (hw0 v)
  set θ : TR.Rinf F := fun v => Complex.arg (w v) with hθ
  set u := TR.expU (fun v => Real.log ‖w v‖) with hu0
  have hu : ∀ v, (u : TR.Rinf F) v = ‖w v‖ := fun v => by
    rw [hu0, TR.expU_val, Real.exp_log (hρ v)]
  have hc : ∀ v, Real.cos (θ v) = r 0 0 v / ‖w v‖ := fun v => Complex.cos_arg (hw0 v)
  have hs : ∀ v, Real.sin (θ v) = r 0 1 v / ‖w v‖ := fun v => Complex.sin_arg _
  have hdec : r = Matrix.GeneralLinearGroup.scalar (Fin 2) u * rotA θ := by
    ext i j v
    have h0 := (hρ v).ne'
    fin_cases i <;> fin_cases j <;>
      simp [rotA, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.GeneralLinearGroup.scalar, hu, hc, hs, (hE v).1, (hE v).2] <;>
      field_simp
  have hj : ∀ v, j1 (k v) (gv v r) iP = Complex.exp (-(Complex.I * k v * ((θ v : ℝ) : ℂ))) := fun v => by
    unfold j1
    have hden : den (gv v r) iP.1 = (‖w v‖ : ℂ) * Complex.exp (-((θ v : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
      have h0 := (hρ v).ne'
      apply Complex.ext <;> simp [den, hgv, (hE v).1, (hE v).2, iP] <;> field_simp
    have hdet : |(gv v r).val.det| = ‖w v‖ ^ 2 := by
      rw [det_eq, Complex.sq_norm, Complex.normSq_apply]
      simp only [hgv, (hE v).1, (hE v).2, hw]
      rw [abs_of_nonneg (by nlinarith [mul_self_nonneg (r 0 0 v), mul_self_nonneg (r 0 1 v)])]
      ring
    have hp : (‖w v‖ ^ 2) ^ (-(k v : ℝ) / 2) = (‖w v‖ ^ (k v))⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast, ← Real.rpow_neg (norm_nonneg _)]
      congr 1
      push_cast
      ring
    rw [hden, hdet, hp, mul_pow, ← Complex.exp_nat_mul, Complex.ofReal_inv, Complex.ofReal_pow, mul_right_comm,
      mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast (hρ v).ne')), one_mul]
    congr 1
    ring
  have hinf : h * TR.infGL F 2 r =
      (h * TR.infGL F 2 (Matrix.GeneralLinearGroup.scalar (Fin 2) u)) * TR.infGL F 2 (rotA θ) := by
    rw [mul_assoc, ← map_mul, ← hdec]
  rw [Finset.prod_congr rfl fun v _ => hj v, ← Complex.exp_sum, Finset.sum_neg_distrib, hinf, rot_eq hφ.wt θ,
    hu0, scal hω hφ]

/- English proof (translation)
Take `⟨r, rfl⟩ : ∃ r, g' = g * r` from `⟨g⁻¹ * g', by group⟩`. Establish `hs : ∀ v, gv v r • iP = iP` using `fun v => by`. Use `h v` as an intermediate fact. Rewrite `this` using `[map_mul, mul_smul]`. Conclude with `((smul_left_cancel_iff _).1 this).symm`.

Establish `hj : ∀ v, j1 (k v) (gv v (g * r)) iP = j1 (k v) (gv v g) iP * j1 (k v) (gv v r) iP` using `fun v => by`. Rewrite using `[map_mul, hB.1, hs v]`. Establish `hc : TR.infGL F 2 (g * r) * finGL F 2 x = (TR.infGL F 2 g * finGL F 2 x) * TR.infGL F 2 r`. Rewrite using `[map_mul, mul_assoc, mul_assoc, inf_fin_comm]`. Rewrite using `[Finset.prod_congr rfl fun v _ => hj v, Finset.prod_mul_distrib, hc, ← stab hω hφ r hs (TR.infGL F 2 g * finGL F 2 x)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem key (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) {φ : TR.Sm F 2}
    (hφ : IsHolV k c ω φ) (g g' : GL (Fin 2) (TR.Rinf F)) (x : GF F) (h : ∀ v, gv v g • iP = gv v g' • iP) :
    φ.1 (TR.infGL F 2 g' * finGL F 2 x) * ∏ v, j1 (k v) (gv v g') iP =
      φ.1 (TR.infGL F 2 g * finGL F 2 x) * ∏ v, j1 (k v) (gv v g) iP := by
  obtain ⟨r, rfl⟩ : ∃ r, g' = g * r := ⟨g⁻¹ * g', by group⟩
  have hs : ∀ v, gv v r • iP = iP := fun v => by
    have := h v
    rw [map_mul, mul_smul] at this
    exact ((smul_left_cancel_iff _).1 this).symm
  have hj : ∀ v, j1 (k v) (gv v (g * r)) iP = j1 (k v) (gv v g) iP * j1 (k v) (gv v r) iP := fun v => by
    rw [map_mul, hB.1, hs v]
  have hc : TR.infGL F 2 (g * r) * finGL F 2 x = (TR.infGL F 2 g * finGL F 2 x) * TR.infGL F 2 r := by
    rw [map_mul, mul_assoc, mul_assoc, inf_fin_comm]
  rw [Finset.prod_congr rfl fun v _ => hj v, Finset.prod_mul_distrib, hc,
    ← stab hω hφ r hs (TR.infGL F 2 g * finGL F 2 x)]
  ring

end UpperTheory.Esk.HyperbolicKernelAlgebraLemmas

/- English proof (translation)
Introduce `hB _ F _ _ _ k c ω φ hω hφ`. Use `⟨fun p => if h : ∃ g : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP) = p.1 then φ.1 (TR.infGL F 2 h.choose * finGL F 2 p.2) * ∏ v, UpperTheory.Esk.j1 (k v) (UpperTheory.Esk.gv v h.choose) UpperTheory.Esk.iP else 0, fun g x => ?_⟩` and prove the remaining obligations. Establish `h : ∃ g' : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g' • UpperTheory.Esk.iP) = fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP` using `⟨g, rfl⟩`. Simplify using `only`. Rewrite using `[dif_pos h]`.

Conclude with `UpperTheory.Esk.HyperbolicKernelAlgebraLemmas.key hB hω hφ h.choose g x fun v => congrFun h.choose_spec v`.
-/
theorem UpperTheory.Esk.hyperbolic_kernel_algebra_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.H1a := by
  intro hB _ F _ _ _ k c ω φ hω hφ
  classical
  refine ⟨fun p => if h : ∃ g : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP) = p.1 then
      φ.1 (TR.infGL F 2 h.choose * finGL F 2 p.2) * ∏ v, UpperTheory.Esk.j1 (k v) (UpperTheory.Esk.gv v h.choose) UpperTheory.Esk.iP else 0,
    fun g x => ?_⟩
  have h : ∃ g' : GL (Fin 2) (TR.Rinf F), (fun v => UpperTheory.Esk.gv v g' • UpperTheory.Esk.iP) = fun v => UpperTheory.Esk.gv v g • UpperTheory.Esk.iP :=
    ⟨g, rfl⟩
  dsimp only
  rw [dif_pos h]
  exact UpperTheory.Esk.HyperbolicKernelAlgebraLemmas.key hB hω hφ h.choose g x fun v => congrFun h.choose_spec v
