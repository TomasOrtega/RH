import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.OpGenSt

noncomputable section

open scoped Matrix ContDiff
open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob.OpGenAH

section Local

variable {m n : ℕ}

local notation "EE" => (Fin m → Fin n → ℂ)

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Take `⟨T, rfl⟩` from `hg`. Conclude with `⟨S + T, by ext u; simp⟩`.
-/
theorem isSch_add' {f g : EE → ℂ} (hf : IsSch f) (hg : IsSch g) : IsSch (fun u => f u + g u) := by
  obtain ⟨S, rfl⟩ := hf
  obtain ⟨T, rfl⟩ := hg
  exact ⟨S + T, by ext u; simp⟩

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Conclude with `⟨c • S, by ext u; simp⟩`.
-/
theorem isSch_cmul (c : ℂ) {f : EE → ℂ} (hf : IsSch f) : IsSch (fun u => c * f u) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨c • S, by ext u; simp⟩

def rmulEquiv (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) : EE ≃L[ℝ] EE :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => (Matrix.of u * a : Matrix (Fin m) (Fin n) ℂ)
      invFun := fun u => (Matrix.of u * a⁻¹ : Matrix (Fin m) (Fin n) ℂ)
      map_add' := fun u v => by
        show Matrix.of (u + v) * a = Matrix.of u * a + Matrix.of v * a
        rw [← Matrix.add_mul]; rfl
      map_smul' := fun c u => by
        show Matrix.of (c • u) * a = c • (Matrix.of u * a)
        ext i j
        simp [Matrix.mul_apply, Finset.smul_sum, mul_assoc]
      left_inv := fun u => by
        show Matrix.of u * a * a⁻¹ = u
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]; rfl
      right_inv := fun u => by
        show Matrix.of u * a⁻¹ * a = u
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.mul_one]; rfl }

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Conclude with `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rmulEquiv a ha) S, by ext u; rfl⟩`.
-/
theorem isSch_rmul (a : Matrix (Fin n) (Fin n) ℂ) (ha : IsUnit a.det) {f : EE → ℂ} (hf : IsSch f) :
    IsSch (fun u => f (Matrix.of u * a)) := by
  obtain ⟨S, rfl⟩ := hf
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rmulEquiv a ha) S, by ext u; rfl⟩

/- English proof (translation)
Establish `key : ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) = fun t : ℝ => Complex.I ^ k * Complex.exp (Complex.I * (t : ℂ))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[iteratedDeriv_succ, ih]`. Use function extensionality and compare the values at `t`. Establish `h1 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) (Complex.I * 1) t` using `((hasDerivAt_id t).ofReal_comp).const_mul Complex.I`. Establish `h2` using `(h1.cexp).const_mul (Complex.I ^ k)`. Rewrite using `[h2.deriv]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨ContDiff.cexp (contDiff_const.mul Complex.ofRealCLM.contDiff), fun k => ⟨0, 1, fun x => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[norm_iteratedFDeriv_eq_norm_iteratedDeriv, key]`. Simplify using `only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, pow_zero]`. Rewrite using `[mul_comm Complex.I (x : ℂ), Complex.norm_exp_ofReal_mul_I]`.
-/
theorem hasTemperateGrowth_expI : (fun t : ℝ => Complex.exp (Complex.I * t)).HasTemperateGrowth := by
  have key : ∀ k : ℕ, iteratedDeriv k (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) =
      fun t : ℝ => Complex.I ^ k * Complex.exp (Complex.I * (t : ℂ)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have h1 : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) (Complex.I * 1) t :=
        ((hasDerivAt_id t).ofReal_comp).const_mul Complex.I
      have h2 := (h1.cexp).const_mul (Complex.I ^ k)
      rw [h2.deriv]
      ring
  refine ⟨ContDiff.cexp (contDiff_const.mul Complex.ofRealCLM.contDiff), fun k => ⟨0, 1, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, key]
  simp only [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, pow_zero]
  rw [mul_comm Complex.I (x : ℂ), Complex.norm_exp_ofReal_mul_I]

def coordL (a : Fin m) (i : Fin n) : EE →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C c`. Establish `e : (fun u : EE => evX (C c) u) = fun _ => c` using `by ext u; simp [evX]`. Rewrite using `[e]`. Conclude with `Function.HasTemperateGrowth.const c`.

Consider the case `add p q hp hq`. Establish `e : (fun u : EE => evX (p + q) u) = (fun u : EE => evX p u) + (fun u : EE => evX q u)`. Use extensionality with `u`. Simplify using `[evX]`. Rewrite using `[e]`.

Conclude with `hp.add hq`. Consider the case `mul_X p k hp`. Establish `hk : (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1).HasTemperateGrowth`. Distinguish the cases in `h : k.2.2`. Simplify using `only [h, if_true]`.

Conclude with `((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).comp (coordL k.1 k.2.1)).hasTemperateGrowth`. Simplify using `only [h]`. Conclude with `(coordL k.1 k.2.1).hasTemperateGrowth`. Establish `e : (fun u : EE => evX (p * X k) u) = (fun u : EE => evX p u) * (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1)`. Use extensionality with `u`.

Simplify using `[evX]`. Rewrite using `[e]`. Conclude with `hp.mul hk`.
-/
theorem hasTemperateGrowth_evX (P : PX m n) : (fun u : EE => evX P u).HasTemperateGrowth := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have e : (fun u : EE => evX (C c) u) = fun _ => c := by ext u; simp [evX]
    rw [e]
    exact Function.HasTemperateGrowth.const c
  | add p q hp hq =>
    have e : (fun u : EE => evX (p + q) u) = (fun u : EE => evX p u) + (fun u : EE => evX q u) := by
      ext u; simp [evX]
    rw [e]
    exact hp.add hq
  | mul_X p k hp =>
    have hk : (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1).HasTemperateGrowth := by
      by_cases h : k.2.2
      · simp only [h, if_true]
        exact ((Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).comp (coordL k.1 k.2.1)).hasTemperateGrowth
      · simp only [h]
        exact (coordL k.1 k.2.1).hasTemperateGrowth
    have e : (fun u : EE => evX (p * X k) u) =
        (fun u : EE => evX p u) * (fun u : EE => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) := by
      ext u; simp [evX]
    rw [e]
    exact hp.mul hk

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, gramX, Qp, Qb, evX, map_sum, mul_comm]`.
-/
theorem gramX_herm (ε : Fin m → Bool) (u : EE) : (gramX ε u)ᴴ = gramX ε u := by
  ext i j
  simp [Matrix.conjTranspose_apply, gramX, Qp, Qb, evX, map_sum, mul_comm]

/- English proof (translation)
Establish `h : star (b * gramX ε u).trace = (b * gramX ε u).trace`. Rewrite using `[← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, gramX_herm, hb, Matrix.trace_mul_comm]`. Conclude with `Complex.conj_eq_iff_re.1 h`.
-/
theorem trace_real (ε : Fin m → Bool) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) (u : EE) :
    (((b * gramX ε u).trace.re : ℝ) : ℂ) = (b * gramX ε u).trace := by
  have h : star (b * gramX ε u).trace = (b * gramX ε u).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, gramX_herm, hb, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.1 h

/- English proof (translation)
Establish `hP : (fun u : EE => (b * gramX ε u).trace) = fun u => evX (∑ i, ∑ j, MvPolynomial.C (b i j) * Qp ε j i) u`. Use function extensionality and compare the values at `u`. Simplify using `[evX, gramX, Matrix.trace, Matrix.mul_apply, map_sum]`. Establish `hT : (fun u : EE => (b * gramX ε u).trace).HasTemperateGrowth`. Rewrite using `[hP]`.

Conclude with `hasTemperateGrowth_evX _`. Establish `hR : (fun u : EE => t * (b * gramX ε u).trace.re).HasTemperateGrowth`. Establish `h1` using `((t • Complex.reCLM : ℂ →L[ℝ] ℝ).hasTemperateGrowth).comp hT`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`.

Simplify using the standard rewrite rules. Establish `h3` using `hasTemperateGrowth_expI.comp hR`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `u`. Simplify using `only [Function.comp]`.

Rewrite using `[Complex.ofReal_mul, trace_real ε b hb u]`. Put the polynomial expressions in normal form.
-/
theorem hasTemperateGrowth_phase (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) :
    (fun u : EE => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)).HasTemperateGrowth := by
  have hP : (fun u : EE => (b * gramX ε u).trace) =
      fun u => evX (∑ i, ∑ j, MvPolynomial.C (b i j) * Qp ε j i) u := by
    funext u
    simp [evX, gramX, Matrix.trace, Matrix.mul_apply, map_sum]
  have hT : (fun u : EE => (b * gramX ε u).trace).HasTemperateGrowth := by
    rw [hP]
    exact hasTemperateGrowth_evX _
  have hR : (fun u : EE => t * (b * gramX ε u).trace.re).HasTemperateGrowth := by
    have h1 := ((t • Complex.reCLM : ℂ →L[ℝ] ℝ).hasTemperateGrowth).comp hT
    convert h1 using 1
    funext u
    simp
  have h3 := hasTemperateGrowth_expI.comp hR
  convert h3 using 1
  funext u
  simp only [Function.comp]
  rw [Complex.ofReal_mul, trace_real ε b hb u]
  ring_nf

/- English proof (translation)
Take `⟨S, rfl⟩` from `hf`. Use `⟨SchwartzMap.smulLeftCLM ℂ (fun u : EE => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)) S, ?_⟩` and prove the remaining obligations. Use extensionality with `u`. Simplify using `[SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase ε t b hb)]`.
-/
theorem isSch_phase (ε : Fin m → Bool) (t : ℝ) (b : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b) {f : EE → ℂ}
    (hf : IsSch f) : IsSch (fun u => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace) * f u) := by
  obtain ⟨S, rfl⟩ := hf
  refine ⟨SchwartzMap.smulLeftCLM ℂ
    (fun u : EE => Complex.exp (Complex.I * (t : ℂ) * (b * gramX ε u).trace)) S, ?_⟩
  ext u
  simp [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_phase ε t b hb)]

/- English proof (translation)
Set `β : ContDiffBump (0 : EE)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h1 : HasCompactSupport (fun u : EE => ((β u : ℝ) : ℂ))` using `β.hasCompactSupport.comp_left Complex.ofReal_zero`. Establish `h2 : ContDiff ℝ ∞ (fun u : EE => ((β u : ℝ) : ℂ))` using `Complex.ofRealCLM.contDiff.comp β.contDiff`. Use `⟨_, ⟨h1.toSchwartzMap h2, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[β.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]`.
-/
theorem exists_isSch_one : ∃ f : EE → ℂ, IsSch f ∧ f 0 = 1 := by
  let β : ContDiffBump (0 : EE) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun u : EE => ((β u : ℝ) : ℂ)) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  have h2 : ContDiff ℝ ∞ (fun u : EE => ((β u : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp β.contDiff
  refine ⟨_, ⟨h1.toSchwartzMap h2, rfl⟩, ?_⟩
  simp [β.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]

end Local

/- English proof (translation)
Introduce `_ _` and use `⟨fun _ _ hf hg => isSch_add' hf hg, fun c _ hf => isSch_cmul c hf, fun a _ ha hf => isSch_rmul a ha hf, fun ε t b _ hb hf => isSch_phase ε t b hb hf, exists_isSch_one⟩`.
-/
theorem _root_.PositivityTheory.Rg.Sw.Glob.schOps : SchOps := fun _ _ =>
  ⟨fun _ _ hf hg => isSch_add' hf hg, fun c _ hf => isSch_cmul c hf, fun a _ ha hf => isSch_rmul a ha hf,
    fun ε t b _ hb hf => isSch_phase ε t b hb hf, exists_isSch_one⟩

end PositivityTheory.Rg.Sw.Glob.OpGenAH
