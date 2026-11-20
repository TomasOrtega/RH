import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.Curve

open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Take `⟨p, hp⟩` from `Ξ.poly i j`. Establish `h : Ξ.coef i j = fun y => MvPolynomial.aeval (fun ab : Fin n × Fin n => y ab.1 ab.2) p`. Use function extensionality and compare the values at `y`. Simplify using `[Pre.coef, hp, MvPolynomial.coe_aeval_eq_eval]`. Rewrite using `[h]`.

Conclude with `(AnalyticAt.aeval_mvPolynomial (fun ab : Fin n × Fin n => (((ContinuousLinearMap.proj ab.2 : (Fin n → ℂ) →L[ℂ] ℂ).comp (ContinuousLinearMap.proj ab.1 : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).analyticAt x)) p).differentiableAt`.
-/
private theorem pre_coef_differentiableAt {n : ℕ} (Ξ : Pre n) (i j : Fin Ξ.d) (x : Fin n → Fin n → ℂ) :
    DifferentiableAt ℂ (Ξ.coef i j) x := by
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun y => MvPolynomial.aeval (fun ab : Fin n × Fin n => y ab.1 ab.2) p := by
    funext y
    simp [Pre.coef, hp, MvPolynomial.coe_aeval_eq_eval]
  rw [h]
  exact (AnalyticAt.aeval_mvPolynomial (fun ab : Fin n × Fin n =>
    (((ContinuousLinearMap.proj ab.2 : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj ab.1 : (Fin n → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))).analyticAt x)) p).differentiableAt

/- English proof (translation)
Establish `hc : HasDerivAt (fun t : ℂ => oneM n + t • of.symm X) (of.symm X) 0`. Simplify using `using ((hasDerivAt_id (0:ℂ)).smul_const (of.symm X)).const_add (oneM n)`. Establish `hf` using `(pre_coef_differentiableAt Ξ k j (oneM n + (0:ℂ) • of.symm X)).hasFDerivAt.comp_hasDerivAt (0:ℂ) hc`. Simplify using `only [zero_smul, add_zero] at hf`. Conclude with `hf`.
-/
private theorem hasDerivAt_pre_mat_one_add_smul {n : ℕ} (Ξ : Pre n) (X : Matrix (Fin n) (Fin n) ℂ) (k j : Fin Ξ.d) :
    HasDerivAt (fun t : ℂ => Ξ.mat (of (oneM n + t • of.symm X)) k j) (Ξ.D X k j) 0 := by
  have hc : HasDerivAt (fun t : ℂ => oneM n + t • of.symm X) (of.symm X) 0 := by
    simpa using ((hasDerivAt_id (0:ℂ)).smul_const (of.symm X)).const_add (oneM n)
  have hf := (pre_coef_differentiableAt Ξ k j (oneM n + (0:ℂ) • of.symm X)).hasFDerivAt.comp_hasDerivAt (0:ℂ) hc
  simp only [zero_smul, add_zero] at hf
  exact hf

/- English proof (translation)
Introduce `n Ξ P Z W h`. Establish `key : ∀ t : ℂ, P * of (oneM n + t • of.symm Z) = of (oneM n + t • of.symm W) * P`. Introduce `t`. Express the relevant statement in the definitionally equal form `P * (1 + t • Z) = (1 + t • W) * P`. Rewrite using `[Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h, mul_one, one_mul]`.

Use extensionality with `i j`. Establish `hZ : HasDerivAt (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j) ((Ξ.mat P * Ξ.D Z) i j) 0`. Simplify using `only [Matrix.mul_apply]`. Conclude with `HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ Z k j).const_mul _`. Establish `hW : HasDerivAt (fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j) ((Ξ.D W * Ξ.mat P) i j) 0`.

Simplify using `only [Matrix.mul_apply]`. Conclude with `HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ W i k).mul_const _`. Establish `hfun : (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j) = fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j`. Use function extensionality and compare the values at `t`. Rewrite using `[← map_mul, ← map_mul, key]`.

Rewrite `hZ` using `[hfun]`. Conclude with `hZ.unique hW`.
-/
theorem UpperTheory.V.Weyl.adEq :
    ∀ (n : ℕ) (Ξ : Pre n) (P Z W : Matrix (Fin n) (Fin n) ℂ), P * Z = W * P → Ξ.mat P * Ξ.D Z = Ξ.D W * Ξ.mat P := by
  intro n Ξ P Z W h
  have key : ∀ t : ℂ, P * of (oneM n + t • of.symm Z) = of (oneM n + t • of.symm W) * P := by
    intro t
    change P * (1 + t • Z) = (1 + t • W) * P
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h, mul_one, one_mul]
  ext i j
  have hZ : HasDerivAt (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j)
      ((Ξ.mat P * Ξ.D Z) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ Z k j).const_mul _
  have hW : HasDerivAt (fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j)
      ((Ξ.D W * Ξ.mat P) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pre_mat_one_add_smul Ξ W i k).mul_const _
  have hfun : (fun t : ℂ => (Ξ.mat P * Ξ.mat (of (oneM n + t • of.symm Z))) i j) =
      fun t : ℂ => (Ξ.mat (of (oneM n + t • of.symm W)) * Ξ.mat P) i j := by
    funext t
    rw [← map_mul, ← map_mul, key]
  rw [hfun] at hZ
  exact hZ.unique hW
