import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.LongWeylFunctional
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSchwartzPolyMulGauss

noncomputable section

open scoped Matrix
open MeasureTheory PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula

namespace PositivityTheory.SiegelWeilFormula.KLI

variable {m n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `[fP, evX, MvPolynomial.eval_add, MvPolynomial.smul_eval, add_mul, mul_assoc]`.
-/
theorem fP_add_smul (a : ℂ) (P Q : PX m n) : fP (a • P + Q) = a • fP P + fP Q := by
  funext u
  simp [fP, evX, MvPolynomial.eval_add, MvPolynomial.smul_eval, add_mul, mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `[fP, evX]`.
-/
theorem fP_zero : fP (0 : PX m n) = 0 := by
  funext u
  simp [fP, evX]

/- English proof (translation)
Simplify using `[fP, evX, gs]`.
-/
theorem fP_one_zero : fP (1 : PX m n) 0 = 1 := by
  simp [fP, evX, gs]

section Real

variable {σ : Type}

def reP (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (MvPolynomial.coeff k p).re

def imaginary (p : MvPolynomial σ ℂ) : MvPolynomial σ ℝ := ∑ k ∈ p.support, MvPolynomial.monomial k (MvPolynomial.coeff k p).im

/- English proof (translation)
Rewrite using `[reP, MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite using `[MvPolynomial.notMem_support_iff.1 h, Complex.zero_re]`.
-/
theorem coeff_reP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : MvPolynomial.coeff k (reP p) = (MvPolynomial.coeff k p).re := by
  classical
  rw [reP, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_re]

/- English proof (translation)
Rewrite using `[imaginary, MvPolynomial.coeff_sum]`. Simplify using `only [MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite using `[MvPolynomial.notMem_support_iff.1 h, Complex.zero_im]`.
-/
theorem coeff_imP (p : MvPolynomial σ ℂ) (k : σ →₀ ℕ) : MvPolynomial.coeff k (imaginary p) = (MvPolynomial.coeff k p).im := by
  classical
  rw [imaginary, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.notMem_support_iff.1 h, Complex.zero_im]

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp => simp [hp]`.
-/
theorem eval_map_real (q : MvPolynomial σ ℝ) (y : σ → ℝ) :
    MvPolynomial.eval (fun i => (y i : ℂ)) (MvPolynomial.map (algebraMap ℝ ℂ) q) = ((MvPolynomial.eval y q : ℝ) : ℂ) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, coeff_reP, coeff_imP]`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
theorem eq_map_re_add_im (p : MvPolynomial σ ℂ) :
    p = MvPolynomial.map (algebraMap ℝ ℂ) (reP p) + MvPolynomial.C Complex.I * MvPolynomial.map (algebraMap ℝ ℂ) (imaginary p) := by
  ext k
  rw [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_map, coeff_reP,
    coeff_imP]
  apply Complex.ext <;> simp

/- English proof (translation)
Establish `hre : ∀ y : σ → ℝ, MvPolynomial.eval y (reP p) = 0 ∧ MvPolynomial.eval y (imaginary p) = 0`. Introduce `y`. Establish `h1` using `h y`. Rewrite `h1` using `[eq_map_re_add_im p, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]`. Rewrite `h1` using `[eval_map_real, eval_map_real]`.

Establish `hr` using `congrArg Complex.re h1`. Establish `hi` using `congrArg Complex.im h1`. Simplify using `at hr hi`. Conclude with `⟨hr, hi⟩`. Establish `a1 : reP p = 0` using `MvPolynomial.funext fun y => by simpa using (hre y).1`.

Establish `a2 : imaginary p = 0` using `MvPolynomial.funext fun y => by simpa using (hre y).2`. Rewrite using `[eq_map_re_add_im p, a1, a2]`. Simplify using the standard rewrite rules.
-/
theorem eq_zero_of_eval_real (p : MvPolynomial σ ℂ) (h : ∀ y : σ → ℝ, MvPolynomial.eval (fun i => (y i : ℂ)) p = 0) :
    p = 0 := by
  have hre : ∀ y : σ → ℝ, MvPolynomial.eval y (reP p) = 0 ∧ MvPolynomial.eval y (imaginary p) = 0 := by
    intro y
    have h1 := h y
    rw [eq_map_re_add_im p, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C] at h1
    rw [eval_map_real, eval_map_real] at h1
    have hr := congrArg Complex.re h1
    have hi := congrArg Complex.im h1
    simp at hr hi
    exact ⟨hr, hi⟩
  have a1 : reP p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).1
  have a2 : imaginary p = 0 := MvPolynomial.funext fun y => by simpa using (hre y).2
  rw [eq_map_re_add_im p, a1, a2]
  simp

end Real

def subF (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)
  else MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.C Complex.I * MvPolynomial.X (k.1, k.2.1, true)

def subG (k : Fin m × Fin n × Bool) : PX m n :=
  if k.2.2 then MvPolynomial.C (2 * Complex.I)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) - MvPolynomial.X (k.1, k.2.1, true))
  else MvPolynomial.C (2 : ℂ)⁻¹ * (MvPolynomial.X (k.1, k.2.1, false) + MvPolynomial.X (k.1, k.2.1, true))

/- English proof (translation)
Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval x _ = MvPolynomial.aeval x P`. Rewrite using `[MvPolynomial.aeval_bind₁, MvPolynomial.aeval_bind₁]`. Establish `e : (fun i => MvPolynomial.aeval (fun i => MvPolynomial.aeval x (subG (m` using `m) (n := n) i)) (subF i)) = x := by`.

Use function extensionality and compare the values at `k`. Take `⟨a, j, b⟩` from `k`. Apply the tactic sequence `cases b <;> simp [subF, subG] <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring`. Rewrite using `[e]`.
-/
theorem subG_subF (P : PX m n) : MvPolynomial.bind₁ subG (MvPolynomial.bind₁ subF P) = P := by
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.aeval x _ = MvPolynomial.aeval x P
  rw [MvPolynomial.aeval_bind₁, MvPolynomial.aeval_bind₁]
  have e : (fun i => MvPolynomial.aeval (fun i => MvPolynomial.aeval x (subG (m := m) (n := n) i)) (subF i)) = x := by
    funext k
    obtain ⟨a, j, b⟩ := k
    cases b <;> simp [subF, subG] <;> field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  rw [e]

/- English proof (translation)
Introduce `P Q h`. Rewrite using `[← sub_eq_zero]`. Use `set R := P - Q`. Establish `hR : ∀ x, evX R x = 0` using `fun x => by`. Simplify using `only [R, evX, map_sub]`.

Conclude with `sub_eq_zero.2 (congrFun h x)`. Establish `h0 : MvPolynomial.bind₁ subF R = 0`. Apply `eq_zero_of_eval_real` to reduce the goal to its premises. Introduce `y`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval (fun i => (y i : ℂ)) _ = 0`.

Rewrite using `[MvPolynomial.aeval_bind₁]`. Use `hR (fun a j => (y (a, j, false) : ℂ) + Complex.I * y (a, j, true))` as an intermediate fact. Rewrite `this` using `[evX]`. Establish `e : (fun i => MvPolynomial.aeval (fun i => (y i : ℂ)) (subF (m` using `m) (n := n) i)) = fun k => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true)) else (y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true) := by`. Use function extensionality and compare the values at `k`.

Take `⟨a, j, b⟩` from `k`. Apply the tactic sequence `cases b <;> simp [subF, Complex.ext_iff]`. Rewrite using `[e]`. Conclude with `this`. Rewrite using `[← subG_subF R, h0, map_zero]`.
-/
theorem evX_injective : Function.Injective (evX (m := m) (n := n)) := by
  intro P Q h
  rw [← sub_eq_zero]
  set R := P - Q
  have hR : ∀ x, evX R x = 0 := fun x => by
    simp only [R, evX, map_sub]; exact sub_eq_zero.2 (congrFun h x)
  have h0 : MvPolynomial.bind₁ subF R = 0 := by
    apply eq_zero_of_eval_real
    intro y
    change MvPolynomial.aeval (fun i => (y i : ℂ)) _ = 0
    rw [MvPolynomial.aeval_bind₁]
    have := hR (fun a j => (y (a, j, false) : ℂ) + Complex.I * y (a, j, true))
    rw [evX] at this
    have e : (fun i => MvPolynomial.aeval (fun i => (y i : ℂ)) (subF (m := m) (n := n) i)) =
        fun k => if k.2.2 then star ((y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true))
          else (y (k.1, k.2.1, false) : ℂ) + Complex.I * y (k.1, k.2.1, true) := by
      funext k
      obtain ⟨a, j, b⟩ := k
      cases b <;> simp [subF, Complex.ext_iff]
    rw [e]
    exact this
  rw [← subG_subF R, h0, map_zero]

/- English proof (translation)
Introduce `P Q h`. Apply `evX_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `u`. Establish `e` using `congrFun h u`. Simplify using `only [fP] at e`.

Conclude with `mul_right_cancel₀ (Complex.exp_ne_zero _) e`.
-/
theorem fP_injective : Function.Injective (fP (m := m) (n := n)) := by
  intro P Q h
  apply evX_injective
  funext u
  have e := congrFun h u
  simp only [fP] at e
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) e

/- English proof (translation)
Take `⟨φ, hφ⟩` from `GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_schwartz_poly_mul_gauss m n P`. Conclude with `⟨φ, hφ⟩`.
-/
theorem isSw_fP (P : PX m n) : IsSw (fP P) := by
  obtain ⟨φ, hφ⟩ := GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_schwartz_poly_mul_gauss m n P
  exact ⟨φ, hφ⟩

/- English proof (translation)
Use function extensionality and compare the values at `u`. Simplify using `only [fP, gs, gZ]`. Use `congr 2`. Establish `htr : Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diag]`.

Rewrite using `[Finset.sum_comm]`. Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`. Establish `hI : Complex.I * ((sg : ℤ) : ℂ) * (Complex.I * ((sg : ℤ) : ℂ)) = -1`.

Apply the tactic sequence `rcases Int.units_eq_one_or sg with rfl | rfl <;> simp`. Rewrite using `[Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, htr, smul_eq_mul]`. Rewrite using `[Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]`. Take the linear combination `(-2 * (Real.pi : ℂ) * ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ)) * hI`.
-/
theorem fP_eq_gZ (sg : ℤˣ) (P : PX m n) :
    fP P = fun u => evX P u * gZ sg ((Complex.I * ((sg : ℤ) : ℂ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) u := by
  funext u
  simp only [fP, gs, gZ]
  congr 2
  have htr : Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u) = ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.diag]
    rw [Finset.sum_comm]
    push_cast
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have hI : Complex.I * ((sg : ℤ) : ℂ) * (Complex.I * ((sg : ℤ) : ℂ)) = -1 := by
    rcases Int.units_eq_one_or sg with rfl | rfl <;> simp
  rw [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, htr, smul_eq_mul]
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  linear_combination (-2 * (Real.pi : ℂ) * ((∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ) : ℂ)) * hI

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem fin_deg (d : ℕ) : FiniteDimensional ℂ (MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d) :=
  inferInstance

def evW (d : ℕ) : MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d →ₗ[ℂ] ((Fin m → Fin n → ℂ) → ℂ) where
  toFun Q u := evX Q.1 u
  map_add' Q Q' := by funext u; simp [evX]
  map_smul' a Q := by funext u; simp [evX]

/- English proof (translation)
Introduce `Q Q' h` and use `Subtype.ext (evX_injective (funext fun u => congrFun h u))`.
-/
theorem evW_injective (d : ℕ) : Function.Injective (evW (m := m) (n := n) d) := fun Q Q' h =>
  Subtype.ext (evX_injective (funext fun u => congrFun h u))

/- English proof (translation)
Use `set W := MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d`. Set `e : W ≃ₗ[ℂ] LinearMap.range (evW (m` to `m) (n := n) d) := LinearEquiv.ofInjective _ (evW_injective d)`. Use `haveI : FiniteDimensional ℂ (LinearMap.range (evW (m := m) (n := n) d)) := e.finiteDimensional`. Set `l' : LinearMap.range (evW (m` to `m) (n := n) d) →ₗ[ℂ] ℂ := l ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap`. Establish `hl' : Continuous l'` using `LinearMap.continuous_of_finiteDimensional l'`.

Establish `hW : ∀ x ∈ S, φ x ∈ W` using `fun x hx => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hd x hx)`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Set `g : S → LinearMap.range (evW (m` to `m) (n := n) d) := fun x => e ⟨φ x, hW x x.2⟩`. Establish `hg : Continuous g`. Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations.

Use `continuous_pi fun u => ?_` and prove the remaining obligations. Conclude with `(hc u).restrict`. Use `(hl'.comp hg).congr fun x => ?_` and prove the remaining obligations. Simplify using `[l', g]`.
-/
theorem continuousOn_of_evX {X : Type} [TopologicalSpace X] {S : Set X} (d : ℕ) (φ : X → PX m n)
    (hd : ∀ x ∈ S, (φ x).totalDegree ≤ d) (hc : ∀ u, ContinuousOn (fun x => evX (φ x) u) S) (l : PX m n →ₗ[ℂ] ℂ) :
    ContinuousOn (fun x => l (φ x)) S := by
  classical
  set W := MvPolynomial.restrictTotalDegree (Fin m × Fin n × Bool) ℂ d
  let e : W ≃ₗ[ℂ] LinearMap.range (evW (m := m) (n := n) d) := LinearEquiv.ofInjective _ (evW_injective d)
  haveI : FiniteDimensional ℂ (LinearMap.range (evW (m := m) (n := n) d)) := e.finiteDimensional
  let l' : LinearMap.range (evW (m := m) (n := n) d) →ₗ[ℂ] ℂ := l ∘ₗ W.subtype ∘ₗ e.symm.toLinearMap
  have hl' : Continuous l' := LinearMap.continuous_of_finiteDimensional l'
  have hW : ∀ x ∈ S, φ x ∈ W := fun x hx => (MvPolynomial.mem_restrictTotalDegree _ _ _).2 (hd x hx)
  rw [continuousOn_iff_continuous_restrict]
  let g : S → LinearMap.range (evW (m := m) (n := n) d) := fun x => e ⟨φ x, hW x x.2⟩
  have hg : Continuous g := by
    refine Continuous.subtype_mk ?_ _
    refine continuous_pi fun u => ?_
    exact (hc u).restrict
  refine (hl'.comp hg).congr fun x => ?_
  simp [l', g]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gramX, Qp, Qb, evX, Matrix.mul_apply, Matrix.conjTranspose_apply, MvPolynomial.eval_sum]`.
-/
theorem gramX_true (x : Fin m → Fin n → ℂ) : gramX (fun _ : Fin m => true) x = (Matrix.of x)ᴴ * Matrix.of x := by
  ext i j
  simp [gramX, Qp, Qb, evX, Matrix.mul_apply, Matrix.conjTranspose_apply, MvPolynomial.eval_sum]

end PositivityTheory.SiegelWeilFormula.KLI

end
