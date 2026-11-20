import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PolyExpBound

noncomputable section

open MvPolynomial MeasureTheory

namespace PositivityTheory.Rg.Sw.LC.NullS

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

/- English proof (translation)
Unfold `mom`. Rewrite using `[← integral_add (integrable_pg c hc P) (integrable_pg c hc Q)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [evX, map_add, add_mul]`.
-/
theorem mom_add (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P + Q) = mom c P + mom c Q := by
  unfold mom
  rw [← integral_add (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp only [evX, map_add, add_mul]

/- English proof (translation)
Unfold `mom`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [evX, map_mul, eval_C, mul_assoc]`.
-/
theorem mom_C_mul (c : ℝ) (a : ℂ) (P : PX m n) : mom c (C a * P) = a * mom c P := by
  unfold mom
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [evX, map_mul, eval_C, mul_assoc]

/- English proof (translation)
Unfold `mom`. Rewrite using `[← integral_sub (integrable_pg c hc P) (integrable_pg c hc Q)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [evX, map_sub, sub_mul]`.
-/
theorem mom_sub (c : ℝ) (hc : 0 < c) (P Q : PX m n) : mom c (P - Q) = mom c P - mom c Q := by
  unfold mom
  rw [← integral_sub (integrable_pg c hc P) (integrable_pg c hc Q)]
  congr 1
  funext x
  simp only [evX, map_sub, sub_mul]

/- English proof (translation)
Unfold `mom`. Rewrite using `[← integral_finset_sum s (fun i _ => integrable_pg c hc (f i))]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [evX, map_sum, Finset.sum_mul]`.
-/
theorem mom_sum (c : ℝ) (hc : 0 < c) {ι : Type*} (s : Finset ι) (f : ι → PX m n) :
    mom c (∑ i ∈ s, f i) = ∑ i ∈ s, mom c (f i) := by
  unfold mom
  rw [← integral_finset_sum s (fun i _ => integrable_pg c hc (f i))]
  congr 1
  funext x
  simp only [evX, map_sum, Finset.sum_mul]

/- English proof (translation)
Take `⟨a, i, b⟩` from `k`. Apply the tactic sequence `cases b <;> simp [Sg, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_comm, ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]`.
-/
theorem pderiv_Sg (c : ℝ) (k : Fin m × Fin n × Bool) :
    pderiv k (Sg c : PX m n) = C (-(c : ℂ)) * X (k.1, k.2.1, !k.2.2) := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> simp [Sg, pderiv_X, Pi.single_apply, Finset.mul_sum, mul_comm, ite_and,
    Finset.sum_ite_eq', Finset.sum_ite_eq]

def Qv (c : ℝ) (P : PX m n) (v : Fin m → Fin n → ℂ) : PX m n :=
  ∑ k, C (crd k v) * (pderiv k P + P * pderiv k (Sg c))

/- English proof (translation)
Establish `hg : HasFDerivAt (fun y : Fin m → Fin n → ℂ => gs c y) (gs c x • dP (Sg c) x) x`. Establish `h` using `(hasFDerivAt_evX (Sg c) x).cexp`. Establish `he : (fun y : Fin m → Fin n → ℂ => gs c y) = fun y => Complex.exp (evX (Sg c) y)`. Use function extensionality and compare the values at `(gs_eq c)`. Rewrite using `[he, gs_eq]`.

Conclude with `h`. Conclude with `(hasFDerivAt_evX P x).mul hg`.
-/
theorem hasFDerivAt_pg (c : ℝ) (P : PX m n) (x : Fin m → Fin n → ℂ) :
    HasFDerivAt (fun y => evX P y * gs c y) (evX P x • (gs c x • dP (Sg c) x) + gs c x • dP P x) x := by
  have hg : HasFDerivAt (fun y : Fin m → Fin n → ℂ => gs c y) (gs c x • dP (Sg c) x) x := by
    have h := (hasFDerivAt_evX (Sg c) x).cexp
    have he : (fun y : Fin m → Fin n → ℂ => gs c y) = fun y => Complex.exp (evX (Sg c) y) :=
      funext (gs_eq c)
    rw [he, gs_eq]
    exact h
  exact (hasFDerivAt_evX P x).mul hg

/- English proof (translation)
Rewrite using `[(hasFDerivAt_pg c P x).fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dP, ContinuousLinearMap.sum_apply, smul_eq_mul, Qv, evX, map_sum, map_add, map_mul, eval_C]`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun k _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fderiv_pg (c : ℝ) (P : PX m n) (x v : Fin m → Fin n → ℂ) :
    fderiv ℝ (fun y => evX P y * gs c y) x v = evX (Qv c P v) x * gs c x := by
  rw [(hasFDerivAt_pg c P x).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dP,
    ContinuousLinearMap.sum_apply, smul_eq_mul, Qv, evX, map_sum, map_add, map_mul, eval_C]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

/- English proof (translation)
Unfold `mom`. Establish `e : (fun x => evX (Qv c P v) x * gs c x) = fun x => (1 : ℂ) * fderiv ℝ (fun y => evX P y * gs c y) x v`. Use function extensionality and compare the values at `x`. Rewrite using `[fderiv_pg, one_mul]`. Rewrite using `[e, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify `integrable_pg c hc (Qv c P v)` using `[fderiv_pg]`. Simplify using `using integrable_pg c hc P`. Introduce `x _`.

Conclude with `differentiableAt_const _`. Introduce `x _`. Conclude with `(hasFDerivAt_pg c P x).differentiableAt`.
-/
theorem integral_fderiv_pg (c : ℝ) (hc : 0 < c) (P : PX m n) (v : Fin m → Fin n → ℂ) :
    mom c (Qv c P v) = 0 := by
  unfold mom
  have e : (fun x => evX (Qv c P v) x * gs c x) =
      fun x => (1 : ℂ) * fderiv ℝ (fun y => evX P y * gs c y) x v := by
    funext x
    rw [fderiv_pg, one_mul]
  rw [e, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  · simp
  · simp
  · simpa [fderiv_pg] using integrable_pg c hc (Qv c P v)
  · simpa using integrable_pg c hc P
  · intro x _
    exact differentiableAt_const _
  · intro x _
    exact (hasFDerivAt_pg c P x).differentiableAt

def ev1 (k : Fin m × Fin n × Bool) (z : ℂ) : Fin m → Fin n → ℂ := fun a i => if a = k.1 ∧ i = k.2.1 then z else 0

/- English proof (translation)
Take `⟨a, i, b⟩` from `k`. Unfold `Qv`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single a, Fintype.sum_prod_type, Finset.sum_eq_single i, Fintype.sum_bool]`. Simplify using `[crd_apply, ev1, add_comm]`. Introduce `j _ hj`.

Simplify using `[crd_apply, ev1, hj]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[crd_apply, ev1, hj]`. Simplify using the standard rewrite rules.
-/
theorem null_operator_evaluation (c : ℝ) (P : PX m n) (k : Fin m × Fin n × Bool) (z : ℂ) :
    Qv c P (ev1 k z) = C z * (pderiv (k.1, k.2.1, false) P + P * pderiv (k.1, k.2.1, false) (Sg c)) +
      C (star z) * (pderiv (k.1, k.2.1, true) P + P * pderiv (k.1, k.2.1, true) (Sg c)) := by
  obtain ⟨a, i, b⟩ := k
  unfold Qv
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Fintype.sum_prod_type, Finset.sum_eq_single i,
    Fintype.sum_bool]
  · simp [crd_apply, ev1, add_comm]
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp
  · intro j _ hj
    simp [crd_apply, ev1, hj]
  · simp

/- English proof (translation)
Take `⟨a, i, b⟩` from `k`. Establish `h1` using `integral_fderiv_pg c hc P (ev1 (a, i, b) 1)`. Establish `h2` using `integral_fderiv_pg c hc P (ev1 (a, i, b) Complex.I)`. Rewrite `h1`, `h2` using `[null_operator_evaluation, mom_add c hc, mom_C_mul, mom_C_mul]`. Simplify using `only [star_one, one_mul, Complex.star_def, Complex.conj_I] at h1 h2`.

Establish `hu : mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0`. Establish `h3 : 2 * Complex.I * mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0`. Take the linear combination `h2 + Complex.I * h1`. Simplify `h3` using `[Complex.I_ne_zero]`. Establish `hw : mom c (pderiv (a, i, true) P + P * pderiv (a, i, true) (Sg c)) = 0`.

Take the linear combination `h1 - hu`. Establish `key : pderiv (a, i, b) P - C (c : ℂ) * X (a, i, !b) * P = pderiv (a, i, b) P + P * pderiv (a, i, b) (Sg c)`. Rewrite using `[pderiv_Sg, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Consider the cases of `b`. Conclude with `hu`. Conclude with `hw`.
-/
theorem mom_dPhi (c : ℝ) (hc : 0 < c) (k : Fin m × Fin n × Bool) (P : PX m n) :
    mom c (pderiv k P - C (c : ℂ) * X (k.1, k.2.1, !k.2.2) * P) = 0 := by
  obtain ⟨a, i, b⟩ := k
  have h1 := integral_fderiv_pg c hc P (ev1 (a, i, b) 1)
  have h2 := integral_fderiv_pg c hc P (ev1 (a, i, b) Complex.I)
  rw [null_operator_evaluation, mom_add c hc, mom_C_mul, mom_C_mul] at h1 h2
  simp only [star_one, one_mul, Complex.star_def, Complex.conj_I] at h1 h2
  have hu : mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
    have h3 : 2 * Complex.I * mom c (pderiv (a, i, false) P + P * pderiv (a, i, false) (Sg c)) = 0 := by
      linear_combination h2 + Complex.I * h1
    simpa [Complex.I_ne_zero] using h3
  have hw : mom c (pderiv (a, i, true) P + P * pderiv (a, i, true) (Sg c)) = 0 := by
    linear_combination h1 - hu
  have key : pderiv (a, i, b) P - C (c : ℂ) * X (a, i, !b) * P =
      pderiv (a, i, b) P + P * pderiv (a, i, b) (Sg c) := by
    rw [pderiv_Sg, map_neg]
    ring
  rw [key]
  cases b
  · exact hu
  · exact hw

end PositivityTheory.Rg.Sw.LC.NullS
