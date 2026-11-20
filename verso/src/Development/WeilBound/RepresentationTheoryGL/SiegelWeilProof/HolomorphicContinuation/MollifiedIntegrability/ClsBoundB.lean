import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsBoundA

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.B

open PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [herm, Pi.add_apply, Matrix.add_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_add (x y : E n) : herm (x + y) = herm x + herm y := by
  ext i j
  simp only [herm, Pi.add_apply, Matrix.add_apply]
  push_cast; ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [herm, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_smul (c : ℝ) (x : E n) : herm (c • x) = (c : ℂ) • herm x := by
  ext i j
  simp only [herm, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  push_cast; ring

/- English proof (translation)
Rewrite using `[dirC, h.fderiv]`.
-/
theorem dirC_of {f : E n → ℂ} {f' : E n →L[ℝ] ℂ} {y : E n} (h : HasFDerivAt f f' y) (w : Fin n → Fin n → ℂ) :
    dirC f w y = f' (fun a b => (w a b).re) + Complex.I * f' (fun a b => (w a b).im) := by
  rw [dirC, h.fderiv]

/- English proof (translation)
Rewrite using `[dirC_of (hasFDerivAt_const c y)]`. Simplify using the standard rewrite rules.
-/
theorem dirC_const (c : ℂ) (w : Fin n → Fin n → ℂ) (y : E n) : dirC (fun _ : E n => c) w y = 0 := by
  rw [dirC_of (hasFDerivAt_const c y)]; simp

/- English proof (translation)
Establish `h : HasFDerivAt (fun x => f x + g x) _ y` using `hf.hasFDerivAt.add hg.hasFDerivAt`. Rewrite using `[dirC_of h, dirC_of hf.hasFDerivAt, dirC_of hg.hasFDerivAt]`. Simplify using `only [ContinuousLinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_add {f g : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => f x + g x) w y = dirC f w y + dirC g w y := by
  have h : HasFDerivAt (fun x => f x + g x) _ y := hf.hasFDerivAt.add hg.hasFDerivAt
  rw [dirC_of h, dirC_of hf.hasFDerivAt, dirC_of hg.hasFDerivAt]
  simp only [ContinuousLinearMap.add_apply]; ring

/- English proof (translation)
Establish `h : HasFDerivAt (fun x => f x * g x) _ y` using `hf.hasFDerivAt.mul hg.hasFDerivAt`. Rewrite using `[dirC_of h, dirC_of hf.hasFDerivAt, dirC_of hg.hasFDerivAt]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_mul {f g : E n → ℂ} {y : E n} (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => f x * g x) w y = f y * dirC g w y + g y * dirC f w y := by
  have h : HasFDerivAt (fun x => f x * g x) _ y := hf.hasFDerivAt.mul hg.hasFDerivAt
  rw [dirC_of h, dirC_of hf.hasFDerivAt, dirC_of hg.hasFDerivAt]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Establish `h` using `hg.comp_hasFDerivAt y hf.hasFDerivAt`. Rewrite using `[show (fun x => g (f x)) = g ∘ f from rfl, dirC_of h, dirC_of hf.hasFDerivAt]`. Simplify using `only [ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_comp {g : ℂ → ℂ} {g' : ℂ} {f : E n → ℂ} {y : E n} (hg : HasDerivAt g g' (f y))
    (hf : DifferentiableAt ℝ f y) (w : Fin n → Fin n → ℂ) : dirC (fun x => g (f x)) w y = g' * dirC f w y := by
  have h := hg.comp_hasFDerivAt y hf.hasFDerivAt
  rw [show (fun x => g (f x)) = g ∘ f from rfl, dirC_of h, dirC_of hf.hasFDerivAt]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

/- English proof (translation)
Proceed by induction on `R using MvPolynomial.induction_on with`. Consider the case `C a => simpa using contDiff_const`. Consider the case `add p q hp hq => simpa using hp.add hq`. Consider the case `mul_X p i hp => simpa using hp.mul (hφ i)`.
-/
theorem contDiff_eval {ι : Type} (φ : ι → E n → ℂ) (hφ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i)) (R : MvPolynomial ι ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => MvPolynomial.eval (fun i => φ i y) R) := by
  induction R using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hφ i)

/- English proof (translation)
Establish `hd : ∀ (P : MvPolynomial ι ℂ), DifferentiableAt ℝ (fun y => MvPolynomial.eval (fun i => φ i y) P) y` using `fun P => ((contDiff_eval φ hφ P).differentiable (by simp)).differentiableAt`. Establish `hdi : ∀ i, DifferentiableAt ℝ (φ i) y` using `fun i => ((hφ i).differentiable (by simp)).differentiableAt`. Proceed by induction on `R using MvPolynomial.induction_on with`. Consider the case `C a => simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]`. Conclude with `dirC_const a w y`.

Consider the case `add p q hp hq`. Simplify using `only [map_add]`. Rewrite using `[dirC_add (hd p) (hd q), hp, hq, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Consider the case `mul_X p j hp`. Establish `hs : ∀ x, (MvPolynomial.eval fun i => φ i y) (MvPolynomial.pderiv x (p * MvPolynomial.X j)) = (MvPolynomial.eval fun i => φ i y) (MvPolynomial.pderiv x p) * φ j y + (if j = x then (MvPolynomial.eval fun i => φ i y) p else 0)`. Introduce `x`. Rewrite using `[Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]`. Distinguish the cases in `hx : j = x`.

Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hx]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [map_mul, MvPolynomial.eval_X]`. Rewrite using `[dirC_mul (hd p) (hdi j), hp]`. Simplify using `only [hs, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Finset.mul_sum, add_comm]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun x _ => by ring`.
-/
theorem dirC_eval {ι : Type} [Fintype ι] [DecidableEq ι] (φ : ι → E n → ℂ) (hφ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (φ i))
    (w : Fin n → Fin n → ℂ) (y : E n) (R : MvPolynomial ι ℂ) :
    dirC (fun y => MvPolynomial.eval (fun i => φ i y) R) w y =
      ∑ i, MvPolynomial.eval (fun i => φ i y) (MvPolynomial.pderiv i R) * dirC (φ i) w y := by
  have hd : ∀ (P : MvPolynomial ι ℂ), DifferentiableAt ℝ (fun y => MvPolynomial.eval (fun i => φ i y) P) y :=
    fun P => ((contDiff_eval φ hφ P).differentiable (by simp)).differentiableAt
  have hdi : ∀ i, DifferentiableAt ℝ (φ i) y := fun i => ((hφ i).differentiable (by simp)).differentiableAt
  induction R using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
           exact dirC_const a w y
  | add p q hp hq =>
    simp only [map_add]
    rw [dirC_add (hd p) (hd q), hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  | mul_X p j hp =>
    have hs : ∀ x, (MvPolynomial.eval fun i => φ i y) (MvPolynomial.pderiv x (p * MvPolynomial.X j)) =
        (MvPolynomial.eval fun i => φ i y) (MvPolynomial.pderiv x p) * φ j y +
          (if j = x then (MvPolynomial.eval fun i => φ i y) p else 0) := by
      intro x
      rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply]
      by_cases hx : j = x
      · subst hx; simp; ring
      · simp [hx]; ring
    simp only [map_mul, MvPolynomial.eval_X]
    rw [dirC_mul (hd p) (hdi j), hp]
    simp only [hs, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, herm, smul_eq_mul]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem hc_eq (w : Fin n → Fin n → ℂ) :
    herm (fun a b => (w a b).re) + Complex.I • herm (fun a b => (w a b).im) =
      fun i j => (1 + Complex.I) / 2 * w i j + (1 - Complex.I) / 2 * w j i := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, herm, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

/- English proof (translation)
Rewrite using `[hc_eq]`. Establish `c1 : (1 + Complex.I) / 2 * ((1 + Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 - Complex.I) / 2) = 0`. Apply the tactic sequence `apply Complex.ext <;> simp <;> norm_num`. Establish `c2 : (1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2) = 1`. Apply the tactic sequence `apply Complex.ext <;> simp <;> norm_num`.

Use extensionality with `i j`. Establish `e1 : (j = k ∧ i = l) ↔ (i = l ∧ j = k)` using `and_comm`. Establish `e2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l)` using `and_comm`. Establish `e3 : (l = i ∧ k = j) ↔ (i = l ∧ j = k)` using `⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩`. Simplify using `only [vkl, Matrix.single_apply, e1, e2, e3]`.

Apply the tactic sequence `by_cases hA : i = k ∧ j = l <;> by_cases hB : i = l ∧ j = k`. Rewrite using `[if_pos hA, if_pos hA, if_pos hB, if_pos hB, if_pos hB]`. Take the linear combination `c1 + c2`. Rewrite using `[if_pos hA, if_pos hA, if_neg hB, if_neg hB, if_neg hB]`. Take the linear combination `c1`.

Rewrite using `[if_neg hA, if_neg hA, if_pos hB, if_pos hB, if_pos hB]`. Take the linear combination `c2`. Rewrite using `[if_neg hA, if_neg hA, if_neg hB, if_neg hB, if_neg hB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hc_vkl (k l : Fin n) :
    herm (fun a b => (vkl k l a b).re) + Complex.I • herm (fun a b => (vkl k l a b).im) = Matrix.single l k 1 := by
  rw [hc_eq]
  have c1 : (1 + Complex.I) / 2 * ((1 + Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 - Complex.I) / 2) = 0 := by
    apply Complex.ext <;> simp <;> norm_num
  have c2 : (1 + Complex.I) / 2 * ((1 - Complex.I) / 2) + (1 - Complex.I) / 2 * ((1 + Complex.I) / 2) = 1 := by
    apply Complex.ext <;> simp <;> norm_num
  ext i j
  have e1 : (j = k ∧ i = l) ↔ (i = l ∧ j = k) := and_comm
  have e2 : (j = l ∧ i = k) ↔ (i = k ∧ j = l) := and_comm
  have e3 : (l = i ∧ k = j) ↔ (i = l ∧ j = k) := ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  simp only [vkl, Matrix.single_apply, e1, e2, e3]
  by_cases hA : i = k ∧ j = l <;> by_cases hB : i = l ∧ j = k
  · rw [if_pos hA, if_pos hA, if_pos hB, if_pos hB, if_pos hB]; linear_combination c1 + c2
  · rw [if_pos hA, if_pos hA, if_neg hB, if_neg hB, if_neg hB]; linear_combination c1
  · rw [if_neg hA, if_neg hA, if_pos hB, if_pos hB, if_pos hB]; linear_combination c2
  · rw [if_neg hA, if_neg hA, if_neg hB, if_neg hB, if_neg hB]; ring

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]`. Rewrite using `[Finset.sum_eq_single k]`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using the standard rewrite rules. Introduce `j _ hj`.

Simplify using `[Ne.symm hj]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`.

Simplify using `[Ne.symm hi]`. Simplify using the standard rewrite rules.
-/
theorem trace_mul_single (M : Matrix (Fin n) (Fin n) ℂ) (k l : Fin n) : (M * Matrix.single l k (1 : ℂ)).trace = M k l := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · simp
  · intro i _ hi; apply Finset.sum_eq_zero; intro j _; simp [Ne.symm hi]
  · simp

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.single_apply]`. Rewrite using `[Finset.sum_eq_single l]`. Apply the tactic sequence `by_cases h : k = c <;> simp [h]`. Introduce `d _ hd`. Simplify using `[Ne.symm hd]`.

Simplify using the standard rewrite rules.
-/
theorem mul_single_apply' (M : Matrix (Fin n) (Fin n) ℂ) (a c k l : Fin n) :
    (M * Matrix.single l k (1 : ℂ)) a c = if k = c then M a l else 0 := by
  simp only [Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single l]
  · by_cases h : k = c <;> simp [h]
  · intro d _ hd; simp [Ne.symm hd]
  · simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [mul_single_apply', ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem entry_mul_single_mul (M : Matrix (Fin n) (Fin n) ℂ) (a b k l : Fin n) :
    (M * Matrix.single l k (1 : ℂ) * M) a b = M a l * M k b := by
  rw [Matrix.mul_apply]
  simp only [mul_single_apply', ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Repeatedly rewrite using `[Matrix.det_apply]`. Use `ContDiff.sum fun σ _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[Units.smul_def, zsmul_eq_mul]`. Conclude with `contDiff_const.mul (contDiff_prod fun i _ => h _ _)`.
-/
theorem contDiff_det_of {M : E n → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => M y a b)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (M y).det) := by
  simp_rw [Matrix.det_apply]
  refine ContDiff.sum fun σ _ => ?_
  simp_rw [Units.smul_def, zsmul_eq_mul]
  exact contDiff_const.mul (contDiff_prod fun i _ => h _ _)

/- English proof (translation)
Establish `e : (fun y => (M y)⁻¹ a b) = fun y => ((M y).det)⁻¹ * ((M y).updateRow b (Pi.single a 1)).det`. Use function extensionality and compare the values at `y`. Rewrite using `[Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]`. Rewrite using `[e]`. Use `((contDiff_det_of h).inv hd).mul (contDiff_det_of fun i j => ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : i = b`. Substitute `hi` using the available equality. Simplify `contDiff_const` using `[Matrix.updateRow_self]`. Simplify `h i j` using `[Matrix.updateRow_ne hi]`.
-/
theorem contDiff_inv_entry_of {M : E n → Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => M y a b)) (hd : ∀ y, (M y).det ≠ 0) (a b : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (M y)⁻¹ a b) := by
  have e : (fun y => (M y)⁻¹ a b) = fun y => ((M y).det)⁻¹ * ((M y).updateRow b (Pi.single a 1)).det := by
    funext y
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [e]
  refine ((contDiff_det_of h).inv hd).mul (contDiff_det_of fun i j => ?_)
  by_cases hi : i = b
  · subst hi; simpa [Matrix.updateRow_self] using contDiff_const
  · simpa [Matrix.updateRow_ne hi] using h i j

/- English proof (translation)
Establish `h : HasFDerivAt (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, fderiv ℝ (f i) y) y`. Use `HasFDerivAt.sum (u := s) fun i _ => (hf i).hasFDerivAt` as an intermediate fact. Rewrite `this` using `[Finset.sum_fn]`. Then use the resulting hypothesis. Rewrite using `[dirC_of h]`. Simplify using `only [ContinuousLinearMap.sum_apply, dirC]`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`.
-/
theorem dirC_sum {ι : Type} (s : Finset ι) {f : ι → E n → ℂ} {y : E n} (hf : ∀ i, DifferentiableAt ℝ (f i) y)
    (w : Fin n → Fin n → ℂ) : dirC (fun x => ∑ i ∈ s, f i x) w y = ∑ i ∈ s, dirC (f i) w y := by
  have h : HasFDerivAt (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, fderiv ℝ (f i) y) y := by
    have := HasFDerivAt.sum (u := s) fun i _ => (hf i).hasFDerivAt
    rwa [Finset.sum_fn] at this
  rw [dirC_of h]
  simp only [ContinuousLinearMap.sum_apply, dirC]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/- English proof (translation)
The claim follows from `(h.differentiable (by simp)).differentiableAt`.
-/
theorem diffAt_of {f : E n → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) f) (y : E n) : DifferentiableAt ℝ f y :=
  (h.differentiable (by simp)).differentiableAt

/- English proof (translation)
Set `D : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun c d => dirC (fun y => (M y)⁻¹ c d) w y`. Establish `hI` using `contDiff_inv_entry_of hM hd`. Establish `key : M y * D = -(N * (M y)⁻¹)`. Use `Matrix.ext fun c d => ?_` and prove the remaining obligations. Establish `e : (fun x => ∑ j, M x c j * (M x)⁻¹ j d) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) c d`.

Use function extensionality and compare the values at `x`. Rewrite using `[← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hd x))]`. Establish `h2` using `congrArg (fun f => dirC f w y) e`. Rewrite `h2` using `[dirC_const, dirC_sum _ (fun j => diffAt_of ((hM c j).mul (hI j d)) y)]`. Simplify using `only [fun j => dirC_mul (diffAt_of (hM c j) y) (diffAt_of (hI j d) y) w, hN] at h2`.

Rewrite `h2` using `[Finset.sum_add_distrib]`. Rewrite using `[Matrix.mul_apply, Matrix.neg_apply, Matrix.mul_apply]`. Simplify using `only [D, Matrix.of_apply]`. Rewrite using `[eq_neg_iff_add_eq_zero, ← h2]`. Use `congr 1`.

Conclude with `Finset.sum_congr rfl fun j _ => mul_comm _ _`. Establish `hu` using `isUnit_iff_ne_zero.mpr (hd y)`. Establish `e2 : D = (M y)⁻¹ * (M y * D)`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Establish `e3 : dirC (fun y => (M y)⁻¹ a b) w y = D a b` using `rfl`.

Rewrite using `[e3, e2, key, Matrix.mul_neg, Matrix.mul_assoc]`.
-/
theorem dirC_inv_entry {M : E n → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (fun y => M y a b))
    (hd : ∀ y, (M y).det ≠ 0) (w : Fin n → Fin n → ℂ) (y : E n) (N : Matrix (Fin n) (Fin n) ℂ)
    (hN : ∀ a b, dirC (fun y => M y a b) w y = N a b) (a b : Fin n) :
    dirC (fun y => (M y)⁻¹ a b) w y = (-((M y)⁻¹ * N * (M y)⁻¹)) a b := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun c d => dirC (fun y => (M y)⁻¹ c d) w y
  have hI := contDiff_inv_entry_of hM hd
  have key : M y * D = -(N * (M y)⁻¹) := by
    refine Matrix.ext fun c d => ?_
    have e : (fun x => ∑ j, M x c j * (M x)⁻¹ j d) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) c d := by
      funext x; rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hd x))]
    have h2 := congrArg (fun f => dirC f w y) e
    rw [dirC_const, dirC_sum _ (fun j => diffAt_of ((hM c j).mul (hI j d)) y)] at h2
    simp only [fun j => dirC_mul (diffAt_of (hM c j) y) (diffAt_of (hI j d) y) w, hN] at h2
    rw [Finset.sum_add_distrib] at h2
    rw [Matrix.mul_apply, Matrix.neg_apply, Matrix.mul_apply]
    simp only [D, Matrix.of_apply]
    rw [eq_neg_iff_add_eq_zero, ← h2]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hu := isUnit_iff_ne_zero.mpr (hd y)
  have e2 : D = (M y)⁻¹ * (M y * D) := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have e3 : dirC (fun y => (M y)⁻¹ a b) w y = D a b := rfl
  rw [e3, e2, key, Matrix.mul_neg, Matrix.mul_assoc]

def hermE (a b : Fin n) : E n →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => herm y a b
      map_add' := fun x y => by rw [herm_add]; rfl
      map_smul' := fun c x => by rw [herm_smul]; simp [Matrix.smul_apply, Complex.real_smul] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermE_apply (a b : Fin n) (y : E n) : hermE a b y = herm y a b := rfl

/- English proof (translation)
Rewrite using `[show (fun y => herm y a b) = hermE a b from rfl, dirC_of (hermE a b).hasFDerivAt, hermE_apply, hermE_apply, ← hc_vkl k l]`. Simplify using `[Matrix.add_apply, Matrix.smul_apply]`.
-/
theorem dirC_herm_entry (a b k l : Fin n) (y : E n) :
    dirC (fun y => herm y a b) (vkl k l) y = Matrix.single l k 1 a b := by
  rw [show (fun y => herm y a b) = hermE a b from rfl, dirC_of (hermE a b).hasFDerivAt, hermE_apply, hermE_apply,
    ← hc_vkl k l]
  simp [Matrix.add_apply, Matrix.smul_apply]

/- English proof (translation)
The claim follows from `(hermE a b).contDiff`.
-/
theorem contDiff_herm_entry (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y : E n => herm y a b) := (hermE a b).contDiff

/- English proof (translation)
Simplify using `only [Am, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `exact contDiff_const.sub (contDiff_const.mul (contDiff_herm_entry a b))`.
-/
theorem contDiff_Am_entry (s : ℂ) (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y => Am s y a b) := by
  simp only [Am, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.sub (contDiff_const.mul (contDiff_herm_entry a b))

/- English proof (translation)
Simplify using `only [Bm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `exact contDiff_const.add (contDiff_const.mul (contDiff_herm_entry a b))`.
-/
theorem contDiff_Bm_entry (s : ℂ) (a b : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun y => Bm s y a b) := by
  simp only [Bm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact contDiff_const.add (contDiff_const.mul (contDiff_herm_entry a b))

/- English proof (translation)
Simplify using `only [Am, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `have h1 := diffAt_of (contDiff_herm_entry a b) y`. Rewrite using `[show (fun y => (1 : Matrix (Fin n) (Fin n) ℂ) a b - Complex.I * s * herm y a b) = fun y => (1 : Matrix (Fin n) (Fin n) ℂ) a b + (-(Complex.I * s)) * herm y a b by funext; ring]`. Rewrite using `[dirC_add (f := fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) (g := fun y => (-(Complex.I * s)) * herm y a b) (differentiableAt_const _) ((differentiableAt_const _).mul h1), dirC_const, dirC_mul (f := fun _ => -(Complex.I * s)) (g := fun y => herm y a b) (differentiableAt_const _) …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_Am_entry (s : ℂ) (y : E n) (a b k l : Fin n) :
    dirC (fun y => Am s y a b) (vkl k l) y = -(Complex.I * s * Matrix.single l k (1 : ℂ) a b) := by
  simp only [Am, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := diffAt_of (contDiff_herm_entry a b) y
  rw [show (fun y => (1 : Matrix (Fin n) (Fin n) ℂ) a b - Complex.I * s * herm y a b) =
      fun y => (1 : Matrix (Fin n) (Fin n) ℂ) a b + (-(Complex.I * s)) * herm y a b by funext; ring]
  rw [dirC_add (f := fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) (g := fun y => (-(Complex.I * s)) * herm y a b)
    (differentiableAt_const _) ((differentiableAt_const _).mul h1), dirC_const,
    dirC_mul (f := fun _ => -(Complex.I * s)) (g := fun y => herm y a b) (differentiableAt_const _) h1, dirC_const,
    dirC_herm_entry]
  ring

/- English proof (translation)
Simplify using `only [Bm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Apply the tactic sequence `have h1 := diffAt_of (contDiff_herm_entry a b) y`. Rewrite using `[dirC_add (f := fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) (g := fun y => (Complex.I * s) * herm y a b) (differentiableAt_const _) ((differentiableAt_const _).mul h1), dirC_const, dirC_mul (f := fun _ => Complex.I * s) (g := fun y => herm y a b) (differentiableAt_const _) h1, d …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dirC_Bm_entry (s : ℂ) (y : E n) (a b k l : Fin n) :
    dirC (fun y => Bm s y a b) (vkl k l) y = Complex.I * s * Matrix.single l k (1 : ℂ) a b := by
  simp only [Bm, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 := diffAt_of (contDiff_herm_entry a b) y
  rw [dirC_add (f := fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) a b) (g := fun y => (Complex.I * s) * herm y a b)
    (differentiableAt_const _) ((differentiableAt_const _).mul h1), dirC_const,
    dirC_mul (f := fun _ => Complex.I * s) (g := fun y => herm y a b) (differentiableAt_const _) h1, dirC_const,
    dirC_herm_entry]
  ring

/- English proof (translation)
The claim follows from `contDiff_inv_entry_of (contDiff_Am_entry s) (det_Am_ne hs) a b`.
-/
theorem contDiff_uM_entry {s : ℂ} (hs : s = 1 ∨ s = -1) (a b : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => uM s y a b) :=
  contDiff_inv_entry_of (contDiff_Am_entry s) (det_Am_ne hs) a b

/- English proof (translation)
The claim follows from `contDiff_inv_entry_of (contDiff_Bm_entry s) (det_Bm_ne hs) a b`.
-/
theorem contDiff_vM_entry {s : ℂ} (hs : s = 1 ∨ s = -1) (a b : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => vM s y a b) :=
  contDiff_inv_entry_of (contDiff_Bm_entry s) (det_Bm_ne hs) a b

/- English proof (translation)
Apply the tactic sequence `rw [show (fun y => uM s y a b) = fun y => (Am s y)⁻¹ a b from rfl, dirC_inv_entry (contDiff_Am_entry s) (det_Am_ne hs) (vkl k l) y (-((Complex.I * s) • Matrix.single l k (1 : ℂ))) (fun a b => by rw [dirC_Am_entry, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]) a b]`. Rewrite using `[← uM_eq, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, entry_mul_single_mul, smul_eq_mul]`.
-/
theorem dirC_uM {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b k l : Fin n) :
    dirC (fun y => uM s y a b) (vkl k l) y = Complex.I * s * (uM s y a l * uM s y k b) := by
  rw [show (fun y => uM s y a b) = fun y => (Am s y)⁻¹ a b from rfl,
    dirC_inv_entry (contDiff_Am_entry s) (det_Am_ne hs) (vkl k l) y (-((Complex.I * s) • Matrix.single l k (1 : ℂ)))
      (fun a b => by rw [dirC_Am_entry, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]) a b]
  rw [← uM_eq, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    entry_mul_single_mul, smul_eq_mul]

/- English proof (translation)
Apply the tactic sequence `rw [show (fun y => vM s y a b) = fun y => (Bm s y)⁻¹ a b from rfl, dirC_inv_entry (contDiff_Bm_entry s) (det_Bm_ne hs) (vkl k l) y ((Complex.I * s) • Matrix.single l k (1 : ℂ)) (fun a b => by rw [dirC_Bm_entry, Matrix.smul_apply, smul_eq_mul]) a b]`. Rewrite using `[← vM_eq, Matrix.neg_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, entry_mul_single_mul, smul_eq_mul]`.
-/
theorem dirC_vM {s : ℂ} (hs : s = 1 ∨ s = -1) (y : E n) (a b k l : Fin n) :
    dirC (fun y => vM s y a b) (vkl k l) y = -(Complex.I * s * (vM s y a l * vM s y k b)) := by
  rw [show (fun y => vM s y a b) = fun y => (Bm s y)⁻¹ a b from rfl,
    dirC_inv_entry (contDiff_Bm_entry s) (det_Bm_ne hs) (vkl k l) y ((Complex.I * s) • Matrix.single l k (1 : ℂ))
      (fun a b => by rw [dirC_Bm_entry, Matrix.smul_apply, smul_eq_mul]) a b]
  rw [← vM_eq, Matrix.neg_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    entry_mul_single_mul, smul_eq_mul]

end PositivityTheory.Rg.Sw.WR.B
