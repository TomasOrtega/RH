import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.InfInvA

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.II

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
The claim follows from `contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) i j`.
-/
theorem contDiff_entry (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => x i j) :=
  contDiff_apply_apply (𝕜 := ℝ) (E := ℂ) i j

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Matrix.conjTranspose_apply]`.
-/
theorem xZx_apply (x Z : M2 n) (i j : Fin n ⊕ Fin n) :
    (x * Z * xᴴ) i j = ∑ l, (∑ m, x i m * Z m l) * starRingEnd ℂ (x j l) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/- English proof (translation)
Repeatedly rewrite using `[xZx_apply]`. Apply the tactic sequence `refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => (contDiff_entry i m).mul contDiff_const) ?_`. Apply the tactic sequence `exact Complex.conjCLE.contDiff.comp (contDiff_entry j l)`.
-/
theorem contDiff_xZx (Z : M2 n) (i j : Fin n ⊕ Fin n) : ContDiff ℝ ∞ (fun x : M2 n => (x * Z * xᴴ) i j) := by
  simp_rw [xZx_apply]
  refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => (contDiff_entry i m).mul contDiff_const) ?_
  exact Complex.conjCLE.contDiff.comp (contDiff_entry j l)

/- English proof (translation)
Introduce `n Z a b`. Conclude with `⟨contDiff_xZx Z (Sum.inr a) (Sum.inr b), (contDiff_xZx Z (Sum.inr a) (Sum.inl b)).neg⟩`.
-/
theorem cDiff : CDiff := by
  intro n Z a b
  exact ⟨contDiff_xZx Z (Sum.inr a) (Sum.inr b), (contDiff_xZx Z (Sum.inr a) (Sum.inl b)).neg⟩

/- English proof (translation)
Establish `hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x` using `((contDiff_xZx Z i j).differentiable (by simp)).differentiableAt`. Use `(hd.lineDeriv_eq_fderiv (v := v)).symm.trans ?_` and prove the remaining obligations. Establish `e : (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) = fun t : ℝ => (x * Z * xᴴ) i j + (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j + (t : ℂ) ^ 2 * (v * Z * vᴴ) i j`. Use function extensionality and compare the values at `t`. Simplify using `only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_smul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hr : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0` using `Complex.ofRealCLM.hasDerivAt`. Establish `h : HasDerivAt (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0`. Rewrite using `[e]`. Establish `h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0`.

Simplify using `using hr.mul_const ((v * Z * xᴴ + x * Z * vᴴ) i j)`. Establish `h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * (v * Z * vᴴ) i j) 0 0`. Simplify using `using (hr.pow 2).mul_const ((v * Z * vᴴ) i j)`. Establish `h3` using `((hasDerivAt_const (0 : ℝ) ((x * Z * xᴴ) i j)).add h1).add h2`. Use `(h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (by simp)` and prove the remaining obligations.

Simplify using the standard rewrite rules. Simplify `h.deriv` using `[lineDeriv]`.
-/
theorem fderiv_xZx (Z x v : M2 n) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x v = (v * Z * xᴴ + x * Z * vᴴ) i j := by
  have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x :=
    ((contDiff_xZx Z i j).differentiable (by simp)).differentiableAt
  refine (hd.lineDeriv_eq_fderiv (v := v)).symm.trans ?_
  have e : (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) = fun t : ℝ =>
      (x * Z * xᴴ) i j + (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j + (t : ℂ) ^ 2 * (v * Z * vᴴ) i j := by
    funext t
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, star_trivial, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_smul]
    ring
  have hr : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
  have h : HasDerivAt (fun t : ℝ => ((x + t • v) * Z * (x + t • v)ᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
    rw [e]
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (v * Z * xᴴ + x * Z * vᴴ) i j) ((v * Z * xᴴ + x * Z * vᴴ) i j) 0 := by
      simpa using hr.mul_const ((v * Z * xᴴ + x * Z * vᴴ) i j)
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 2 * (v * Z * vᴴ) i j) 0 0 := by
      simpa using (hr.pow 2).mul_const ((v * Z * vᴴ) i j)
    have h3 := ((hasDerivAt_const (0 : ℝ) ((x * Z * xᴴ) i j)).add h1).add h2
    refine (h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (by simp)
    simp
  simpa [lineDeriv] using h.deriv

/- English proof (translation)
Simplify using `only [reK, imK, smul_smul, smul_sub, smul_add]`. Establish `h : Complex.I * (-Complex.I / 2) = 1 / 2`. Rewrite using `[mul_div_assoc', mul_neg, Complex.I_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`.

Use `module`.
-/
theorem reK_add_imK (e : M2 n) : reK e + Complex.I • imK e = e := by
  simp only [reK, imK, smul_smul, smul_sub, smul_add]
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]; ring
  rw [h]
  module

/- English proof (translation)
Simplify using `only [reK, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]`. Establish `: star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Rewrite using `[this]`. Use `module`.
-/
theorem reK_conj (e : M2 n) : (reK e)ᴴ = -reK e := by
  simp only [reK, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this]; module

/- English proof (translation)
Simplify using `only [imK, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]`. Establish `: star (-Complex.I / 2) = -(-Complex.I / 2)` using `by simp [Complex.conj_I]; ring`. Rewrite using `[this]`. Use `module`.
-/
theorem imK_conj (e : M2 n) : (imK e)ᴴ = -imK e := by
  simp only [imK, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  have : star (-Complex.I / 2) = -(-Complex.I / 2) := by simp [Complex.conj_I]; ring
  rw [this]; module

/- English proof (translation)
Rewrite using `[fderiv_xZx, Matrix.conjTranspose_mul, hE]`. Use `congr 1`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg]`.
-/
theorem fderiv_xZx_skew (Z x E : M2 n) (hE : Eᴴ = -E) (i j : Fin n ⊕ Fin n) :
    fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) i j) x (E * x) = (E * (x * Z * xᴴ) - (x * Z * xᴴ) * E) i j := by
  rw [fderiv_xZx, Matrix.conjTranspose_mul, hE]
  congr 1
  simp only [Matrix.mul_assoc, Matrix.mul_neg, sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[dK, fderiv_xZx_skew Z x _ (reK_conj e), fderiv_xZx_skew Z x _ (imK_conj e)]`. Use `conv_rhs => rw [← reK_add_imK e]`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dK_xZx (Z x e : M2 n) (i j : Fin n ⊕ Fin n) :
    dK (fun y : M2 n => (y * Z * yᴴ) i j) x e = (e * (x * Z * xᴴ) - (x * Z * xᴴ) * e) i j := by
  rw [dK, fderiv_xZx_skew Z x _ (reK_conj e), fderiv_xZx_skew Z x _ (imK_conj e)]
  conv_rhs => rw [← reK_add_imK e]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toBlocks₂₂_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₂₂ a b = M (Sum.inr a) (Sum.inr b) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toBlocks₂₁_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₂₁ a b = M (Sum.inr a) (Sum.inl b) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toBlocks₁₁_apply' (M : M2 n) (a b : Fin n) : M.toBlocks₁₁ a b = M (Sum.inl a) (Sum.inl b) := rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with a' | a' <;> rcases j with b' | b' <;>`. Simplify using `[eA, eB, Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]`.
-/
theorem decomp (M : M2 n) : M = fromBlocks (M.toBlocks₁₁ - M.toBlocks₂₂) (M.toBlocks₁₂ + M.toBlocks₂₁) 0 0 +
    ∑ a, ∑ b, (M.toBlocks₂₂ a b • eA a b + (-M.toBlocks₂₁ a b) • eB a b) := by
  ext i j
  rcases i with a' | a' <;> rcases j with b' | b' <;>
    simp [eA, eB, Matrix.sum_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

/- English proof (translation)
Simplify using `[eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]`.
-/
theorem eA_mul_apply (M : M2 n) (a b : Fin n) : (eA a b * M) (Sum.inr a) (Sum.inr b) = M (Sum.inr b) (Sum.inr b) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

/- English proof (translation)
Simplify using `[eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]`.
-/
theorem mul_eA_apply (M : M2 n) (a b : Fin n) : (M * eA a b) (Sum.inr a) (Sum.inr b) = M (Sum.inr a) (Sum.inr a) := by
  simp [eA, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

/- English proof (translation)
Simplify using `[eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]`.
-/
theorem eB_mul_apply (M : M2 n) (a b : Fin n) : (eB a b * M) (Sum.inr a) (Sum.inl b) = -M (Sum.inl b) (Sum.inl b) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

/- English proof (translation)
Simplify using `[eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]`.
-/
theorem mul_eB_apply (M : M2 n) (a b : Fin n) : (M * eB a b) (Sum.inr a) (Sum.inl b) = -M (Sum.inr a) (Sum.inr a) := by
  simp [eB, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.single_apply]

/- English proof (translation)
Simplify using `only [Matrix.sub_apply, eA_mul_apply, mul_eA_apply, Finset.sum_sub_distrib]`. Rewrite using `[Finset.sum_comm (f := fun a b => M (Sum.inr b) (Sum.inr b))]`. Simplify using the standard rewrite rules.
-/
theorem sumA (M : M2 n) : ∑ a, ∑ b, ((eA a b * M - M * eA a b : M2 n) (Sum.inr a) (Sum.inr b)) = 0 := by
  simp only [Matrix.sub_apply, eA_mul_apply, mul_eA_apply, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b => M (Sum.inr b) (Sum.inr b))]
  simp

/- English proof (translation)
Simplify using `only [Matrix.sub_apply, eB_mul_apply, mul_eB_apply, neg_sub, neg_neg, sub_neg_eq_add, Finset.sum_sub_distrib]`. Simplify using `only [Matrix.trace, Matrix.diag, toBlocks₁₁_apply', toBlocks₂₂_apply', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sub]`. Establish `h : ∀ a b : Fin n, -(-M (Sum.inl b) (Sum.inl b) + M (Sum.inr a) (Sum.inr a)) = M (Sum.inl b) (Sum.inl b) - M (Sum.inr a) (Sum.inr a)` using `fun _ _ => by ring`. Simplify using `only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]`.
-/
theorem sumB (M : M2 n) : ∑ a, ∑ b, -((eB a b * M - M * eB a b : M2 n) (Sum.inr a) (Sum.inl b)) =
    (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) := by
  simp only [Matrix.sub_apply, eB_mul_apply, mul_eB_apply, neg_sub, neg_neg, sub_neg_eq_add, Finset.sum_sub_distrib]
  simp only [Matrix.trace, Matrix.diag, toBlocks₁₁_apply', toBlocks₂₂_apply', Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_sub]
  have h : ∀ a b : Fin n, -(-M (Sum.inl b) (Sum.inl b) + M (Sum.inr a) (Sum.inr a)) =
      M (Sum.inl b) (Sum.inl b) - M (Sum.inr a) (Sum.inr a) := fun _ _ => by ring
  simp only [h, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.mul_sum]

/- English proof (translation)
Introduce `n Θ x Z hx hΘ hlaw`. Use `set M := x * Z * xᴴ with hM`. Establish `hxZ : x * Z = M * x` using `by rw [hM, Matrix.mul_assoc (x * Z), hx.2, Matrix.mul_one]`. Establish `hΘd : DifferentiableAt ℂ Θ x` using `hΘ.differentiableAt (by simp)`. Establish `hR : ∀ v, fderiv ℝ Θ x v = fderiv ℂ Θ x v` using `fun v => by`.

Establish `h` using `(hΘd.hasFDerivAt.restrictScalars ℝ).fderiv`. Conclude with `(congrArg (fun L => L v) h).trans rfl`. Establish `hdK : ∀ e, dK Θ x e = fderiv ℂ Θ x (e * x)` using `fun e => by`. Rewrite using `[dK, hR, hR]`. Use `conv_rhs => rw [← reK_add_imK e]`.

Rewrite using `[Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul]`. Establish `hLeib : ∀ c : M2 n → ℂ, DifferentiableAt ℝ c x → ∀ e, dK (fun y => c y * Θ y) x e = dK c x e * Θ x + c x * dK Θ x e` using `fun c hc e => by`. Establish `hΘr : DifferentiableAt ℝ Θ x` using `hΘd.restrictScalars ℝ`. Establish `h` using `(hc.hasFDerivAt.mul hΘr.hasFDerivAt).fderiv`. Establish `hv : ∀ v, fderiv ℝ (fun y => c y * Θ y) x v = c x * fderiv ℝ Θ x v + Θ x * fderiv ℝ c x v` using `fun v => by`.

Conclude with `(congrArg (fun L : M2 n →L[ℝ] ℂ => L v) h).trans rfl`. Simplify using `only [dK, hv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcA : ∀ a b, DifferentiableAt ℝ (cA Z a b) x` using `fun a b => ((cDiff n Z a b).1.differentiable (by simp)).differentiableAt`. Establish `hcB : ∀ a b, DifferentiableAt ℝ (cB Z a b) x` using `fun a b => ((cDiff n Z a b).2.differentiable (by simp)).differentiableAt`.

Establish `hdA : ∀ a b e, dK (cA Z a b) x e = (e * M - M * e) (Sum.inr a) (Sum.inr b)` using `fun a b e => dK_xZx Z x e (Sum.inr a) (Sum.inr b)`. Establish `hdB : ∀ a b e, dK (cB Z a b) x e = -((e * M - M * e) (Sum.inr a) (Sum.inl b))` using `fun a b e => by`. Establish `: cB Z a b = fun y => -((y * Z * yᴴ) (Sum.inr a) (Sum.inl b))` using `rfl`. Establish `hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x` using `((contDiff_xZx Z _ _).differentiable (by simp)).differentiableAt`. Establish `hn` using `hd.hasFDerivAt.neg.fderiv`.

Establish `hv : ∀ v, fderiv ℝ (fun y : M2 n => -(y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v = -fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v` using `fun v => by`. Conclude with `(congrArg (fun L : M2 n →L[ℝ] ℂ => L v) hn).trans rfl`. Establish `h` using `dK_xZx Z x e (Sum.inr a) (Sum.inl b)`. Rewrite `h` using `[dK]`. Rewrite using `[this, dK, hv, hv, ← h]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hL : fderiv ℂ Θ x (x * Z) = (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) * Θ x + ∑ a, ∑ b, (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b))`. Rewrite using `[hxZ]`. Use `conv_lhs => rw [decomp M]`. Rewrite using `[Matrix.add_mul, map_add, hlaw _ (by simp)]`.

Simplify using `only [Matrix.sum_mul, map_sum, Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul, hdK]`. Use `congr 1`. Simplify using `[Matrix.trace_sub]`. Rewrite using `[hL]`. Simplify using `only [hLeib _ (hcA _ _), hLeib _ (hcB _ _), hdA, hdB]`.

Establish `e1 : ∀ a b, (eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) * Θ x + cA Z a b x * dK Θ x (eA a b) + (-((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b)) * Θ x + cB Z a b x * dK Θ x (eB a b)) = ((eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) + -((eB a b * M - M * eB a b) (Sum …` using `fun a b => by ring`. Simplify using `only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, sumA, sumB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ptId : PtId := by
  intro n Θ x Z hx hΘ hlaw
  set M := x * Z * xᴴ with hM
  have hxZ : x * Z = M * x := by rw [hM, Matrix.mul_assoc (x * Z), hx.2, Matrix.mul_one]
  have hΘd : DifferentiableAt ℂ Θ x := hΘ.differentiableAt (by simp)
  have hR : ∀ v, fderiv ℝ Θ x v = fderiv ℂ Θ x v := fun v => by
    have h := (hΘd.hasFDerivAt.restrictScalars ℝ).fderiv
    exact (congrArg (fun L => L v) h).trans rfl
  have hdK : ∀ e, dK Θ x e = fderiv ℂ Θ x (e * x) := fun e => by
    rw [dK, hR, hR]
    conv_rhs => rw [← reK_add_imK e]
    rw [Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul]
  have hLeib : ∀ c : M2 n → ℂ, DifferentiableAt ℝ c x → ∀ e,
      dK (fun y => c y * Θ y) x e = dK c x e * Θ x + c x * dK Θ x e := fun c hc e => by
    have hΘr : DifferentiableAt ℝ Θ x := hΘd.restrictScalars ℝ
    have h := (hc.hasFDerivAt.mul hΘr.hasFDerivAt).fderiv
    have hv : ∀ v, fderiv ℝ (fun y => c y * Θ y) x v = c x * fderiv ℝ Θ x v + Θ x * fderiv ℝ c x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) h).trans rfl
    simp only [dK, hv]
    ring
  have hcA : ∀ a b, DifferentiableAt ℝ (cA Z a b) x := fun a b =>
    ((cDiff n Z a b).1.differentiable (by simp)).differentiableAt
  have hcB : ∀ a b, DifferentiableAt ℝ (cB Z a b) x := fun a b =>
    ((cDiff n Z a b).2.differentiable (by simp)).differentiableAt
  have hdA : ∀ a b e, dK (cA Z a b) x e = (e * M - M * e) (Sum.inr a) (Sum.inr b) := fun a b e =>
    dK_xZx Z x e (Sum.inr a) (Sum.inr b)
  have hdB : ∀ a b e, dK (cB Z a b) x e = -((e * M - M * e) (Sum.inr a) (Sum.inl b)) := fun a b e => by
    have : cB Z a b = fun y => -((y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) := rfl
    have hd : DifferentiableAt ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x :=
      ((contDiff_xZx Z _ _).differentiable (by simp)).differentiableAt
    have hn := hd.hasFDerivAt.neg.fderiv
    have hv : ∀ v, fderiv ℝ (fun y : M2 n => -(y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v =
        -fderiv ℝ (fun y : M2 n => (y * Z * yᴴ) (Sum.inr a) (Sum.inl b)) x v := fun v => by
      exact (congrArg (fun L : M2 n →L[ℝ] ℂ => L v) hn).trans rfl
    have h := dK_xZx Z x e (Sum.inr a) (Sum.inl b)
    rw [dK] at h
    rw [this, dK, hv, hv, ← h]; ring

  have hL : fderiv ℂ Θ x (x * Z) = (n : ℂ) * (M.toBlocks₁₁.trace - M.toBlocks₂₂.trace) * Θ x +
      ∑ a, ∑ b, (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := by
    rw [hxZ]
    conv_lhs => rw [decomp M]
    rw [Matrix.add_mul, map_add, hlaw _ (by simp)]
    simp only [Matrix.sum_mul, map_sum, Matrix.add_mul, Matrix.smul_mul, map_add, map_smul, smul_eq_mul, hdK]
    congr 1
    · simp [Matrix.trace_sub]
  rw [hL]
  simp only [hLeib _ (hcA _ _), hLeib _ (hcB _ _), hdA, hdB]
  have e1 : ∀ a b, (eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) * Θ x + cA Z a b x * dK Θ x (eA a b) +
      (-((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b)) * Θ x + cB Z a b x * dK Θ x (eB a b)) =
      ((eA a b * M - M * eA a b) (Sum.inr a) (Sum.inr b) + -((eB a b * M - M * eB a b) (Sum.inr a) (Sum.inl b))) * Θ x +
      (cA Z a b x * dK Θ x (eA a b) + cB Z a b x * dK Θ x (eB a b)) := fun a b => by ring
  simp only [e1, Finset.sum_add_distrib, ← Finset.sum_mul, sumA, sumB]
  ring

end PositivityTheory.Rg.Sw.LVs.II
