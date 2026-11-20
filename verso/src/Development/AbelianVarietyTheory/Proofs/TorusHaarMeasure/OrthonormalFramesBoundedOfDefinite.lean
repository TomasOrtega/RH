import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Use `set y := x.map (starRingEnd ℂ) with hy`. Establish `h1 : xᵀ * (s • (G * y)) = 1`. Rewrite using `[Matrix.mul_smul, ← Matrix.mul_assoc, h, smul_smul, hs, one_smul]`. Establish `h2 : (s • (G * y)) * xᵀ = 1` using `mul_eq_one_comm.1 h1`. Establish `h3 : G * (s • (y * xᵀ)) = 1`.

Rewrite using `[Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul]`. Conclude with `h2`. Establish `hinv : G⁻¹ = s • (y * xᵀ)` using `Matrix.inv_eq_right_inv h3`. Apply the tactic sequence `have hentry : G⁻¹ a a = s * ((∑ c, ‖x a c‖ ^ 2 : ℝ) : ℂ) := by`. Rewrite using `[hinv, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]`.

Use `congr 1`. Use `push_cast`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `[hy, Matrix.transpose_apply, Complex.conj_mul']`. Establish `hsn : ‖s‖ = 1`.

Establish `h4` using `congrArg norm hs`. Rewrite `h4` using `[norm_mul, norm_one]`. Use polynomial arithmetic with `[norm_nonneg s]`. Establish `hsum : 0 ≤ ∑ c, ‖x a c‖ ^ 2` using `Finset.sum_nonneg fun c _ => sq_nonneg _`. Establish `hnorm : ‖G⁻¹ a a‖ = ∑ c, ‖x a c‖ ^ 2`.

Rewrite using `[hentry, norm_mul, hsn, one_mul, Complex.norm_of_nonneg hsum]`. Establish `hle : ‖x a b‖ ^ 2 ≤ ∑ c, ‖x a c‖ ^ 2` using `Finset.single_le_sum (f := fun c => ‖x a c‖ ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)`. Rewrite using `[hnorm]`. Use polynomial arithmetic with `[sq_nonneg (‖x a b‖ - 1), norm_nonneg (x a b)]`.
-/
theorem _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one {r : ℕ} (G x : Matrix (Fin r) (Fin r) ℂ) (s : ℂ)
    (hs : s * s = 1) (h : xᵀ * G * x.map (starRingEnd ℂ) = s • (1 : Matrix (Fin r) (Fin r) ℂ))
    (a b : Fin r) : ‖x a b‖ ≤ 1 + ‖G⁻¹ a a‖ := by
  set y := x.map (starRingEnd ℂ) with hy
  have h1 : xᵀ * (s • (G * y)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, h, smul_smul, hs, one_smul]
  have h2 : (s • (G * y)) * xᵀ = 1 := mul_eq_one_comm.1 h1
  have h3 : G * (s • (y * xᵀ)) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.smul_mul]; exact h2
  have hinv : G⁻¹ = s • (y * xᵀ) := Matrix.inv_eq_right_inv h3
  have hentry : G⁻¹ a a = s * ((∑ c, ‖x a c‖ ^ 2 : ℝ) : ℂ) := by
    rw [hinv, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hy, Matrix.transpose_apply, Complex.conj_mul']
  have hsn : ‖s‖ = 1 := by
    have h4 := congrArg norm hs
    rw [norm_mul, norm_one] at h4
    nlinarith [norm_nonneg s]
  have hsum : 0 ≤ ∑ c, ‖x a c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hnorm : ‖G⁻¹ a a‖ = ∑ c, ‖x a c‖ ^ 2 := by
    rw [hentry, norm_mul, hsn, one_mul, Complex.norm_of_nonneg hsum]
  have hle : ‖x a b‖ ^ 2 ≤ ∑ c, ‖x a c‖ ^ 2 :=
    Finset.single_le_sum (f := fun c => ‖x a c‖ ^ 2) (fun c _ => sq_nonneg _) (Finset.mem_univ b)
  rw [hnorm]
  nlinarith [sq_nonneg (‖x a b‖ - 1), norm_nonneg (x a b)]

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `r X hp`. Use `⟨1 + ∑ τ : X.Ψ, ∑ a : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖, fun x hx τ a b => ?_⟩` and prove the remaining obligations. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx`. Establish `hτ` using `hx τ`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hdiag⟩ : ∃ s : ℂ, s * s = 1 ∧ Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = s • 1 := by`.

Break down `hp with h | h` into its components or cases. Use `⟨-1, by norm_num, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `[h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]`. Use `⟨1, by norm_num, ?_⟩` and prove the remaining obligations.

Use extensionality with `i j`. Simplify using `[h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]`. Establish `key : (Matrix.of (x τ))ᵀ * X.Gm.map (τ : E →+* ℂ) * (Matrix.of (x τ)).map (starRingEnd ℂ) = s • 1`. Rewrite using `[← hdiag, ← hτ]`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.mat`.

Use extensionality with `i j`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hb` using `_root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one _ _ s hs key a b`. Establish `h1 : ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖ ≤ ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖` using `Finset.single_le_sum (f := fun a' => ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ a)`.

Establish `h2 : ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ ≤ ∑ τ' : X.Ψ, ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖` using `Finset.single_le_sum (f := fun τ' : X.Ψ => ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖) (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)`. Establish `hx' : ‖x τ a b‖ = ‖Matrix.of (x τ) a b‖` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.orthonormal_frames_bounded_of_definite :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ X.p0 = r) →
      ∃ R : ℝ, ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ τ a b, ‖x τ a b‖ ≤ R) := by
  intro r X hp
  refine ⟨1 + ∑ τ : X.Ψ, ∑ a : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖,
    fun x hx τ a b => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx
  have hτ := hx τ
  obtain ⟨s, hs, hdiag⟩ : ∃ s : ℂ, s * s = 1 ∧
      Matrix.diagonal (fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = s • 1 := by
    rcases hp with h | h
    · refine ⟨-1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
    · refine ⟨1, by norm_num, ?_⟩
      ext i j
      simp [h, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.diagonal_apply, Matrix.one_apply]
  have key : (Matrix.of (x τ))ᵀ * X.Gm.map (τ : E →+* ℂ) * (Matrix.of (x τ)).map (starRingEnd ℂ)
      = s • 1 := by
    rw [← hdiag, ← hτ]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.gram _root_.ReciprocityTheory.ChartRestriction.G.FD.mat
    ext i j
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC, _root_.ReciprocityTheory.ChartRestriction.G.FD.col, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hb := _root_.GlobalTheory.norm_entry_le_of_gram_eq_smul_one _ _ s hs key a b
  have h1 : ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a a‖ ≤ ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun a' => ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h2 : ∑ a' : Fin r, ‖((X.Gm.map (τ : E →+* ℂ))⁻¹) a' a'‖ ≤
      ∑ τ' : X.Ψ, ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖ :=
    Finset.single_le_sum (f := fun τ' : X.Ψ => ∑ a' : Fin r, ‖((X.Gm.map (τ' : E →+* ℂ))⁻¹) a' a'‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hx' : ‖x τ a b‖ = ‖Matrix.of (x τ) a b‖ := rfl
  linarith

end GlobalTheory
