import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open scoped Matrix in
/- English proof (translation)
Simplify using `only [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]`.
-/
private theorem gram_mul_eq_transpose_mul_gram_mul_conj {F : Type} [Field F] {r : ℕ} (τ : F →+* ℂ)
    (G : Matrix (Fin r) (Fin r) F) (A g : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (A * g) = gᵀ * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G A * g.map (starRingEnd ℂ) := by
  simp only [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul,
    Matrix.mul_assoc]

open scoped Matrix in
/- English proof (translation)
Establish `hBd : B = Matrix.diagonal fun a => B a a`. Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.diagonal_apply_ne _ hij, hdiag i j (Ne.symm hij)]`. Rewrite using `[hBd]`. Simplify using `only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Rewrite using `[← Complex.mul_conj]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℂ} (d : Fin r → ℂ) (hdiag : ∀ a c, c ≠ a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) =
      Matrix.diagonal fun a => ((Complex.normSq (B a a) : ℝ) : ℂ) * d a := by
  have hBd : B = Matrix.diagonal fun a => B a a := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hdiag i j (Ne.symm hij)]
  rw [hBd]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
  congr 1
  funext a
  rw [← Complex.mul_conj]
  ring

open scoped Matrix in
/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hunit : IsUnit B.det` using `isUnit_iff_ne_zero.2 hdet`. Establish `htri : B.BlockTriangular id` using `fun i j hij => hup i j hij`. Use `letI := B.invertibleOfIsUnitDet hunit`.

Establish `hinv : B⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular htri`. Establish `h2 : Matrix.diagonal d * B.map (starRingEnd ℂ) = (B⁻¹)ᵀ * Matrix.diagonal d`. Establish `h3 : (B⁻¹)ᵀ * (Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ)) = (B⁻¹)ᵀ * Matrix.diagonal d` using `by rw [h]`. Rewrite `h3` using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hunit, Matrix.transpose_one, Matrix.one_mul]`. Then use the resulting hypothesis. Establish `hoff : ∀ a c, a < c → B a c = 0`.

Introduce `a c hac`. Establish `h4` using `congrFun (congrFun h2 a) c`. Rewrite `h4` using `[Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hinv hac, zero_mul, Matrix.map_apply]`. Establish `h5` using `(mul_eq_zero.1 h4).resolve_left (hd a)`. Simplify using `using h5`.

Establish `hdiag : ∀ a c, c ≠ a → B a c = 0`. Introduce `a c hca`. Break down `lt_or_gt_of_ne hca with hlt | hlt` into its components or cases. Conclude with `hup a c hlt`. Conclude with `hoff a c hlt`.

Rewrite `h` using `[transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d hdiag]`. Introduce `a`. Use `⟨?_, hdiag a⟩` and prove the remaining obligations. Establish `h6` using `congrFun (congrFun h a) a`. Simplify using `only [Matrix.diagonal_apply_eq] at h6`.

Establish `h7 : ((Complex.normSq (B a a) : ℝ) : ℂ) = 1` using `mul_right_cancel₀ (hd a) (h6.trans (one_mul _).symm)`. Establish `h8 : ‖B a a‖ ^ 2 = 1`. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Conclude with `h7` after adjusting the coercions. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h8`.

Introduce `h`. Rewrite using `[transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d fun a c hca => (h a).2 c hca]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Complex.normSq_eq_norm_sq, (h a).1]`.

Simplify using the standard rewrite rules.
-/
private theorem transpose_mul_diagonal_mul_conj_eq_diagonal_iff {r : ℕ} {B : Matrix (Fin r) (Fin r) ℂ}
    {d : Fin r → ℂ} (hd : ∀ a, d a ≠ 0) (hdet : B.det ≠ 0) (hup : ∀ a c, c < a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) = Matrix.diagonal d ↔
      ∀ a, ‖B a a‖ = 1 ∧ ∀ c, c ≠ a → B a c = 0 := by
  constructor
  · intro h
    have hunit : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
    have htri : B.BlockTriangular id := fun i j hij => hup i j hij
    letI := B.invertibleOfIsUnitDet hunit
    have hinv : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular htri
    have h2 : Matrix.diagonal d * B.map (starRingEnd ℂ) = (B⁻¹)ᵀ * Matrix.diagonal d := by
      have h3 : (B⁻¹)ᵀ * (Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ)) =
          (B⁻¹)ᵀ * Matrix.diagonal d := by rw [h]
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
        Matrix.mul_nonsing_inv _ hunit, Matrix.transpose_one, Matrix.one_mul] at h3
    have hoff : ∀ a c, a < c → B a c = 0 := by
      intro a c hac
      have h4 := congrFun (congrFun h2 a) c
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hinv hac, zero_mul,
        Matrix.map_apply] at h4
      have h5 := (mul_eq_zero.1 h4).resolve_left (hd a)
      simpa using h5
    have hdiag : ∀ a c, c ≠ a → B a c = 0 := by
      intro a c hca
      rcases lt_or_gt_of_ne hca with hlt | hlt
      · exact hup a c hlt
      · exact hoff a c hlt
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d hdiag] at h
    intro a
    refine ⟨?_, hdiag a⟩
    have h6 := congrFun (congrFun h a) a
    simp only [Matrix.diagonal_apply_eq] at h6
    have h7 : ((Complex.normSq (B a a) : ℝ) : ℂ) = 1 :=
      mul_right_cancel₀ (hd a) (h6.trans (one_mul _).symm)
    have h8 : ‖B a a‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast h7
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h8
  · intro h
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d fun a c hca => (h a).2 c hca]
    congr 1
    funext a
    rw [Complex.normSq_eq_norm_sq, (h a).1]
    simp

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in

/- English proof (translation)
Introduce `r X x b hx hb`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx ⊢`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb`. Simplify using `only [Set.mem_setOf_eq] at hb`. Establish `hd : ∀ a : Fin r, ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ) ≠ 0`.

Introduce `a`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hprod : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ` using `fun τ => rfl`. Prove the components needed by the constructor for the conclusion.

Introduce `h τ`. Establish `key` using `h τ`. Rewrite `key` using `[hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ]`. Conclude with `(transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).1 key`. Introduce `h τ`.

Rewrite using `[hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ]`. Conclude with `(transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).2 (h τ)`.
-/
theorem _root_.GlobalTheory.isOrth_rmul_iff_unitary_diagonal :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r →
      (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ↔ ∀ τ a, ‖b τ a a‖ = 1 ∧ ∀ c, c ≠ a → b τ a c = 0)) := by
  intro r X x b hx hb
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx ⊢
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  simp only [Set.mem_setOf_eq] at hb
  have hd : ∀ a : Fin r, ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro a
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hprod : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := fun τ => rfl
  constructor
  · intro h τ
    have key := h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ] at key
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).1 key
  · intro h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ]
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).2 (h τ)

end GlobalTheory
