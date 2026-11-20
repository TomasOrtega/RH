import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.Frames
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

namespace GlobalTheory.DefiniteFrames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
/- English proof (translation)
Break down `hp with h | h` into its components or cases. Use `⟨-1, by norm_num, ?_⟩` and prove the remaining obligations. Use extensionality with `a b`. Apply the tactic sequence `by_cases hab : a = b <;> simp [Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, h, hab]`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations.

Use extensionality with `a b`. Establish `ha : (a : ℕ) < X.p0` using `lt_of_lt_of_le a.isLt h`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using `[Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]`.

Simplify using `[Matrix.diagonal_apply, Matrix.one_apply, hab]`.
-/
private lemma exists_diagonal_sgn_eq_smul_one (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hp : X.p0 = 0 ∨ r ≤ X.p0) :
    ∃ c : ℂ, c ≠ 0 ∧
      (Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) = c • 1 := by
  rcases hp with h | h
  · refine ⟨-1, by norm_num, ?_⟩
    ext a b
    by_cases hab : a = b <;> simp [Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, h, hab]
  · refine ⟨1, one_ne_zero, ?_⟩
    ext a b
    have ha : (a : ℕ) < X.p0 := lt_of_lt_of_le a.isLt h
    by_cases hab : a = b
    · subst hab
      simp [Matrix.diagonal_apply, Matrix.one_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn, ha]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hab]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
/- English proof (translation)
Take `⟨V, rfl⟩ : ∃ V, M = M₀ * V` from `⟨M₀⁻¹ * M, (Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr h₀)).symm⟩`. Establish `hVV : V.transpose * V.map (starRingEnd ℂ) = 1`. Rewrite `hM` using `[Matrix.transpose_mul, Matrix.map_mul]`. Establish `h : V.transpose * (M₀.transpose * G * M₀.map (starRingEnd ℂ)) * V.map (starRingEnd ℂ) = c • 1`. Rewrite using `[← hM]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite `h` using `[hM₀, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]`. Conclude with `smul_right_injective _ hc h`. Establish `hVV' : V.map (starRingEnd ℂ) * V.transpose = 1` using `mul_eq_one_comm.mp hVV`. Establish `hbound : ∀ a b, ‖V a b‖ ≤ 1`.

Introduce `a b`. Establish `h` using `congrFun (congrFun hVV' a) a`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h`. Establish `hs : ∑ k, Complex.normSq (V a k) = 1`. Establish `h' : ((∑ k, Complex.normSq (V a k) : ℝ) : ℂ) = 1`.

Rewrite using `[← h]`. Use `push_cast`. Simplify using `[Complex.normSq_eq_conj_mul_self]`. Conclude with `h'` after adjusting the coercions. Establish `hle : Complex.normSq (V a b) ≤ 1` using `hs ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (V a k)) (Finset.mem_univ b)`.

Rewrite `hle` using `[Complex.normSq_eq_norm_sq]`. Use polynomial arithmetic with `[norm_nonneg (V a b)]`. Rewrite using `[Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`.

Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hbound k j)`.
-/
private lemma norm_apply_le_sum_of_gram_eq_smul_one {n : ℕ} (G M M₀ : Matrix (Fin n) (Fin n) ℂ)
    (c : ℂ) (hc : c ≠ 0) (h₀ : M₀.det ≠ 0)
    (hM₀ : M₀.transpose * G * M₀.map (starRingEnd ℂ) = c • 1)
    (hM : M.transpose * G * M.map (starRingEnd ℂ) = c • 1) (i j : Fin n) :
    ‖M i j‖ ≤ ∑ k, ‖M₀ i k‖ := by
  obtain ⟨V, rfl⟩ : ∃ V, M = M₀ * V :=
    ⟨M₀⁻¹ * M, (Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.mpr h₀)).symm⟩
  have hVV : V.transpose * V.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.transpose_mul, Matrix.map_mul] at hM
    have h : V.transpose * (M₀.transpose * G * M₀.map (starRingEnd ℂ)) * V.map (starRingEnd ℂ)
        = c • 1 := by
      rw [← hM]; simp only [Matrix.mul_assoc]
    rw [hM₀, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h
    exact smul_right_injective _ hc h
  have hVV' : V.map (starRingEnd ℂ) * V.transpose = 1 := mul_eq_one_comm.mp hVV
  have hbound : ∀ a b, ‖V a b‖ ≤ 1 := by
    intro a b
    have h := congrFun (congrFun hVV' a) a
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
      Matrix.one_apply_eq] at h
    have hs : ∑ k, Complex.normSq (V a k) = 1 := by
      have h' : ((∑ k, Complex.normSq (V a k) : ℝ) : ℂ) = 1 := by
        rw [← h]; push_cast; simp [Complex.normSq_eq_conj_mul_self]
      exact_mod_cast h'
    have hle : Complex.normSq (V a b) ≤ 1 :=
      hs ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (V a k)) (Finset.mem_univ b)
    rw [Complex.normSq_eq_norm_sq] at hle
    nlinarith [norm_nonneg (V a b)]
  rw [Matrix.mul_apply]
  calc ‖∑ k, M₀ i k * V k j‖ ≤ ∑ k, ‖M₀ i k * V k j‖ := norm_sum_le _ _
    _ ≤ ∑ k, ‖M₀ i k‖ := Finset.sum_le_sum fun k _ => by
      rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hbound k j)

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

/- English proof (translation)
Take `⟨c, hc, hD⟩` from `exists_diagonal_sgn_eq_smul_one X hp`. Break down `Set.eq_empty_or_nonempty {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} with he | ⟨x₀, hx₀⟩` into its components or cases. Rewrite using `[he]`. Conclude with `isCompact_empty`. Establish `hgram : ∀ {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}, X.IsOrtho x → ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).transpose * X.Gm.map (τ : E →+* ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).map (starRingEnd ℂ) = c • 1`.

Introduce `x hx τ`. Rewrite using `[← _root_.PIW.FdPA.gram_eq, ← hD]`. Conclude with `hx τ`. Establish `hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ).det ≠ 0` using `fun τ => _root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm _ (by rw [_root_.PIW.FdPA.gram_eq, hgram hx₀ τ]; simp [hc])`. Establish `hU : ∀ τ : X.Ψ, Continuous fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ` using `fun τ => continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))`.

Use `IsCompact.of_isClosed_subset (s := Set.univ.pi fun τ => Set.univ.pi fun i => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) (∑ k, ‖x₀ τ i k‖)) (isCompact_univ_pi fun τ => isCompact_univ_pi fun i => isCompact_univ_pi fun _ => isCompact_closedBall _ _) ?_ ?_` and prove the remaining obligations. Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho, Set.setOf_forall]`. Use `isClosed_iInter fun τ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Simplify using `only [_root_.PIW.FdPA.gram_eq]`. Conclude with `((hU τ).matrix_transpose.matrix_mul continuous_const).matrix_mul ((hU τ).matrix_map Complex.continuous_conj)`.

Introduce `x hx`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]`. Introduce `τ i j`. Conclude with `norm_apply_le_sum_of_gram_eq_smul_one (X.Gm.map (τ : E →+* ℂ)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ) c hc (hdet τ) (hgram hx₀ τ) (hgram hx τ) i j`.
-/
theorem _root_.GlobalTheory.DefiniteFrames.isCompact_ortho (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hp : X.p0 = 0 ∨ r ≤ X.p0) :
    IsCompact {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} := by
  obtain ⟨c, hc, hD⟩ := exists_diagonal_sgn_eq_smul_one X hp
  rcases Set.eq_empty_or_nonempty {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r | X.IsOrtho x} with he | ⟨x₀, hx₀⟩
  · rw [he]; exact isCompact_empty
  have hgram : ∀ {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r}, X.IsOrtho x → ∀ τ : X.Ψ,
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).transpose * X.Gm.map (τ : E →+* ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).map (starRingEnd ℂ)
        = c • 1 := by
    intro x hx τ
    rw [← _root_.PIW.FdPA.gram_eq, ← hD]
    exact hx τ
  have hdet : ∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ).det ≠ 0 := fun τ =>
    _root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm _ (by rw [_root_.PIW.FdPA.gram_eq, hgram hx₀ τ]; simp [hc])
  have hU : ∀ τ : X.Ψ, Continuous fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ := fun τ =>
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))
  refine IsCompact.of_isClosed_subset (s := Set.univ.pi fun τ => Set.univ.pi fun i =>
      Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) (∑ k, ‖x₀ τ i k‖))
    (isCompact_univ_pi fun τ => isCompact_univ_pi fun i => isCompact_univ_pi fun _ =>
      isCompact_closedBall _ _) ?_ ?_
  · simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho, Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    simp only [_root_.PIW.FdPA.gram_eq]
    exact ((hU τ).matrix_transpose.matrix_mul continuous_const).matrix_mul
      ((hU τ).matrix_map Complex.continuous_conj)
  · intro x hx
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro τ i j
    exact norm_apply_le_sum_of_gram_eq_smul_one (X.Gm.map (τ : E →+* ℂ)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
      (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x₀ τ) c hc (hdet τ) (hgram hx₀ τ) (hgram hx τ) i j

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
/- English proof (translation)
Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho at hx`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG`. Establish `hsgn : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0` using `fun a => by`. Apply the tactic sequence `rcases _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq X.p0 a with h | h <;> simp [h]`. Introduce `τ`.

Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Apply `_root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm` to reduce the goal to its premises. Rewrite using `[hx τ, Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast hsgn a`. Establish `hmin : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ)`.

Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn`. Rewrite using `[hx τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal, Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]`. Simplify using the standard rewrite rules. Establish `hne : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun a _ => hsgn a`. Rewrite using `[hmin, Complex.ofReal_re]`. Conclude with `mul_self_pos.mpr hne`.
-/
private lemma mem_dom_of_isOrtho' (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : X.IsOrtho x) :
    x ∈ X.dom := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsOrtho at hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.dom _root_.ReciprocityTheory.ChartRestriction.G.FD.GG
  have hsgn : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := fun a => by
    rcases _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_sq X.p0 a with h | h <;> simp [h]
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · apply _root_.PIW.FdPA.det_ne_of_gram (τ : E →+* ℂ) X.Gm
    rw [hx τ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => by exact_mod_cast hsgn a
  · have hmin : _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((_root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.dmin _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
      rw [hx τ, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.lminor_diagonal, Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range]
      simp
    have hne : _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0 := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.psgn
      exact Finset.prod_ne_zero_iff.mpr fun a _ => hsgn a
    rw [hmin, Complex.ofReal_re]
    exact mul_self_pos.mpr hne

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

/- English proof (translation)
Introduce `E _ _ _ r X hp`. Use `⟨{x | X.IsOrtho x}, _root_.GlobalTheory.DefiniteFrames.isCompact_ortho X hp, fun x hx => mem_dom_of_isOrtho' X hx, fun x hx => ⟨1, X.Γ.one_mem, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.b …` and prove the remaining obligations. Establish `h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.Reciprocity …`. Unfold `_root_.ReciprocityTheory.ChartRestriction.G.FD.lact`. Use function extensionality and compare the values at `τ`.

Rewrite using `[Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx`.
-/
theorem _root_.GlobalTheory.DefiniteFrames.exists_compact_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (X.p0 = 0 ∨ r ≤ X.p0) → ∃ C : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom, ∃ γ ∈ X.Γ, ∃ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r, _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ∈ C := by
  intro E _ _ _ r X hp
  refine ⟨{x | X.IsOrtho x}, _root_.GlobalTheory.DefiniteFrames.isCompact_ortho X hp,
    fun x hx => mem_dom_of_isOrtho' X hx,
    fun x hx => ⟨1, X.Γ.one_mem, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x, _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx, ?_⟩⟩
  have h1 : _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
    funext τ
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    rfl
  rw [h1]
  exact _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx

end GlobalTheory.DefiniteFrames
