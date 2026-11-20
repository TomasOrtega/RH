import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ConjBound

open GlobalTheory.EigenNorm

variable {g : ℕ}

/- English proof (translation)
Establish `hz : z ∈ Submodule.span ℝ S` using `hS ▸ Submodule.mem_top`. Establish `hw : w ∈ Submodule.span ℝ S` using `hS ▸ Submodule.mem_top`. Establish `hr : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v` using `fun r v => by`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules.

Proceed by induction on `hz, hw using Submodule.span_induction₂ with`. Consider the case `mem_mem z w hz hw => exact h z hz w hw`. Consider the case `zero_left w _ => simp [hermForm]`. Consider the case `zero_right z _ => simp [hermForm]`. Consider the case `add_left z z' w _ _ _ h1 h2`.

Rewrite using `[mul_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]`. Consider the case `add_right z w w' _ _ _ h1 h2`. Rewrite using `[mul_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]`. Consider the case `smul_left r z w _ _ h1`. Rewrite using `[hr, mul_smul_comm, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1]`.

Consider the case `smul_right r z w _ _ h1`. Rewrite using `[hr, mul_smul_comm, hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1]`.
-/
theorem im_adjoint_of_span (Hm : Matrix (Fin g) (Fin g) ℂ) (t u : Fin g → ℂ) (S : Set (Fin g → ℂ))
    (hS : Submodule.span ℝ S = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ S, (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im) (z w : Fin g → ℂ) :
    (hermForm Hm (t * z) w).im = (hermForm Hm z (u * w)).im := by
  have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hw : w ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
  have hr : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v := fun r v => by
    funext i; simp
  induction hz, hw using Submodule.span_induction₂ with
  | mem_mem z w hz hw => exact h z hz w hw
  | zero_left w _ => simp [hermForm]
  | zero_right z _ => simp [hermForm]
  | add_left z z' w _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_left, hermForm_add_left, Complex.add_im, Complex.add_im, h1, h2]
  | add_right z w w' _ _ _ h1 h2 =>
    rw [mul_add, hermForm_add_right, hermForm_add_right, Complex.add_im, Complex.add_im, h1, h2]
  | smul_left r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_left, hermForm_smul_left, Complex.im_ofReal_mul, Complex.im_ofReal_mul, h1]
  | smul_right r z w _ _ h1 =>
    rw [hr, mul_smul_comm, hermForm_smul_right, hermForm_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul,
      Complex.im_ofReal_mul, h1]

/- English proof (translation)
Simplify using `[hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, _root_.mul_assoc]`.
-/
theorem hermForm_eq_sum (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z w = ∑ i, ∑ j, z i * Hm i j * starRingEnd ℂ (w j) := by
  simp [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, _root_.mul_assoc]

/- English proof (translation)
Establish `key : ∀ s : ℂ, (s * (t i * Hm i j)).im = (s * (Hm i j * t j)).im` using `fun s => by`. Use `h (Pi.single i s) (Pi.single j 1)` as an intermediate fact. Rewrite `this` using `[hermForm_eq_sum, hermForm_eq_sum]`. Simplify using `only [Pi.mul_apply, Pi.single_apply, Pi.star_apply, mul_ite, mul_zero, _root_.mul_one, ite_mul, zero_mul, apply_ite (starRingEnd ℂ), map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true, RCLike.star_def, Complex.conj_conj] at this`. Apply the tactic sequence `convert this using 2 <;> ring`.

Establish `h1` using `key 1`. Establish `h2` using `key Complex.I`. Rewrite `h1` using `[_root_.one_mul, _root_.one_mul]`. Rewrite `h2` using `[Complex.I_mul_im, Complex.I_mul_im]`. Conclude with `Complex.ext h2 h1`.
-/
theorem entry_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ)
    (h : ∀ z w, (hermForm Hm (t * z) w).im = (hermForm Hm z (star t * w)).im) (i j : Fin g) :
    t i * Hm i j = Hm i j * t j := by
  have key : ∀ s : ℂ, (s * (t i * Hm i j)).im = (s * (Hm i j * t j)).im := fun s => by
    have := h (Pi.single i s) (Pi.single j 1)
    rw [hermForm_eq_sum, hermForm_eq_sum] at this
    simp only [Pi.mul_apply, Pi.single_apply, Pi.star_apply, mul_ite, mul_zero, _root_.mul_one, ite_mul, zero_mul,
      apply_ite (starRingEnd ℂ), map_zero, map_one, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      RCLike.star_def, Complex.conj_conj] at this
    convert this using 2 <;> ring
  have h1 := key 1
  have h2 := key Complex.I
  rw [_root_.one_mul, _root_.one_mul] at h1
  rw [Complex.I_mul_im, Complex.I_mul_im] at h2
  exact Complex.ext h2 h1

/- English proof (translation)
Set `s : Fin g → ℂ` to `fun i => (Real.sqrt (κ - ‖t i‖ ^ 2) : ℝ)`. Establish `hs0 : ∀ i, s i ≠ 0` using `fun i => by`. Establish `: 0 < Real.sqrt (κ - ‖t i‖ ^ 2)` using `Real.sqrt_pos.2 (sub_pos.2 (ht i))`. Conclude with `Complex.ofReal_ne_zero.2 this.ne'`. Establish `hsy : s * y ≠ 0` using `fun h0 => hy (by`.

Use function extensionality and compare the values at `i`. Use `congrFun h0 i` as an intermediate fact. Simplify `this)` using `[hs0 i]`. Establish `hss : ∀ i, s i * starRingEnd ℂ (s i) + t i * starRingEnd ℂ (t i) = κ` using `fun i => by`. Rewrite using `[Complex.mul_conj', Complex.mul_conj']`.

Establish `: ‖s i‖ ^ 2 = κ - ‖t i‖ ^ 2`. Simplify using `only [s, Complex.norm_real, Real.norm_eq_abs, sq_abs]`. Conclude with `Real.sq_sqrt (sub_pos.2 (ht i)).le`. Rewrite using `[← Complex.ofReal_pow, this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsum : hermForm Hm (s * y) (s * y) + hermForm Hm (t * y) (t * y) = κ * hermForm Hm y y`. Simplify using `only [hermForm_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : Hm i j = 0`.

Simplify using `[h0]`. Establish `hij : t i = t j`. Use `hc i j` as an intermediate fact. Rewrite `this` using `[mul_comm]`. Conclude with `mul_left_cancel₀ h0 this`.

Establish `hsij : s i = s j` using `by simp only [s, hij]`. Simplify using `only [Pi.mul_apply, map_mul, hij, hsij, ← hss j]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `hpos _ hsy`. Establish `h2` using `congrArg Complex.re hsum`.

Rewrite `h2` using `[Complex.add_re, Complex.re_ofReal_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem re_lt_of_comm (Hm : Matrix (Fin g) (Fin g) ℂ) (t : Fin g → ℂ) (κ : ℝ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hc : ∀ i j, t i * Hm i j = Hm i j * t j) (ht : ∀ i, ‖t i‖ ^ 2 < κ) (y : Fin g → ℂ) (hy : y ≠ 0) :
    (hermForm Hm (t * y) (t * y)).re < κ * (hermForm Hm y y).re := by
  let s : Fin g → ℂ := fun i => (Real.sqrt (κ - ‖t i‖ ^ 2) : ℝ)
  have hs0 : ∀ i, s i ≠ 0 := fun i => by
    have : 0 < Real.sqrt (κ - ‖t i‖ ^ 2) := Real.sqrt_pos.2 (sub_pos.2 (ht i))
    exact Complex.ofReal_ne_zero.2 this.ne'
  have hsy : s * y ≠ 0 := fun h0 => hy (by
    funext i
    have := congrFun h0 i
    simpa [hs0 i] using this)
  have hss : ∀ i, s i * starRingEnd ℂ (s i) + t i * starRingEnd ℂ (t i) = κ := fun i => by
    rw [Complex.mul_conj', Complex.mul_conj']
    have : ‖s i‖ ^ 2 = κ - ‖t i‖ ^ 2 := by
      simp only [s, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Real.sq_sqrt (sub_pos.2 (ht i)).le
    rw [← Complex.ofReal_pow, this]
    push_cast; ring
  have hsum : hermForm Hm (s * y) (s * y) + hermForm Hm (t * y) (t * y) = κ * hermForm Hm y y := by
    simp only [hermForm_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : Hm i j = 0
    · simp [h0]
    · have hij : t i = t j := by
        have := hc i j
        rw [mul_comm] at this
        exact mul_left_cancel₀ h0 this
      have hsij : s i = s j := by simp only [s, hij]
      simp only [Pi.mul_apply, map_mul, hij, hsij, ← hss j]
      ring
  have h1 := hpos _ hsy
  have h2 := congrArg Complex.re hsum
  rw [Complex.add_re, Complex.re_ofReal_mul] at h2
  linarith

/- English proof (translation)
Introduce `E _ _ _ H D g ty Q Hm a κ hlin ⟨_, _, hspan, _, hpos, him⟩ hκ`. Set `t : Fin g → ℂ` to `fun i => ty i (a : E)`. Establish `h1 : ∀ x, t * Q x = Q (a • x)` using `fun x => funext fun i => (hlin a x i).symm`. Establish `h2 : ∀ x, star t * Q x = Q (H.bar a • x)` using `fun x => funext fun i => by`. Rewrite using `[hlin, H.bar_eq, IsCMField.complexEmbedding_complexConj]`.

Both sides reduce to the same expression. Use `⟨LinearMap.mulLeft ℂ t, h1, fun y hy => ?_⟩` and prove the remaining obligations. Use `re_lt_of_comm Hm t κ hpos (entry_comm Hm t (im_adjoint_of_span Hm t (star t) _ hspan ?_)) (fun i => hκ (ty i)) y hy` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩ _ ⟨x', rfl⟩`. Rewrite using `[h1, h2, him, him, D.adj]`.
-/
theorem exists_action_lt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Q : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (a : 𝓞 E) (κ : ℕ), (∀ (c : 𝓞 E) x i, Q (c • x) i = ty i (c : E) * Q x i) → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = D.EF x y) → (∀ τ : E →+* ℂ, ‖τ (a : E)‖ ^ 2 < κ) → ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (a • x)) ∧ ∀ y, y ≠ 0 → (hermForm Hm (F y) (F y)).re < κ * (hermForm Hm y y).re := by
  intro E _ _ _ H D g ty Q Hm a κ hlin ⟨_, _, hspan, _, hpos, him⟩ hκ
  let t : Fin g → ℂ := fun i => ty i (a : E)
  have h1 : ∀ x, t * Q x = Q (a • x) := fun x => funext fun i => (hlin a x i).symm
  have h2 : ∀ x, star t * Q x = Q (H.bar a • x) := fun x => funext fun i => by
    rw [hlin, H.bar_eq, IsCMField.complexEmbedding_complexConj]; rfl
  refine ⟨LinearMap.mulLeft ℂ t, h1, fun y hy => ?_⟩
  refine re_lt_of_comm Hm t κ hpos (entry_comm Hm t (im_adjoint_of_span Hm t (star t) _ hspan ?_))
    (fun i => hκ (ty i)) y hy
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
  rw [h1, h2, him, him, D.adj]

end GlobalTheory.ConjBound
