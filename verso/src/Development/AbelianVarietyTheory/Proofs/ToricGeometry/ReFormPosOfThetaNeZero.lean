import Mathlib

open Complex Matrix Filter Topology
open scoped BigOperators Real

namespace GlobalTheory.ThetaPositivity

variable {g : ℕ}

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Rewrite using `[← star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, ← Matrix.dotProduct_mulVec]`.
-/
lemma _root_.GlobalTheory.ThetaPositivity.form_conj {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    w ⬝ᵥ Hm.mulVec (star z) = star (z ⬝ᵥ Hm.mulVec (star w)) := by
  rw [← star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, ← Matrix.dotProduct_mulVec]

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
/- English proof (translation)
Rewrite using `[star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, _root_.GlobalTheory.ThetaPositivity.form_conj hH z w]`. Simplify using `only [Complex.add_re, Complex.star_def, Complex.conj_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma _root_.GlobalTheory.ThetaPositivity.form_add_self {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    ((z + w) ⬝ᵥ Hm.mulVec (star (z + w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (z ⬝ᵥ Hm.mulVec (star w)).re
        + (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
    _root_.GlobalTheory.ThetaPositivity.form_conj hH z w]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
/- English proof (translation)
The claim follows from `Complex.continuous_re.comp (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))`.
-/
private lemma continuous_re_dotProduct_mulVec_star (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous (fun z : Fin g → ℂ => (z ⬝ᵥ Hm.mulVec (star z)).re) :=
  Complex.continuous_re.comp (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star))

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Use `set F : (Fin g → ℂ) → ℝ := fun z => ‖θ z‖ * Real.exp (-(Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)) with hFdef`. Establish `hF : Continuous F` using `hθ.norm.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_re_dotProduct_mulVec_star Hm)).neg))`. Establish `hper : ∀ (l : Λ) z, F (z + l) = F z`. Introduce `l z`. Establish `hre : ∀ a b : ℂ, ((Real.pi : ℂ) * a + Real.pi / 2 * b).re = Real.pi * a.re + Real.pi / 2 * b.re` using `fun a b => by`.

Simplify using `[Complex.add_re, Complex.re_ofReal_mul]`. Simplify using `only [hFdef, htr, norm_mul, hχ, one_mul, Complex.norm_exp, hre, _root_.GlobalTheory.ThetaPositivity.form_add_self hH]`. Rewrite using `[mul_comm (Real.exp _) ‖θ z‖, mul_assoc, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.

Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `bR` to `Module.Basis.ofZLatticeBasis ℝ Λ b`. Establish `hK : IsCompact (closure (ZSpan.fundamentalDomain bR))` using `(ZSpan.fundamentalDomain_isBounded bR).isCompact_closure`. Take `⟨C, hC⟩` from `hK.exists_bound_of_continuousOn hF.continuousOn`. Use `⟨C, fun z => ?_⟩` and prove the remaining obligations.

Establish `hmem : ((ZSpan.floor bR z : Submodule.span ℤ (Set.range bR)) : Fin g → ℂ) ∈ Λ`. Conclude with `(Module.Basis.ofZLatticeBasis_span ℝ Λ b).le (ZSpan.floor bR z).2`. Establish `hz : F z = F (ZSpan.fract bR z)`. Use `hper ⟨_, hmem⟩ (ZSpan.fract bR z)` as an intermediate fact. Rewrite using `[← this, ZSpan.fract_apply]`.

Simplify using the standard rewrite rules. Establish `hbd : F z ≤ C`. Rewrite using `[hz]`. Conclude with `(le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain bR z)))`. Establish `hexp` using `Real.exp_pos (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hFdef, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]`. Use `_ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := mul_le_mul_of_nonneg_right hbd hexp.le`.
-/
lemma _root_.GlobalTheory.ThetaPositivity.exists_norm_le (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (χ : Λ → ℂ) (hχ : ∀ l, ‖χ l‖ = 1)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Continuous θ)
    (htr : ∀ (l : Λ) z, θ (z + l) =
      (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
        Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) :
    ∃ C : ℝ, ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
  classical
  set F : (Fin g → ℂ) → ℝ := fun z =>
    ‖θ z‖ * Real.exp (-(Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)) with hFdef
  have hF : Continuous F :=
    hθ.norm.mul (Real.continuous_exp.comp ((continuous_const.mul (continuous_re_dotProduct_mulVec_star Hm)).neg))
  have hper : ∀ (l : Λ) z, F (z + l) = F z := by
    intro l z
    have hre : ∀ a b : ℂ, ((Real.pi : ℂ) * a + Real.pi / 2 * b).re
        = Real.pi * a.re + Real.pi / 2 * b.re := fun a b => by
      simp [Complex.add_re, Complex.re_ofReal_mul]
    simp only [hFdef, htr, norm_mul, hχ, one_mul, Complex.norm_exp, hre,
      _root_.GlobalTheory.ThetaPositivity.form_add_self hH]
    rw [mul_comm (Real.exp _) ‖θ z‖, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  have hK : IsCompact (closure (ZSpan.fundamentalDomain bR)) :=
    (ZSpan.fundamentalDomain_isBounded bR).isCompact_closure
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨C, fun z => ?_⟩
  have hmem : ((ZSpan.floor bR z : Submodule.span ℤ (Set.range bR)) : Fin g → ℂ) ∈ Λ := by
    exact (Module.Basis.ofZLatticeBasis_span ℝ Λ b).le (ZSpan.floor bR z).2
  have hz : F z = F (ZSpan.fract bR z) := by
    have := hper ⟨_, hmem⟩ (ZSpan.fract bR z)
    rw [← this, ZSpan.fract_apply]
    simp
  have hbd : F z ≤ C := by
    rw [hz]
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      hC _ (subset_closure (ZSpan.fract_mem_fundamentalDomain bR z)))
  have hexp := Real.exp_pos (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re)
  calc ‖θ z‖ = F z * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) := by
        rw [hFdef, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re) :=
        mul_le_mul_of_nonneg_right hbd hexp.le

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
/- English proof (translation)
Rewrite using `[_root_.GlobalTheory.ThetaPositivity.form_add_self hH]`. Establish `h1 : z ⬝ᵥ Hm.mulVec (star (t • w)) = star t * (z ⬝ᵥ Hm.mulVec (star w))`. Rewrite using `[star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`. Establish `h2 : (t • w) ⬝ᵥ Hm.mulVec (star (t • w)) = (Complex.normSq t : ℂ) * (w ⬝ᵥ Hm.mulVec (star w))`. Rewrite using `[star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, ← mul_assoc, mul_comm (star t), Complex.star_def, Complex.mul_conj]`.

Rewrite using `[h1, h2, Complex.re_ofReal_mul]`.
-/
private lemma re_form_add_smul_of_isHermitian {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) (t : ℂ) :
    ((z + t • w) ⬝ᵥ Hm.mulVec (star (z + t • w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (star t * (z ⬝ᵥ Hm.mulVec (star w))).re
        + Complex.normSq t * (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [_root_.GlobalTheory.ThetaPositivity.form_add_self hH]
  have h1 : z ⬝ᵥ Hm.mulVec (star (t • w)) = star t * (z ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (t • w) ⬝ᵥ Hm.mulVec (star (t • w)) =
      (Complex.normSq t : ℂ) * (w ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm (star t), Complex.star_def, Complex.mul_conj]
  rw [h1, h2, Complex.re_ofReal_mul]

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `hC0 : 0 ≤ C`. Establish `h` using `hC 0`. Establish `hp` using `Real.exp_pos (Real.pi / 2 * ((0 : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star 0)).re)`. Use polynomial arithmetic with `[norm_nonneg (θ 0)]`.

Use `set a := -(w ⬝ᵥ Hm.mulVec (star w)).re with ha`. Establish `ha0 : 0 < a` using `by rw [ha]; linarith`. Use `set A := (z ⬝ᵥ Hm.mulVec (star z)).re with hA`. Use `set B := ‖z ⬝ᵥ Hm.mulVec (star w)‖ with hB`. Use `set f : ℂ → ℂ := fun t => θ (z + t • w) with hfdef`.

Establish `hf : Differentiable ℂ f` using `hθ.comp ((differentiable_const _).add (differentiable_id.smul_const w))`. Establish `hbound : ∀ t, ‖f t‖ ≤ C * Real.exp (Real.pi / 2 * (A + 2 * B * ‖t‖ - a * ‖t‖ ^ 2))`. Introduce `t`. Use `(hC _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises.

Rewrite using `[re_form_add_smul_of_isHermitian hH, Complex.normSq_eq_norm_sq]`. Establish `h : (star t * (z ⬝ᵥ Hm.mulVec (star w))).re ≤ ‖t‖ * B`. Use `(Complex.re_le_norm _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_star]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hlim : Tendsto (fun r : ℝ => C * Real.exp (Real.pi / 2 * (A + 2 * B * r - a * r ^ 2))) atTop (𝓝 0)`. Establish `h2 : Tendsto (fun r : ℝ => (A + 2 * B ^ 2 / a) + (-(a / 2)) * r ^ 2) atTop atBot` using `tendsto_atBot_add_const_left _ _ ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith))`. Establish `h1 : Tendsto (fun r : ℝ => A + 2 * B * r - a * r ^ 2) atTop atBot`. Use `tendsto_atBot_mono (fun r => ?_) h2` and prove the remaining obligations. Establish `key : 2 * B ^ 2 / a + a / 2 * r ^ 2 - 2 * B * r = (a * r - 2 * B) ^ 2 / (2 * a)`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `: 0 ≤ (a * r - 2 * B) ^ 2 / (2 * a)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3` using `Real.tendsto_exp_atBot.comp (h1.const_mul_atBot (by positivity : 0 < Real.pi / 2))`.

Simplify using `using h3.const_mul C`. Establish `hf0 : Tendsto f (cocompact ℂ) (𝓝 0)` using `squeeze_zero_norm hbound (hlim.comp tendsto_norm_cocompact_atTop)`. Use `hf.apply_eq_of_tendsto_cocompact 0 hf0` as an intermediate fact. Simplify `this` using `[hfdef]`.
-/
lemma _root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) {C : ℝ}
    (hC : ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re))
    {w : Fin g → ℂ} (hw : (w ⬝ᵥ Hm.mulVec (star w)).re < 0) : θ = 0 := by
  funext z
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have hp := Real.exp_pos (Real.pi / 2 * ((0 : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star 0)).re)
    nlinarith [norm_nonneg (θ 0)]
  set a := -(w ⬝ᵥ Hm.mulVec (star w)).re with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set A := (z ⬝ᵥ Hm.mulVec (star z)).re with hA
  set B := ‖z ⬝ᵥ Hm.mulVec (star w)‖ with hB
  set f : ℂ → ℂ := fun t => θ (z + t • w) with hfdef
  have hf : Differentiable ℂ f :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const w))
  have hbound : ∀ t, ‖f t‖ ≤ C * Real.exp (Real.pi / 2 * (A + 2 * B * ‖t‖ - a * ‖t‖ ^ 2)) := by
    intro t
    refine (hC _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [re_form_add_smul_of_isHermitian hH, Complex.normSq_eq_norm_sq]
    have h : (star t * (z ⬝ᵥ Hm.mulVec (star w))).re ≤ ‖t‖ * B := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_star]
    nlinarith
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (Real.pi / 2 * (A + 2 * B * r - a * r ^ 2)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => (A + 2 * B ^ 2 / a) + (-(a / 2)) * r ^ 2) atTop atBot :=
      tendsto_atBot_add_const_left _ _
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith))
    have h1 : Tendsto (fun r : ℝ => A + 2 * B * r - a * r ^ 2) atTop atBot := by
      refine tendsto_atBot_mono (fun r => ?_) h2
      have key : 2 * B ^ 2 / a + a / 2 * r ^ 2 - 2 * B * r = (a * r - 2 * B) ^ 2 / (2 * a) := by
        field_simp
        ring
      have : 0 ≤ (a * r - 2 * B) ^ 2 / (2 * a) := by positivity
      nlinarith
    have h3 := Real.tendsto_exp_atBot.comp (h1.const_mul_atBot (by positivity : 0 < Real.pi / 2))
    simpa using h3.const_mul C
  have hf0 : Tendsto f (cocompact ℂ) (𝓝 0) :=
    squeeze_zero_norm hbound (hlim.comp tendsto_norm_cocompact_atTop)
  have := hf.apply_eq_of_tendsto_cocompact 0 hf0
  simpa [hfdef] using this

/- English proof (translation)
Use `ZLattice.module_free ℝ Λ` as an intermediate fact. Use `ZLattice.module_finite ℝ Λ` as an intermediate fact. Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `B` to `b.ofZLatticeBasis ℝ Λ`. Establish `hdet : (LinearMap.toMatrix₂ b b Ef).det ≠ 0` using `(LinearMap.separatingLeft_iff_det_ne_zero b).mp (LinearMap.separatingLeft_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hinj))`.

Set `M` to `(LinearMap.toMatrix₂ b b Ef).map (Int.castRingHom ℝ)`. Establish `hM : M.det ≠ 0`. Establish `h` using `(Int.castRingHom ℝ).map_det (LinearMap.toMatrix₂ b b Ef)`. Rewrite `h` using `[RingHom.mapMatrix_apply]`. Rewrite using `[← h]`.

Simplify using `using hdet`. Establish `hsum : ∑ j, B.repr w j • (b j : Fin g → ℂ) = w` using `by conv_rhs => rw [← B.sum_repr w]`. Simplify using `[B]`. Establish `hv : M.mulVec (B.repr w) = 0`. Use function extensionality and compare the values at `i`.

Establish `h : ((b i : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star w)).im = 0` using `by simp [hw]`. Rewrite `h` using `[← hsum, star_sum, mulVec_sum, dotProduct_sum, im_sum]`. Rewrite using `[Pi.zero_apply, ← h]`. Simplify using `only [mulVec, M]`. Express the relevant statement in the definitionally equal form `∑ j, _ = _`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[star_smul, star_trivial]`. Express the relevant statement in the definitionally equal form `_ = ((b i : Fin g → ℂ) ⬝ᵥ Hm.mulVec (B.repr w j • star (b j : Fin g → ℂ))).im`. Rewrite using `[mulVec_smul, dotProduct_smul, smul_im, ← hE]`. Simplify using `[mul_comm]`.

Establish `h0` using `Matrix.eq_zero_of_mulVec_eq_zero hM hv`. Rewrite using `[← hsum, h0]`. Simplify using the standard rewrite rules.
-/
lemma eq_zero_of_mulVec_eq_zero (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] {Hm : Matrix (Fin g) (Fin g) ℂ} (Ef : LinearMap.BilinForm ℤ Λ)
    (hE : ∀ l m : Λ, (Ef l m : ℝ) =
      ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)
    (hinj : Function.Injective Ef) {w : Fin g → ℂ} (hw : Hm.mulVec (star w) = 0) : w = 0 := by
  classical
  have := ZLattice.module_free ℝ Λ
  have := ZLattice.module_finite ℝ Λ
  let b := Module.Free.chooseBasis ℤ Λ
  let B := b.ofZLatticeBasis ℝ Λ
  have hdet : (LinearMap.toMatrix₂ b b Ef).det ≠ 0 :=
    (LinearMap.separatingLeft_iff_det_ne_zero b).mp
      (LinearMap.separatingLeft_iff_ker_eq_bot.mpr (LinearMap.ker_eq_bot.mpr hinj))
  let M := (LinearMap.toMatrix₂ b b Ef).map (Int.castRingHom ℝ)
  have hM : M.det ≠ 0 := by
    have h := (Int.castRingHom ℝ).map_det (LinearMap.toMatrix₂ b b Ef)
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    simpa using hdet
  have hsum : ∑ j, B.repr w j • (b j : Fin g → ℂ) = w := by
    conv_rhs => rw [← B.sum_repr w]
    simp [B]
  have hv : M.mulVec (B.repr w) = 0 := by
    funext i
    have h : ((b i : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star w)).im = 0 := by simp [hw]
    rw [← hsum, star_sum, mulVec_sum, dotProduct_sum, im_sum] at h
    rw [Pi.zero_apply, ← h]
    simp only [mulVec, M]
    change ∑ j, _ = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_smul, star_trivial]
    change _ = ((b i : Fin g → ℂ) ⬝ᵥ Hm.mulVec (B.repr w j • star (b j : Fin g → ℂ))).im
    rw [mulVec_smul, dotProduct_smul, smul_im, ← hE]
    simp [mul_comm]
  have h0 := Matrix.eq_zero_of_mulVec_eq_zero hM hv
  rw [← hsum, h0]
  simp

open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in

/- English proof (translation)
Introduce `g Λ hdisc hspan Hm χ Ef θ hH hχ hE hinj hθ hθ0 htr z hz`. Use `haveI : IsZLattice ℝ Λ := ⟨hspan⟩`. Establish `hpsd : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re`. Introduce `w`. Assume the negation of the conclusion as `hw`.

Use `push_neg at hw`. Take `⟨C, hC⟩` from `_root_.GlobalTheory.ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr`. Conclude with `hθ0 (_root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg hH hθ hC hw)`. Use `lt_of_le_of_ne (hpsd z) (fun hz0 => hz ?_)` and prove the remaining obligations. Establish `him : ∀ v : Fin g → ℂ, (z ⬝ᵥ Hm.mulVec (star v)).im = 0`.

Introduce `v`. Establish `key : ∀ s : ℝ, 0 ≤ 2 * s * (z ⬝ᵥ Hm.mulVec (star v)).im + s ^ 2 * (v ⬝ᵥ Hm.mulVec (star v)).re`. Introduce `s`. Establish `h` using `hpsd (z + ((s : ℂ) * Complex.I) • v)`. Rewrite `h` using `[re_form_add_smul_of_isHermitian hH, ← hz0]`.

Establish `e1 : (star ((s : ℂ) * Complex.I) * (z ⬝ᵥ Hm.mulVec (star v))).re = s * (z ⬝ᵥ Hm.mulVec (star v)).im`. Simplify using `[Complex.mul_re]`. Establish `e2 : Complex.normSq ((s : ℂ) * Complex.I) = s ^ 2` using `by simp [sq]`. Rewrite `h` using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set c := (z ⬝ᵥ Hm.mulVec (star v)).im`. Use `set d := (v ⬝ᵥ Hm.mulVec (star v)).re`. Establish `hd1 : 0 < d + 1` using `by linarith [hpsd v]`. Establish `h' : 0 ≤ -(c ^ 2 * (d + 2)) / (d + 1) ^ 2`. Establish `e : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Combine the linear relations using `[key (-c / (d + 1))]`. Rewrite `h'` using `[neg_div, neg_nonneg, div_le_iff₀ (by positivity), zero_mul]`. Establish `hc2 : c ^ 2 = 0` using `by nlinarith [sq_nonneg c, hpsd v]`.

Conclude with `(pow_eq_zero_iff two_ne_zero).mp hc2`. Set `b` to `Module.Free.chooseBasis ℤ Λ`. Set `bR` to `Module.Basis.ofZLatticeBasis ℝ Λ b`. Set `M : Matrix _ _ ℤ` to `Matrix.of fun i j => Ef (b i) (b j)`. Establish `hdet : M.det ≠ 0`.

Introduce `h0`. Take `⟨c, hc0, hc⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr h0`. Apply `hc0` to reduce the goal to its premises. Establish `hl : Ef (b.equivFun.symm c) = 0`. Use `b.ext fun j => ?_` and prove the remaining obligations.

Use `congrFun hc j` as an intermediate fact. Simplify `this` using `[Module.Basis.equivFun_symm_apply, map_sum, Matrix.vecMul, dotProduct, M]`. Use `hinj (hl.trans (map_zero Ef).symm)` as an intermediate fact. Establish `h2` using `congrArg b.equivFun this`. Rewrite `h2` using `[LinearEquiv.apply_symm_apply, map_zero]`. Then use the resulting hypothesis.

Establish `hr : (fun i => bR.repr z i) ᵥ* M.map (Int.cast : ℤ → ℝ) = 0`. Use function extensionality and compare the values at `j`. Establish `h` using `him (b j : Fin g → ℂ)`. Rewrite `h` using `[← bR.sum_repr z]`. Simplify using `only [sum_dotProduct, smul_dotProduct, Complex.im_sum, Complex.smul_im, Module.Basis.ofZLatticeBasis_apply, bR, ← hE] at h`.

Simplify `h` using `[Matrix.vecMul, dotProduct, M]`. Establish `hdetR : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0`. Establish `e : (M.map (Int.castRingHom ℝ)).det = Int.castRingHom ℝ M.det` using `(RingHom.map_det _ _).symm`. Simplify using `using e ▸ (Int.cast_ne_zero.mpr hdet)`. Establish `hr0 : (fun i => bR.repr z i) = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hdetR (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hr⟩)`. Establish `hz' : bR.repr z = 0`. Use extensionality with `i`. Conclude with `congrFun hr0 i`.

Simplify using `using hz'`.
-/
theorem _root_.GlobalTheory.ThetaPositivity.re_form_pos_of_theta_ne_zero :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (Ef : LinearMap.BilinForm ℤ Λ)
        (θ : (Fin g → ℂ) → ℂ), Hm.IsHermitian → (∀ l, ‖χ l‖ = 1) →
        (∀ l m : Λ, (Ef l m : ℝ) = ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im) →
        Function.Injective Ef → Differentiable ℂ θ → θ ≠ 0 →
        (∀ (l : Λ) z, θ (z + l) =
          (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) +
            Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) →
        ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re := by
  intro g Λ hdisc hspan Hm χ Ef θ hH hχ hE hinj hθ hθ0 htr z hz
  classical
  haveI : IsZLattice ℝ Λ := ⟨hspan⟩
  have hpsd : ∀ w : Fin g → ℂ, 0 ≤ (w ⬝ᵥ Hm.mulVec (star w)).re := by
    intro w
    by_contra hw
    push_neg at hw
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.ThetaPositivity.exists_norm_le Λ hH χ hχ hθ.continuous htr
    exact hθ0 (_root_.GlobalTheory.ThetaPositivity.eq_zero_of_neg hH hθ hC hw)
  refine lt_of_le_of_ne (hpsd z) (fun hz0 => hz ?_)
  have him : ∀ v : Fin g → ℂ, (z ⬝ᵥ Hm.mulVec (star v)).im = 0 := by
    intro v
    have key : ∀ s : ℝ, 0 ≤ 2 * s * (z ⬝ᵥ Hm.mulVec (star v)).im
        + s ^ 2 * (v ⬝ᵥ Hm.mulVec (star v)).re := by
      intro s
      have h := hpsd (z + ((s : ℂ) * Complex.I) • v)
      rw [re_form_add_smul_of_isHermitian hH, ← hz0] at h
      have e1 : (star ((s : ℂ) * Complex.I) * (z ⬝ᵥ Hm.mulVec (star v))).re =
          s * (z ⬝ᵥ Hm.mulVec (star v)).im := by
        simp [Complex.mul_re]
      have e2 : Complex.normSq ((s : ℂ) * Complex.I) = s ^ 2 := by simp [sq]
      rw [e1, e2] at h
      linarith
    set c := (z ⬝ᵥ Hm.mulVec (star v)).im
    set d := (v ⬝ᵥ Hm.mulVec (star v)).re
    have hd1 : 0 < d + 1 := by linarith [hpsd v]
    have h' : 0 ≤ -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
      have e : 2 * (-c / (d + 1)) * c + (-c / (d + 1)) ^ 2 * d = -(c ^ 2 * (d + 2)) / (d + 1) ^ 2 := by
        field_simp
        ring
      linarith [key (-c / (d + 1))]
    rw [neg_div, neg_nonneg, div_le_iff₀ (by positivity), zero_mul] at h'
    have hc2 : c ^ 2 = 0 := by nlinarith [sq_nonneg c, hpsd v]
    exact (pow_eq_zero_iff two_ne_zero).mp hc2
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  let M : Matrix _ _ ℤ := Matrix.of fun i j => Ef (b i) (b j)
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hc0
    have hl : Ef (b.equivFun.symm c) = 0 := by
      refine b.ext fun j => ?_
      have := congrFun hc j
      simpa [Module.Basis.equivFun_symm_apply, map_sum, Matrix.vecMul, dotProduct, M] using this
    have := hinj (hl.trans (map_zero Ef).symm)
    have h2 := congrArg b.equivFun this
    rwa [LinearEquiv.apply_symm_apply, map_zero] at h2
  have hr : (fun i => bR.repr z i) ᵥ* M.map (Int.cast : ℤ → ℝ) = 0 := by
    funext j
    have h := him (b j : Fin g → ℂ)
    rw [← bR.sum_repr z] at h
    simp only [sum_dotProduct, smul_dotProduct, Complex.im_sum, Complex.smul_im,
      Module.Basis.ofZLatticeBasis_apply, bR, ← hE] at h
    simpa [Matrix.vecMul, dotProduct, M] using h
  have hdetR : (M.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    have e : (M.map (Int.castRingHom ℝ)).det = Int.castRingHom ℝ M.det := (RingHom.map_det _ _).symm
    simpa using e ▸ (Int.cast_ne_zero.mpr hdet)
  have hr0 : (fun i => bR.repr z i) = 0 := by
    by_contra hne
    exact hdetR (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hr⟩)
  have hz' : bR.repr z = 0 := by
    ext i
    exact congrFun hr0 i
  simpa using hz'

end GlobalTheory.ThetaPositivity
