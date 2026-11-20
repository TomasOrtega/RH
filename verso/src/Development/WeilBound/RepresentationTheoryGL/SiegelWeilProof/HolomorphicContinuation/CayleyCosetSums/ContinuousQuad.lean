import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolTBase

noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

def imM (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (-(Complex.I / 2)) • (Z - Zᴴ)

/- English proof (translation)
Apply the tactic sequence `apply Complex.ext <;> simp <;> norm_num`.
-/
theorem star_c : star (-(Complex.I / 2)) = -(-(Complex.I / 2)) := by
  apply Complex.ext <;> simp <;> norm_num

/- English proof (translation)
Unfold `imM`. Rewrite using `[IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, star_c, neg_smul, ← smul_neg, neg_sub]`.
-/
theorem imM_herm (Z : Matrix (Fin n) (Fin n) ℂ) : (imM Z).IsHermitian := by
  unfold imM
  rw [IsHermitian, conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, star_c, neg_smul,
    ← smul_neg, neg_sub]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_dom_iff (Z : Fin n → Fin n → ℂ) : Z ∈ Dom n ↔ (imM (Matrix.of Z)).PosDef := Iff.rfl

/- English proof (translation)
Rewrite using `[posDef_iff_dotProduct_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩ x hx`. Conclude with `(Complex.lt_def.1 (h hx)).1`. Introduce `h`.

Use `⟨hM, fun x hx => ?_⟩` and prove the remaining obligations. Establish `him : (star x ⬝ᵥ (M *ᵥ x)).im = 0` using `hM.im_star_dotProduct_mulVec_self x`. Conclude with `Complex.lt_def.2 ⟨h x hx, by simpa using him.symm⟩`.
-/
theorem posdef_iff_re {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsHermitian) :
    M.PosDef ↔ ∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩ x hx
    exact (Complex.lt_def.1 (h hx)).1
  · intro h
    refine ⟨hM, fun x hx => ?_⟩
    have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := hM.im_star_dotProduct_mulVec_self x
    exact Complex.lt_def.2 ⟨h x hx, by simpa using him.symm⟩

/- English proof (translation)
Rewrite using `[star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]`. Simplify using `only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_smul_quad (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (c : ℝ) :
    (star ((c : ℂ) • x) ⬝ᵥ (M *ᵥ ((c : ℂ) • x))).re = c ^ 2 * (star x ⬝ᵥ (M *ᵥ x)).re := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Establish `h1 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ)` using `continuous_fst`. Establish `h2 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => imM (Matrix.of p.1)`. Unfold `imM`. Conclude with `(h1.sub h1.matrix_conjTranspose).const_smul (-(Complex.I / 2) : ℂ)`. Conclude with `Complex.continuous_re.comp (continuous_snd.star.dotProduct (h2.matrix_mulVec continuous_snd))`.
-/
theorem continuous_quad : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) =>
    (star p.2 ⬝ᵥ (imM (Matrix.of p.1) *ᵥ p.2)).re := by
  have h1 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_fst
  have h2 : Continuous fun p : (Fin n → Fin n → ℂ) × (Fin n → ℂ) => imM (Matrix.of p.1) := by
    unfold imM
    exact (h1.sub h1.matrix_conjTranspose).const_smul (-(Complex.I / 2) : ℂ)
  exact Complex.continuous_re.comp (continuous_snd.star.dotProduct (h2.matrix_mulVec continuous_snd))

/- English proof (translation)
Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `Z hZ`. Establish `hsph : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1)` using `isCompact_sphere 0 1`. Establish `key : ∀ᶠ W in 𝓝 Z, ∀ y ∈ Metric.sphere (0 : Fin n → ℂ) 1, 0 < (star y ⬝ᵥ (imM (Matrix.of W) *ᵥ y)).re`. Apply `hsph.eventually_forall_of_forall_eventually` to reduce the goal to its premises.

Introduce `y hy`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hy`. Establish `hpos : 0 < (star y ⬝ᵥ (imM (Matrix.of Z) *ᵥ y)).re` using `(posdef_iff_re (imM_herm _)).1 ((mem_dom_iff Z).1 hZ) y hy0`.

Conclude with `(continuous_quad.tendsto (Z, y)).eventually (lt_mem_nhds hpos)`. Use `filter_upwards [key] with W hW`. Rewrite using `[mem_dom_iff, posdef_iff_re (imM_herm _)]`. Introduce `x hx`. Establish `hn : 0 < ‖x‖` using `norm_pos_iff.2 hx`.

Establish `hy : (((‖x‖⁻¹ : ℝ) : ℂ) • x) ∈ Metric.sphere (0 : Fin n → ℂ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul]`. Simplify using `[hn.ne']`. Establish `hxe : x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x)`. Rewrite using `[smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]`.

Rewrite using `[hxe, re_smul_quad]`. Conclude with `mul_pos (pow_pos hn 2) (hW _ hy)`.
-/
theorem isOpen_dom' : IsOpen (Dom n) := by
  rw [isOpen_iff_mem_nhds]
  intro Z hZ
  have hsph : IsCompact (Metric.sphere (0 : Fin n → ℂ) 1) := isCompact_sphere 0 1
  have key : ∀ᶠ W in 𝓝 Z, ∀ y ∈ Metric.sphere (0 : Fin n → ℂ) 1,
      0 < (star y ⬝ᵥ (imM (Matrix.of W) *ᵥ y)).re := by
    apply hsph.eventually_forall_of_forall_eventually
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy
    have hpos : 0 < (star y ⬝ᵥ (imM (Matrix.of Z) *ᵥ y)).re :=
      (posdef_iff_re (imM_herm _)).1 ((mem_dom_iff Z).1 hZ) y hy0
    exact (continuous_quad.tendsto (Z, y)).eventually (lt_mem_nhds hpos)
  filter_upwards [key] with W hW
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)]
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hy : (((‖x‖⁻¹ : ℝ) : ℂ) • x) ∈ Metric.sphere (0 : Fin n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul]
    simp [hn.ne']
  have hxe : x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hn.ne', Complex.ofReal_one, one_smul]
  rw [hxe, re_smul_quad]
  exact mul_pos (pow_pos hn 2) (hW _ hy)

/- English proof (translation)
Introduce `Z hZ W hW a b ha hb hab`. Rewrite `hZ`, `hW`, the goal using `[mem_dom_iff, posdef_iff_re (imM_herm _)]`. Introduce `x hx`. Establish `hm : imM (Matrix.of (a • Z + b • W)) = (a : ℂ) • imM (Matrix.of Z) + (b : ℂ) • imM (Matrix.of W)`. Use extensionality with `i j`.

Simplify using `[imM, Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hq : (star x ⬝ᵥ (imM (Matrix.of (a • Z + b • W)) *ᵥ x)).re = a * (star x ⬝ᵥ (imM (Matrix.of Z) *ᵥ x)).re + b * (star x ⬝ᵥ (imM (Matrix.of W) *ᵥ x)).re`. Rewrite using `[hm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`. Rewrite using `[hq]`.

Establish `hp` using `hZ x hx`. Establish `hq'` using `hW x hx`. Break down `ha.eq_or_lt with rfl | ha'` into its components or cases. Establish `hb1 : b = 1` using `by linarith`. Substitute `hb1` using the available equality.

Simplify using `using hq'`. Combine the linear relations using `[mul_pos ha' hp, mul_nonneg hb hq'.le]`.
-/
theorem convex_dom' : Convex ℝ (Dom n) := by
  intro Z hZ W hW a b ha hb hab
  rw [mem_dom_iff, posdef_iff_re (imM_herm _)] at hZ hW ⊢
  intro x hx
  have hm : imM (Matrix.of (a • Z + b • W)) = (a : ℂ) • imM (Matrix.of Z) + (b : ℂ) • imM (Matrix.of W) := by
    ext i j
    simp [imM, Complex.real_smul]
    ring
  have hq : (star x ⬝ᵥ (imM (Matrix.of (a • Z + b • W)) *ᵥ x)).re
      = a * (star x ⬝ᵥ (imM (Matrix.of Z) *ᵥ x)).re + b * (star x ⬝ᵥ (imM (Matrix.of W) *ᵥ x)).re := by
    rw [hm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, dotProduct_smul, Complex.add_re, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul,
      Complex.re_ofReal_mul]
  rw [hq]
  have hp := hZ x hx
  have hq' := hW x hx
  rcases ha.eq_or_lt with rfl | ha'
  · have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hq'
  · linarith [mul_pos ha' hp, mul_nonneg hb hq'.le]

/- English proof (translation)
Simplify using `only [conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Take the linear combination `(norm := skip) h1 + h4 + (-Complex.I) • h2 + Complex.I • h3`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring`.
-/
private theorem conjTranspose_I_smul_add_sub_eq_neg_two_I (A B C D : Matrix (Fin n) (Fin n) ℂ)
    (h1 : -(Cᴴ * A) + Aᴴ * C = 0) (h2 : -(Cᴴ * B) + Aᴴ * D = 1)
    (h3 : -(Dᴴ * A) + Bᴴ * C = -1) (h4 : -(Dᴴ * B) + Bᴴ * D = 0) :
    (Complex.I • A + B)ᴴ * (Complex.I • C + D) - (Complex.I • C + D)ᴴ * (Complex.I • A + B)
      = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [conjTranspose_add, conjTranspose_smul, Complex.star_def, Complex.conj_I, Matrix.add_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  linear_combination (norm := skip) h1 + h4 + (-Complex.I) • h2 + Complex.I • h3
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/- English proof (translation)
Establish `hker : ∀ v, U *ᵥ v = 0 → v = 0`. Introduce `v hv`. Establish `e : star v ⬝ᵥ ((Xᴴ * U - Uᴴ * X) *ᵥ v) = star v ⬝ᵥ (((-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v)`. Rewrite using `[hk]`. Rewrite `e` using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero, zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec, hv, star_zero, zero_dotProduct, neg_zero, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]`.

Establish `h2I : -(2 * Complex.I) ≠ 0` using `by simp`. Establish `hvv : star v ⬝ᵥ v = 0` using `(mul_eq_zero.1 e.symm).resolve_left h2I`. Conclude with `dotProduct_star_self_eq_zero.1 hvv`. Establish `hinj : Function.Injective U.mulVec`. Introduce `v w hvw`.

Establish `h0 : U *ᵥ (v - w) = 0`. Rewrite using `[Matrix.mulVec_sub, sub_eq_zero]`. Conclude with `hvw`. Conclude with `sub_eq_zero.1 (hker _ h0)`. Establish `hU : IsUnit U` using `mulVec_injective_iff_isUnit.1 hinj`.

Establish `hUU : U * U⁻¹ = 1` using `Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)`. Establish `hc : (U⁻¹)ᴴ * Uᴴ = 1`. Rewrite using `[← conjTranspose_mul, hUU, conjTranspose_one]`. Establish `e1 : X * U⁻¹ - (X * U⁻¹)ᴴ = (U⁻¹)ᴴ * (Uᴴ * X - Xᴴ * U) * U⁻¹`. Rewrite using `[conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Uᴴ X, hc, Matrix.one_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Xᴴ U, Matrix.mul_assoc _ U U⁻¹, hUU, Matrix.mul_one]`.

Establish `e2 : Uᴴ * X - Xᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← neg_sub, hk, neg_smul, neg_neg]`. Establish `e3 : imM (X * U⁻¹) = (U⁻¹)ᴴ * 1 * U⁻¹`. Unfold `imM`. Rewrite using `[e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]`.

Establish `hs : -(Complex.I / 2) * (2 * Complex.I) = 1`. Put the polynomial expressions in normal form. Simplify using `[Complex.I_sq]`. Rewrite using `[hs, one_smul]`. Establish `hinv : Function.Injective (U⁻¹).mulVec`.

Introduce `v w hvw`. Use `congrArg (fun z => U *ᵥ z) hvw` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hUU]`. Rewrite using `[e3]`. Conclude with `Matrix.PosDef.one.conjTranspose_mul_mul_same hinv`.
-/
private theorem posDef_imM_mul_inv_of_skew_relation (X U : Matrix (Fin n) (Fin n) ℂ)
    (hk : Xᴴ * U - Uᴴ * X = (-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (imM (X * U⁻¹)).PosDef := by
  have hker : ∀ v, U *ᵥ v = 0 → v = 0 := by
    intro v hv
    have e : star v ⬝ᵥ ((Xᴴ * U - Uᴴ * X) *ᵥ v)
        = star v ⬝ᵥ (((-(2 * Complex.I)) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ v) := by
      rw [hk]
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero,
      zero_sub, dotProduct_neg, dotProduct_mulVec, ← star_mulVec, hv, star_zero, zero_dotProduct,
      neg_zero, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at e
    have h2I : -(2 * Complex.I) ≠ 0 := by simp
    have hvv : star v ⬝ᵥ v = 0 := (mul_eq_zero.1 e.symm).resolve_left h2I
    exact dotProduct_star_self_eq_zero.1 hvv
  have hinj : Function.Injective U.mulVec := by
    intro v w hvw
    have h0 : U *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact hvw
    exact sub_eq_zero.1 (hker _ h0)
  have hU : IsUnit U := mulVec_injective_iff_isUnit.1 hinj
  have hUU : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U ((Matrix.isUnit_iff_isUnit_det U).1 hU)
  have hc : (U⁻¹)ᴴ * Uᴴ = 1 := by
    rw [← conjTranspose_mul, hUU, conjTranspose_one]
  have e1 : X * U⁻¹ - (X * U⁻¹)ᴴ = (U⁻¹)ᴴ * (Uᴴ * X - Xᴴ * U) * U⁻¹ := by
    rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Uᴴ X, hc,
      Matrix.one_mul, ← Matrix.mul_assoc (U⁻¹)ᴴ Xᴴ U, Matrix.mul_assoc _ U U⁻¹, hUU, Matrix.mul_one]
  have e2 : Uᴴ * X - Xᴴ * U = (2 * Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← neg_sub, hk, neg_smul, neg_neg]
  have e3 : imM (X * U⁻¹) = (U⁻¹)ᴴ * 1 * U⁻¹ := by
    unfold imM
    rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    have hs : -(Complex.I / 2) * (2 * Complex.I) = 1 := by
      ring_nf
      simp [Complex.I_sq]
    rw [hs, one_smul]
  have hinv : Function.Injective (U⁻¹).mulVec := by
    intro v w hvw
    have := congrArg (fun z => U *ᵥ z) hvw
    simpa [Matrix.mulVec_mulVec, hUU] using this
  rw [e3]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinv

/- English proof (translation)
Establish `hM : (mR y)ᴴ * JJ n * mR y = JJ n` using `y.2`. Establish `hblk : mR y = fromBlocks (toBlocks₁₁ (mR y)) (toBlocks₁₂ (mR y)) (toBlocks₂₁ (mR y)) (toBlocks₂₂ (mR y))` using `(fromBlocks_toBlocks _).symm`. Rewrite `hM` using `[hblk, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at hM`. Take `⟨h1, h2, h3, h4⟩` from `Matrix.fromBlocks_inj.1 hM`.

Establish `hk` using `conjTranspose_I_smul_add_sub_eq_neg_two_I _ _ _ _ h1 h2 h3 h4`. Use `(mem_dom_iff (n := n) (zOf y)).2 ?_` and prove the remaining obligations. Conclude with `posDef_imM_mul_inv_of_skew_relation _ _ hk`.
-/
theorem zOf_mem' (y : GR n) : zOf y ∈ Dom n := by
  have hM : (mR y)ᴴ * JJ n * mR y = JJ n := y.2
  have hblk : mR y = fromBlocks (toBlocks₁₁ (mR y)) (toBlocks₁₂ (mR y)) (toBlocks₂₁ (mR y))
      (toBlocks₂₂ (mR y)) :=
    (fromBlocks_toBlocks _).symm
  rw [hblk, JJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at hM
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at hM
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 hM
  have hk := conjTranspose_I_smul_add_sub_eq_neg_two_I _ _ _ _ h1 h2 h3 h4
  refine (mem_dom_iff (n := n) (zOf y)).2 ?_
  exact posDef_imM_mul_inv_of_skew_relation _ _ hk

/- English proof (translation)
Establish `h : imM (Matrix.of (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)) = imM (Matrix.of W)`. Express the relevant statement in the definitionally equal form `imM (-(Matrix.of W)ᴴ) = imM (Matrix.of W)`. Use extensionality with `i j`. Simplify using `[imM]`. Expand and normalize the polynomial expressions, which then agree.

Use `(mem_dom_iff (n := n) (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)).2 ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `(mem_dom_iff W).1 hW`.
-/
theorem neg_conj_mem' {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) :
    (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ) ∈ Dom n := by
  have h : imM (Matrix.of (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)) = imM (Matrix.of W) := by
    change imM (-(Matrix.of W)ᴴ) = imM (Matrix.of W)
    ext i j
    simp [imM]
    ring
  refine (mem_dom_iff (n := n) (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ)).2 ?_
  rw [h]
  exact (mem_dom_iff W).1 hW

end PositivityTheory.Rg.Sw.HSt.HolTPf
