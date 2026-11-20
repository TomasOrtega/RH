import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SymplecticSiegelActionMemUpperHalfSpaceAndCocyclStatement
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real

namespace GlobalTheory.SW

/- English proof (translation)
Establish `h : (τ.map fun z => (z.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im)`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[h, ← RingHom.map_det]`. Conclude with `(hτ.2.det_pos.ne'.isUnit).map _`.
-/
theorem isUnit_det_im_of_mem_siegel {ι : Type} [Fintype ι] [DecidableEq ι] {τ : Matrix ι ι ℂ}
    (hτ : τ ∈ Siegel ι) : IsUnit (τ.map fun z => (z.im : ℂ)).det := by
  have h : (τ.map fun z => (z.im : ℂ)) = Complex.ofRealHom.mapMatrix (τ.map Complex.im) := by
    ext i j; simp
  rw [h, ← RingHom.map_det]
  exact (hτ.2.det_pos.ne'.isUnit).map _

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.SW.qm]`.
-/
private lemma qm_add' {α β : Type} (M N : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (M + N) = _root_.GlobalTheory.SW.qm M + _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.SW.qm]`.
-/
private lemma qm_neg' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm (-M) = -_root_.GlobalTheory.SW.qm M := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.SW.qm, Matrix.mul_apply]`.
-/
private lemma qm_mul_siegel_theta_transformation {α β γ : Type} [Fintype β] (M : Matrix α β ℚ) (N : Matrix β γ ℚ) :
    _root_.GlobalTheory.SW.qm (M * N) = _root_.GlobalTheory.SW.qm M * _root_.GlobalTheory.SW.qm N := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, Matrix.mul_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma qm_transpose' {α β : Type} (M : Matrix α β ℚ) :
    _root_.GlobalTheory.SW.qm Mᵀ = (_root_.GlobalTheory.SW.qm M)ᵀ := rfl

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.SW.qm]`.
-/
private lemma qm_zero' {α β : Type} : _root_.GlobalTheory.SW.qm (0 : Matrix α β ℚ) = 0 := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [_root_.GlobalTheory.SW.qm, one_apply, h]`.
-/
private lemma qm_one' : _root_.GlobalTheory.SW.qm (1 : Matrix ι ι ℚ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [_root_.GlobalTheory.SW.qm, one_apply, h]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Establish `h` using `hτ.apply i j`. Simplify using `only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, h]`. Rewrite using `[show star (τ i j) = conj (τ i j) from rfl, Complex.sub_conj]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma sub_conjTranspose_of_isSymm (τ : Matrix ι ι ℂ) (hτ : τ.IsSymm) :
    τ - τᴴ = (2 * I) • τ.map fun z => (z.im : ℂ) := by
  ext i j
  have h := hτ.apply i j
  simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul, h]
  rw [show star (τ i j) = conj (τ i j) from rfl, Complex.sub_conj]
  push_cast
  ring

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `[_root_.GlobalTheory.SW.qm, conjTranspose_apply]`.
-/
private lemma qm_conjTranspose_eq_transpose {α β : Type} (M : Matrix α β ℚ) :
    (_root_.GlobalTheory.SW.qm M)ᴴ = (_root_.GlobalTheory.SW.qm M)ᵀ := by
  ext i j
  simp [_root_.GlobalTheory.SW.qm, conjTranspose_apply]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Simplify using `only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Simplify using `[Complex.mul_re, Complex.mul_im]`.
-/
private lemma re_star_dotProduct_ofReal_mulVec (Y : Matrix ι ι ℝ) (v : ι → ℂ) :
    (star v ⬝ᵥ (Y.map (fun t => (t : ℂ)) *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (Y *ᵥ fun i => (v i).re) + (fun i => (v i).im) ⬝ᵥ (Y *ᵥ fun i => (v i).im) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]

open Matrix Complex in
open scoped ComplexConjugate Real in
variable {ι : Type} [Fintype ι] [DecidableEq ι] in
/- English proof (translation)
Rewrite using `[mulVec_transpose, dotProduct_comm, dotProduct_mulVec]`.
-/
private lemma dotProduct_transpose_mulVec_self (N : Matrix ι ι ℂ) (ζ : ι → ℂ) :
    ζ ⬝ᵥ (Nᵀ *ᵥ ζ) = ζ ⬝ᵥ (N *ᵥ ζ) := by
  rw [mulVec_transpose, dotProduct_comm, dotProduct_mulVec]

open Matrix Complex in
open scoped ComplexConjugate Real in

/- English proof (translation)
Introduce `ι _ _ σ hσ τ hτ ζ`. Take `⟨hsym, hpos⟩` from `hτ`. Establish `h2` using `SymplecticGroup.mem_iff'.mp hσ`. Rewrite `h2` using `[← fromBlocks_toBlocks σ]`. Simplify using `[Matrix.J, fromBlocks_transpose, fromBlocks_multiply] at h2`.

Take `⟨r1, r2, r3, r4⟩` from `h2`. Use `replace r1 := congrArg _root_.GlobalTheory.SW.qm r1`. Use `replace r2 := congrArg _root_.GlobalTheory.SW.qm r2`. Use `replace r3 := congrArg _root_.GlobalTheory.SW.qm r3`. Use `replace r4 := congrArg _root_.GlobalTheory.SW.qm r4`.

Simplify using `only [qm_add', qm_neg', qm_mul_siegel_theta_transformation, qm_transpose', qm_zero', qm_one'] at r1 r2 r3 r4`. Use `set A := _root_.GlobalTheory.SW.qm σ.toBlocks₁₁ with hA`. Use `set B := _root_.GlobalTheory.SW.qm σ.toBlocks₁₂ with hB`. Use `set C := _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ with hC`. Use `set D := _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ with hD`.

Use `set J := _root_.GlobalTheory.SW.spDen σ τ with hJdef`. Establish `hJ : J = C * τ + D` using `rfl`. Use `set M := A * τ + B with hM`. Establish `hact : _root_.GlobalTheory.SW.spAct σ τ = M * J⁻¹` using `rfl`. Use `set Y := τ.map fun z => (z.im : ℂ) with hYdef`.

Establish `hY : τ - τᴴ = (2 * I) • Y` using `sub_conjTranspose_of_isSymm τ hsym`. Establish `hτt : τᵀ = τ` using `hsym`. Establish `hCh : Cᴴ = Cᵀ` using `qm_conjTranspose_eq_transpose _`. Establish `hDh : Dᴴ = Dᵀ` using `qm_conjTranspose_eq_transpose _`. Establish `hAh : Aᴴ = Aᵀ` using `qm_conjTranspose_eq_transpose _`.

Establish `hBh : Bᴴ = Bᵀ` using `qm_conjTranspose_eq_transpose _`. Establish `hI1 : Jᴴ * M - Mᴴ * J = τ - τᴴ`. Rewrite using `[hJ, hM, conjTranspose_add, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hCh, hDh, hAh, hBh]`. Establish `hE : (τᴴ * Cᵀ + Dᵀ) * (A * τ + B) - (τᴴ * Aᵀ + Bᵀ) * (C * τ + D) = τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D)) + (Dᵀ * A + -(Bᵀ * C)) * τ + (Dᵀ * B + -(Bᵀ * D))` using `by noncomm_ring`. Rewrite using `[hE, r1, r2, r3, r4]`.

Use `noncomm_ring`. Establish `hI2 : Mᵀ * J = Jᵀ * M`. Rewrite using `[hJ, hM, transpose_add, transpose_add, transpose_mul, transpose_mul, hτt]`. Establish `hE : (τ * Aᵀ + Bᵀ) * (C * τ + D) - (τ * Cᵀ + Dᵀ) * (A * τ + B) = -(τ * (Cᵀ * A + -(Aᵀ * C)) * τ) - τ * (Cᵀ * B + -(Aᵀ * D)) - (Dᵀ * A + -(Bᵀ * C)) * τ - (Dᵀ * B + -(Bᵀ * D))` using `by noncomm_ring`. Rewrite `hE` using `[r1, r2, r3, r4]`.

Rewrite using `[← sub_eq_zero, hE]`. Use `noncomm_ring`. Establish `hYr : Y = (τ.map Complex.im).map (fun t => (t : ℂ))` using `rfl`. Establish `hdetY : Y.det ≠ 0`. Establish `: Y.det = ((τ.map Complex.im).det : ℂ)`.

Rewrite using `[hYr]`. Conclude with `(RingHom.map_det Complex.ofRealHom _).symm`. Rewrite using `[this, Complex.ofReal_ne_zero]`. Conclude with `hpos.det_pos.ne'`. Establish `h2I : (2 * I : ℂ) ≠ 0` using `by simp`.

Establish `hdetJ : J.det ≠ 0`. Introduce `hdet`. Take `⟨v, hv, hJv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Establish `h0 : star v ⬝ᵥ ((Jᴴ * M - Mᴴ * J) *ᵥ v) = 0`. Rewrite using `[sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hJv, mulVec_zero, dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hJv, star_zero, zero_dotProduct, sub_zero]`.

Rewrite `h0` using `[hI1, hY, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero]`. Establish `h1` using `congrArg Complex.re (h0.resolve_left h2I)`. Rewrite `h1` using `[hYr, re_star_dotProduct_ofReal_mulVec, Complex.zero_re]`. Establish `hna` using `hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)`. Establish `hnb` using `hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)`.

Simplify using `only [star_trivial] at hna hnb`. Establish `ha : (fun i => (v i).re) = 0`. Assume the negation of the conclusion as `h`. Use `hpos.dotProduct_mulVec_pos h` as an intermediate fact. Simplify using `only [star_trivial] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb : (fun i => (v i).im) = 0`. Assume the negation of the conclusion as `h`. Use `hpos.dotProduct_mulVec_pos h` as an intermediate fact. Simplify using `only [star_trivial] at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Apply `hv` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using congrFun ha i`.

Simplify using `using congrFun hb i`. Establish `hJu : IsUnit J.det` using `isUnit_iff_ne_zero.mpr hdetJ`. Establish `hYu : IsUnit Y.det` using `isUnit_iff_ne_zero.mpr hdetY`. Establish `hJJ : J * J⁻¹ = 1` using `mul_nonsing_inv J hJu`. Establish `hJJ' : J⁻¹ * J = 1` using `nonsing_inv_mul J hJu`.

Establish `hYY : Y⁻¹ * Y = 1` using `nonsing_inv_mul Y hYu`. Establish `hτ'sym : (M * J⁻¹).IsSymm`. Establish `hJtu : IsUnit Jᵀ.det` using `by rwa [det_transpose]`. Unfold `Matrix.IsSymm`. Rewrite using `[transpose_mul, transpose_nonsing_inv]`.

Combine the equalities or inequalities in the displayed calculation. Use `set Y' := (_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ) with hY'def`. Establish `hY' : (2 * I) • Y' = M * J⁻¹ - (M * J⁻¹)ᴴ`. Rewrite using `[hY'def, hact]`. Conclude with `(sub_conjTranspose_of_isSymm _ hτ'sym).symm`.

Establish `hkey : Jᴴ * Y' * J = Y`. Apply `smul_right_injective _ h2I` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]`. Use `congr 1`.

Simplify using `only [Matrix.mul_assoc, hJJ', Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc Jᴴ, ← conjTranspose_mul, hJJ', conjTranspose_one, Matrix.one_mul]`. Use `_ = (2 * I) • Y := by rw [hI1, hY]`. Establish `hY'inv : Y'⁻¹ = J * Y⁻¹ * Jᴴ`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Use `_ = 1 := by rw [hkey, Matrix.mul_assoc J, hYY, Matrix.mul_one, hJJ]`. Establish `hJh : Jᴴ = Jᵀ - (2 * I) • (Y * Cᵀ)`. Establish `hτh : τᴴ = τ - (2 * I) • Y` using `by rw [← hY]; abel`.

Rewrite using `[hJ, conjTranspose_add, conjTranspose_mul, transpose_add, transpose_mul, hCh, hDh, hτt, hτh, Matrix.sub_mul, Matrix.smul_mul]`. Normalize the expressions using the abelian group laws. Establish `hJt : Jᵀ * (J⁻¹)ᵀ = 1` using `by rw [← transpose_mul, hJJ', transpose_one]`. Establish `hmat : J⁻¹ * (J * Y⁻¹ * Jᴴ) * (J⁻¹)ᵀ = Y⁻¹ - (2 * I) • (J⁻¹ * C)ᵀ`. Rewrite using `[hJh, transpose_mul]`.

Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hJJ', Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc Y⁻¹ Jᵀ, hJt, Matrix.mul_one, hYY, Matrix.one_mul]`. Rewrite using `[hY'inv, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hmat, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_transpose_mulVec_self, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.SW.canon_exponent_invariant : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℚ), σ ∈ Matrix.symplecticGroup ι ℚ → ∀ τ ∈ _root_.GlobalTheory.SW.Siegel ι, ∀ ζ : ι → ℂ, (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) ⬝ᵥ ((_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ))⁻¹ *ᵥ (ζ ᵥ* (_root_.GlobalTheory.SW.spDen σ τ)⁻¹) + 2 * I * (ζ ⬝ᵥ ((_root_.GlobalTheory.SW.spDen σ τ)⁻¹ * _root_.GlobalTheory.SW.qm σ.toBlocks₂₁) *ᵥ ζ) = ζ ⬝ᵥ (τ.map fun z => (z.im : ℂ))⁻¹ *ᵥ ζ := by
  intro ι _ _ σ hσ τ hτ ζ
  obtain ⟨hsym, hpos⟩ := hτ
  have h2 := SymplecticGroup.mem_iff'.mp hσ
  rw [← fromBlocks_toBlocks σ] at h2
  simp [Matrix.J, fromBlocks_transpose, fromBlocks_multiply] at h2
  obtain ⟨r1, r2, r3, r4⟩ := h2
  replace r1 := congrArg _root_.GlobalTheory.SW.qm r1
  replace r2 := congrArg _root_.GlobalTheory.SW.qm r2
  replace r3 := congrArg _root_.GlobalTheory.SW.qm r3
  replace r4 := congrArg _root_.GlobalTheory.SW.qm r4
  simp only [qm_add', qm_neg', qm_mul_siegel_theta_transformation, qm_transpose',
    qm_zero', qm_one'] at r1 r2 r3 r4
  set A := _root_.GlobalTheory.SW.qm σ.toBlocks₁₁ with hA
  set B := _root_.GlobalTheory.SW.qm σ.toBlocks₁₂ with hB
  set C := _root_.GlobalTheory.SW.qm σ.toBlocks₂₁ with hC
  set D := _root_.GlobalTheory.SW.qm σ.toBlocks₂₂ with hD
  set J := _root_.GlobalTheory.SW.spDen σ τ with hJdef
  have hJ : J = C * τ + D := rfl
  set M := A * τ + B with hM
  have hact : _root_.GlobalTheory.SW.spAct σ τ = M * J⁻¹ := rfl
  set Y := τ.map fun z => (z.im : ℂ) with hYdef
  have hY : τ - τᴴ = (2 * I) • Y := sub_conjTranspose_of_isSymm τ hsym
  have hτt : τᵀ = τ := hsym
  have hCh : Cᴴ = Cᵀ := qm_conjTranspose_eq_transpose _
  have hDh : Dᴴ = Dᵀ := qm_conjTranspose_eq_transpose _
  have hAh : Aᴴ = Aᵀ := qm_conjTranspose_eq_transpose _
  have hBh : Bᴴ = Bᵀ := qm_conjTranspose_eq_transpose _
  have hI1 : Jᴴ * M - Mᴴ * J = τ - τᴴ := by
    rw [hJ, hM, conjTranspose_add, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, hCh, hDh, hAh, hBh]
    have hE : (τᴴ * Cᵀ + Dᵀ) * (A * τ + B) - (τᴴ * Aᵀ + Bᵀ) * (C * τ + D) =
        τᴴ * (Cᵀ * A + -(Aᵀ * C)) * τ + τᴴ * (Cᵀ * B + -(Aᵀ * D)) + (Dᵀ * A + -(Bᵀ * C)) * τ +
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [hE, r1, r2, r3, r4]
    noncomm_ring
  have hI2 : Mᵀ * J = Jᵀ * M := by
    rw [hJ, hM, transpose_add, transpose_add, transpose_mul, transpose_mul, hτt]
    have hE : (τ * Aᵀ + Bᵀ) * (C * τ + D) - (τ * Cᵀ + Dᵀ) * (A * τ + B) =
        -(τ * (Cᵀ * A + -(Aᵀ * C)) * τ) - τ * (Cᵀ * B + -(Aᵀ * D)) - (Dᵀ * A + -(Bᵀ * C)) * τ -
          (Dᵀ * B + -(Bᵀ * D)) := by noncomm_ring
    rw [r1, r2, r3, r4] at hE
    rw [← sub_eq_zero, hE]
    noncomm_ring
  have hYr : Y = (τ.map Complex.im).map (fun t => (t : ℂ)) := rfl
  have hdetY : Y.det ≠ 0 := by
    have : Y.det = ((τ.map Complex.im).det : ℂ) := by
      rw [hYr]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [this, Complex.ofReal_ne_zero]
    exact hpos.det_pos.ne'
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hdetJ : J.det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have h0 : star v ⬝ᵥ ((Jᴴ * M - Mᴴ * J) *ᵥ v) = 0 := by
      rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec, hJv, mulVec_zero,
        dotProduct_zero, dotProduct_mulVec, ← star_mulVec, hJv, star_zero, zero_dotProduct, sub_zero]
    rw [hI1, hY, smul_mulVec, dotProduct_smul, smul_eq_mul, mul_eq_zero] at h0
    have h1 := congrArg Complex.re (h0.resolve_left h2I)
    rw [hYr, re_star_dotProduct_ofReal_mulVec, Complex.zero_re] at h1
    have hna := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
    have hnb := hpos.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
    simp only [star_trivial] at hna hnb
    have ha : (fun i => (v i).re) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    have hb : (fun i => (v i).im) = 0 := by
      by_contra h
      have := hpos.dotProduct_mulVec_pos h
      simp only [star_trivial] at this
      linarith
    apply hv
    funext i
    apply Complex.ext
    · simpa using congrFun ha i
    · simpa using congrFun hb i
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hdetJ
  have hYu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hdetY
  have hJJ : J * J⁻¹ = 1 := mul_nonsing_inv J hJu
  have hJJ' : J⁻¹ * J = 1 := nonsing_inv_mul J hJu
  have hYY : Y⁻¹ * Y = 1 := nonsing_inv_mul Y hYu
  have hτ'sym : (M * J⁻¹).IsSymm := by
    have hJtu : IsUnit Jᵀ.det := by rwa [det_transpose]
    unfold Matrix.IsSymm
    rw [transpose_mul, transpose_nonsing_inv]
    calc (Jᵀ)⁻¹ * Mᵀ = (Jᵀ)⁻¹ * (Mᵀ * J) * J⁻¹ := by simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = M * J⁻¹ := by rw [hI2, ← Matrix.mul_assoc (Jᵀ)⁻¹, nonsing_inv_mul _ hJtu, Matrix.one_mul]
  set Y' := (_root_.GlobalTheory.SW.spAct σ τ).map fun z => (z.im : ℂ) with hY'def
  have hY' : (2 * I) • Y' = M * J⁻¹ - (M * J⁻¹)ᴴ := by
    rw [hY'def, hact]
    exact (sub_conjTranspose_of_isSymm _ hτ'sym).symm
  have hkey : Jᴴ * Y' * J = Y := by
    apply smul_right_injective _ h2I
    calc (2 * I) • (Jᴴ * Y' * J) = Jᴴ * ((2 * I) • Y') * J := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = Jᴴ * (M * J⁻¹ - (M * J⁻¹)ᴴ) * J := by rw [hY']
      _ = Jᴴ * M - Mᴴ * J := by
        rw [conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul]
        congr 1
        · simp only [Matrix.mul_assoc, hJJ', Matrix.mul_one]
        · rw [← Matrix.mul_assoc Jᴴ, ← conjTranspose_mul, hJJ', conjTranspose_one, Matrix.one_mul]
      _ = (2 * I) • Y := by rw [hI1, hY]
  have hY'inv : Y'⁻¹ = J * Y⁻¹ * Jᴴ := by
    apply Matrix.inv_eq_left_inv
    calc J * Y⁻¹ * Jᴴ * Y' = J * Y⁻¹ * (Jᴴ * Y' * J) * J⁻¹ := by
          simp only [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = 1 := by rw [hkey, Matrix.mul_assoc J, hYY, Matrix.mul_one, hJJ]
  have hJh : Jᴴ = Jᵀ - (2 * I) • (Y * Cᵀ) := by
    have hτh : τᴴ = τ - (2 * I) • Y := by rw [← hY]; abel
    rw [hJ, conjTranspose_add, conjTranspose_mul, transpose_add, transpose_mul, hCh, hDh, hτt, hτh,
      Matrix.sub_mul, Matrix.smul_mul]
    abel
  have hJt : Jᵀ * (J⁻¹)ᵀ = 1 := by rw [← transpose_mul, hJJ', transpose_one]
  have hmat : J⁻¹ * (J * Y⁻¹ * Jᴴ) * (J⁻¹)ᵀ = Y⁻¹ - (2 * I) • (J⁻¹ * C)ᵀ := by
    rw [hJh, transpose_mul]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hJJ',
      Matrix.one_mul]
    rw [Matrix.mul_assoc Y⁻¹ Jᵀ, hJt, Matrix.mul_one, hYY, Matrix.one_mul]
  rw [hY'inv, ← dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, hmat, sub_mulVec,
    dotProduct_sub, smul_mulVec, dotProduct_smul, dotProduct_transpose_mulVec_self, smul_eq_mul]
  ring

end GlobalTheory.SW
