import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.WpK

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
Establish `h` using `d.ex_add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `mul_eq_left.1 h.symm`.
-/
theorem ex_zero : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => rw [zero_smul, pow_zero, ex_zero]`. Consider the case `succ i ih => rw [succ_nsmul, d.ex_add, ih, pow_succ]`.
-/
theorem ex_nsmul (i : ℕ) (z : Fin g' → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero => rw [zero_smul, pow_zero, ex_zero]
  | succ i ih => rw [succ_nsmul, d.ex_add, ih, pow_succ]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [cubN, d.fr_zero]`. Consider the case `succ k ih`. Establish `h` using `d.cub (k • x') x' x`. Rewrite `h` using `[ex_nsmul]`.

Rewrite `ih` using `[cubN]`. Rewrite using `[cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]`. Use `replace h := congrArg Additive.ofMul h`. Use `replace ih := congrArg Additive.ofMul ih`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [pow_succ, ofMul_mul] at h ih ⊢`. Take the linear combination `(norm := abel) h + ih`.
-/
theorem cubN_frame (k : ℕ) (x' x : Fin g' → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.fr_zero]
  | succ k ih =>
    have h := d.cub (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

/- English proof (translation)
Simplify using `[CD.full, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, d.symm.eq, d.toricPeriodBlock_isSymm.eq]`.
-/
theorem full_transpose : (d.full σ 0)ᵀ = d.full σ 0 := by
  simp [CD.full, Matrix.transpose_submatrix, Matrix.fromBlocks_transpose, d.symm.eq, d.toricPeriodBlock_isSymm.eq]

/- English proof (translation)
Simplify using `only [dotProduct, zP, tP]`. Rewrite using `[← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]`.
-/
theorem dot_split' (u v : Fin g → ℂ) : u ⬝ᵥ v = zP σ u ⬝ᵥ zP σ v + tP σ u ⬝ᵥ tP σ v := by
  simp only [dotProduct, zP, tP]
  rw [← Equiv.sum_comp σ.symm, Fintype.sum_sum_type]

end GlobalTheory.MBLow.Cl.WpK
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.WpK
variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Use `set Z := (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hZ`. Use `set Z' := (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn' with hZ'`. Use `set z := zP σ Z`. Use `set z' := zP σ Z'`.

Use `set y' := p'.1.1.toAdd with hy'`. Establish `hco : co bX y' = cv (tP σ Nn')` using `by rw [hy', h'.1]; exact Exp.co_sum _`. Use `set cy := d.t12 *ᵥ co bX y' with hcy`. Use `set per' := perV d.τ (zP σ M') (zP σ Nn') with hper`. Establish `e : k • z' = cy + per'`.

Establish `: k • z' = zP σ (perV (d.full σ 0) M' Nn')`. Use function extensionality and compare the values at `i`. Simplify using `only [z', Z', zP, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]`. Rewrite using `[← _root_.mul_assoc, mul_inv_cancel₀ hk', _root_.one_mul]`. Rewrite using `[this, Exp.leftComponent_periodVector, hcy, hco, add_comm]`.

Establish `e2 : k • z' + z = (cy + z) + per'` using `by rw [e]; abel`. Establish `c` using `congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k z' z)`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val] at c`. Rewrite `c` using `[e2]`. Establish `s` using `h.2.2 y'`.

Establish `f1` using `Exp.fr_shift d (zP σ M') (zP σ Nn') (cy + z)`. Establish `f2` using `Exp.fr_shift d (zP σ M') (zP σ Nn') cy`. Rewrite `c` using `[e]`. Rewrite `f1` using `[dotProduct_add, Exp.exp_two_pi_add]`. Establish `hT : cv Nn' ⬝ᵥ Z = cv (zP σ Nn') ⬝ᵥ z + co bX y' ⬝ᵥ tP σ Z`.

Rewrite using `[dot_split' σ, hco]`. Both sides reduce to the same expression. Rewrite using `[hT, Exp.exp_two_pi_add, NumD.tk, h.2.1, h'.2.1, Units.val_mul]`. Use `set E1 := Complex.exp (2 * Real.pi * Complex.I * (co bX y' ⬝ᵥ tP σ Z))`. Use `set E2 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ z))`.

Use `set E3 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ cy))`. Establish `nA` using `(d.fr (cy + z)).ne_zero`. Establish `nB` using `(d.fr (cy + per')).ne_zero`. Establish `nC` using `(d.fr z).ne_zero`. Apply `mul_left_cancel₀ (mul_ne_zero (mul_ne_zero nA nB) nC)` to reduce the goal to its premises.

Take the linear combination `(((cubN N.θ k 1 (d.ex z') (d.ex z) : ℂˣ) : ℂ) * d.fr (cy + per') * d.fr z * (d.fr (z' + z) : ℂ) ^ k) * s + (E1 * d.fr cy * d.fr z) * c + (E1 * d.fr cy * d.fr z * ((d.fr z' : ℂ) * d.fr z) ^ k) * f1 - (E2 * E1 * ((d.fr z' : ℂ) * d.fr z) ^ k * d.fr (cy + z) * d.fr z) * f2`.
-/
theorem tk_frame {k : ℕ} (hk : 0 < k) {M Nn M' Nn' : Fin g → ℤ} {p p' : N.QT k} (h : d.Rep σ k M Nn p)
    (h' : d.Rep σ k M' Nn' p') :
    (N.tk p p' : ℂ) * (d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') + zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * (cv Nn' ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) *
        ((d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn')) : ℂ) * d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn))) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set Z := (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hZ
  set Z' := (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn' with hZ'
  set z := zP σ Z
  set z' := zP σ Z'
  set y' := p'.1.1.toAdd with hy'
  have hco : co bX y' = cv (tP σ Nn') := by rw [hy', h'.1]; exact Exp.co_sum _
  set cy := d.t12 *ᵥ co bX y' with hcy
  set per' := perV d.τ (zP σ M') (zP σ Nn') with hper
  have e : k • z' = cy + per' := by
    have : k • z' = zP σ (perV (d.full σ 0) M' Nn') := by
      funext i
      simp only [z', Z', zP, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul]
      rw [← _root_.mul_assoc, mul_inv_cancel₀ hk', _root_.one_mul]
    rw [this, Exp.leftComponent_periodVector, hcy, hco, add_comm]
  have e2 : k • z' + z = (cy + z) + per' := by rw [e]; abel
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k z' z)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  rw [e2] at c
  have s := h.2.2 y'
  have f1 := Exp.fr_shift d (zP σ M') (zP σ Nn') (cy + z)
  have f2 := Exp.fr_shift d (zP σ M') (zP σ Nn') cy
  rw [e] at c
  rw [dotProduct_add, Exp.exp_two_pi_add] at f1
  have hT : cv Nn' ⬝ᵥ Z = cv (zP σ Nn') ⬝ᵥ z + co bX y' ⬝ᵥ tP σ Z := by
    rw [dot_split' σ, hco]; rfl
  rw [hT, Exp.exp_two_pi_add, NumD.tk, h.2.1, h'.2.1, Units.val_mul]
  set E1 := Complex.exp (2 * Real.pi * Complex.I * (co bX y' ⬝ᵥ tP σ Z))
  set E2 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ z))
  set E3 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn') ⬝ᵥ cy))
  have nA := (d.fr (cy + z)).ne_zero
  have nB := (d.fr (cy + per')).ne_zero
  have nC := (d.fr z).ne_zero
  apply mul_left_cancel₀ (mul_ne_zero (mul_ne_zero nA nB) nC)
  linear_combination (((cubN N.θ k 1 (d.ex z') (d.ex z) : ℂˣ) : ℂ) * d.fr (cy + per') * d.fr z * (d.fr (z' + z) : ℂ) ^ k) * s +
    (E1 * d.fr cy * d.fr z) * c + (E1 * d.fr cy * d.fr z * ((d.fr z' : ℂ) * d.fr z) ^ k) * f1 -
    (E2 * E1 * ((d.fr z' : ℂ) * d.fr z) ^ k * d.fr (cy + z) * d.fr z) * f2

end GlobalTheory.MBLow.Cl.WpK
end

namespace GlobalTheory.MBLow.Cl

/- English proof (translation)
Introduce `N g' r g bX d σ k hk M Nn M' Nn' p p' h h'`. Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `a` using `WpK.tk_frame d σ hk h h'`. Establish `b` using `WpK.tk_frame d σ hk h' h`. Rewrite `b` using `[add_comm, mul_comm (d.fr _ : ℂ)]`.

Establish `n1` using `pow_ne_zero k (d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') + zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn))).ne_zero`. Establish `hs : cv Nn' ⬝ᵥ d.full σ 0 *ᵥ cv Nn = cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn'`. Rewrite using `[Exp.dotProduct_mulVec_eq_transpose_mulVec, WpK.full_transpose]`. Establish `key : Complex.exp (2 * Real.pi * Complex.I * (cv Nn' ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) = Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) * Complex.exp (2 * Real.pi * Complex.I * (cv Nn ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn'))`. Rewrite using `[← Complex.exp_add]`.

Use `congr 1`. Simplify using `only [perV, dotProduct_smul, dotProduct_add, smul_eq_mul]`. Rewrite using `[hs, dotProduct_comm (cv M) (cv Nn')]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]`. Apply `mul_right_cancel₀ n1` to reduce the goal to its premises. Rewrite using `[a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]`.
-/
theorem wp_classical : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ k : ℕ, 0 < k → ∀ M Nn M' Nn' p p', d.Rep σ k M Nn p →
    d.Rep σ k M' Nn' p' → (N.wp p p' : ℂ) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) := by
  intro N g' r g bX d σ k hk M Nn M' Nn' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := WpK.tk_frame d σ hk h h'
  have b := WpK.tk_frame d σ hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn') +
    zP σ ((k : ℂ)⁻¹ • perV (d.full σ 0) M Nn))).ne_zero
  have hs : cv Nn' ⬝ᵥ d.full σ 0 *ᵥ cv Nn = cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn' := by
    rw [Exp.dotProduct_mulVec_eq_transpose_mulVec, WpK.full_transpose]
  have key : Complex.exp (2 * Real.pi * Complex.I * (cv Nn' ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) =
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * (cv M ⬝ᵥ cv Nn' - cv Nn ⬝ᵥ cv M') / k) *
      Complex.exp (2 * Real.pi * Complex.I * (cv Nn ⬝ᵥ (k : ℂ)⁻¹ • perV (d.full σ 0) M' Nn')) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [perV, dotProduct_smul, dotProduct_add, smul_eq_mul]
    rw [hs, dotProduct_comm (cv M) (cv Nn')]
    field_simp
    ring
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.MBLow.Cl
