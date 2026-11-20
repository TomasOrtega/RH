import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch.Wp

variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero`. Rewrite using `[zero_smul, pow_zero]`. Conclude with `(d.ab.2.2.1 0).2 (zero_mem _)`. Consider the case `succ i ih => rw [succ_nsmul, d.ab.1, ih, pow_succ]`.
-/
theorem ex_nsmul (d : Dict N B) (i : ℕ) (z : Fin B.gB → ℂ) : d.ex (i • z) = d.ex z ^ i := by
  induction i with
  | zero =>
    rw [zero_smul, pow_zero]
    exact (d.ab.2.2.1 0).2 (zero_mem _)
  | succ i ih => rw [succ_nsmul, d.ab.1, ih, pow_succ]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [cubN, d.ab.2.2.2.1]`. Consider the case `succ k ih`. Establish `h` using `d.ab.2.2.2.2.2.1 (k • x') x' x`. Rewrite `h` using `[ex_nsmul]`.

Rewrite `ih` using `[cubN]`. Rewrite using `[cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]`. Use `replace h := congrArg Additive.ofMul h`. Use `replace ih := congrArg Additive.ofMul ih`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [pow_succ, ofMul_mul] at h ih ⊢`. Take the linear combination `(norm := abel) h + ih`.
-/
theorem cubN_frame (d : Dict N B) (k : ℕ) (x' x : Fin B.gB → ℂ) :
    cubN N.θ k 1 (d.ex x') (d.ex x) * d.fr (k • x') * d.fr x * d.fr (x' + x) ^ k =
      d.fr (k • x' + x) * (d.fr x' * d.fr x) ^ k := by
  induction k with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ k ih =>
    have h := d.ab.2.2.2.2.2.1 (k • x') x' x
    rw [ex_nsmul] at h
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, succ_nsmul, _root_.one_mul (d.ex x' ^ k)]
    replace h := congrArg Additive.ofMul h
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [pow_succ, ofMul_mul] at h ih ⊢
    linear_combination (norm := abel) h + ih

/- English proof (translation)
Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Use `set x := ((k : ℂ)⁻¹ • B.P0 la).2 with hx`. Use `set x' := ((k : ℂ)⁻¹ • B.P0 la').2 with hx'`. Establish `e : k • x' = B.ct la'.y + la'.l`. Rewrite using `[hx', Prod.smul_snd, AnArc.degeneratingTori_basePeriodMap_snd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk', one_smul]`.

Establish `c` using `congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k x' x)`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val] at c`. Establish `s` using `h.2.2 la'.y`. Establish `f1` using `d.ab.2.2.2.2.1 la'.l (B.ct la'.y + x)`. Establish `f2` using `d.ab.2.2.2.2.1 la'.l (B.ct la'.y)`.

Rewrite `f1` using `[AnArc.ah_add, add_right_comm, ← e]`. Rewrite `f2` using `[← e]`. Rewrite `s` using `[← hx, f1, f2, eTwoPi]`. Rewrite using `[NumD.tk, h'.1, h.2.1, h'.2.1, Units.val_mul, Complex.exp_sub, ← hx, ← hx']`. Establish `n1` using `B.ah_ne_zero la'.l (B.ct la'.y)`.

Establish `n2` using `(d.fr (k • x')).ne_zero`. Establish `n3` using `(d.fr x).ne_zero`. Establish `n4` using `(d.fr (k • x' + x)).ne_zero`. Establish `n5` using `Complex.exp_ne_zero (Real.pi * B.H x la'.l)`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff n5]`.

Apply `mul_left_cancel₀ (mul_ne_zero n1 (mul_ne_zero n2 (mul_ne_zero n3 n4)))` to reduce the goal to its premises. Take the linear combination `(B.ah la'.l (B.ct la'.y) * Complex.exp (Real.pi * B.H x la'.l) * (d.fr (k • x' + x) : ℂ) * (p.1.2.s (d.eX la'.y) : ℂ)) * c + (((d.fr x' : ℂ) * d.fr x) ^ k * (d.fr (k • x' + x) : ℂ)) * s`.
-/
theorem tk_frame (d : Dict N B) {k : ℕ} (hk : 0 < k) {la la' : B.La} {p p' : N.QT k} (h : d.Rep k la p)
    (h' : d.Rep k la' p') :
    (N.tk p p' : ℂ) * (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2) : ℂ) ^ k =
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) *
        ((d.fr ((k : ℂ)⁻¹ • B.P0 la').2 : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2) ^ k := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  set x := ((k : ℂ)⁻¹ • B.P0 la).2 with hx
  set x' := ((k : ℂ)⁻¹ • B.P0 la').2 with hx'
  have e : k • x' = B.ct la'.y + la'.l := by
    rw [hx', Prod.smul_snd, AnArc.degeneratingTori_basePeriodMap_snd, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hk', one_smul]
  have c := congrArg (Units.val : ℂˣ → ℂ) (cubN_frame d k x' x)
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at c
  have s := h.2.2 la'.y
  have f1 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y + x)
  have f2 := d.ab.2.2.2.2.1 la'.l (B.ct la'.y)
  rw [AnArc.ah_add, add_right_comm, ← e] at f1
  rw [← e] at f2
  rw [← hx, f1, f2, eTwoPi] at s
  rw [NumD.tk, h'.1, h.2.1, h'.2.1, Units.val_mul, Complex.exp_sub, ← hx, ← hx']
  have n1 := B.ah_ne_zero la'.l (B.ct la'.y)
  have n2 := (d.fr (k • x')).ne_zero
  have n3 := (d.fr x).ne_zero
  have n4 := (d.fr (k • x' + x)).ne_zero
  have n5 := Complex.exp_ne_zero (Real.pi * B.H x la'.l)
  rw [div_mul_eq_mul_div, eq_div_iff n5]
  apply mul_left_cancel₀ (mul_ne_zero n1 (mul_ne_zero n2 (mul_ne_zero n3 n4)))
  linear_combination (B.ah la'.l (B.ct la'.y) * Complex.exp (Real.pi * B.H x la'.l) * (d.fr (k • x' + x) : ℂ) *
    (p.1.2.s (d.eX la'.y) : ℂ)) * c + (((d.fr x' : ℂ) * d.fr x) ^ k * (d.fr (k • x' + x) : ℂ)) * s

/- English proof (translation)
Introduce `O _ _ N B d k hk la la' p p' h h'`. Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `a` using `tk_frame d hk h h'`. Establish `b` using `tk_frame d hk h' h`. Rewrite `b` using `[add_comm, mul_comm (d.fr _ : ℂ)]`.

Establish `n1` using `pow_ne_zero k (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2)).ne_zero`. Establish `E : (B.Ef la.l la'.l : ℂ) = ((B.H la.l la'.l).im : ℂ)`. Rewrite using `[← B.Ef_eq_im]`. Simplify using the standard rewrite rules. Establish `C` using `Complex.sub_conj (B.H la.l la'.l)`.

Rewrite `C` using `[B.H_conj]`. Establish `key : Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y - Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) = Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k) * Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la').1 la.y - Real.pi * B.H ((k …`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.degeneratingTori_basePeriodMap_snd, AnArc.H_smul_left, AnArc.H_add_left, smul_eq_mul, AnArc.EF_apply, B.T_symm la'.y la.y]`.

Move the coercions through the operations in `at C ⊢`. Rewrite using `[E]`. Establish `hI` using `Complex.I_ne_zero`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-1 : ℂ) * C`.

Rewrite using `[NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]`. Apply `mul_right_cancel₀ n1` to reduce the goal to its premises. Rewrite using `[a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]`.
-/
theorem wp_eq : WpSt := by
  intro O _ _ N B d k hk la la' p p' h h'
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have a := tk_frame d hk h h'
  have b := tk_frame d hk h' h
  rw [add_comm, mul_comm (d.fr _ : ℂ)] at b
  have n1 := pow_ne_zero k (d.fr (((k : ℂ)⁻¹ • B.P0 la').2 + ((k : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  have E : (B.Ef la.l la'.l : ℂ) = ((B.H la.l la'.l).im : ℂ) := by
    rw [← B.Ef_eq_im]; simp
  have C := Complex.sub_conj (B.H la.l la'.l)
  rw [B.H_conj] at C
  have key : Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la).1 la'.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la'.l) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (B.EF la la' : ℂ) / k) *
      Complex.exp (2 * Real.pi * Complex.I * ((k : ℂ)⁻¹ • B.P0 la').1 la.y -
          Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la').2 la.l) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.degeneratingTori_basePeriodMap_snd,
      AnArc.H_smul_left, AnArc.H_add_left, smul_eq_mul, AnArc.EF_apply, B.T_symm la'.y la.y]
    push_cast at C ⊢
    rw [E]
    have hI := Complex.I_ne_zero
    field_simp
    linear_combination (-1 : ℂ) * C
  rw [NumD.wp, Units.val_div_eq_div_val, div_eq_iff (N.tk p' p).ne_zero]
  apply mul_right_cancel₀ n1
  rw [a, key, _root_.mul_assoc _ (N.tk p' p : ℂ), b, _root_.mul_assoc]

end GlobalTheory.Ex.Arch.Wp
end
