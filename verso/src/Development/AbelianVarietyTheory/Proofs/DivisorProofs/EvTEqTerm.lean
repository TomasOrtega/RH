import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DotProductMulVecEqTransposeMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCharBlockPeriodMatrixFourierJacobiExpansion
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.Ev

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)

/- English proof (translation)
Establish `h` using `d.ex_add 0 0`. Rewrite `h` using `[add_zero]`. Simplify using `using h.symm`.
-/
theorem ex_zero : d.ex 0 = 1 := by
  have h := d.ex_add 0 0
  rw [add_zero] at h
  simpa using h.symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [ex_zero]`. Consider the case `succ n ih => rw [Nat.cast_succ, add_smul, one_smul, d.ex_add, ih, pow_succ]`.
-/
theorem ex_smul (n : ℕ) (x : Fin g' → ℂ) : d.ex ((n : ℂ) • x) = d.ex x ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, d.ex_add, ih, pow_succ]

/- English proof (translation)
The claim follows from `eq_inv_of_mul_eq_one_left (by rw [← d.ex_add, neg_add_cancel, ex_zero])`.
-/
theorem ex_neg (x : Fin g' → ℂ) : d.ex (-x) = (d.ex x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← d.ex_add, neg_add_cancel, ex_zero])

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [cubN, d.fr_zero]`. Consider the case `succ k ih`. Establish `a` using `d.cub ((k : ℂ) • x) x z`. Rewrite `a` using `[ex_smul]`.

Rewrite `ih` using `[cubN]`. Rewrite using `[cubN, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, _root_.one_mul, pow_succ (d.fr (x + z)), pow_succ (d.fr x), pow_succ (d.fr z)]`. Use `replace a := congrArg Additive.ofMul a`. Use `replace ih := congrArg Additive.ofMul ih`. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_pow] at a ih ⊢`. Take the linear combination `(norm := abel) a + ih`.
-/
theorem cubN_fr (k : ℕ) (x z : Fin g' → ℂ) :
    cubN N.θ k 1 (d.ex x) (d.ex z) * d.fr ((k : ℂ) • x) * d.fr z * d.fr (x + z) ^ k =
      d.fr ((k : ℂ) • x + z) * d.fr x ^ k * d.fr z ^ k := by
  induction k with
  | zero => simp [cubN, d.fr_zero]
  | succ k ih =>
    have a := d.cub ((k : ℂ) • x) x z
    rw [ex_smul] at a
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, _root_.one_mul, pow_succ (d.fr (x + z)),
      pow_succ (d.fr x), pow_succ (d.fr z)]
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow] at a ih ⊢
    linear_combination (norm := abel) a + ih

/- English proof (translation)
Establish `a` using `d.cub x (-x) x`. Establish `b` using `d.sym x`. Rewrite `a` using `[add_neg_cancel, neg_add_cancel, zero_add, d.fr_zero, ex_neg]`. Use `replace a := congrArg Additive.ofMul a`. Use `replace b := congrArg Additive.ofMul b`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [dbl, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a b ⊢`. Take the linear combination `(norm := abel) a - b`.
-/
theorem dbl_fr (x : Fin g' → ℂ) : dbl N.θ N.σ (d.ex x) * d.fr (x + x) = d.fr x ^ 4 := by
  have a := d.cub x (-x) x
  have b := d.sym x
  rw [add_neg_cancel, neg_add_cancel, zero_add, d.fr_zero, ex_neg] at a
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a b ⊢
  linear_combination (norm := abel) a - b

/- English proof (translation)
Establish `a` using `congrArg Additive.ofMul (cubN_fr d i x x)`. Establish `b` using `congrArg (fun t => Additive.ofMul (t ^ i)) (dbl_fr d x)`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢`. Take the linear combination `(norm := module) a - b`.
-/
theorem cubN_div (x : Fin g' → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ i * d.fr ((i : ℂ) • x) * d.fr x * d.fr x ^ (2 * i) =
      d.fr ((i : ℂ) • x + x) := by
  have a := congrArg Additive.ofMul (cubN_fr d i x x)
  have b := congrArg (fun t => Additive.ofMul (t ^ i)) (dbl_fr d x)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢
  linear_combination (norm := module) a - b

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [mulq, d.fr_zero]`. Consider the case `succ n ih`. Rewrite `ih` using `[mulq]`. Rewrite using `[mulq, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, ← cubN_div, ← ih, show (n + 1) ^ 2 = n ^ 2 + 1 + 2 * n by ring, pow_add, pow_succ]`.

The two sides agree by associativity and commutativity.
-/
theorem mulq_fr (x : Fin g' → ℂ) (n : ℕ) :
    mulq N.θ N.σ n (d.ex x) * d.fr x ^ (n ^ 2) = d.fr ((n : ℂ) • x) := by
  induction n with
  | zero => simp [mulq, d.fr_zero]
  | succ n ih =>
    rw [mulq] at ih
    rw [mulq, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, ← cubN_div, ← ih,
      show (n + 1) ^ 2 = n ^ 2 + 1 + 2 * n by ring, pow_add, pow_succ]
    ac_rfl

end GlobalTheory.MBLow.Cl.Ev
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.Ev

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
Use `⟨∑ i, if a i = 0 then 0 else M i, ?_⟩` and prove the remaining obligations. Simplify using `only [dotProduct, cv, Finset.mul_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases ha i with h | h <;> simp [h]`.
-/
theorem half_int {k : ℕ} {a : Fin k → ℂ} (ha : Half a) (M : Fin k → ℤ) : ∃ n : ℤ, 2 * (a ⬝ᵥ cv M) = n := by
  refine ⟨∑ i, if a i = 0 then 0 else M i, ?_⟩
  simp only [dotProduct, cv, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases ha i with h | h <;> simp [h]

/- English proof (translation)
Introduce `j` and use `by simp only [CD.aF] rcases σ j with i | l · exact d.ha i · left; rfl`.
-/
theorem half_aF : Half (d.aF σ) := fun j => by
  simp only [CD.aF]
  rcases σ j with i | l
  · exact d.ha i
  · left; rfl

/- English proof (translation)
Introduce `j` and use `by simp only [CD.bF] rcases σ j with i | l · exact d.hb i · exact d.hb2 l`.
-/
theorem half_bF : Half (d.bF σ) := fun j => by
  simp only [CD.bF]
  rcases σ j with i | l
  · exact d.hb i
  · exact d.hb2 l

/- English proof (translation)
The claim follows from `(Exp.isPt_one_iff d σ 0).2 ⟨0, 0, funext fun _ => rfl, by simp [perV, Exp.cv_zero]⟩`.
-/
theorem isPt_zero : d.IsPt σ 0 1 :=
  (Exp.isPt_one_iff d σ 0).2 ⟨0, 0, funext fun _ => rfl, by simp [perV, Exp.cv_zero]⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, zero_smul, pow_zero]`. Conclude with `isPt_zero d σ`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ, add_smul, one_smul, pow_succ]`.

Conclude with `Exp.IsPt.add d σ ih hx`.
-/
theorem isPt_pow {V : Fin g → ℂ} {x : N.Gt} (hx : d.IsPt σ V x) (n : ℕ) : d.IsPt σ ((n : ℂ) • V) (x ^ n) := by
  induction n with
  | zero => rw [Nat.cast_zero, zero_smul, pow_zero]; exact isPt_zero d σ
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul, pow_succ]
    exact Exp.IsPt.add d σ ih hx

/- English proof (translation)
Establish `a` using `hx.2 χ`. Establish `b` using `d.ψ_eq χ`. Establish `t` using `d.th (d.t12 *ᵥ co bX χ + zP σ W)`. Rewrite using `[NumD.vt, hx.1, d.c_eq, ← d.ex_add, t]`. Simplify using `only [CD.fj, add_zero, Units.val_mul]`.

Rewrite using `[dotProduct_add, add_comm (zP σ W)]`. Establish `e : Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ W + co bX χ ⬝ᵥ d.b2)) = Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ W)) * Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX χ) + 2 * Real.pi * …`. Rewrite using `[← Complex.exp_add]`. Put the polynomial expressions in normal form. Rewrite using `[e]`.

Take the linear combination `((N.ψ χ : ℂ) * d.c * thetaChar d.τ d.a d.b (d.t12 *ᵥ co bX χ + zP σ W)) * a + (d.c * thetaChar d.τ d.a d.b (d.t12 *ᵥ co bX χ + zP σ W) * Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ W)) * d.fr (zP σ W)) * b`.
-/
theorem vt_eq {W : Fin g → ℂ} {x : N.Gt} (hx : d.IsPt σ W x) (χ : N.X) :
    N.vt x χ = d.c * d.fj σ 0 χ W * d.fr (zP σ W) := by
  have a := hx.2 χ
  have b := d.ψ_eq χ
  have t := d.th (d.t12 *ᵥ co bX χ + zP σ W)
  rw [NumD.vt, hx.1, d.c_eq, ← d.ex_add, t]
  simp only [CD.fj, add_zero, Units.val_mul]
  rw [dotProduct_add, add_comm (zP σ W)]
  have e : Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX χ) +
      2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ W + co bX χ ⬝ᵥ d.b2)) =
      Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ W)) *
        Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ d.t22 *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ d.b2)) := by
    rw [← Complex.exp_add]; ring_nf
  rw [e]
  linear_combination ((N.ψ χ : ℂ) * d.c * thetaChar d.τ d.a d.b (d.t12 *ᵥ co bX χ + zP σ W)) * a +
    (d.c * thetaChar d.τ d.a d.b (d.t12 *ᵥ co bX χ + zP σ W) *
      Complex.exp (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ tP σ W)) * d.fr (zP σ W)) * b

end GlobalTheory.MBLow.Cl.Ev
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.Ev

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX)

/- English proof (translation)
Establish `h1` using `congrArg Units.val (mulq_fr d x k)`. Establish `h4 : (d.fr ((k : ℂ) • x + x) : ℂ) = d.fr (d.t12 *ᵥ co bX y + x) * Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ (d.t12 *ᵥ co bX y + x))) * d.fr (perV d.τ M' n')`. Rewrite using `[hkx, show perV d.τ M' n' + d.t12 *ᵥ co bX y + x = (d.t12 *ᵥ co bX y + x) + perV d.τ M' n' by abel, Exp.fr_shift]`. Establish `h5 : (d.fr ((k : ℂ) • x) : ℂ) = d.fr (d.t12 *ᵥ co bX y) * Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ d.t12 *ᵥ co bX y)) * d.fr (perV d.τ M' n')`. Rewrite using `[hkx, add_comm, Exp.fr_shift]`.

Establish `h6` using `d.ψ_eq y`. Establish `h7 : (d.fr (perV d.τ M' n') : ℂ) * autV d.τ d.a d.b M' n' 0 = 1`. Use `d.fr_per M' n' 0` as an intermediate fact. Rewrite `this` using `[d.fr_zero, zero_add, Units.val_one]`. Take the linear combination `-this`.

Establish `h2` using `congrArg Units.val (cubN_div d x k)`. Establish `ht : (k - 1) / 2 = t` using `by omega`. Rewrite using `[NumD.wQ, NumB.wS, hb, ht, hy, mul_div_assoc ((p : Multiplicative N.X × N.Gt).2.s y)]`. Generalize the expression as in `cubN N.θ k 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ k = C at h2 ⊢`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val] at h1 h2 ⊢`.

Use `set s : ℂ := ((p : Multiplicative N.X × N.Gt).2.s y : ℂ)`. Establish `hD : s * C * d.fr x ^ (2 * k) * Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ d.t12 *ᵥ co bX y)) = e4 * Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ (d.t12 *ᵥ co bX y + x)))`. Apply `mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (d.fr (d.t12 *ᵥ co bX y)).ne_zero (d.fr (perV d.τ M' n')).ne_zero) (d.fr x).ne_zero)` to reduce the goal to its premises. Take the linear combination `-(s * C * d.fr x ^ (2 * k) * d.fr x) * h5 + s * h2 + s * h4 + Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ (d.t12 *ᵥ co bX y + x))) * d.fr (perV d.τ M' n') * hs`. Rewrite using `[← hD]`.

Establish `hDne : s * C ≠ 0` using `mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)`. Rewrite using `[div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hDne), mul_pow, mul_pow, ← pow_mul]`. Establish `hk2 : (d.fr x : ℂ) ^ k * d.fr x ^ (2 * k * t) = d.fr x ^ (k ^ 2)`. Rewrite using `[← pow_add]`. Use `congr 1`.

Substitute `hk` using the available equality. Expand and normalize the polynomial expressions, which then agree. Use `set e3 := Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ d.t12 *ᵥ co bX y))`. Use `set e6 := Complex.exp (Real.pi * Complex.I * (co bX y ⬝ᵥ d.t22 *ᵥ co bX y) + 2 * Real.pi * Complex.I * (co bX y ⬝ᵥ d.b2))`. Use `set A0 := autV d.τ d.a d.b M' n' 0`.

Use `set mq := ((mulq N.θ N.σ k (d.ex x) : ℂˣ) : ℂ)`. Use `set ψ := (N.ψ y : ℂ)`. Take the linear combination `(ψ * (s * C) ^ t * e3 ^ t * A0 * mq) * hk2 + (ψ * (s * C) ^ t * e3 ^ t * A0) * h1 + (ψ * (s * C) ^ t * e3 ^ t * A0) * h5 + ((s * C) ^ t * e3 ^ (t + 1) * A0 * d.fr (perV d.τ M' n')) * h6 + (e6 * (s * C) ^ t * e3 ^ (t + 1)) * h7`.
-/
theorem wQ_core {k t : ℕ} (hk : k = 2 * t + 1) (p : N.QT k) (y : N.X)
    (hy : Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 = y) (x : Fin g' → ℂ) (M' n' : Fin g' → ℤ)
    (hb : (p : Multiplicative N.X × N.Gt).2.b = d.ex x)
    (hkx : (k : ℂ) • x = perV d.τ M' n' + d.t12 *ᵥ co bX y) (e4 : ℂ)
    (hs : ((p : Multiplicative N.X × N.Gt).2.s y : ℂ) * d.fr (d.t12 *ᵥ co bX y + x) =
      e4 * d.fr (d.t12 *ᵥ co bX y) * d.fr x) :
    (N.wQ p : ℂ) * d.fr x ^ k *
      ((e4 * Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ (d.t12 *ᵥ co bX y + x)))) ^ t * autV d.τ d.a d.b M' n' 0) =
      Complex.exp (Real.pi * Complex.I * (co bX y ⬝ᵥ d.t22 *ᵥ co bX y) + 2 * Real.pi * Complex.I * (co bX y ⬝ᵥ d.b2)) *
        Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ d.t12 *ᵥ co bX y)) ^ (t + 1) := by
  have h1 := congrArg Units.val (mulq_fr d x k)
  have h4 : (d.fr ((k : ℂ) • x + x) : ℂ) = d.fr (d.t12 *ᵥ co bX y + x) *
      Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ (d.t12 *ᵥ co bX y + x))) * d.fr (perV d.τ M' n') := by
    rw [hkx, show perV d.τ M' n' + d.t12 *ᵥ co bX y + x = (d.t12 *ᵥ co bX y + x) + perV d.τ M' n' by abel, Exp.fr_shift]
  have h5 : (d.fr ((k : ℂ) • x) : ℂ) = d.fr (d.t12 *ᵥ co bX y) *
      Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ d.t12 *ᵥ co bX y)) * d.fr (perV d.τ M' n') := by
    rw [hkx, add_comm, Exp.fr_shift]
  have h6 := d.ψ_eq y
  have h7 : (d.fr (perV d.τ M' n') : ℂ) * autV d.τ d.a d.b M' n' 0 = 1 := by
    have := d.fr_per M' n' 0
    rw [d.fr_zero, zero_add, Units.val_one] at this
    linear_combination -this
  have h2 := congrArg Units.val (cubN_div d x k)
  have ht : (k - 1) / 2 = t := by omega
  rw [NumD.wQ, NumB.wS, hb, ht, hy, mul_div_assoc ((p : Multiplicative N.X × N.Gt).2.s y)]
  generalize cubN N.θ k 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ k = C at h2 ⊢
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val] at h1 h2 ⊢
  set s : ℂ := ((p : Multiplicative N.X × N.Gt).2.s y : ℂ)
  have hD : s * C * d.fr x ^ (2 * k) * Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ d.t12 *ᵥ co bX y)) =
      e4 * Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ (d.t12 *ᵥ co bX y + x))) := by
    apply mul_right_cancel₀ (mul_ne_zero (mul_ne_zero (d.fr (d.t12 *ᵥ co bX y)).ne_zero
      (d.fr (perV d.τ M' n')).ne_zero) (d.fr x).ne_zero)
    linear_combination -(s * C * d.fr x ^ (2 * k) * d.fr x) * h5 + s * h2 + s * h4 +
      Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ (d.t12 *ᵥ co bX y + x))) * d.fr (perV d.τ M' n') * hs
  rw [← hD]
  have hDne : s * C ≠ 0 := mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff (pow_ne_zero _ hDne), mul_pow, mul_pow, ← pow_mul]
  have hk2 : (d.fr x : ℂ) ^ k * d.fr x ^ (2 * k * t) = d.fr x ^ (k ^ 2) := by
    rw [← pow_add]; congr 1; subst hk; ring
  set e3 := Complex.exp (2 * Real.pi * Complex.I * (cv n' ⬝ᵥ d.t12 *ᵥ co bX y))
  set e6 := Complex.exp (Real.pi * Complex.I * (co bX y ⬝ᵥ d.t22 *ᵥ co bX y) + 2 * Real.pi * Complex.I * (co bX y ⬝ᵥ d.b2))
  set A0 := autV d.τ d.a d.b M' n' 0
  set mq := ((mulq N.θ N.σ k (d.ex x) : ℂˣ) : ℂ)
  set ψ := (N.ψ y : ℂ)
  linear_combination (ψ * (s * C) ^ t * e3 ^ t * A0 * mq) * hk2 + (ψ * (s * C) ^ t * e3 ^ t * A0) * h1 +
    (ψ * (s * C) ^ t * e3 ^ t * A0) * h5 + ((s * C) ^ t * e3 ^ (t + 1) * A0 * d.fr (perV d.τ M' n')) * h6 +
    (e6 * (s * C) ^ t * e3 ^ (t + 1)) * h7

end GlobalTheory.MBLow.Cl.Ev
end

noncomputable section
namespace GlobalTheory.MBLow.Cl.Ev

variable {N : NumD ℂ} {g' r g : ℕ} {bX : Module.Basis (Fin r) ℤ N.X} (d : CD N g' r bX) (σ : Fin g ≃ Fin g' ⊕ Fin r)

/- English proof (translation)
Assemble the required witnesses or components as `⟨∑ i, u i * v i, by simp [cv, dotProduct]⟩`.
-/
theorem int_dot {k : ℕ} (u v : Fin k → ℤ) : ∃ n : ℤ, cv u ⬝ᵥ cv v = n :=
  ⟨∑ i, u i * v i, by simp [cv, dotProduct]⟩

/- English proof (translation)
Take `⟨hp1, hP⟩` from `hp`. Establish `hy : co bX (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) = cv (tP σ Nn)`. Rewrite using `[hp1]`. Conclude with `Exp.co_sum _`. Establish `m0 : (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (by rintro rfl; omega)`.

Establish `k0 : ((m ^ 2 : ℕ) : ℂ) ≠ 0` using `by push_cast; exact pow_ne_zero _ m0`. Use `set y := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hydef`. Use `set P := ((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hPdef`. Establish `hkx : ((m ^ 2 : ℕ) : ℂ) • zP σ P = perV d.τ (zP σ M) (zP σ Nn) + d.t12 *ᵥ co bX y`. Establish `: ((m ^ 2 : ℕ) : ℂ) • zP σ P = zP σ (perV (d.full σ 0) M Nn)`.

Rewrite using `[hPdef, show zP σ (((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn) = ((m ^ 2 : ℕ) : ℂ)⁻¹ • zP σ (perV (d.full σ 0) M Nn) from rfl, smul_inv_smul₀ k0]`. Rewrite using `[this, Exp.leftComponent_periodVector, hy]`. Establish `hcore` using `wQ_core d ht p y rfl (zP σ P) (zP σ M) (zP σ Nn) hP.1 hkx _ (hP.2 y)`. Use `mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))) (Complex.exp_ne_zero _)) (hcore.trans ?_)` and prove the remaining obligations. Establish `R1 : cv (zP σ Nn) ⬝ᵥ zP σ P + co bX y ⬝ᵥ tP σ P = ((m : ℂ) ^ 2)⁻¹ * (cv Nn ⬝ᵥ cv M + cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn)`.

Use `FJ.dot_split σ (cv Nn) P` as an intermediate fact. Rewrite `this` using `[Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy]`. Rewrite using `[← this, hPdef, dotProduct_smul, perV, dotProduct_add, smul_eq_mul]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `R2 : cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn = cv (zP σ Nn) ⬝ᵥ d.τ *ᵥ cv (zP σ Nn) + 2 * (cv (zP σ Nn) ⬝ᵥ d.t12 *ᵥ co bX y) + co bX y ⬝ᵥ d.t22 *ᵥ co bX y`. Rewrite using `[CD.full, FJ.quad_full, Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy, add_zero]`. Establish `R3a : d.aF σ ⬝ᵥ cv M = d.a ⬝ᵥ cv (zP σ M)`. Establish `h1 : zP σ (d.aF σ) = d.a` using `by funext i; simp [zP, CD.aF]`. Establish `h2 : tP σ (d.aF σ) = 0` using `by funext i; simp [tP, CD.aF]`.

Rewrite using `[FJ.dot_split σ, h1, h2, zero_dotProduct, add_zero, Exp.leftComponent_intCast]`. Establish `R3b : d.bF σ ⬝ᵥ cv Nn = d.b ⬝ᵥ cv (zP σ Nn) + co bX y ⬝ᵥ d.b2`. Establish `h1 : zP σ (d.bF σ) = d.b` using `by funext i; simp [zP, CD.bF]`. Establish `h2 : tP σ (d.bF σ) = d.b2` using `by funext i; simp [tP, CD.bF]`. Rewrite using `[FJ.dot_split σ, h1, h2, Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy, dotProduct_comm d.b2]`.

Take `⟨nL, hL⟩` from `int_dot Nn M`. Take `⟨nA, hA⟩` from `half_int (half_aF d σ) M`. Take `⟨nB, hB⟩` from `half_int (half_bF d σ) Nn`. Establish `hw : (m : ℂ) ^ 2 * ((m : ℂ) ^ 2)⁻¹ = 1` using `mul_inv_cancel₀ (pow_ne_zero _ m0)`. Establish `htc : (m : ℂ) ^ 2 = 2 * t + 1` using `by exact_mod_cast ht`.

Simplify using `only [autV, ← Complex.exp_add, ← Complex.exp_nat_mul, dotProduct_zero, mul_zero, sub_zero]`. Rewrite using `[Complex.exp_eq_exp_iff_exists_int]`. Use `⟨-(nL + nA - nB), ?_⟩` and prove the remaining obligations. Use `push_cast`. Simplify using `only [dotProduct_add]`.

Take the linear combination `-((2 * Real.pi * Complex.I * t) * R1 + (Real.pi * Complex.I) * R2 - (2 * Real.pi * Complex.I) * R3a + (2 * Real.pi * Complex.I) * R3b + (Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M + cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn)) * hw - (Real.pi * Complex.I * ((m : ℂ) ^ 2)⁻¹ * (cv Nn ⬝ᵥ cv M + cv Nn ⬝ᵥ …`.
-/
theorem wQ_fr {m t : ℕ} (ht : m ^ 2 = 2 * t + 1) (M Nn : Fin g → ℤ) (p : N.QT (m ^ 2)) (hp : d.Rep σ (m ^ 2) M Nn p) :
    (N.wQ p : ℂ) * d.fr (zP σ (((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn)) ^ (m ^ 2) =
      Complex.exp (Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M) + Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M) / (m : ℂ) ^ 2 +
        2 * Real.pi * Complex.I * (d.aF σ ⬝ᵥ cv M - d.bF σ ⬝ᵥ cv Nn) +
        Real.pi * Complex.I * (cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn) / (m : ℂ) ^ 2) := by
  obtain ⟨hp1, hP⟩ := hp
  have hy : co bX (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) = cv (tP σ Nn) := by
    rw [hp1]; exact Exp.co_sum _
  have m0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; omega)
  have k0 : ((m ^ 2 : ℕ) : ℂ) ≠ 0 := by push_cast; exact pow_ne_zero _ m0
  set y := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hydef
  set P := ((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hPdef
  have hkx : ((m ^ 2 : ℕ) : ℂ) • zP σ P = perV d.τ (zP σ M) (zP σ Nn) + d.t12 *ᵥ co bX y := by
    have : ((m ^ 2 : ℕ) : ℂ) • zP σ P = zP σ (perV (d.full σ 0) M Nn) := by
      rw [hPdef, show zP σ (((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn) =
        ((m ^ 2 : ℕ) : ℂ)⁻¹ • zP σ (perV (d.full σ 0) M Nn) from rfl, smul_inv_smul₀ k0]
    rw [this, Exp.leftComponent_periodVector, hy]
  have hcore := wQ_core d ht p y rfl (zP σ P) (zP σ M) (zP σ Nn) hP.1 hkx _ (hP.2 y)
  refine mul_right_cancel₀ (mul_ne_zero (pow_ne_zero _ (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)))
    (Complex.exp_ne_zero _)) (hcore.trans ?_)

  have R1 : cv (zP σ Nn) ⬝ᵥ zP σ P + co bX y ⬝ᵥ tP σ P =
      ((m : ℂ) ^ 2)⁻¹ * (cv Nn ⬝ᵥ cv M + cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn) := by
    have := FJ.dot_split σ (cv Nn) P
    rw [Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy] at this
    rw [← this, hPdef, dotProduct_smul, perV, dotProduct_add, smul_eq_mul]; push_cast; rfl
  have R2 : cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn = cv (zP σ Nn) ⬝ᵥ d.τ *ᵥ cv (zP σ Nn) +
      2 * (cv (zP σ Nn) ⬝ᵥ d.t12 *ᵥ co bX y) + co bX y ⬝ᵥ d.t22 *ᵥ co bX y := by
    rw [CD.full, FJ.quad_full, Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy, add_zero]
  have R3a : d.aF σ ⬝ᵥ cv M = d.a ⬝ᵥ cv (zP σ M) := by
    have h1 : zP σ (d.aF σ) = d.a := by funext i; simp [zP, CD.aF]
    have h2 : tP σ (d.aF σ) = 0 := by funext i; simp [tP, CD.aF]
    rw [FJ.dot_split σ, h1, h2, zero_dotProduct, add_zero, Exp.leftComponent_intCast]
  have R3b : d.bF σ ⬝ᵥ cv Nn = d.b ⬝ᵥ cv (zP σ Nn) + co bX y ⬝ᵥ d.b2 := by
    have h1 : zP σ (d.bF σ) = d.b := by funext i; simp [zP, CD.bF]
    have h2 : tP σ (d.bF σ) = d.b2 := by funext i; simp [tP, CD.bF]
    rw [FJ.dot_split σ, h1, h2, Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy, dotProduct_comm d.b2]
  obtain ⟨nL, hL⟩ := int_dot Nn M
  obtain ⟨nA, hA⟩ := half_int (half_aF d σ) M
  obtain ⟨nB, hB⟩ := half_int (half_bF d σ) Nn
  have hw : (m : ℂ) ^ 2 * ((m : ℂ) ^ 2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ m0)
  have htc : (m : ℂ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
  simp only [autV, ← Complex.exp_add, ← Complex.exp_nat_mul, dotProduct_zero, mul_zero, sub_zero]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(nL + nA - nB), ?_⟩
  push_cast
  simp only [dotProduct_add]
  linear_combination -((2 * Real.pi * Complex.I * t) * R1 + (Real.pi * Complex.I) * R2 - (2 * Real.pi * Complex.I) * R3a +
    (2 * Real.pi * Complex.I) * R3b +
    (Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M + cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn)) * hw -
    (Real.pi * Complex.I * ((m : ℂ) ^ 2)⁻¹ * (cv Nn ⬝ᵥ cv M + cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn)) * htc +
    (2 * Real.pi * Complex.I) * hL + (2 * Real.pi * Complex.I) * hA - (2 * Real.pi * Complex.I) * hB)

end GlobalTheory.MBLow.Cl.Ev
end

namespace GlobalTheory.MBLow.Cl

open Ev in

/- English proof (translation)
Introduce `N g' r g bX d σ m hm M Nn p hp Z h hZ χ`. Take `⟨t, ht⟩` from `hm.pow (n := 2)`. Establish `m0 : (m : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hm.pos.ne'`. Establish `k0 : ((m ^ 2 : ℕ) : ℂ) ≠ 0` using `by push_cast; exact pow_ne_zero _ m0`. Establish `hQ` using `wQ_fr d σ ht M Nn p hp`.

Establish `hy : co bX (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) = cv (tP σ Nn)`. Rewrite using `[hp.1]`. Conclude with `Exp.co_sum _`. Establish `hs` using `hZ.2 (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1)`. Establish `hW` using `isPt_pow d σ (Exp.IsPt.add d σ hZ hp.2) m`.

Establish `hv` using `vt_eq d σ hW χ`. Establish `hpb` using `hp.2.1`. Use `set y := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hydef`. Use `set P := ((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hPdef`. Establish `hkx : ((m ^ 2 : ℕ) : ℂ) • zP σ P = perV d.τ (zP σ M) (zP σ Nn) + d.t12 *ᵥ co bX y`.

Establish `: ((m ^ 2 : ℕ) : ℂ) • zP σ P = zP σ (perV (d.full σ 0) M Nn)`. Rewrite using `[hPdef, show zP σ (((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn) = ((m ^ 2 : ℕ) : ℂ)⁻¹ • zP σ (perV (d.full σ 0) M Nn) from rfl, smul_inv_smul₀ k0]`. Rewrite using `[this, Exp.leftComponent_periodVector, hy]`. Establish `hWeq : (m : ℂ) • (Z + P) = (m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ 0) M Nn`. Rewrite using `[hPdef, smul_add, smul_smul]`.

Use `congr 2`. Use `push_cast`. Rewrite using `[sq, mul_inv, ← _root_.mul_assoc, mul_inv_cancel₀ m0, _root_.one_mul]`. Establish `hz' : zP σ ((m : ℂ) • (Z + P)) = (m : ℂ) • (zP σ Z + zP σ P)` using `rfl`. Establish `hmq` using `congrArg Units.val (mulq_fr d (zP σ Z + zP σ P) m)`.

Establish `hcub` using `congrArg Units.val (cubN_fr d (m ^ 2) (zP σ P) (zP σ Z))`. Rewrite `hcub` using `[add_comm (zP σ P) (zP σ Z)]`. Establish `hd : (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P + zP σ Z) : ℂ) = d.fr (d.t12 *ᵥ co bX y + zP σ Z) * Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ (d.t12 *ᵥ co bX y + zP σ Z))) * d.fr (perV d.τ (zP σ M) (zP σ Nn))`. Rewrite using `[hkx, show perV d.τ (zP σ M) (zP σ Nn) + d.t12 *ᵥ co bX y + zP σ Z = (d.t12 *ᵥ co bX y + zP σ Z) + perV d.τ (zP σ M) (zP σ Nn) by abel, Exp.fr_shift]`. Establish `he : (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P) : ℂ) = d.fr (d.t12 *ᵥ co bX y) * Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ d.t12 *ᵥ co bX y)) * d.fr (perV d.τ (zP σ M) (zP σ Nn))`.

Rewrite using `[hkx, add_comm, Exp.fr_shift]`. Use `set E := Complex.exp (Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M) + Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M) / (m : ℂ) ^ 2 + 2 * Real.pi * Complex.I * (d.aF σ ⬝ᵥ cv M - d.bF σ ⬝ᵥ cv Nn) + Real.pi * Complex.I * (cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn) / (m : ℂ) ^ 2) with hEdef`. Establish `hg : Complex.exp (2 * Real.pi * Complex.I * (co bX y ⬝ᵥ tP σ Z)) * Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ (d.t12 *ᵥ co bX y + zP σ Z))) * E = trFac (d.full σ 0) (d.aF σ) (d.bF σ) m M Nn Z * Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ d.t12 *ᵥ co bX y) …`. Rewrite using `[hEdef, trFac]`. Simplify using `only [← Complex.exp_add]`.

Use `congr 1`. Use `FJ.dot_split σ (cv Nn) Z` as an intermediate fact. Rewrite `this` using `[Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy]`. Rewrite using `[this, dotProduct_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[NumD.evT, hv, CD.term, ← hWeq, hz', hZ.1, hpb, ← d.ex_add]`. Simplify using `only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at hmq hcub ⊢`. Rewrite using `[div_mul_eq_mul_div, div_eq_iff (Units.ne_zero _)]`. Apply `mul_right_cancel₀ (mul_ne_zero (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P)).ne_zero (d.fr (zP σ Z)).ne_zero)` to reduce the goal to its premises. Use `set s := (h.s y : ℂ)`.

Use `set C := ((cubN N.θ (m ^ 2) 1 (d.ex (zP σ P)) (d.ex (zP σ Z)) : ℂˣ) : ℂ)`. Use `set w := (N.wQ p : ℂ)`. Use `set mq := ((mulq N.θ N.σ m (d.ex (zP σ Z + zP σ P)) : ℂˣ) : ℂ)`. Use `set Fkx := (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P) : ℂ)`. Use `set Fkxz := (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P + zP σ Z) : ℂ)`.

Use `set Fz := (d.fr (zP σ Z) : ℂ)`. Use `set Fp := (d.fr (perV d.τ (zP σ M) (zP σ Nn)) : ℂ)`. Use `set F2 := (d.fr (d.t12 *ᵥ co bX y) : ℂ)`. Use `set e2 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ (d.t12 *ᵥ co bX y + zP σ Z)))`. Use `set T := trFac (d.full σ 0) (d.aF σ) (d.bF σ) m M Nn Z`.

Use `set f := d.fj σ 0 χ ((m : ℂ) • (Z + P))`. Take the linear combination `(d.c * f) * (-(s * C * w * Fkx * Fz) * hmq + mq * (s * w * hcub + s * Fkxz * Fz ^ (m ^ 2) * hQ + s * Fz ^ (m ^ 2) * E * hd + Fz ^ (m ^ 2) * E * e2 * Fp * hs + Fz ^ (m ^ 2) * Fp * F2 * Fz * hg - Fz ^ (m ^ 2) * T * Fz * he))`.
-/
theorem evT_eq_term : AllCD fun {N} {g'} {r} {g} {bX} d σ => ∀ m : ℕ, Odd m → ∀ M Nn (p : N.QT (m ^ 2)),
    d.Rep σ (m ^ 2) M Nn p → ∀ Z h, d.IsPt σ Z h → ∀ χ,
      N.evT m p h χ = d.c * (d.fr (zP σ Z) : ℂ) ^ (m ^ 2) * d.term σ 0 m M Nn χ Z := by
  intro N g' r g bX d σ m hm M Nn p hp Z h hZ χ
  obtain ⟨t, ht⟩ := hm.pow (n := 2)
  have m0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.pos.ne'
  have k0 : ((m ^ 2 : ℕ) : ℂ) ≠ 0 := by push_cast; exact pow_ne_zero _ m0
  have hQ := wQ_fr d σ ht M Nn p hp
  have hy : co bX (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1) = cv (tP σ Nn) := by
    rw [hp.1]; exact Exp.co_sum _
  have hs := hZ.2 (Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1)
  have hW := isPt_pow d σ (Exp.IsPt.add d σ hZ hp.2) m
  have hv := vt_eq d σ hW χ
  have hpb := hp.2.1
  set y := Multiplicative.toAdd (p : Multiplicative N.X × N.Gt).1 with hydef
  set P := ((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn with hPdef
  have hkx : ((m ^ 2 : ℕ) : ℂ) • zP σ P = perV d.τ (zP σ M) (zP σ Nn) + d.t12 *ᵥ co bX y := by
    have : ((m ^ 2 : ℕ) : ℂ) • zP σ P = zP σ (perV (d.full σ 0) M Nn) := by
      rw [hPdef, show zP σ (((m ^ 2 : ℕ) : ℂ)⁻¹ • perV (d.full σ 0) M Nn) =
        ((m ^ 2 : ℕ) : ℂ)⁻¹ • zP σ (perV (d.full σ 0) M Nn) from rfl, smul_inv_smul₀ k0]
    rw [this, Exp.leftComponent_periodVector, hy]
  have hWeq : (m : ℂ) • (Z + P) = (m : ℂ) • Z + (m : ℂ)⁻¹ • perV (d.full σ 0) M Nn := by
    rw [hPdef, smul_add, smul_smul]
    congr 2
    push_cast
    rw [sq, mul_inv, ← _root_.mul_assoc, mul_inv_cancel₀ m0, _root_.one_mul]
  have hz' : zP σ ((m : ℂ) • (Z + P)) = (m : ℂ) • (zP σ Z + zP σ P) := rfl
  have hmq := congrArg Units.val (mulq_fr d (zP σ Z + zP σ P) m)
  have hcub := congrArg Units.val (cubN_fr d (m ^ 2) (zP σ P) (zP σ Z))
  rw [add_comm (zP σ P) (zP σ Z)] at hcub
  have hd : (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P + zP σ Z) : ℂ) = d.fr (d.t12 *ᵥ co bX y + zP σ Z) *
      Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ (d.t12 *ᵥ co bX y + zP σ Z))) *
      d.fr (perV d.τ (zP σ M) (zP σ Nn)) := by
    rw [hkx, show perV d.τ (zP σ M) (zP σ Nn) + d.t12 *ᵥ co bX y + zP σ Z =
      (d.t12 *ᵥ co bX y + zP σ Z) + perV d.τ (zP σ M) (zP σ Nn) by abel, Exp.fr_shift]
  have he : (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P) : ℂ) = d.fr (d.t12 *ᵥ co bX y) *
      Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ d.t12 *ᵥ co bX y)) * d.fr (perV d.τ (zP σ M) (zP σ Nn)) := by
    rw [hkx, add_comm, Exp.fr_shift]
  set E := Complex.exp (Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M) + Real.pi * Complex.I * (cv Nn ⬝ᵥ cv M) / (m : ℂ) ^ 2 +
        2 * Real.pi * Complex.I * (d.aF σ ⬝ᵥ cv M - d.bF σ ⬝ᵥ cv Nn) +
        Real.pi * Complex.I * (cv Nn ⬝ᵥ d.full σ 0 *ᵥ cv Nn) / (m : ℂ) ^ 2) with hEdef
  have hg : Complex.exp (2 * Real.pi * Complex.I * (co bX y ⬝ᵥ tP σ Z)) *
      Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ (d.t12 *ᵥ co bX y + zP σ Z))) * E =
      trFac (d.full σ 0) (d.aF σ) (d.bF σ) m M Nn Z *
        Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ d.t12 *ᵥ co bX y)) := by
    rw [hEdef, trFac]
    simp only [← Complex.exp_add]
    congr 1
    have := FJ.dot_split σ (cv Nn) Z
    rw [Exp.leftComponent_intCast, Exp.secondBlock_intCast, ← hy] at this
    rw [this, dotProduct_add]
    ring
  rw [NumD.evT, hv, CD.term, ← hWeq, hz', hZ.1, hpb, ← d.ex_add]
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val] at hmq hcub ⊢
  rw [div_mul_eq_mul_div, div_eq_iff (Units.ne_zero _)]
  apply mul_right_cancel₀ (mul_ne_zero (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P)).ne_zero (d.fr (zP σ Z)).ne_zero)
  set s := (h.s y : ℂ)
  set C := ((cubN N.θ (m ^ 2) 1 (d.ex (zP σ P)) (d.ex (zP σ Z)) : ℂˣ) : ℂ)
  set w := (N.wQ p : ℂ)
  set mq := ((mulq N.θ N.σ m (d.ex (zP σ Z + zP σ P)) : ℂˣ) : ℂ)
  set Fkx := (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P) : ℂ)
  set Fkxz := (d.fr (((m ^ 2 : ℕ) : ℂ) • zP σ P + zP σ Z) : ℂ)
  set Fz := (d.fr (zP σ Z) : ℂ)
  set Fp := (d.fr (perV d.τ (zP σ M) (zP σ Nn)) : ℂ)
  set F2 := (d.fr (d.t12 *ᵥ co bX y) : ℂ)
  set e2 := Complex.exp (2 * Real.pi * Complex.I * (cv (zP σ Nn) ⬝ᵥ (d.t12 *ᵥ co bX y + zP σ Z)))
  set T := trFac (d.full σ 0) (d.aF σ) (d.bF σ) m M Nn Z
  set f := d.fj σ 0 χ ((m : ℂ) • (Z + P))
  linear_combination (d.c * f) * (-(s * C * w * Fkx * Fz) * hmq + mq * (s * w * hcub + s * Fkxz * Fz ^ (m ^ 2) * hQ +
    s * Fz ^ (m ^ 2) * E * hd + Fz ^ (m ^ 2) * E * e2 * Fp * hs + Fz ^ (m ^ 2) * Fp * F2 * Fz * hg -
    Fz ^ (m ^ 2) * T * Fz * he))

end GlobalTheory.MBLow.Cl
