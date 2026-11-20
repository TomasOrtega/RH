import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementF

universe u

namespace Formalism.L2.Th1.A

namespace IsDer

variable {A : Type u} [CommRing A] {D : A → A}

/- English proof (translation)
The claim follows from `h.1 a b`.
-/
theorem map_add (h : IsDer D) (a b : A) : D (a + b) = D a + D b := h.1 a b

/- English proof (translation)
The claim follows from `h.2 a b`.
-/
theorem map_mul (h : IsDer D) (a b : A) : D (a * b) = a * D b + b * D a := h.2 a b

/- English proof (translation)
Establish `h0` using `h.1 0 0`. Rewrite `h0` using `[add_zero]`. Take the linear combination `-h0`.
-/
theorem map_zero (h : IsDer D) : D 0 = 0 := by
  have h0 := h.1 0 0
  rw [add_zero] at h0
  linear_combination -h0

/- English proof (translation)
Establish `h1` using `h.2 1 1`. Rewrite `h1` using `[show (1 : A) * 1 = 1 by ring]`. Take the linear combination `-h1`.
-/
theorem map_one (h : IsDer D) : D 1 = 0 := by
  have h1 := h.2 1 1
  rw [show (1 : A) * 1 = 1 by ring] at h1
  linear_combination -h1

/- English proof (translation)
Establish `h1` using `h.1 a (-a)`. Rewrite `h1` using `[show a + -a = 0 by ring, h.map_zero]`. Take the linear combination `-h1`.
-/
theorem map_neg (h : IsDer D) (a : A) : D (-a) = -D a := by
  have h1 := h.1 a (-a)
  rw [show a + -a = 0 by ring, h.map_zero] at h1
  linear_combination -h1

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, h.map_add, h.map_neg, ← sub_eq_add_neg]`.
-/
theorem map_sub (h : IsDer D) (a b : A) : D (a - b) = D a - D b := by
  rw [sub_eq_add_neg, h.map_add, h.map_neg, ← sub_eq_add_neg]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero]`. Conclude with `h.map_zero`. Consider the case `succ n ih => rw [Nat.cast_succ, h.map_add, ih, h.map_one, add_zero]`.
-/
theorem map_natCast (h : IsDer D) (n : ℕ) : D (n : A) = 0 := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact h.map_zero
  | succ n ih => rw [Nat.cast_succ, h.map_add, ih, h.map_one, add_zero]

/- English proof (translation)
Break down `n with n | n` into its components or cases. Rewrite using `[Int.ofNat_eq_coe, Int.cast_natCast]`. Conclude with `h.map_natCast n`. Rewrite using `[Int.cast_negSucc, h.map_neg, h.map_natCast, neg_zero]`.
-/
theorem map_intCast (h : IsDer D) (n : ℤ) : D (n : A) = 0 := by
  rcases n with n | n
  · rw [Int.ofNat_eq_coe, Int.cast_natCast]
    exact h.map_natCast n
  · rw [Int.cast_negSucc, h.map_neg, h.map_natCast, neg_zero]

/- English proof (translation)
Establish `h1` using `h.map_natCast (OfNat.ofNat n)`. Rewrite `h1` using `[Nat.cast_ofNat]`. Then use the resulting hypothesis.
-/
theorem map_ofNat (h : IsDer D) (n : ℕ) [n.AtLeastTwo] : D (OfNat.ofNat n : A) = 0 := by
  have h1 := h.map_natCast (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at h1

/- English proof (translation)
Rewrite using `[pow_two, h.map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_sq (h : IsDer D) (a : A) : D (a ^ 2) = 2 * a * D a := by
  rw [pow_two, h.map_mul]
  ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, h.map_mul, ih]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_pow_succ (h : IsDer D) (a : A) (n : ℕ) :
    D (a ^ (n + 1)) = (n + 1 : A) * a ^ n * D a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, h.map_mul, ih]
    push_cast
    ring

/- English proof (translation)
Break down `n with _ | n` into its components or cases. Rewrite using `[pow_zero, h.map_one, Nat.cast_zero, zero_mul, zero_mul]`. Rewrite using `[h.map_pow_succ, Nat.add_sub_cancel]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem map_pow (h : IsDer D) (a : A) (n : ℕ) : D (a ^ n) = (n : A) * a ^ (n - 1) * D a := by
  rcases n with _ | n
  · rw [pow_zero, h.map_one, Nat.cast_zero, zero_mul, zero_mul]
  · rw [h.map_pow_succ, Nat.add_sub_cancel]
    push_cast
    ring

/- English proof (translation)
Establish `h2` using `h.2 v w`. Rewrite `h2` using `[hvw, h.map_one]`. Take the linear combination `(-D v) * hvw - v * h2`.
-/
theorem map_of_mul_eq_one (h : IsDer D) {v w : A} (hvw : v * w = 1) : D v = -v ^ 2 * D w := by
  have h2 := h.2 v w
  rw [hvw, h.map_one] at h2
  linear_combination (-D v) * hvw - v * h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b => by show -D (a + b) = -D a + -D b rw [h.map_add] ring, fun a b => by show -D (a * b) = a * -D b + b * -D a rw [h.map_mul] ring⟩`.
-/
theorem neg (h : IsDer D) : IsDer (fun a => -D a) :=
  ⟨fun a b => by
    show -D (a + b) = -D a + -D b
    rw [h.map_add]
    ring,
   fun a b => by
    show -D (a * b) = a * -D b + b * -D a
    rw [h.map_mul]
    ring⟩

def toDerivation (h : IsDer D) : Derivation ℤ A A :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap ⟨⟨D, h.map_zero⟩, h.1⟩) fun a b => by
    simpa [smul_eq_mul] using h.2 a b

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem toDerivation_apply (h : IsDer D) (a : A) : h.toDerivation a = D a := rfl

end IsDer

/- English proof (translation)
Introduce `A _ W D u w v h hF hvw`. Take `⟨hW, hDu, hDw⟩` from `hF`. Unfold `WEq at hW`. Establish `hDv : D v = -v ^ 2 * fuAt W u w` using `by rw [h.map_of_mul_eq_one hvw, hDw]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[WeierstrassCurve.Affine.equation_iff]`. Take the linear combination `((-1) * v^2 + (1) * W.a₁ * u * v^2 + (1) * W.a₃ * v + (1) * W.a₃ * w * v^2 + (1) * W.a₂ * u^2 * v^2 + (1) * W.a₄ * u * v + (1) * W.a₄ * u * w * v^2 + (1) * W.a₆ + (1) * W.a₆ * w * v + (1) * W.a₆ * w^2 * v^2) * hvw + ((1) * v^3) * hW`. Rewrite using `[h.map_mul, hDv, hDu]`. Simplify using `only [fwAt, fuAt]`. Take the linear combination `((-3) * v + (2) * W.a₁ * u * v + (1) * W.a₂ * u^2 * v + (3) * W.a₃ * w * v + (2) * W.a₄ * u * w * v + (3) * W.a₆ * w^2 * v + (1) * W.a₃) * hvw + ((3) * v^2) * hW`.

Rewrite using `[h.map_neg, hDv]`. Simplify using `only [fuAt]`. Take the linear combination `((2) * W.a₂ * u * v + (1) * W.a₄ + (1) * W.a₄ * w * v + (1) * W.a₁ * v) * hvw`.
-/
theorem chartFlowToFlow : FlowOfUW.{u} := by
  intro A _ W D u w v h hF hvw
  obtain ⟨hW, hDu, hDw⟩ := hF
  unfold WEq at hW
  have hDv : D v = -v ^ 2 * fuAt W u w := by rw [h.map_of_mul_eq_one hvw, hDw]
  refine ⟨?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.equation_iff]
    linear_combination ((-1) * v^2 + (1) * W.a₁ * u * v^2 + (1) * W.a₃ * v + (1) * W.a₃ * w * v^2 + (1) * W.a₂ * u^2 * v^2 + (1) * W.a₄ * u * v + (1) * W.a₄ * u * w * v^2 + (1) * W.a₆ + (1) * W.a₆ * w * v + (1) * W.a₆ * w^2 * v^2) * hvw + ((1) * v^3) * hW
  · rw [h.map_mul, hDv, hDu]
    simp only [fwAt, fuAt]
    linear_combination ((-3) * v + (2) * W.a₁ * u * v + (1) * W.a₂ * u^2 * v + (3) * W.a₃ * w * v + (2) * W.a₄ * u * w * v + (3) * W.a₆ * w^2 * v + (1) * W.a₃) * hvw + ((3) * v^2) * hW
  · rw [h.map_neg, hDv]
    simp only [fuAt]
    linear_combination ((2) * W.a₂ * u * v + (1) * W.a₄ + (1) * W.a₄ * w * v + (1) * W.a₁ * v) * hvw

/- English proof (translation)
Introduce `A _ W D x y h hC hF`. Take `⟨c1, c2, c3, c4, c6⟩` from `hC`. Take `⟨hE, hDx, hDy⟩` from `hF`. Rewrite `hE` using `[WeierstrassCurve.Affine.equation_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hDx, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`. Take the linear combination `4 * hE`. Rewrite using `[hDx]`. Simplify using `only [h.map_add, h.map_mul, h.map_ofNat, c1, c3, hDx, hDy]`. Rewrite using `[WeierstrassCurve.b₂, WeierstrassCurve.b₄]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem flowDifferentialEquation : FlowSq.{u} := by
  intro A _ W D x y h hC hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hE, hDx, hDy⟩ := hF
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  refine ⟨?_, ?_⟩
  · rw [hDx, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    linear_combination 4 * hE
  · rw [hDx]
    simp only [h.map_add, h.map_mul, h.map_ofNat, c1, c3, hDx, hDy]
    rw [WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring

/- English proof (translation)
Introduce `A _ W D x y c g2 g3 h hC hF hu6 h12c h12g2 h216g3`. Take `⟨hsq1, hsq2⟩` from `flowDifferentialEquation A W D x y h hC hF`. Take `⟨c1, c2, c3, c4, c6⟩` from `hC`. Take `⟨hE, hDx, hDy⟩` from `hF`. Take `⟨s, hs⟩` from `hu6.exists_right_inv`.

Establish `hb` using `congrArg D h12c`. Simplify using `only [WeierstrassCurve.b₂, h.map_add, h.map_mul, h.map_sq, h.map_ofNat, c1, c2] at hb`. Establish `h12 : 12 * D c = 0` using `by linear_combination hb`. Establish `hDc : D c = 0` using `by linear_combination (-(6 * s + 1) * D c) * hs + 3 * s ^ 2 * h12`. Establish `hDxc : D (x + c) = D x` using `by rw [h.map_add, hDc, add_zero]`.

Rewrite `h12g2` using `[WeierstrassCurve.c₄]`. Rewrite `h216g3` using `[WeierstrassCurve.c₆]`. Establish `hb4 : 2 * W.b₄ = 12 * c ^ 2 - g2`. Take the linear combination `(-(6 * s + 1) * (2 * W.b₄ - (12 * c ^ 2 - g2))) * hs + 3 * s ^ 2 * h12g2 - 3 * s ^ 2 * (12 * c + W.b₂) * h12c`. Establish `hb6 : W.b₆ = -g3 + 4 * c ^ 3 - c * g2`.

Take the linear combination `(-(36 * s ^ 2 + 6 * s + 1) * (W.b₆ - (-g3 + 4 * c ^ 3 - c * g2))) * hs + s ^ 3 * (h216g3 + (144 * c ^ 2 + 12 * c * W.b₂ + W.b₂ ^ 2 - 36 * W.b₄) * h12c + 216 * c * hb4)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hDxc, hDx]`. Rewrite using `[hDxc]`. Take the linear combination `hsq1 - x ^ 2 * h12c + x * hb4 + hb6`.

Rewrite using `[hDxc]`. Take the linear combination `2 * hsq2 - 2 * x * h12c + hb4`.
-/
theorem flowWeierstrassForm : FlowWp.{u} := by
  intro A _ W D x y c g2 g3 h hC hF hu6 h12c h12g2 h216g3
  obtain ⟨hsq1, hsq2⟩ := flowDifferentialEquation A W D x y h hC hF
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hE, hDx, hDy⟩ := hF
  obtain ⟨s, hs⟩ := hu6.exists_right_inv
  have hb := congrArg D h12c
  simp only [WeierstrassCurve.b₂, h.map_add, h.map_mul, h.map_sq, h.map_ofNat, c1, c2] at hb
  have h12 : 12 * D c = 0 := by linear_combination hb
  have hDc : D c = 0 := by linear_combination (-(6 * s + 1) * D c) * hs + 3 * s ^ 2 * h12
  have hDxc : D (x + c) = D x := by rw [h.map_add, hDc, add_zero]
  rw [WeierstrassCurve.c₄] at h12g2
  rw [WeierstrassCurve.c₆] at h216g3
  have hb4 : 2 * W.b₄ = 12 * c ^ 2 - g2 := by
    linear_combination (-(6 * s + 1) * (2 * W.b₄ - (12 * c ^ 2 - g2))) * hs + 3 * s ^ 2 * h12g2
      - 3 * s ^ 2 * (12 * c + W.b₂) * h12c
  have hb6 : W.b₆ = -g3 + 4 * c ^ 3 - c * g2 := by
    linear_combination (-(36 * s ^ 2 + 6 * s + 1) * (W.b₆ - (-g3 + 4 * c ^ 3 - c * g2))) * hs
      + s ^ 3 * (h216g3 + (144 * c ^ 2 + 12 * c * W.b₂ + W.b₂ ^ 2 - 36 * W.b₄) * h12c
        + 216 * c * hb4)
  refine ⟨?_, ?_, ?_⟩
  · rw [hDxc, hDx]
  · rw [hDxc]
    linear_combination hsq1 - x ^ 2 * h12c + x * hb4 + hb6
  · rw [hDxc]
    linear_combination 2 * hsq2 - 2 * x * h12c + hb4

/- English proof (translation)
Introduce `A _ W D u w r h hC hF hr`. Take `⟨c1, c2, c3, c4, c6⟩` from `hC`. Take `⟨hW, hDu, hDw⟩` from `hF`. Unfold `WEq at hW`. Establish `hDq : D (-1 + W.a₁ * u + W.a₃ * w) = W.a₁ * fwAt W u w + W.a₃ * fuAt W u w`.

Simplify using `only [h.map_add, h.map_neg, h.map_one, h.map_mul, c1, c3, hDu, hDw]`. Expand and normalize the polynomial expressions, which then agree. Establish `hDr : D r = -r ^ 2 * (W.a₁ * fwAt W u w + W.a₃ * fuAt W u w)`. Rewrite using `[h.map_of_mul_eq_one hr, hDq]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `WEq`. Take the linear combination `((-1) * w * r + (1) * w * r^2) * hr + ((1) * r^3) * hW`. Use `show -D (u * r) = fwAt W (u * r) (w * r)`. Rewrite using `[h.map_mul, hDr, hDu]`. Simplify using `only [fwAt, fuAt]`.

Take the linear combination `((-1) * W.a₁ * u * r + (-1) * W.a₂ * u^2 * r + (-3) * W.a₃ * w * r + (-2) * W.a₄ * u * w * r + (-3) * W.a₆ * w^2 * r + (1) * 1) * hr + ((-3) * W.a₃ * r^2) * hW`. Use `show -D (w * r) = fuAt W (u * r) (w * r)`. Rewrite using `[h.map_mul, hDr, hDw]`. Simplify using `only [fwAt, fuAt]`. Take the linear combination `((3) * u^2 * r + (2) * W.a₁ * w * r + (2) * W.a₂ * u * w * r + (1) * W.a₄ * w^2 * r) * hr + ((3) * W.a₁ * r^2) * hW`.
-/
theorem chartFlowNegation : FlowNegUW.{u} := by
  intro A _ W D u w r h hC hF hr
  obtain ⟨c1, c2, c3, c4, c6⟩ := hC
  obtain ⟨hW, hDu, hDw⟩ := hF
  unfold WEq at hW
  have hDq : D (-1 + W.a₁ * u + W.a₃ * w) = W.a₁ * fwAt W u w + W.a₃ * fuAt W u w := by
    simp only [h.map_add, h.map_neg, h.map_one, h.map_mul, c1, c3, hDu, hDw]
    ring
  have hDr : D r = -r ^ 2 * (W.a₁ * fwAt W u w + W.a₃ * fuAt W u w) := by
    rw [h.map_of_mul_eq_one hr, hDq]
  refine ⟨?_, ?_, ?_⟩
  · unfold WEq
    linear_combination ((-1) * w * r + (1) * w * r^2) * hr + ((1) * r^3) * hW
  · show -D (u * r) = fwAt W (u * r) (w * r)
    rw [h.map_mul, hDr, hDu]
    simp only [fwAt, fuAt]
    linear_combination ((-1) * W.a₁ * u * r + (-1) * W.a₂ * u^2 * r + (-3) * W.a₃ * w * r + (-2) * W.a₄ * u * w * r + (-3) * W.a₆ * w^2 * r + (1) * 1) * hr + ((-3) * W.a₃ * r^2) * hW
  · show -D (w * r) = fuAt W (u * r) (w * r)
    rw [h.map_mul, hDr, hDw]
    simp only [fwAt, fuAt]
    linear_combination ((3) * u^2 * r + (2) * W.a₁ * w * r + (2) * W.a₂ * u * w * r + (1) * W.a₄ * w^2 * r) * hr + ((3) * W.a₁ * r^2) * hW

/- English proof (translation)
Introduce `A _ W x y xP yP t h1 h2 ht`. Rewrite `h1`, `h2` using `[WeierstrassCurve.Affine.equation_iff]`. Establish `hX : W.toAffine.addX x xP ((y - yP) * t) = xP + ((W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * x - (2 * yP + W.a₁ * xP + W.a₃) * y + (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3)) * t ^ 2`. Simplify using `only [WeierstrassCurve.Affine.addX]`. Take the linear combination `t ^ 2 * h1 + t ^ 2 * h2 - (W.a₁ * (y - yP) * t - (W.a₂ + x + 2 * xP) * (1 + t * (x - xP))) * ht`.

Use `⟨hX, ?_⟩` and prove the remaining obligations. Simplify using `only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.negY]`. Take the linear combination `(y - yP) * ht`.
-/
theorem chordFormula : ChordRegular.{u} := by
  intro A _ W x y xP yP t h1 h2 ht
  rw [WeierstrassCurve.Affine.equation_iff] at h1 h2
  have hX : W.toAffine.addX x xP ((y - yP) * t) = xP +
      ((W.a₄ - W.a₁ * yP + 2 * W.a₂ * xP + 3 * xP ^ 2) * x - (2 * yP + W.a₁ * xP + W.a₃) * y
        + (2 * W.a₆ + W.a₄ * xP - W.a₃ * yP - xP ^ 3)) * t ^ 2 := by
    simp only [WeierstrassCurve.Affine.addX]
    linear_combination t ^ 2 * h1 + t ^ 2 * h2
      - (W.a₁ * (y - yP) * t - (W.a₂ + x + 2 * xP) * (1 + t * (x - xP))) * ht
  refine ⟨hX, ?_⟩
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY]
  linear_combination (y - yP) * ht

end Formalism.L2.Th1.A
