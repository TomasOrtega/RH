import Mathlib

namespace GlobalTheory

open WeierstrassCurve WeierstrassCurve.Affine

/- English proof (translation)
Distinguish the cases in `hP : P = 0`. Simplify using `[hP, h0]`. Distinguish the cases in `hQ : Q = 0`. Simplify using `[hQ, h0]`. Distinguish the cases in `hR : P + Q = 0`.

Establish `: P = -Q` using `eq_neg_of_add_eq_zero_left hR`. Rewrite using `[hR, h0, this, hneg, neg_add_cancel]`. Use `h3 P Q (-(P + Q)) hP hQ (neg_ne_zero.mpr hR) (add_neg_cancel _)` as an intermediate fact. Rewrite `this` using `[hneg]`. Conclude with `(add_neg_eq_zero.mp this).symm`.
-/
theorem map_add_of_triples {A B : Type*} [AddCommGroup A] [AddCommGroup B] (f : A → B)
    (h0 : f 0 = 0) (hneg : ∀ P, f (-P) = -f P)
    (h3 : ∀ P Q R, P ≠ 0 → Q ≠ 0 → R ≠ 0 → P + Q + R = 0 → f P + f Q + f R = 0) (P Q : A) :
    f (P + Q) = f P + f Q := by
  by_cases hP : P = 0
  · simp [hP, h0]
  by_cases hQ : Q = 0
  · simp [hQ, h0]
  by_cases hR : P + Q = 0
  · have : P = -Q := eq_neg_of_add_eq_zero_left hR
    rw [hR, h0, this, hneg, neg_add_cancel]
  have := h3 P Q (-(P + Q)) hP hQ (neg_ne_zero.mpr hR) (add_neg_cancel _)
  rw [hneg] at this
  exact (add_neg_eq_zero.mp this).symm

variable {k : Type*} [Field k] [DecidableEq k] {W : Affine k}

/- English proof (translation)
Establish `key : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) ∧ W.slope x₁ x₂ y₁ y₂ = l`. Distinguish the cases in `hx : x₁ = x₂`. Substitute `hx` using the available equality. Establish `hy : y₁ = y₂` using `e₁.trans e₂.symm`. Substitute `hy` using the available equality.

Establish `ht : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ = l * (y₁ - W.negY x₁ y₁)`. Rewrite using `[negY]`. Take the linear combination `(2 * x₁) * s₁ - s₂ - (W.a₁ + 2 * l) * e₁`. Establish `hne : y₁ ≠ W.negY x₁ y₁`. Introduce `h`.

Rewrite `h₁` using `[nonsingular_iff]`. Break down `h₁.2 with h' | h'` into its components or cases. Apply `h'` to reduce the goal to its premises. Rewrite `ht` using `[← h, sub_self, mul_zero]`. Take the linear combination `-ht`.

Conclude with `h' h`. Use `⟨fun h => hne h.2, ?_⟩` and prove the remaining obligations. Rewrite using `[slope_of_Y_ne rfl hne, ht, mul_div_assoc, div_self (sub_ne_zero.mpr hne), mul_one]`. Use `⟨fun h => hx h.1, ?_⟩` and prove the remaining obligations. Rewrite using `[slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]`.

Take the linear combination `e₁ - e₂`. Rewrite using `[Point.add_some key.1]`. Apply `Point.add_of_Y_eq` to reduce the goal to its premises. Rewrite using `[key.2, addX]`. Take the linear combination `-s₁`.

Establish `hx : W.addX x₁ x₂ l = x₃`. Rewrite using `[addX]`. Take the linear combination `-s₁`. Rewrite using `[key.2, addY, negAddY, hx]`. Use `congr 1`.

Take the linear combination `e₁ - e₃`.
-/
theorem add_add_eq_zero_of_line {x₁ y₁ x₂ y₂ x₃ y₃ : k} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (h₃ : W.Nonsingular x₃ y₃) (l n : k)
    (e₁ : y₁ = l * x₁ + n) (e₂ : y₂ = l * x₂ + n) (e₃ : y₃ = l * x₃ + n)
    (s₁ : x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂)
    (s₂ : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l) :
    Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0 := by
  have key : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) ∧ W.slope x₁ x₂ y₁ y₂ = l := by
    by_cases hx : x₁ = x₂
    · subst hx
      have hy : y₁ = y₂ := e₁.trans e₂.symm
      subst hy
      have ht : 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ = l * (y₁ - W.negY x₁ y₁) := by
        rw [negY]
        linear_combination (2 * x₁) * s₁ - s₂ - (W.a₁ + 2 * l) * e₁
      have hne : y₁ ≠ W.negY x₁ y₁ := by
        intro h
        rw [nonsingular_iff] at h₁
        rcases h₁.2 with h' | h'
        · apply h'
          rw [← h, sub_self, mul_zero] at ht
          linear_combination -ht
        · exact h' h
      refine ⟨fun h => hne h.2, ?_⟩
      rw [slope_of_Y_ne rfl hne, ht, mul_div_assoc, div_self (sub_ne_zero.mpr hne), mul_one]
    · refine ⟨fun h => hx h.1, ?_⟩
      rw [slope_of_X_ne hx, div_eq_iff (sub_ne_zero.mpr hx)]
      linear_combination e₁ - e₂
  rw [Point.add_some key.1]
  apply Point.add_of_Y_eq
  · rw [key.2, addX]
    linear_combination -s₁
  · have hx : W.addX x₁ x₂ l = x₃ := by
      rw [addX]
      linear_combination -s₁
    rw [key.2, addY, negAddY, hx]
    congr 1
    linear_combination e₁ - e₃

/- English proof (translation)
Establish `hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂)`. Introduce and unpack `⟨hx, hy⟩`. Rewrite `h` using `[Point.add_of_Y_eq hx hy, zero_add]`. Conclude with `Point.some_ne_zero _ h`. Rewrite `h` using `[Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq]`.

Take `⟨hx, hy⟩` from `h`. Establish `hp` using `addPolynomial_slope h₁.1 h₂.1 hxy`. Rewrite `hp` using `[addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hx]`. Establish `hl : W.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂`. Distinguish the cases in `hx' : x₁ = x₂`.

Use `Y_eq_of_Y_ne h₁.1 h₂.1 hx' (fun h => hxy ⟨hx', h⟩)` as an intermediate fact. Rewrite using `[hx', this, sub_self, sub_self, mul_zero]`. Rewrite using `[slope_of_X_ne hx', div_mul_cancel₀ _ (sub_ne_zero.mpr hx')]`. Rewrite `hy` using `[addY, negAddY, hx, negY, negY]`. Use `set l := W.slope x₁ x₂ y₁ y₂`.

Simplify using `only [Cubic.mk.injEq, true_and] at hp`. Take `⟨p₁, p₂, p₃⟩` from `hp`. Use `⟨l, y₁ - l * x₁, by ring, by linear_combination hl, by linear_combination hy, by linear_combination p₁, by linear_combination -p₂, by linear_combination p₃⟩` and prove the remaining obligations.
-/
theorem exists_line_of_add_add_eq_zero {x₁ y₁ x₂ y₂ x₃ y₃ : k} {h₁ : W.Nonsingular x₁ y₁}
    {h₂ : W.Nonsingular x₂ y₂} {h₃ : W.Nonsingular x₃ y₃}
    (h : Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂ + Point.some x₃ y₃ h₃ = 0) :
    ∃ l n : k, y₁ = l * x₁ + n ∧ y₂ = l * x₂ + n ∧ y₃ = l * x₃ + n ∧
      x₁ + x₂ + x₃ = l ^ 2 + W.a₁ * l - W.a₂ ∧
      x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = W.a₄ - 2 * l * n - W.a₁ * n - W.a₃ * l ∧
      x₁ * x₂ * x₃ = n ^ 2 + W.a₃ * n - W.a₆ := by
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.negY x₂ y₂) := by
    rintro ⟨hx, hy⟩
    rw [Point.add_of_Y_eq hx hy, zero_add] at h
    exact Point.some_ne_zero _ h
  rw [Point.add_some hxy, add_eq_zero_iff_eq_neg, Point.neg_some, Point.some.injEq] at h
  obtain ⟨hx, hy⟩ := h
  have hp := addPolynomial_slope h₁.1 h₂.1 hxy
  rw [addPolynomial_eq, neg_inj, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective, hx] at hp
  have hl : W.slope x₁ x₂ y₁ y₂ * (x₁ - x₂) = y₁ - y₂ := by
    by_cases hx' : x₁ = x₂
    · have := Y_eq_of_Y_ne h₁.1 h₂.1 hx' (fun h => hxy ⟨hx', h⟩)
      rw [hx', this, sub_self, sub_self, mul_zero]
    · rw [slope_of_X_ne hx', div_mul_cancel₀ _ (sub_ne_zero.mpr hx')]
  rw [addY, negAddY, hx, negY, negY] at hy
  set l := W.slope x₁ x₂ y₁ y₂
  simp only [Cubic.mk.injEq, true_and] at hp
  obtain ⟨p₁, p₂, p₃⟩ := hp
  refine ⟨l, y₁ - l * x₁, by ring, by linear_combination hl, by linear_combination hy,
    by linear_combination p₁, by linear_combination -p₂, by linear_combination p₃⟩

section VariableChange

omit [DecidableEq k] in

/- English proof (translation)
Establish `hu : (C.u : k) ≠ 0` using `C.u.ne_zero`. Simplify using `only [nonsingular_iff', equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]`. Take `⟨u, r, s, t⟩` from `C`. Simplify using `only at hu ⊢`. Generalize the expression as in `(u : k) = v at hu ⊢`.

Take `⟨a₁, a₂, a₃, a₄, a₆⟩` from `W`. Simplify using `only [toAffine]`. Use `and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`.

Clear denominators, using `at h` for the nonvanishing conditions. Take the linear combination `h`. Rewrite using `[← not_iff_not]`. Simplify using `only [not_or, not_not]`. Use `⟨fun ⟨h, h'⟩ => ⟨?_, ?_⟩, fun ⟨h, h'⟩ => ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Take the linear combination `h + s * h'`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h'`. Clear denominators, using `at h h'` for the nonvanishing conditions.

Conclude with `⟨by linear_combination h - s * h', by linear_combination h'⟩`.
-/
theorem nonsingular_variableChange_iff (W : WeierstrassCurve k) (C : VariableChange k) (x y : k) :
    W.toAffine.Nonsingular ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t) ↔ (C • W).toAffine.Nonsingular x y := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  simp only [nonsingular_iff', equation_iff', variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
  obtain ⟨u, r, s, t⟩ := C
  dsimp only at hu ⊢
  generalize (u : k) = v at hu ⊢
  obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := W
  dsimp only [toAffine]
  refine and_congr ⟨fun h => ?_, fun h => ?_⟩ ?_
  · field_simp
    linear_combination h
  · field_simp at h
    linear_combination h
  · rw [← not_iff_not]
    simp only [not_or, not_not]
    refine ⟨fun ⟨h, h'⟩ => ⟨?_, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
    · field_simp
      linear_combination h + s * h'
    · field_simp
      linear_combination h'
    · field_simp at h h'
      exact ⟨by linear_combination h - s * h', by linear_combination h'⟩

def variableChangePointFun {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point → W.toAffine.Point
  | .zero => 0
  | .some x y hP => .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP))

def variableChangePoint {W W' : WeierstrassCurve k} (C : VariableChange k) (h : C • W = W') :
    W'.toAffine.Point →+ W.toAffine.Point :=
  AddMonoidHom.mk' (variableChangePointFun C h) <| by
    subst h
    have hu : (C.u : k) ≠ 0 := C.u.ne_zero
    refine map_add_of_triples _ rfl ?_ ?_
    · rintro (_ | ⟨x, y, hP⟩)
      · rfl
      · simp only [Point.neg_some, variableChangePointFun, Point.some.injEq, true_and, negY,
          variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
        field_simp
        ring
    · rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) (_ | ⟨x₃, y₃, h₃⟩) hP hQ hR h
      any_goals first | exact absurd rfl hP | exact absurd rfl hQ | exact absurd rfl hR
      obtain ⟨l, n, e₁, e₂, e₃, s₁, s₂, -⟩ := exists_line_of_add_add_eq_zero h
      simp only [variableChange_a₁, variableChange_a₂,
        variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val] at s₁ s₂
      field_simp at s₁ s₂
      refine add_add_eq_zero_of_line _ _ _ ((C.u : k) * l + C.s)
        ((C.u : k) ^ 3 * n + C.t - C.r * ((C.u : k) * l + C.s)) ?_ ?_ ?_ ?_ ?_
      · rw [e₁]; ring
      · rw [e₂]; ring
      · rw [e₃]; ring
      · linear_combination s₁
      · linear_combination s₂ + 2 * C.r * s₁

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem variableChangePoint_some {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') {x y : k} (hP : W'.toAffine.Nonsingular x y) :
    variableChangePoint C h (.some x y hP) = .some ((C.u : k) ^ 2 * x + C.r)
      ((C.u : k) ^ 3 * y + (C.u : k) ^ 2 * C.s * x + C.t)
      ((nonsingular_variableChange_iff W C x y).mpr (h ▸ hP)) :=
  rfl

/- English proof (translation)
Establish `hu : (C.u : k) ≠ 0` using `C.u.ne_zero`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `(_ | ⟨x, y, hP⟩) h0`. Both sides reduce to the same expression.

Conclude with `absurd h0 (Point.some_ne_zero _)`. Introduce and unpack `(_ | ⟨x, y, hP⟩)`. Conclude with `⟨0, map_zero _⟩`. Establish `hx : x = (C.u : k) ^ 2 * ((x - C.r) / (C.u : k) ^ 2) + C.r` using `by field_simp; ring`. Establish `hy : y = (C.u : k) ^ 3 * ((y - C.s * (x - C.r) - C.t) / (C.u : k) ^ 3) + (C.u : k) ^ 2 * C.s * ((x - C.r) / (C.u : k) ^ 2) + C.t` using `by field_simp; ring`.

Establish `hP'` using `hP`. Rewrite `hP'` using `[hx, hy, ← hx]`. Use `nth_rw 1 [hx] at hP'`. Rewrite `hP'` using `[nonsingular_variableChange_iff, h]`. Use `⟨.some _ _ hP', ?_⟩` and prove the remaining obligations.

Rewrite using `[variableChangePoint_some, Point.some.injEq]`. Conclude with `⟨hx.symm, hy.symm⟩`.
-/
theorem variableChangePoint_bijective {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : Function.Bijective (variableChangePoint C h) := by
  have hu : (C.u : k) ≠ 0 := C.u.ne_zero
  constructor
  · rw [injective_iff_map_eq_zero]
    rintro (_ | ⟨x, y, hP⟩) h0
    · rfl
    · exact absurd h0 (Point.some_ne_zero _)
  · rintro (_ | ⟨x, y, hP⟩)
    · exact ⟨0, map_zero _⟩
    · have hx : x = (C.u : k) ^ 2 * ((x - C.r) / (C.u : k) ^ 2) + C.r := by field_simp; ring
      have hy : y = (C.u : k) ^ 3 * ((y - C.s * (x - C.r) - C.t) / (C.u : k) ^ 3)
          + (C.u : k) ^ 2 * C.s * ((x - C.r) / (C.u : k) ^ 2) + C.t := by field_simp; ring
      have hP' := hP
      rw [hx, hy, ← hx] at hP'
      nth_rw 1 [hx] at hP'
      rw [nonsingular_variableChange_iff, h] at hP'
      refine ⟨.some _ _ hP', ?_⟩
      rw [variableChangePoint_some, Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩

noncomputable def variableChangePointEquiv {W W' : WeierstrassCurve k} (C : VariableChange k)
    (h : C • W = W') : W'.toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (variableChangePoint C h) (variableChangePoint_bijective C h)

end VariableChange

end GlobalTheory
