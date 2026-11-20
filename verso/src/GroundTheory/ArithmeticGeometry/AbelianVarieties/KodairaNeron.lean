import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupReduction
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.SlopeVcCountableNeighbourhoods

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

section Ring

variable {R : Type*} [CommRing R] (C : VariableChange R)

def vcX (x : R) : R := ((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)

def vcY (x y : R) : R := ((C.u⁻¹ : Rˣ) : R) ^ 3 * (y - C.s * (x - C.r) - C.t)

def vcX' (x' : R) : R := (C.u : R) ^ 2 * x' + C.r

def vcY' (x' y' : R) : R := (C.u : R) ^ 3 * y' + C.s * (C.u : R) ^ 2 * x' + C.t

/- English proof (translation)
Conclude with `Units.inv_mul C.u`.
-/
theorem inv_mul_u : ((C.u⁻¹ : Rˣ) : R) * C.u = 1 := by
  exact Units.inv_mul C.u

/- English proof (translation)
Establish `h` using `inv_mul_u C`. Simplify using `only [vcX, vcX']`. Take the linear combination `(x' * (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h`.
-/
theorem vcX_vcX' (x' : R) : vcX C (vcX' C x') = x' := by
  have h := inv_mul_u C
  simp only [vcX, vcX']
  linear_combination (x' * (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h

/- English proof (translation)
Establish `h` using `inv_mul_u C`. Simplify using `only [vcY, vcX', vcY']`. Take the linear combination `(y' * ((((C.u⁻¹ : Rˣ) : R) * C.u) ^ 2 + ((C.u⁻¹ : Rˣ) : R) * C.u + 1) + C.s * ((C.u⁻¹ : Rˣ) : R) * x' * (((C.u⁻¹ : Rˣ) : R) * C.u + 1) - C.s * ((C.u⁻¹ : Rˣ) : R) * x' * (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h`.
-/
theorem vcY_vcY' (x' y' : R) : vcY C (vcX' C x') (vcY' C x' y') = y' := by
  have h := inv_mul_u C
  simp only [vcY, vcX', vcY']
  linear_combination (y' * ((((C.u⁻¹ : Rˣ) : R) * C.u) ^ 2 + ((C.u⁻¹ : Rˣ) : R) * C.u + 1)
    + C.s * ((C.u⁻¹ : Rˣ) : R) * x' * (((C.u⁻¹ : Rˣ) : R) * C.u + 1) - C.s * ((C.u⁻¹ : Rˣ) : R) * x' *
      (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h

/- English proof (translation)
Establish `h` using `inv_mul_u C`. Simplify using `only [vcX, vcX']`. Take the linear combination `((x - C.r) * (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h`.
-/
theorem vcX'_vcX (x : R) : vcX' C (vcX C x) = x := by
  have h := inv_mul_u C
  simp only [vcX, vcX']
  linear_combination ((x - C.r) * (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h

/- English proof (translation)
Establish `h` using `inv_mul_u C`. Simplify using `only [vcX, vcY, vcX', vcY']`. Take the linear combination `((y - C.s * (x - C.r) - C.t) * ((((C.u⁻¹ : Rˣ) : R) * C.u) ^ 2 + ((C.u⁻¹ : Rˣ) : R) * C.u + 1) + C.s * (x - C.r) * (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h`.
-/
theorem vcY'_vcY (x y : R) : vcY' C (vcX C x) (vcY C x y) = y := by
  have h := inv_mul_u C
  simp only [vcX, vcY, vcX', vcY']
  linear_combination ((y - C.s * (x - C.r) - C.t) * ((((C.u⁻¹ : Rˣ) : R) * C.u) ^ 2 +
    ((C.u⁻¹ : Rˣ) : R) * C.u + 1) + C.s * (x - C.r) * (((C.u⁻¹ : Rˣ) : R) * C.u + 1)) * h

/- English proof (translation)
Simplify using `[vcX, VariableChange.map, Units.coe_map_inv]`.
-/
theorem map_vcX {S : Type*} [CommRing S] (f : R →+* S) (x : R) :
    f (vcX C x) = vcX (C.map f) (f x) := by
  simp [vcX, VariableChange.map, Units.coe_map_inv]

/- English proof (translation)
Simplify using `[vcY, VariableChange.map, Units.coe_map_inv]`.
-/
theorem map_vcY {S : Type*} [CommRing S] (f : R →+* S) (x y : R) :
    f (vcY C x y) = vcY (C.map f) (f x) (f y) := by
  simp [vcY, VariableChange.map, Units.coe_map_inv]

/- English proof (translation)
Simplify using `[vcX', VariableChange.map]`.
-/
theorem map_vcX' {S : Type*} [CommRing S] (f : R →+* S) (x' : R) :
    f (vcX' C x') = vcX' (C.map f) (f x') := by
  simp [vcX', VariableChange.map]

/- English proof (translation)
Simplify using `[vcY', VariableChange.map]`.
-/
theorem map_vcY' {S : Type*} [CommRing S] (f : R →+* S) (x' y' : R) :
    f (vcY' C x' y') = vcY' (C.map f) (f x') (f y') := by
  simp [vcY', VariableChange.map]

end Ring

section Field

variable {F : Type*} [Field F] (C : VariableChange F)

/- English proof (translation)
The claim follows from `Units.ne_zero _`.
-/
theorem u_inv_ne_zero : ((C.u⁻¹ : Fˣ) : F) ≠ 0 := Units.ne_zero _

variable (W : WeierstrassCurve F)

/- English proof (translation)
Simplify using `only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄, variableChange_a₆]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem equation_expr_vc (x y : F) :
    vcY C x y ^ 2 + (C • W).a₁ * vcX C x * vcY C x y + (C • W).a₃ * vcY C x y -
      (vcX C x ^ 3 + (C • W).a₂ * vcX C x ^ 2 + (C • W).a₄ * vcX C x + (C • W).a₆) =
    ((C.u⁻¹ : Fˣ) : F) ^ 6 * (y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)) := by
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆]
  ring

/- English proof (translation)
Rewrite using `[equation_iff', equation_iff', equation_expr_vc, mul_eq_zero]`. Simplify using the standard rewrite rules.
-/
theorem equation_vc (x y : F) :
    (C • W).toAffine.Equation (vcX C x) (vcY C x y) ↔ W.toAffine.Equation x y := by
  rw [equation_iff', equation_iff', equation_expr_vc, mul_eq_zero]
  simp

/- English proof (translation)
Simplify using `only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polX_vc (x y : F) :
    (C • W).a₁ * vcY C x y - (3 * vcX C x ^ 2 + 2 * (C • W).a₂ * vcX C x + (C • W).a₄) =
    ((C.u⁻¹ : Fˣ) : F) ^ 4 * ((W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) +
      C.s * (2 * y + W.a₁ * x + W.a₃)) := by
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
  ring

/- English proof (translation)
Simplify using `only [vcX, vcY, variableChange_a₁, variableChange_a₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem polY_vc (x y : F) :
    2 * vcY C x y + (C • W).a₁ * vcX C x + (C • W).a₃ =
    ((C.u⁻¹ : Fˣ) : F) ^ 3 * (2 * y + W.a₁ * x + W.a₃) := by
  simp only [vcX, vcY, variableChange_a₁, variableChange_a₃]
  ring

/- English proof (translation)
Rewrite using `[nonsingular_iff', nonsingular_iff', equation_vc, polX_vc, polY_vc]`. Use `and_congr_right fun _ => ?_` and prove the remaining obligations. Establish `hv` using `u_inv_ne_zero C`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`.

Assume the negation of the conclusion as `hc push Not at hc`. Conclude with `h (by rw [hc.1, hc.2]; ring)`. Conclude with `Or.inr fun h' => h (by rw [h']; ring)`. Introduce and unpack `(h | h)`. Distinguish the cases in `hB : 2 * y + W.a₁ * x + W.a₃ = 0`.

Use `left`. Rewrite using `[hB]`. Simplify using `[h]`. Use `right`. Simplify using `[hB]`.

Use `right`. Simplify using `[h]`.
-/
theorem nonsingular_vc (x y : F) :
    (C • W).toAffine.Nonsingular (vcX C x) (vcY C x y) ↔ W.toAffine.Nonsingular x y := by
  rw [nonsingular_iff', nonsingular_iff', equation_vc, polX_vc, polY_vc]
  refine and_congr_right fun _ => ?_
  have hv := u_inv_ne_zero C
  constructor
  · rintro (h | h)
    · by_contra hc
      push Not at hc
      exact h (by rw [hc.1, hc.2]; ring)
    · exact Or.inr fun h' => h (by rw [h']; ring)
  · rintro (h | h)
    · by_cases hB : 2 * y + W.a₁ * x + W.a₃ = 0
      · left; rw [hB]; simp [h]
      · right; simp [hB]
    · right; simp [h]

/- English proof (translation)
Simplify using `only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem negY_vc (x y : F) :
    (C • W).toAffine.negY (vcX C x) (vcY C x y) = vcY C x (W.toAffine.negY x y) := by
  simp only [negY, vcX, vcY, variableChange_a₁, variableChange_a₃]
  ring

/- English proof (translation)
Use `⟨fun h => ?_, fun h => h ▸ rfl⟩` and prove the remaining obligations. Use `congrArg (vcX' C) h` as an intermediate fact. Rewrite `this` using `[vcX'_vcX, vcX'_vcX]`. Then use the resulting hypothesis.
-/
theorem vcX_inj {x₁ x₂ : F} : vcX C x₁ = vcX C x₂ ↔ x₁ = x₂ := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have := congrArg (vcX' C) h
  rwa [vcX'_vcX, vcX'_vcX] at this

/- English proof (translation)
Use `⟨fun h => ?_, fun h => h ▸ rfl⟩` and prove the remaining obligations. Use `congrArg (vcY' C (vcX C x)) h` as an intermediate fact. Rewrite `this` using `[vcY'_vcY, vcY'_vcY]`. Then use the resulting hypothesis.
-/
theorem vcY_inj {x y₁ y₂ : F} : vcY C x y₁ = vcY C x y₂ ↔ y₁ = y₂ := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have := congrArg (vcY' C (vcX C x)) h
  rwa [vcY'_vcY, vcY'_vcY] at this

/- English proof (translation)
Apply the tactic sequence `apply _root_.GroundTheory.Variant₂.N1.slope_variableChange <;> assumption`.
-/
theorem slope_vc [DecidableEq F] {x₁ x₂ y₁ y₂ : F} (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) :
    (C • W).toAffine.slope (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (vcY C x₂ y₂) =
      ((C.u⁻¹ : Fˣ) : F) * (W.toAffine.slope x₁ x₂ y₁ y₂ - C.s) :=
  by apply _root_.GroundTheory.Variant₂.N1.slope_variableChange <;> assumption

/- English proof (translation)
Simplify using `only [addX, vcX, variableChange_a₁, variableChange_a₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem addX_vc (x₁ x₂ ℓ : F) :
    (C • W).toAffine.addX (vcX C x₁) (vcX C x₂) (((C.u⁻¹ : Fˣ) : F) * (ℓ - C.s)) =
      vcX C (W.toAffine.addX x₁ x₂ ℓ) := by
  simp only [addX, vcX, variableChange_a₁, variableChange_a₂]
  ring

/- English proof (translation)
Establish `hneg : (C • W).toAffine.negAddY (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (((C.u⁻¹ : Fˣ) : F) * (ℓ - C.s)) = vcY C (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.negAddY x₁ x₂ y₁ ℓ)`. Simplify using `only [negAddY, addX, vcX, vcY, variableChange_a₁, variableChange_a₂]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[addY, addY, hneg, addX_vc, negY_vc]`.
-/
theorem addY_vc (x₁ x₂ y₁ ℓ : F) :
    (C • W).toAffine.addY (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁) (((C.u⁻¹ : Fˣ) : F) * (ℓ - C.s)) =
      vcY C (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
  have hneg : (C • W).toAffine.negAddY (vcX C x₁) (vcX C x₂) (vcY C x₁ y₁)
      (((C.u⁻¹ : Fˣ) : F) * (ℓ - C.s)) =
      vcY C (W.toAffine.addX x₁ x₂ ℓ) (W.toAffine.negAddY x₁ x₂ y₁ ℓ) := by
    simp only [negAddY, addX, vcX, vcY, variableChange_a₁, variableChange_a₂]
    ring
  rw [addY, addY, hneg, addX_vc, negY_vc]

variable {W}

def vcPoint {W₂ : WeierstrassCurve F} (h : C • W = W₂) : W.toAffine.Point → W₂.toAffine.Point
  | 0 => 0
  | .some x y hP => .some (vcX C x) (vcY C x y) (h ▸ (nonsingular_vc C W x y).2 hP)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vcPoint_zero {W₂ : WeierstrassCurve F} (h : C • W = W₂) : vcPoint C h 0 = 0 := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vcPoint_some {W₂ : WeierstrassCurve F} (h : C • W = W₂) {x y : F}
    (hP : W.toAffine.Nonsingular x y) :
    vcPoint C h (.some x y hP) =
      .some (vcX C x) (vcY C x y) (h ▸ (nonsingular_vc C W x y).2 hP) := rfl

/- English proof (translation)
Substitute `h` using the available equality. Apply the tactic sequence `rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩`. Both sides reduce to the same expression. Both sides reduce to the same expression. Both sides reduce to the same expression.

Distinguish the cases in `hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂`. Rewrite using `[Point.add_of_Y_eq hxy.1 hxy.2, vcPoint_some, vcPoint_some, vcPoint_zero, Point.add_of_Y_eq ((vcX_inj C).2 hxy.1) (by rw [negY_vc, hxy.2, hxy.1])]`. Establish `hxy' : ¬(vcX C x₁ = vcX C x₂ ∧ vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂))`. Introduce and unpack `⟨hx, hy⟩`. Rewrite `hx` using `[vcX_inj]`.

Substitute `hx` using the available equality. Rewrite `hy` using `[negY_vc, vcY_inj]`. Conclude with `hxy ⟨rfl, hy⟩`. Rewrite using `[Point.add_some hxy, vcPoint_some, vcPoint_some, vcPoint_some, Point.add_some hxy', Point.some.injEq, slope_vc C W h₁.1 h₂.1 hxy, addX_vc, addY_vc]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem vcPoint_add [DecidableEq F] {W₂ : WeierstrassCurve F} (h : C • W = W₂)
    (P Q : W.toAffine.Point) : vcPoint C h (P + Q) = vcPoint C h P + vcPoint C h Q := by
  subst h
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2, vcPoint_some, vcPoint_some, vcPoint_zero,
      Point.add_of_Y_eq ((vcX_inj C).2 hxy.1) (by rw [negY_vc, hxy.2, hxy.1])]
  · have hxy' : ¬(vcX C x₁ = vcX C x₂ ∧
        vcY C x₁ y₁ = (C • W).toAffine.negY (vcX C x₂) (vcY C x₂ y₂)) := by
      rintro ⟨hx, hy⟩
      rw [vcX_inj] at hx
      subst hx
      rw [negY_vc, vcY_inj] at hy
      exact hxy ⟨rfl, hy⟩
    rw [Point.add_some hxy, vcPoint_some, vcPoint_some, vcPoint_some, Point.add_some hxy',
      Point.some.injEq, slope_vc C W h₁.1 h₂.1 hxy, addX_vc, addY_vc]
    exact ⟨rfl, rfl⟩

/- English proof (translation)
Substitute `h` using the available equality. Introduce and unpack `(_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) e`. Both sides reduce to the same expression. Conclude with `absurd e.symm (Point.some_ne_zero _)`. Conclude with `absurd e (Point.some_ne_zero _)`.

Rewrite `e` using `[vcPoint_some, vcPoint_some, Point.some.injEq]`. Take `⟨hx, hy⟩` from `e`. Rewrite `hx` using `[vcX_inj]`. Substitute `hx` using the available equality. Rewrite `hy` using `[vcY_inj]`.

Substitute `hy` using the available equality. Both sides reduce to the same expression.
-/
theorem vcPoint_injective {W₂ : WeierstrassCurve F} (h : C • W = W₂) :
    Function.Injective (vcPoint C h) := by
  subst h
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) e
  · rfl
  · exact absurd e.symm (Point.some_ne_zero _)
  · exact absurd e (Point.some_ne_zero _)
  · rw [vcPoint_some, vcPoint_some, Point.some.injEq] at e
    obtain ⟨hx, hy⟩ := e
    rw [vcX_inj] at hx
    subst hx
    rw [vcY_inj] at hy
    subst hy
    rfl

/- English proof (translation)
Substitute `h` using the available equality. Introduce and unpack `(_ | ⟨x', y', h'⟩)`. Conclude with `⟨0, rfl⟩`. Establish `hP : W.toAffine.Nonsingular (vcX' C x') (vcY' C x' y')`. Rewrite using `[← nonsingular_vc C W, vcX_vcX', vcY_vcY']`.

Conclude with `h'`. Use `⟨.some _ _ hP, ?_⟩` and prove the remaining obligations. Rewrite using `[vcPoint_some, Point.some.injEq]`. Conclude with `⟨vcX_vcX' C x', vcY_vcY' C x' y'⟩`.
-/
theorem vcPoint_surjective {W₂ : WeierstrassCurve F} (h : C • W = W₂) :
    Function.Surjective (vcPoint C h) := by
  subst h
  rintro (_ | ⟨x', y', h'⟩)
  · exact ⟨0, rfl⟩
  · have hP : W.toAffine.Nonsingular (vcX' C x') (vcY' C x' y') := by
      rw [← nonsingular_vc C W, vcX_vcX', vcY_vcY']; exact h'
    refine ⟨.some _ _ hP, ?_⟩
    rw [vcPoint_some, Point.some.injEq]
    exact ⟨vcX_vcX' C x', vcY_vcY' C x' y'⟩

def vcPointEquiv [DecidableEq F] {W₂ : WeierstrassCurve F} (h : C • W = W₂) :
    W.toAffine.Point ≃+ W₂.toAffine.Point :=
  AddEquiv.ofBijective (AddMonoidHom.mk' (vcPoint C h) (vcPoint_add C h))
    ⟨vcPoint_injective C h, vcPoint_surjective C h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vcPointEquiv_apply [DecidableEq F] {W₂ : WeierstrassCurve F} (h : C • W = W₂)
    (P : W.toAffine.Point) : vcPointEquiv C h P = vcPoint C h P := rfl

end Field

section DVR

open IsLocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)
  (C : VariableChange 𝒪)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsFractionRing 𝒪 K] in
/- English proof (translation)
The claim follows from `map_variableChange W C (algebraMap 𝒪 K)`.
-/
theorem map_vc_eq : (C.map (algebraMap 𝒪 K)) • (W.map (algebraMap 𝒪 K)) =
    (C • W).map (algebraMap 𝒪 K) :=
  map_variableChange W C (algebraMap 𝒪 K)

/- English proof (translation)
The claim follows from `map_variableChange W C (residue 𝒪)`.
-/
theorem map_vc_eq_residue : (C.map (residue 𝒪)) • (W.map (residue 𝒪)) =
    (C • W).map (residue 𝒪) :=
  map_variableChange W C (residue 𝒪)

instance isElliptic_map_vc [(W.map (algebraMap 𝒪 K)).IsElliptic] :
    ((C • W).map (algebraMap 𝒪 K)).IsElliptic := by
  rw [isElliptic_iff, ← map_vc_eq K W C, variableChange_Δ]
  exact ((Units.isUnit _).pow 12).mul (W.map (algebraMap 𝒪 K)).isUnit_Δ

variable [DecidableEq K]

def vcEquivK : (curveK K W).Point ≃+ (curveK K (C • W)).Point :=
  vcPointEquiv (C.map (algebraMap 𝒪 K)) (map_vc_eq K W C)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vcEquivK_some {X Y : K} (h : (curveK K W).Nonsingular X Y)
    (h' : (curveK K (C • W)).Nonsingular (vcX (C.map (algebraMap 𝒪 K)) X)
      (vcY (C.map (algebraMap 𝒪 K)) X Y)) :
    vcEquivK K W C (.some _ _ h) = .some _ _ h' := rfl

/- English proof (translation)
Use `(nonsingular_vc (C.map (algebraMap 𝒪 K)) (W.map (algebraMap 𝒪 K)) X Y).2 h` as an intermediate fact. Rewrite `this` using `[map_vc_eq]`. Then use the resulting hypothesis.
-/
theorem nonsingular_K_vc {X Y : K} (h : (curveK K W).Nonsingular X Y) :
    (curveK K (C • W)).Nonsingular (vcX (C.map (algebraMap 𝒪 K)) X)
      (vcY (C.map (algebraMap 𝒪 K)) X Y) := by
  have := (nonsingular_vc (C.map (algebraMap 𝒪 K)) (W.map (algebraMap 𝒪 K)) X Y).2 h
  rwa [map_vc_eq] at this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem vcEquivK_zero : vcEquivK K W C 0 = 0 := rfl

/- English proof (translation)
Rewrite using `[map_vcX, map_vcY, ← nonsingular_vc (C.map (residue 𝒪)) (W.map (residue 𝒪)), map_vc_eq_residue]`.
-/
theorem nonsingular_red_vc {x y : 𝒪} :
    (curveRed (C • W)).Nonsingular (residue 𝒪 (vcX C x)) (residue 𝒪 (vcY C x y)) ↔
      (curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y) := by
  rw [map_vcX, map_vcY, ← nonsingular_vc (C.map (residue 𝒪)) (W.map (residue 𝒪)),
    map_vc_eq_residue]

/- English proof (translation)
Break down `P with _ | ⟨X, Y, h⟩` into its components or cases. Conclude with `⟨fun _ => zero_mem_E0Set K _, fun _ => zero_mem_E0Set K _⟩`. Rewrite using `[vcEquivK_some K W C h (nonsingular_K_vc K W C h)]`. Prove the components needed by the constructor for the conclusion. Introduce `hP x' y' h' e`.

Rewrite `e` using `[WeierstrassCurve.Affine.Point.some.injEq]`. Establish `hX : X = algebraMap 𝒪 K (vcX' C x')`. Rewrite using `[map_vcX', ← e.1, vcX'_vcX]`. Establish `hY : Y = algebraMap 𝒪 K (vcY' C x' y')`. Rewrite using `[map_vcY', ← e.1, ← e.2, vcY'_vcY]`.

Substitute `hX hY` using the available equality. Use `hP _ _ h rfl` as an intermediate fact. Rewrite `this` using `[← nonsingular_red_vc (C := C), vcX_vcX', vcY_vcY']`. Conclude with `this`. Introduce `hP x y h' e`.

Rewrite `e` using `[WeierstrassCurve.Affine.Point.some.injEq]`. Take `⟨rfl, rfl⟩` from `e`. Use `hP (vcX C x) (vcY C x y) (by rw [map_vcX, map_vcY]; exact nonsingular_K_vc K W C h) (by rw [WeierstrassCurve.Affine.Point.some.injEq, map_vcX, map_vcY]; exact ⟨rfl, rfl⟩)` as an intermediate fact. Rewrite `this` using `[nonsingular_red_vc]`. Then use the resulting hypothesis.
-/
theorem mem_E0Set_vc_iff (P : (curveK K W).Point) :
    P ∈ E0Set K W ↔ vcEquivK K W C P ∈ E0Set K (C • W) := by
  rcases P with _ | ⟨X, Y, h⟩
  · exact ⟨fun _ => zero_mem_E0Set K _, fun _ => zero_mem_E0Set K _⟩
  rw [vcEquivK_some K W C h (nonsingular_K_vc K W C h)]
  constructor
  · intro hP x' y' h' e
    rw [WeierstrassCurve.Affine.Point.some.injEq] at e
    have hX : X = algebraMap 𝒪 K (vcX' C x') := by
      rw [map_vcX', ← e.1, vcX'_vcX]
    have hY : Y = algebraMap 𝒪 K (vcY' C x' y') := by
      rw [map_vcY', ← e.1, ← e.2, vcY'_vcY]
    subst hX hY
    have := hP _ _ h rfl
    rw [← nonsingular_red_vc (C := C), vcX_vcX', vcY_vcY'] at this
    exact this
  · intro hP x y h' e
    rw [WeierstrassCurve.Affine.Point.some.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    have := hP (vcX C x) (vcY C x y) (by rw [map_vcX, map_vcY]; exact nonsingular_K_vc K W C h)
      (by rw [WeierstrassCurve.Affine.Point.some.injEq, map_vcX, map_vcY]; exact ⟨rfl, rfl⟩)
    rwa [nonsingular_red_vc] at this

variable [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [(W.map (algebraMap 𝒪 K)).IsElliptic]

/- English proof (translation)
Use extensionality with `Q`. Take `⟨P, rfl⟩` from `(vcEquivK K W C).surjective Q`. Rewrite using `[AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply, mem_E0_iff, mem_E0_iff, mem_E0Set_vc_iff]`.
-/
theorem map_E0_variableChange : (E0 K W).map (vcEquivK K W C).toAddMonoidHom = E0 K (C • W) := by
  ext Q
  obtain ⟨P, rfl⟩ := (vcEquivK K W C).surjective Q
  rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply, mem_E0_iff, mem_E0_iff,
    mem_E0Set_vc_iff]

def quotientE0VariableChangeEquiv :
    (curveK K W).Point ⧸ E0 K W ≃+ (curveK K (C • W)).Point ⧸ E0 K (C • W) :=
  QuotientAddGroup.congr (E0 K W) (E0 K (C • W)) (vcEquivK K W C) (map_E0_variableChange K W C)

end DVR

end

end GroundTheory.Arith.Abelian
