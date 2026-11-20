import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisorsValuation
import GroundTheory.ArithmeticGeometry.AbelianVarieties.Isogeny

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain WithZero

open scoped nonZeroDivisors

universe u

variable {F : Type u} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

noncomputable def constPoint :
    W.toAffine.Point →+ (W.baseChange W.toAffine.FunctionField).toAffine.Point :=
  Point.map (W' := W) (Algebra.ofId F W.toAffine.FunctionField)

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, rfl⟩`.
-/
theorem constPoint_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ∃ h' : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
      (algebraMap F W.toAffine.FunctionField x) (algebraMap F W.toAffine.FunctionField y),
      constPoint W (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

/- English proof (translation)
Establish `h` using `Point.map_map (W' := W) (Algebra.ofId F W.toAffine.FunctionField) ψ R`. Establish `e : ψ.comp (Algebra.ofId F W.toAffine.FunctionField) = Algebra.ofId F _` using `Subsingleton.elim _ _`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem map_constPoint (ψ : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    (R : W.toAffine.Point) : Point.map ψ (constPoint W R) = constPoint W R := by
  have h := Point.map_map (W' := W) (Algebra.ofId F W.toAffine.FunctionField) ψ R
  have e : ψ.comp (Algebra.ofId F W.toAffine.FunctionField) = Algebra.ofId F _ :=
    Subsingleton.elim _ _
  rw [e] at h
  exact h

omit [DecidableEq F] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨_, rfl⟩`.
-/
theorem map_genericPoint_eq (ψ : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)
    [W.IsElliptic] :
    ∃ h, Point.map ψ (genericPoint W) = .some (ψ (genX W)) (ψ (genY W)) h :=
  ⟨_, rfl⟩

omit [DecidableEq F] in

/- English proof (translation)
Establish `key` using `IntermediateField.algHom_ext_of_eq_adjoin F (S := (⊤ : IntermediateField F W.toAffine.FunctionField)) (adjoin_genX_genY W).symm (φ₁ := ψ₁.comp (IntermediateField.val ⊤)) (φ₂ := ψ₂.comp (IntermediateField.val ⊤)) (by`. Introduce and unpack `z (rfl | rfl)`. Conclude with `hx`. Conclude with `hy)`. Use `AlgHom.ext fun z => ?_` and prove the remaining obligations.

Conclude with `DFunLike.congr_fun key ⟨z, IntermediateField.mem_top⟩`.
-/
theorem algHom_ext_gen {L : Type*} [Field L] [Algebra F L]
    {ψ₁ ψ₂ : W.toAffine.FunctionField →ₐ[F] L} (hx : ψ₁ (genX W) = ψ₂ (genX W))
    (hy : ψ₁ (genY W) = ψ₂ (genY W)) : ψ₁ = ψ₂ := by
  have key := IntermediateField.algHom_ext_of_eq_adjoin F
    (S := (⊤ : IntermediateField F W.toAffine.FunctionField)) (adjoin_genX_genY W).symm
    (φ₁ := ψ₁.comp (IntermediateField.val ⊤)) (φ₂ := ψ₂.comp (IntermediateField.val ⊤)) (by
      rintro z (rfl | rfl)
      · exact hx
      · exact hy)
  refine AlgHom.ext fun z => ?_
  exact DFunLike.congr_fun key ⟨z, IntermediateField.mem_top⟩

variable [W.IsElliptic]

omit [DecidableEq F] in

/- English proof (translation)
Take `⟨h₁, e₁⟩` from `map_genericPoint_eq W ψ₁`. Take `⟨h₂, e₂⟩` from `map_genericPoint_eq W ψ₂`. Rewrite `h` using `[e₁, e₂, Point.some.injEq]`. Conclude with `algHom_ext_gen W h.1 h.2`.
-/
theorem algHom_eq_of_map_genericPoint
    {ψ₁ ψ₂ : W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField}
    (h : Point.map ψ₁ (genericPoint W) = Point.map ψ₂ (genericPoint W)) : ψ₁ = ψ₂ := by
  obtain ⟨h₁, e₁⟩ := map_genericPoint_eq W ψ₁
  obtain ⟨h₂, e₂⟩ := map_genericPoint_eq W ψ₂
  rw [e₁, e₂, Point.some.injEq] at h
  exact algHom_ext_gen W h.1 h.2

omit [DecidableEq F] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem map_id_genericPoint :
    Point.map (AlgHom.id F W.toAffine.FunctionField) (genericPoint W) = genericPoint W := rfl

omit [DecidableEq F] [W.IsElliptic] in

/- English proof (translation)
Establish `hint` using `hu.isIntegral`. Establish `hdeg` using `IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint)`. Take `⟨c, hc⟩` from `minpoly.natDegree_eq_one_iff.mp (natDegree_eq_of_degree_eq_some hdeg)`. Conclude with `⟨c, hc⟩`.
-/
theorem exists_algebraMap_eq_of_isAlgebraic [IsAlgClosed F] {u : W.toAffine.FunctionField}
    (hu : IsAlgebraic F u) : ∃ c : F, algebraMap F W.toAffine.FunctionField c = u := by
  have hint := hu.isIntegral
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible F (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp (natDegree_eq_of_degree_eq_some hdeg)
  exact ⟨c, hc⟩

/- English proof (translation)
Consider the cases of `R with`. Consider the case `zero => exact fun h => Point.some_ne_zero _ (h.symm.trans (map_zero _))`. Consider the case `some x y h`. Take `⟨h', e⟩` from `constPoint_some W h`. Rewrite using `[e, genericPoint, Ne, Point.some.injEq]`.

Introduce `hxy`. Conclude with `transcendental_genX W (hxy.1 ▸ isAlgebraic_algebraMap x)`.
-/
theorem constPoint_ne_genericPoint (R : W.toAffine.Point) : constPoint W R ≠ genericPoint W := by
  cases R with
  | zero => exact fun h => Point.some_ne_zero _ (h.symm.trans (map_zero _))
  | some x y h =>
    obtain ⟨h', e⟩ := constPoint_some W h
    rw [e, genericPoint, Ne, Point.some.injEq]
    intro hxy
    exact transcendental_genX W (hxy.1 ▸ isAlgebraic_algebraMap x)

/- English proof (translation)
Introduce `h`. Apply `constPoint_ne_genericPoint W (-R)` to reduce the goal to its premises. Rewrite using `[map_neg, eq_comm, ← add_eq_zero_iff_eq_neg]`. Conclude with `h`.
-/
theorem genericPoint_add_constPoint_ne_zero (R : W.toAffine.Point) :
    genericPoint W + constPoint W R ≠ 0 := by
  intro h
  apply constPoint_ne_genericPoint W (-R)
  rw [map_neg, eq_comm, ← add_eq_zero_iff_eq_neg]
  exact h

/- English proof (translation)
The claim follows from `eq_some_xOf_yOf _ (genericPoint_add_constPoint_ne_zero W R)`.
-/
theorem exists_translate_eq (R : W.toAffine.Point) :
    ∃ h : (W.baseChange W.toAffine.FunctionField).toAffine.Nonsingular
      (xOf _ (genericPoint W + constPoint W R)) (yOf _ (genericPoint W + constPoint W R)),
      genericPoint W + constPoint W R = .some _ _ h :=
  eq_some_xOf_yOf _ (genericPoint_add_constPoint_ne_zero W R)

/- English proof (translation)
Introduce `halg`. Take `⟨h, e⟩` from `exists_translate_eq W R`. Take `⟨c, hc⟩` from `exists_algebraMap_eq_of_isAlgebraic W halg`. Use `set u := xOf _ (genericPoint W + constPoint W R)`. Use `set v := yOf _ (genericPoint W + constPoint W R)`.

Establish `heq` using `(equation_iff _ _).mp h.1`. Simplify using `only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq`. Establish `hvalg : IsAlgebraic F v`. Use `⟨X ^ 2 + C (W.a₁ * c + W.a₃) * X - C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆), ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Use `congrArg natDegree h0` as an intermediate fact. Rewrite `this` using `[natDegree_zero]`. Establish `h2 : (X ^ 2 + C (W.a₁ * c + W.a₃) * X - C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) : F[X]).natDegree = 2` using `by compute_degree!`. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hc]`.

Take the linear combination `heq`. Take `⟨d, hd⟩` from `exists_algebraMap_eq_of_isAlgebraic W hvalg`. Establish `hcd : W.toAffine.Nonsingular c d`. Establish `h'` using `h`. Rewrite `h'` using `[← hc, ← hd]`.

Conclude with `(W.toAffine.baseChange_nonsingular (f := Algebra.ofId F W.toAffine.FunctionField) (algebraMap F _).injective c d).mp h'`. Establish `hS : genericPoint W + constPoint W R = constPoint W (.some c d hcd)`. Rewrite using `[e]`. Take `⟨h'', e''⟩` from `constPoint_some W hcd`. Rewrite using `[e'']`.

Simplify using `only [Point.some.injEq]`. Conclude with `⟨hc.symm, hd.symm⟩`. Apply `constPoint_ne_genericPoint W (.some c d hcd - R)` to reduce the goal to its premises. Rewrite using `[map_sub, ← hS, add_sub_cancel_right]`.
-/
theorem transcendental_xOf_translate [IsAlgClosed F] (R : W.toAffine.Point) :
    Transcendental F (xOf _ (genericPoint W + constPoint W R)) := by
  intro halg
  obtain ⟨h, e⟩ := exists_translate_eq W R
  obtain ⟨c, hc⟩ := exists_algebraMap_eq_of_isAlgebraic W halg
  set u := xOf _ (genericPoint W + constPoint W R)
  set v := yOf _ (genericPoint W + constPoint W R)
  have heq := (equation_iff _ _).mp h.1
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at heq
  have hvalg : IsAlgebraic F v := by
    refine ⟨X ^ 2 + C (W.a₁ * c + W.a₃) * X - C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆), ?_, ?_⟩
    · intro h0
      have := congrArg natDegree h0
      rw [natDegree_zero] at this
      have h2 : (X ^ 2 + C (W.a₁ * c + W.a₃) * X -
          C (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) : F[X]).natDegree = 2 := by
        compute_degree!
      omega
    · simp only [map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, hc]
      linear_combination heq
  obtain ⟨d, hd⟩ := exists_algebraMap_eq_of_isAlgebraic W hvalg
  have hcd : W.toAffine.Nonsingular c d := by
    have h' := h
    rw [← hc, ← hd] at h'
    exact (W.toAffine.baseChange_nonsingular (f := Algebra.ofId F W.toAffine.FunctionField)
      (algebraMap F _).injective c d).mp h'
  have hS : genericPoint W + constPoint W R = constPoint W (.some c d hcd) := by
    rw [e]
    obtain ⟨h'', e''⟩ := constPoint_some W hcd
    rw [e'']
    simp only [Point.some.injEq]
    exact ⟨hc.symm, hd.symm⟩
  apply constPoint_ne_genericPoint W (.some c d hcd - R)
  rw [map_sub, ← hS, add_sub_cancel_right]

noncomputable def translate [IsAlgClosed F] (R : W.toAffine.Point) :
    W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField :=
  liftPoint W (exists_translate_eq W R).choose.1 (transcendental_xOf_translate W R)

variable [IsAlgClosed F]

/- English proof (translation)
Rewrite using `[translate, map_liftPoint_genericPoint]`. Conclude with `(exists_translate_eq W R).choose_spec.symm`.
-/
theorem map_translate_genericPoint (R : W.toAffine.Point) :
    Point.map (translate W R) (genericPoint W) = genericPoint W + constPoint W R := by
  rw [translate, map_liftPoint_genericPoint]
  exact (exists_translate_eq W R).choose_spec.symm

/- English proof (translation)
Apply `algHom_eq_of_map_genericPoint` to reduce the goal to its premises. Rewrite using `[map_translate_genericPoint, map_zero, add_zero, map_id_genericPoint]`.
-/
theorem translate_zero : translate W 0 = AlgHom.id F W.toAffine.FunctionField := by
  apply algHom_eq_of_map_genericPoint
  rw [map_translate_genericPoint, map_zero, add_zero, map_id_genericPoint]

/- English proof (translation)
Apply `algHom_eq_of_map_genericPoint` to reduce the goal to its premises. Rewrite using `[← Point.map_map, map_translate_genericPoint, map_add, map_translate_genericPoint, map_constPoint, add_assoc, ← map_add, add_neg_cancel, map_zero, add_zero, map_id_genericPoint]`.
-/
theorem translate_comp_translate_neg (R : W.toAffine.Point) :
    (translate W R).comp (translate W (-R)) = AlgHom.id F W.toAffine.FunctionField := by
  apply algHom_eq_of_map_genericPoint
  rw [← Point.map_map, map_translate_genericPoint, map_add, map_translate_genericPoint,
    map_constPoint, add_assoc, ← map_add, add_neg_cancel, map_zero, add_zero, map_id_genericPoint]

/- English proof (translation)
The claim follows from `DFunLike.congr_fun (translate_comp_translate_neg W R) f`.
-/
theorem translate_translate_neg (R : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    translate W R (translate W (-R) f) = f :=
  DFunLike.congr_fun (translate_comp_translate_neg W R) f

local notation "ι" => algebraMap F (WeierstrassCurve.Affine.FunctionField
  (WeierstrassCurve.toAffine W))

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Establish `h` using `ordInfty_X W`. Establish `h0 : genX W ≠ 0`. Introduce `h0`. Express the relevant statement in the definitionally equal form `ordInfty W (genX W) = -2 at h`. Rewrite `h` using `[h0]`.

Simplify using `[ordInfty] at h`. Rewrite using `[valuationInfty_eq_exp W h0]`. Express the relevant statement in the definitionally equal form `exp (-ordInfty W (genX W)) = _`. Rewrite using `[show ordInfty W (genX W) = -2 from h]`. Both sides reduce to the same expression.
-/
theorem valuationInfty_genX : valuationInfty W (genX W) = exp 2 := by
  have h := ordInfty_X W
  have h0 : genX W ≠ 0 := by
    intro h0
    change ordInfty W (genX W) = -2 at h
    rw [h0] at h
    simp [ordInfty] at h
  rw [valuationInfty_eq_exp W h0]
  change exp (-ordInfty W (genX W)) = _
  rw [show ordInfty W (genX W) = -2 from h]
  rfl

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Establish `h` using `ordInfty_Y W`. Rewrite using `[valuationInfty_eq_exp W (genY_ne_zero W)]`. Express the relevant statement in the definitionally equal form `exp (-ordInfty W (genY W)) = _`. Rewrite using `[show ordInfty W (genY W) = -3 from h]`. Both sides reduce to the same expression.
-/
theorem valuationInfty_genY : valuationInfty W (genY W) = exp 3 := by
  have h := ordInfty_Y W
  rw [valuationInfty_eq_exp W (genY_ne_zero W)]
  change exp (-ordInfty W (genY W)) = _
  rw [show ordInfty W (genY W) = -3 from h]
  rfl

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Break down `eq_or_ne c 0 with rfl | hc` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc), ordInfty_algebraMap_const W hc, neg_zero, exp_zero]`.
-/
theorem valuationInfty_const_le (c : F) : valuationInfty W (ι c) ≤ 1 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc),
      ordInfty_algebraMap_const W hc, neg_zero, exp_zero]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Rewrite using `[Valuation.map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem valuationInfty_const_mul_le (c : F) {t : W.toAffine.FunctionField} {g : ℤᵐ⁰}
    (ht : valuationInfty W t ≤ g) : valuationInfty W (ι c * t) ≤ g := by
  rw [Valuation.map_mul]
  calc _ ≤ 1 * valuationInfty W t := mul_le_mul_left (valuationInfty_const_le W c) _
    _ ≤ g := by rw [one_mul]; exact ht

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Rewrite using `[Valuation.map_sub_eq_of_lt_left _ ?_, valuationInfty_genX]`. Rewrite using `[valuationInfty_genX]`. Conclude with `lt_of_le_of_lt (valuationInfty_const_le W c) (by rw [← exp_zero, exp_lt_exp]; norm_num)`.
-/
theorem valuationInfty_genX_sub_const (c : F) :
    valuationInfty W (genX W - ι c) = exp 2 := by
  rw [Valuation.map_sub_eq_of_lt_left _ ?_, valuationInfty_genX]
  rw [valuationInfty_genX]
  exact lt_of_le_of_lt (valuationInfty_const_le W c) (by rw [← exp_zero, exp_lt_exp]; norm_num)

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Introduce `h`. Use `valuationInfty_genX_sub_const W c` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `exp_ne_zero this.symm`.
-/
theorem genX_sub_const_ne_zero (c : F) : genX W - ι c ≠ 0 := by
  intro h
  have := valuationInfty_genX_sub_const W c
  rw [h, map_zero] at this
  exact exp_ne_zero this.symm

/- English proof (translation)
Establish `hne : genX W ≠ ι xR` using `fun h => genX_sub_const_ne_zero W xR (sub_eq_zero.mpr h)`. Take `⟨hR', eR⟩` from `constPoint_some W hR`. Establish `hx : translate W (.some xR yR hR) (genX W) = xOf _ (genericPoint W + constPoint W (.some xR yR hR))` using `liftPoint_genX _ _ _`. Establish `hy : translate W (.some xR yR hR) (genY W) = yOf _ (genericPoint W + constPoint W (.some xR yR hR))` using `liftPoint_genY _ _ _`. Rewrite `hx`, `hy` using `[eR, genericPoint, Point.add_of_X_ne hne]`.

Simplify using `only [xOf, yOf] at hx hy`. Rewrite `hx`, `hy` using `[slope_of_X_ne hne]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Simplify using `[addX, WeierstrassCurve.baseChange]`.

Rewrite using `[hy, hx]`. Simplify using `[addY, negY, negAddY, addX, WeierstrassCurve.baseChange]`.
-/
theorem translate_coords {xR yR : F} (hR : W.toAffine.Nonsingular xR yR) :
    translate W (.some xR yR hR) (genX W) =
        ((genY W - ι yR) / (genX W - ι xR)) ^ 2 + ι W.a₁ * ((genY W - ι yR) / (genX W - ι xR)) -
          ι W.a₂ - genX W - ι xR ∧
      translate W (.some xR yR hR) (genY W) =
        -((genY W - ι yR) / (genX W - ι xR) * (translate W (.some xR yR hR) (genX W) - genX W) +
          genY W) - ι W.a₁ * translate W (.some xR yR hR) (genX W) - ι W.a₃ := by
  have hne : genX W ≠ ι xR := fun h => genX_sub_const_ne_zero W xR (sub_eq_zero.mpr h)
  obtain ⟨hR', eR⟩ := constPoint_some W hR
  have hx : translate W (.some xR yR hR) (genX W) =
      xOf _ (genericPoint W + constPoint W (.some xR yR hR)) := liftPoint_genX _ _ _
  have hy : translate W (.some xR yR hR) (genY W) =
      yOf _ (genericPoint W + constPoint W (.some xR yR hR)) := liftPoint_genY _ _ _
  rw [eR, genericPoint, Point.add_of_X_ne hne] at hx hy
  simp only [xOf, yOf] at hx hy
  rw [slope_of_X_ne hne] at hx hy
  refine ⟨?_, ?_⟩
  · rw [hx]
    simp [addX, WeierstrassCurve.baseChange]
  · rw [hy, hx]
    simp [addY, negY, negAddY, addX, WeierstrassCurve.baseChange]

/- English proof (translation)
Take `⟨hu, -⟩` from `translate_coords W hR`. Use `set u := translate W (.some xR yR hR) (genX W)`. Use `set D := genX W - ι xR with hDdef`. Establish `hD : D ≠ 0` using `genX_sub_const_ne_zero W xR`. Use `set ℓ := (genY W - ι yR) / D`.

Establish `hℓ : ℓ * D = genY W - ι yR` using `div_mul_cancel₀ _ hD`. Establish `hid : D ^ 2 * (u - ι xR) = ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W + ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W + ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2)`. Rewrite using `[hu]`. Simplify using `only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]`. Take the linear combination `(ℓ * D + (genY W - ι yR)) * hℓ + ι W.a₁ * D * hℓ + genY_sq_add W`.

Establish `hN : valuationInfty W (ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W + ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W + ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2)) ≤ exp 3`. Use `Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_` and prove the remaining obligations. Conclude with `valuationInfty_const_mul_le W _ (valuationInfty_genY W).le`. Conclude with `valuationInfty_const_mul_le W _ (by rw [valuationInfty_genX, exp_le_exp]; norm_num)`. Conclude with `(valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num)`.

Establish `hv` using `congrArg (valuationInfty W) hid`. Rewrite `hv` using `[Valuation.map_mul, Valuation.map_pow, valuationInfty_genX_sub_const]`. Rewrite `hN` using `[← hv]`. Assume the negation of the conclusion as `hge`. Rewrite `hge` using `[not_lt]`.

Establish `: exp 2 ^ 2 ≤ exp 2 ^ 2 * valuationInfty W (u - ι xR)` using `le_mul_of_one_le_right' hge`. Establish `h4 : (exp 2 : ℤᵐ⁰) ^ 2 = exp 4` using `by rw [← exp_nsmul]; norm_num`. Rewrite `this` using `[h4]`. Use `this.trans hN` as an intermediate fact. Rewrite `this` using `[exp_le_exp]`.

Evaluate the numerical expressions using `at this`.
-/
theorem valuationInfty_translate_genX_sub_lt {xR yR : F} (hR : W.toAffine.Nonsingular xR yR) :
    valuationInfty W (translate W (.some xR yR hR) (genX W) - ι xR) < 1 := by
  obtain ⟨hu, -⟩ := translate_coords W hR
  set u := translate W (.some xR yR hR) (genX W)
  set D := genX W - ι xR with hDdef
  have hD : D ≠ 0 := genX_sub_const_ne_zero W xR
  set ℓ := (genY W - ι yR) / D
  have hℓ : ℓ * D = genY W - ι yR := div_mul_cancel₀ _ hD
  have hid : D ^ 2 * (u - ι xR) = ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W +
      ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W +
      ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2) := by
    rw [hu]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
    linear_combination (ℓ * D + (genY W - ι yR)) * hℓ + ι W.a₁ * D * hℓ + genY_sq_add W
  have hN : valuationInfty W (ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W +
      ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W +
      ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2)) ≤ exp 3 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_
    · exact valuationInfty_const_mul_le W _ (valuationInfty_genY W).le
    · exact valuationInfty_const_mul_le W _ (by rw [valuationInfty_genX, exp_le_exp]; norm_num)
    · exact (valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
  have hv := congrArg (valuationInfty W) hid
  rw [Valuation.map_mul, Valuation.map_pow, valuationInfty_genX_sub_const] at hv
  rw [← hv] at hN
  by_contra hge
  rw [not_lt] at hge
  have : exp 2 ^ 2 ≤ exp 2 ^ 2 * valuationInfty W (u - ι xR) := le_mul_of_one_le_right' hge
  have h4 : (exp 2 : ℤᵐ⁰) ^ 2 = exp 4 := by rw [← exp_nsmul]; norm_num
  rw [h4] at this
  have := this.trans hN
  rw [exp_le_exp] at this
  norm_num at this

/- English proof (translation)
Take `⟨hu, hvv⟩` from `translate_coords W hR`. Use `set u := translate W (.some xR yR hR) (genX W)`. Use `set vv := translate W (.some xR yR hR) (genY W)`. Use `set D := genX W - ι xR with hDdef`. Establish `hD : D ≠ 0` using `genX_sub_const_ne_zero W xR`.

Use `set ℓ := (genY W - ι yR) / D`. Establish `hℓ : ℓ * D = genY W - ι yR` using `div_mul_cancel₀ _ hD`. Establish `hid : D ^ 2 * (u - ι xR) = ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W + ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W + ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2)`. Rewrite using `[hu]`. Simplify using `only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]`.

Take the linear combination `(ℓ * D + (genY W - ι yR)) * hℓ + ι W.a₁ * D * hℓ + genY_sq_add W`. Establish `hid2 : D ^ 3 * (vv - ι yR) = (ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W + ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 - W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) * genY W + ι (W.a₁ ^ 2 * yR - W.a₁ * W.a₂ * x …`. Rewrite using `[hvv]`. Simplify using `only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat] at hid ⊢`. Take the linear combination `(-(D ^ 2 * u) + D ^ 2 * genX W) * hℓ + (-(genY W - ι yR) - ι W.a₁ * D) * hid + (ι W.a₁ * ι xR + ι W.a₃ + 2 * ι yR) * genY_sq_add W`.

Establish `hx2 : valuationInfty W (genX W) ≤ exp 5`. Rewrite using `[valuationInfty_genX, exp_le_exp]`. Evaluate the numerical expressions. Establish `hM : valuationInfty W ((ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W + ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 - W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) * genY W + ι (W.a₁ ^ 2 * yR - W.a₁ * W.a₂ * xR - W. …`. Use `Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_` and prove the remaining obligations.

Rewrite using `[Valuation.map_mul, valuationInfty_genY]`. Establish `h1 : valuationInfty W (ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W + ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 - W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) ≤ exp 2` using `Valuation.map_add_le _ (valuationInfty_const_mul_le W _ (valuationInfty_genX W).le) ((valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num))`. Combine the equalities or inequalities in the displayed calculation. Use `valuationInfty_const_mul_le W _ ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_pow, valuationInfty_genX, ← exp_nsmul, exp_le_exp]`.

Evaluate the numerical expressions. Conclude with `valuationInfty_const_mul_le W _ hx2`. Conclude with `(valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num)`. Establish `hv` using `congrArg (valuationInfty W) hid2`. Rewrite `hv` using `[Valuation.map_mul, Valuation.map_pow, valuationInfty_genX_sub_const]`.

Rewrite `hM` using `[← hv]`. Assume the negation of the conclusion as `hge`. Rewrite `hge` using `[not_lt]`. Establish `: exp 2 ^ 3 ≤ exp 2 ^ 3 * valuationInfty W (vv - ι yR)` using `le_mul_of_one_le_right' hge`. Establish `h6 : (exp 2 : ℤᵐ⁰) ^ 3 = exp 6` using `by rw [← exp_nsmul]; norm_num`.

Rewrite `this` using `[h6]`. Use `this.trans hM` as an intermediate fact. Rewrite `this` using `[exp_le_exp]`. Evaluate the numerical expressions using `at this`.
-/
theorem valuationInfty_translate_genY_sub_lt {xR yR : F} (hR : W.toAffine.Nonsingular xR yR) :
    valuationInfty W (translate W (.some xR yR hR) (genY W) - ι yR) < 1 := by
  obtain ⟨hu, hvv⟩ := translate_coords W hR
  set u := translate W (.some xR yR hR) (genX W)
  set vv := translate W (.some xR yR hR) (genY W)
  set D := genX W - ι xR with hDdef
  have hD : D ≠ 0 := genX_sub_const_ne_zero W xR
  set ℓ := (genY W - ι yR) / D
  have hℓ : ℓ * D = genY W - ι yR := div_mul_cancel₀ _ hD
  have hid : D ^ 2 * (u - ι xR) = ι (-(W.a₁ * xR + W.a₃ + 2 * yR)) * genY W +
      ι (3 * xR ^ 2 + 2 * W.a₂ * xR + W.a₄ - W.a₁ * yR) * genX W +
      ι (W.a₁ * xR * yR - W.a₂ * xR ^ 2 + W.a₆ - 2 * xR ^ 3 + yR ^ 2) := by
    rw [hu]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
    linear_combination (ℓ * D + (genY W - ι yR)) * hℓ + ι W.a₁ * D * hℓ + genY_sq_add W
  have hid2 : D ^ 3 * (vv - ι yR) =
      (ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W +
        ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 -
          W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) * genY W +
      ι (W.a₁ ^ 2 * yR - W.a₁ * W.a₂ * xR - W.a₁ * W.a₄ + W.a₂ * W.a₃ + 2 * W.a₂ * yR +
        3 * W.a₃ * xR + 6 * xR * yR) * genX W ^ 2 +
      ι (-2 * W.a₁ ^ 2 * xR * yR + 3 * W.a₁ * W.a₂ * xR ^ 2 + 2 * W.a₁ * W.a₄ * xR -
        W.a₁ * W.a₆ + 2 * W.a₁ * xR ^ 3 - 2 * W.a₁ * yR ^ 2 + 2 * W.a₂ * xR * yR + W.a₃ * W.a₄ -
        3 * W.a₃ * xR ^ 2 + 3 * W.a₄ * yR - 3 * xR ^ 2 * yR) * genX W +
      ι (W.a₁ ^ 2 * xR ^ 2 * yR - W.a₁ * W.a₂ * xR ^ 3 + 2 * W.a₁ * W.a₆ * xR - W.a₁ * xR ^ 4 +
        2 * W.a₁ * xR * yR ^ 2 - W.a₂ * xR ^ 2 * yR + W.a₃ * W.a₆ + W.a₃ * xR ^ 3 +
        3 * W.a₆ * yR + yR ^ 3) := by
    rw [hvv]
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat] at hid ⊢
    linear_combination (-(D ^ 2 * u) + D ^ 2 * genX W) * hℓ +
      (-(genY W - ι yR) - ι W.a₁ * D) * hid +
      (ι W.a₁ * ι xR + ι W.a₃ + 2 * ι yR) * genY_sq_add W
  have hx2 : valuationInfty W (genX W) ≤ exp 5 := by
    rw [valuationInfty_genX, exp_le_exp]; norm_num
  have hM : valuationInfty W ((ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W +
        ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 -
          W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) * genY W +
      ι (W.a₁ ^ 2 * yR - W.a₁ * W.a₂ * xR - W.a₁ * W.a₄ + W.a₂ * W.a₃ + 2 * W.a₂ * yR +
        3 * W.a₃ * xR + 6 * xR * yR) * genX W ^ 2 +
      ι (-2 * W.a₁ ^ 2 * xR * yR + 3 * W.a₁ * W.a₂ * xR ^ 2 + 2 * W.a₁ * W.a₄ * xR -
        W.a₁ * W.a₆ + 2 * W.a₁ * xR ^ 3 - 2 * W.a₁ * yR ^ 2 + 2 * W.a₂ * xR * yR + W.a₃ * W.a₄ -
        3 * W.a₃ * xR ^ 2 + 3 * W.a₄ * yR - 3 * xR ^ 2 * yR) * genX W +
      ι (W.a₁ ^ 2 * xR ^ 2 * yR - W.a₁ * W.a₂ * xR ^ 3 + 2 * W.a₁ * W.a₆ * xR - W.a₁ * xR ^ 4 +
        2 * W.a₁ * xR * yR ^ 2 - W.a₂ * xR ^ 2 * yR + W.a₃ * W.a₆ + W.a₃ * xR ^ 3 +
        3 * W.a₆ * yR + yR ^ 3)) ≤ exp 5 := by
    refine Valuation.map_add_le _ (Valuation.map_add_le _ (Valuation.map_add_le _ ?_ ?_) ?_) ?_
    · rw [Valuation.map_mul, valuationInfty_genY]
      have h1 : valuationInfty W (ι (W.a₁ * yR - 2 * W.a₂ * xR - W.a₄ - 3 * xR ^ 2) * genX W +
          ι (-W.a₁ ^ 2 * xR ^ 2 - 2 * W.a₁ * W.a₃ * xR - 4 * W.a₁ * xR * yR + W.a₂ * xR ^ 2 -
            W.a₃ ^ 2 - 3 * W.a₃ * yR - W.a₆ + 2 * xR ^ 3 - 3 * yR ^ 2)) ≤ exp 2 :=
        Valuation.map_add_le _ (valuationInfty_const_mul_le W _ (valuationInfty_genX W).le)
          ((valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num))
      calc _ ≤ exp 2 * exp 3 := mul_le_mul_left h1 _
        _ = exp 5 := by rw [← exp_add]; norm_num
    · refine valuationInfty_const_mul_le W _ ?_
      rw [Valuation.map_pow, valuationInfty_genX, ← exp_nsmul, exp_le_exp]; norm_num
    · exact valuationInfty_const_mul_le W _ hx2
    · exact (valuationInfty_const_le W _).trans (by rw [← exp_zero, exp_le_exp]; norm_num)
  have hv := congrArg (valuationInfty W) hid2
  rw [Valuation.map_mul, Valuation.map_pow, valuationInfty_genX_sub_const] at hv
  rw [← hv] at hM
  by_contra hge
  rw [not_lt] at hge
  have : exp 2 ^ 3 ≤ exp 2 ^ 3 * valuationInfty W (vv - ι yR) := le_mul_of_one_le_right' hge
  have h6 : (exp 2 : ℤᵐ⁰) ^ 3 = exp 6 := by rw [← exp_nsmul]; norm_num
  rw [h6] at this
  have := this.trans hM
  rw [exp_le_exp] at this
  norm_num at this

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Rewrite using `[← algebraMap_X_sub_C, ← IsScalarTower.algebraMap_apply, map_sub, algebraMap_C_functionField, ← genX_eq]`.
-/
theorem algebraMap_XClass (x : F) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (XClass W.toAffine x) =
      genX W - ι x := by
  rw [← algebraMap_X_sub_C, ← IsScalarTower.algebraMap_apply, map_sub,
    algebraMap_C_functionField, ← genX_eq]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/- English proof (translation)
Rewrite using `[YClass, map_sub, map_sub]`. Both sides reduce to the same expression.
-/
theorem algebraMap_YClass (y : F) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField (YClass W.toAffine (C y)) =
      genY W - ι y := by
  rw [YClass, map_sub, map_sub]
  rfl

/- English proof (translation)
Consider the cases of `R with`. Consider the case `zero`. Rewrite using `[show (Point.zero : W.toAffine.Point) = 0 from rfl, translate_zero]`. Both sides reduce to the same expression. Consider the case `some xR yR hR`.

Set `w` to `(valuationInfty W).comap (translate W (.some xR yR hR)).toRingHom`. Establish `hwapp : ∀ g, w g = valuationInfty W (translate W (.some xR yR hR) g)` using `fun g => rfl`. Establish `hF : ∀ c : F, c ≠ 0 → w (ι c) = 1` using `fun c hc => by`. Rewrite using `[hwapp, AlgHom.commutes, valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc), ordInfty_algebraMap_const W hc, neg_zero, exp_zero]`. Establish `hx : w (genX W) ≤ 1`.

Rewrite using `[hwapp, ← sub_add_cancel (translate W (.some xR yR hR) (genX W)) (ι xR)]`. Conclude with `Valuation.map_add_le _ (valuationInfty_translate_genX_sub_lt W hR).le (valuationInfty_const_le W xR)`. Take `⟨t, ht⟩` from `exists_valuationPoint_eq_exp_neg_one W 0`. Express the relevant statement in the definitionally equal form `valuationInfty W t = exp (-1) at ht`. Establish `hinv` using `translate_translate_neg W (.some xR yR hR) t`.

Establish `ht0 : translate W (-(.some xR yR hR)) t ≠ 0`. Introduce `h0`. Rewrite `hinv` using `[h0, map_zero]`. Rewrite `ht` using `[← hinv, map_zero]`. Conclude with `exp_ne_zero ht.symm`.

Establish `hwt : w (translate W (-(.some xR yR hR)) t) = exp (-1)` using `by rw [hwapp, hinv, ht]`. Establish `hnt : ∃ g, g ≠ 0 ∧ w g ≠ 1` using `⟨_, ht0, by`. Rewrite using `[hwt, Ne, ← exp_zero, exp_inj]`. Use the proof step `norm_num⟩`. Take `⟨v, hv, e, he, hwe⟩` from `exists_eq_pow_valuation_of_le_one w hF hx hnt`.

Establish `hvR : v = heightOneOfNonsingular hR`. Establish `hle : XYIdeal W.toAffine xR (C yR) ≤ v.asIdeal`. Rewrite using `[XYIdeal, Ideal.span_le]`. Introduce and unpack `_ (rfl | rfl)`. Rewrite using `[SetLike.mem_coe, hv, algebraMap_XClass, hwapp, map_sub, AlgHom.commutes]`.

Conclude with `valuationInfty_translate_genX_sub_lt W hR`. Rewrite using `[SetLike.mem_coe, hv, algebraMap_YClass, hwapp, map_sub, AlgHom.commutes]`. Conclude with `valuationInfty_translate_genY_sub_lt W hR`. Conclude with `HeightOneSpectrum.ext ((isMaximal_XYIdeal hR.1).eq_of_le v.isPrime.ne_top hle).symm`. Substitute `hvR` using the available equality.

Establish `he1 : e = 1`. Establish `h1` using `hwe (translate W (-(.some xR yR hR)) t)`. Rewrite `h1` using `[hwt]`. Establish `hγ : (heightOneOfNonsingular hR).valuation W.toAffine.FunctionField (translate W (-(.some xR yR hR)) t) ≠ 0` using `(Valuation.ne_zero_iff _).mpr ht0`. Take `⟨g, hg⟩ : ∃ g : ℤ, (heightOneOfNonsingular hR).valuation W.toAffine.FunctionField (translate W (-(.some xR yR hR)) t) = exp g` from `⟨_, (exp_log hγ).symm⟩`.

Rewrite `h1` using `[hg, ← exp_nsmul, exp_inj, nsmul_eq_mul]`. Establish `hdvd : (e : ℤ) ∣ 1` using `⟨-g, by linarith⟩`. Use `Int.eq_one_of_dvd_one (by positivity) hdvd` as an intermediate fact. Conclude with `this` after adjusting the coercions. Substitute `he1` using the available equality.

Rewrite using `[← hwapp, hwe, pow_one]`. Both sides reduce to the same expression.
-/
theorem valuationInfty_translate (R : W.toAffine.Point) (f : W.toAffine.FunctionField) :
    valuationInfty W (translate W R f) = valuationPoint W R f := by
  cases R with
  | zero =>
    rw [show (Point.zero : W.toAffine.Point) = 0 from rfl, translate_zero]
    rfl
  | some xR yR hR =>
    let w := (valuationInfty W).comap (translate W (.some xR yR hR)).toRingHom
    have hwapp : ∀ g, w g = valuationInfty W (translate W (.some xR yR hR) g) := fun g => rfl
    have hF : ∀ c : F, c ≠ 0 → w (ι c) = 1 := fun c hc => by
      rw [hwapp, AlgHom.commutes,
        valuationInfty_eq_exp W ((map_ne_zero_iff _ (algebraMap F _).injective).mpr hc),
        ordInfty_algebraMap_const W hc, neg_zero, exp_zero]
    have hx : w (genX W) ≤ 1 := by
      rw [hwapp, ← sub_add_cancel (translate W (.some xR yR hR) (genX W)) (ι xR)]
      exact Valuation.map_add_le _ (valuationInfty_translate_genX_sub_lt W hR).le
        (valuationInfty_const_le W xR)
    obtain ⟨t, ht⟩ := exists_valuationPoint_eq_exp_neg_one W 0
    change valuationInfty W t = exp (-1) at ht
    have hinv := translate_translate_neg W (.some xR yR hR) t
    have ht0 : translate W (-(.some xR yR hR)) t ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hinv
      rw [← hinv, map_zero] at ht
      exact exp_ne_zero ht.symm
    have hwt : w (translate W (-(.some xR yR hR)) t) = exp (-1) := by rw [hwapp, hinv, ht]
    have hnt : ∃ g, g ≠ 0 ∧ w g ≠ 1 := ⟨_, ht0, by
      rw [hwt, Ne, ← exp_zero, exp_inj]; norm_num⟩
    obtain ⟨v, hv, e, he, hwe⟩ := exists_eq_pow_valuation_of_le_one w hF hx hnt
    have hvR : v = heightOneOfNonsingular hR := by
      have hle : XYIdeal W.toAffine xR (C yR) ≤ v.asIdeal := by
        rw [XYIdeal, Ideal.span_le]
        rintro _ (rfl | rfl)
        · rw [SetLike.mem_coe, hv, algebraMap_XClass, hwapp, map_sub, AlgHom.commutes]
          exact valuationInfty_translate_genX_sub_lt W hR
        · rw [SetLike.mem_coe, hv, algebraMap_YClass, hwapp, map_sub, AlgHom.commutes]
          exact valuationInfty_translate_genY_sub_lt W hR
      exact HeightOneSpectrum.ext ((isMaximal_XYIdeal hR.1).eq_of_le v.isPrime.ne_top hle).symm
    subst hvR
    have he1 : e = 1 := by
      have h1 := hwe (translate W (-(.some xR yR hR)) t)
      rw [hwt] at h1
      have hγ : (heightOneOfNonsingular hR).valuation W.toAffine.FunctionField
          (translate W (-(.some xR yR hR)) t) ≠ 0 := (Valuation.ne_zero_iff _).mpr ht0
      obtain ⟨g, hg⟩ : ∃ g : ℤ, (heightOneOfNonsingular hR).valuation W.toAffine.FunctionField
          (translate W (-(.some xR yR hR)) t) = exp g := ⟨_, (exp_log hγ).symm⟩
      rw [hg, ← exp_nsmul, exp_inj, nsmul_eq_mul] at h1
      have hdvd : (e : ℤ) ∣ 1 := ⟨-g, by linarith⟩
      have := Int.eq_one_of_dvd_one (by positivity) hdvd
      exact_mod_cast this
    subst he1
    rw [← hwapp, hwe, pow_one]
    rfl

end GroundTheory.Arith.Abelian
