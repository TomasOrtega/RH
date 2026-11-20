import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Introduce `i j h`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `e : k ≤ i`. Rewrite using `[hN i k e, zero_mul]`.

Rewrite using `[hU k j (lt_of_le_of_lt h (not_le.mp e)), mul_zero]`.
-/
private theorem UpperTheory.V.Ws.Bl.sup_mul_up {R : Type} [CommRing R] {N U : M4 R} (hN : IsSUp N) (hU : IsUp U) :
    IsSUp (N * U) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases e : k ≤ i
  · rw [hN i k e, zero_mul]
  · rw [hU k j (lt_of_le_of_lt h (not_le.mp e)), mul_zero]

/- English proof (translation)
Introduce `R _ X X' Z y u hX hX' hX'X hZM hyM hu hUp hS`. Establish `g` using `grp R`. Establish `hZ : Z ∈ hAB R` using `hZM.1`. Establish `hy : y ∈ hAB R` using `hyM.1`. Establish `hys : adj y = -y` using `hyM.2`.

Establish `hP : X * y * X' ∈ hAB R` using `hAB_mul_mul hX hy hX'`. Establish `hyZ : y * Z = 0` using `hAB_mul_hAB hy hZ`. Establish `hyP : y * (X * y * X') = 0` using `hAB_mul_hAB hy hP`. Establish `hZP : Z * (X * y * X') = 0` using `hAB_mul_hAB hZ hP`. Establish `adjneg : ∀ W : M4 R, adj (-W) = -adj W`.

Introduce `W`. Rewrite using `[← neg_one_smul R W, g.2.2.2.1, neg_one_smul]`. Establish `huu : u * adj u = 1`. Establish `h : adj u * u = 1`. Establish `h0 : adj u * u = (1 : R) • 1` using `hu`.

Rewrite using `[h0, one_smul]`. Conclude with `mul_eq_one_comm.mp h`. Establish `e0 : (1 + y) * (1 + Z) = 1 + y + Z`. Rewrite using `[add_mul, one_mul, mul_add, mul_one, hyZ, add_zero]`. Normalize the expressions using the abelian group laws.

Establish `e1 : X * (1 + -y) = (1 - X * y * X') * X`. Rewrite using `[sub_mul, one_mul, mul_assoc (X * y), hX'X, mul_one, mul_add, mul_one, mul_neg, sub_eq_add_neg]`. Establish `e2 : (1 + y + Z) * (1 - X * y * X') = 1 + (Z - (X * y * X' - y))`. Rewrite using `[mul_sub, mul_one, add_mul, add_mul, one_mul, hyP, hZP]`. Normalize the expressions using the abelian group laws.

Establish `hmid : (1 + y) * ((1 + Z) * X) * (1 + -y) = (1 + (Z - (X * y * X' - y))) * X`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = (1 + y + Z) * ((1 - X * y * X') * X) := by rw [e0, e1]`. Use `_ = ((1 + y + Z) * (1 - X * y * X')) * X := (mul_assoc _ _ _).symm`.

Use `_ = (1 + (Z - (X * y * X' - y))) * X := by rw [e2]`. Establish `key : adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u) = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u)`. Rewrite using `[show (1 : M4 R) - y = 1 + -y from sub_eq_add_neg 1 y, g.1, g.2.2.1, g.2.2.2.2.1, adjneg, hys, neg_neg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[add_mul, one_mul, mul_add, add_mul]`.

Use `_ = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u) := by`. Use `congr 1`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc u (adj u), huu, one_mul]`. Rewrite using `[key]`.

Prove the components needed by the constructor for the conclusion. Introduce `i j hji`. Rewrite using `[Matrix.add_apply, hUp i j hji, sup_mul_up hS hUp i j hji.le, add_zero]`. Introduce `i`. Rewrite using `[Matrix.add_apply, sup_mul_up hS hUp i i le_rfl, add_zero]`.
-/
theorem UpperTheory.V.Ws.Bl.twistFlag :
    ∀ (R : Type) [CommRing R] (X X' Z y u : M4 R), IsBlock X → IsBlock X' → X' * X = 1 → Z ∈ uM R → y ∈ uM R → IsGSp 1 u → IsUp (adj u * X * u) → IsSUp (adj u * (Z - (X * y * X' - y)) * u) →
          IsUp (adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u)) ∧ ∀ i, (adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u) : M4 R) i i = (adj u * X * u : M4 R) i i := by
  intro R _ X X' Z y u hX hX' hX'X hZM hyM hu hUp hS
  have g := grp R
  have hZ : Z ∈ hAB R := hZM.1
  have hy : y ∈ hAB R := hyM.1
  have hys : adj y = -y := hyM.2
  have hP : X * y * X' ∈ hAB R := hAB_mul_mul hX hy hX'
  have hyZ : y * Z = 0 := hAB_mul_hAB hy hZ
  have hyP : y * (X * y * X') = 0 := hAB_mul_hAB hy hP
  have hZP : Z * (X * y * X') = 0 := hAB_mul_hAB hZ hP
  have adjneg : ∀ W : M4 R, adj (-W) = -adj W := by
    intro W
    rw [← neg_one_smul R W, g.2.2.2.1, neg_one_smul]
  have huu : u * adj u = 1 := by
    have h : adj u * u = 1 := by
      have h0 : adj u * u = (1 : R) • 1 := hu
      rw [h0, one_smul]
    exact mul_eq_one_comm.mp h
  have e0 : (1 + y) * (1 + Z) = 1 + y + Z := by
    rw [add_mul, one_mul, mul_add, mul_one, hyZ, add_zero]
    abel
  have e1 : X * (1 + -y) = (1 - X * y * X') * X := by
    rw [sub_mul, one_mul, mul_assoc (X * y), hX'X, mul_one, mul_add, mul_one, mul_neg, sub_eq_add_neg]
  have e2 : (1 + y + Z) * (1 - X * y * X') = 1 + (Z - (X * y * X' - y)) := by
    rw [mul_sub, mul_one, add_mul, add_mul, one_mul, hyP, hZP]
    abel
  have hmid : (1 + y) * ((1 + Z) * X) * (1 + -y) = (1 + (Z - (X * y * X' - y))) * X := by
    calc (1 + y) * ((1 + Z) * X) * (1 + -y) = ((1 + y) * (1 + Z)) * (X * (1 + -y)) := by
          simp only [mul_assoc]
      _ = (1 + y + Z) * ((1 - X * y * X') * X) := by rw [e0, e1]
      _ = ((1 + y + Z) * (1 - X * y * X')) * X := (mul_assoc _ _ _).symm
      _ = (1 + (Z - (X * y * X' - y))) * X := by rw [e2]
  have key : adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u)
      = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u) := by
    rw [show (1 : M4 R) - y = 1 + -y from sub_eq_add_neg 1 y, g.1, g.2.2.1, g.2.2.2.2.1, adjneg, hys, neg_neg]
    calc adj u * (1 + y) * ((1 + Z) * X) * ((1 + -y) * u)
          = adj u * ((1 + y) * ((1 + Z) * X) * (1 + -y)) * u := by simp only [mul_assoc]
      _ = adj u * ((1 + (Z - (X * y * X' - y))) * X) * u := by rw [hmid]
      _ = adj u * X * u + adj u * ((Z - (X * y * X' - y)) * X) * u := by
          rw [add_mul, one_mul, mul_add, add_mul]
      _ = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u) := by
          congr 1
          simp only [mul_assoc]
          rw [← mul_assoc u (adj u), huu, one_mul]
  rw [key]
  constructor
  · intro i j hji
    rw [Matrix.add_apply, hUp i j hji, sup_mul_up hS hUp i j hji.le, add_zero]
  · intro i
    rw [Matrix.add_apply, sup_mul_up hS hUp i i le_rfl, add_zero]
