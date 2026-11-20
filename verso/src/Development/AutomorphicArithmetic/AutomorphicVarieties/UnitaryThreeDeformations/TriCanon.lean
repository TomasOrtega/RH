import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Simplify using `[conjBy, GG.mat, hg]`.
-/
private theorem tc_conj_mat {R D : Type} [CommRing R] [Group D] (r : D →* GG 3 R) (h : GL (Fin 3) R) (g : D)
    (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

/- English proof (translation)
Establish `h1 : (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1`. Use extensionality with `a b`. Use `(residue_eq_zero_iff _).2 (hh a b)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, this]`.

Apply the tactic sequence `by_cases e : a = b <;> simp [Matrix.one_apply, e]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `: (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h).map (residue R) = 1`. Rewrite using `[Units.inv_mul]`. Simplify using the standard rewrite rules.

Rewrite `this` using `[Matrix.map_mul, h1, Matrix.mul_one]`. Then use the resulting hypothesis.
-/
private theorem tc_res {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h) :
    (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 ∧
      ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
  have h1 : (h : Matrix (Fin 3) (Fin 3) R).map (residue R) = 1 := by
    ext a b
    have := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [Matrix.map_apply, this]
    by_cases e : a = b <;> simp [Matrix.one_apply, e]
  refine ⟨h1, ?_⟩
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h).map (residue R) = 1 := by
    rw [Units.inv_mul]; simp
  rwa [Matrix.map_mul, h1, Matrix.mul_one] at this

/- English proof (translation)
Establish `: (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).map (residue R) = X.map (residue R)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, (tc_res h hh).1, (tc_res h hh).2, Matrix.one_mul, Matrix.mul_one]`. Conclude with `congrFun (congrFun this a) b`.
-/
private theorem tc_res_conj {R : Type} [CommRing R] [IsLocalRing R] (h : GL (Fin 3) R) (hh : InHat h)
    (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    residue R ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) a b) = residue R (X a b) := by
  have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h).map (residue R) = X.map (residue R) := by
    rw [Matrix.map_mul, Matrix.map_mul, (tc_res h hh).1, (tc_res h hh).2, Matrix.one_mul, Matrix.mul_one]
  exact congrFun (congrFun this a) b

/- English proof (translation)
Establish `e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1` using `Units.mul_inv t`. Establish `h1 : IsUnit ((t : O) - 1)`. Rewrite `ht` using `[show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring]`. Conclude with `isUnit_of_mul_isUnit_left ht`. Establish `h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O))`.

Use `ht.mul (t⁻¹).isUnit` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-(t : O)) * e`. Establish `h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O))`. Use `h1.mul (t⁻¹).isUnit` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-1 : O) * e`. Establish `h1'` using `h1.neg`. Establish `h2'` using `h2.neg`. Establish `h3'` using `h3.neg`.

Rewrite `h1'`, `h2'`, `h3'` using `[neg_sub]`. Establish `w0 : wt1 0 = 1` using `rfl`. Establish `w1 : wt1 1 = 0` using `rfl`. Establish `w2 : wt1 2 = -1` using `rfl`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;>`.

Apply the tactic sequence `simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg, Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption`.
-/
private theorem tc_unit {O : Type} [CommRing O] (t : Oˣ) (ht : IsUnit ((t : O) ^ 2 - 1)) (a b : Fin 3)
    (hab : a ≠ b) : IsUnit (((t ^ wt1 a : Oˣ) : O) - ((t ^ wt1 b : Oˣ) : O)) := by
  have e : (t : O) * ((t⁻¹ : Oˣ) : O) = 1 := Units.mul_inv t
  have h1 : IsUnit ((t : O) - 1) := by
    rw [show (t : O) ^ 2 - 1 = ((t : O) - 1) * (t + 1) by ring] at ht
    exact isUnit_of_mul_isUnit_left ht
  have h2 : IsUnit ((t : O) - ((t⁻¹ : Oˣ) : O)) := by
    have := ht.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-(t : O)) * e
  have h3 : IsUnit (1 - ((t⁻¹ : Oˣ) : O)) := by
    have := h1.mul (t⁻¹).isUnit
    convert this using 1
    linear_combination (-1 : O) * e
  have h1' := h1.neg
  have h2' := h2.neg
  have h3' := h3.neg
  rw [neg_sub] at h1' h2' h3'
  have w0 : wt1 0 = 1 := rfl
  have w1 : wt1 1 = 0 := rfl
  have w2 : wt1 2 = -1 := rfl
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg,
      Units.val_one, ne_eq, not_true_eq_false] at hab ⊢ <;> assumption

/- English proof (translation)
Establish `e10` using `congrFun (congrFun e 1) 0`. Establish `e20` using `congrFun (congrFun e 2) 0`. Establish `e21` using `congrFun (congrFun e 2) 1`. Establish `u10` using `hU 1 0 (by decide)`. Establish `u20` using `hU 2 0 (by decide)`.

Establish `u21` using `hU 2 1 (by decide)`. Establish `d10 : Δ 1 0 = 0` using `hΔ (by decide)`. Establish `d12 : Δ 1 2 = 0` using `hΔ (by decide)`. Establish `d20 : Δ 2 0 = 0` using `hΔ (by decide)`. Establish `d21 : Δ 2 1 = 0` using `hΔ (by decide)`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, d10, d12, d20, d21] at e10 e20 e21`. Establish `k10 : k 1 0 = 0` using `(hu 1 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e10)`. Establish `k20 : k 2 0 = 0` using `(hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)`. Establish `k21 : k 2 1 = 0` using `(hu 2 1 (by decide)).mul_right_eq_zero.1 (by`. Rewrite `e21` using `[k20]`.

Take the linear combination `e21)`. Introduce `a b hab`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)`.
-/
private theorem tc_up {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, wt a b < 0 → k a b = 0 := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d20 : Δ 2 0 = 0 := hΔ (by decide)
  have d21 : Δ 2 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, d10, d12, d20, d21] at e10 e20 e21
  have k10 : k 1 0 = 0 := (hu 1 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e10)
  have k20 : k 2 0 = 0 := (hu 2 0 (by decide)).mul_right_eq_zero.1 (by linear_combination e20)
  have k21 : k 2 1 = 0 := (hu 2 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k20] at e21; linear_combination e21)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

/- English proof (translation)
Establish `e01` using `congrFun (congrFun e 0) 1`. Establish `e02` using `congrFun (congrFun e 0) 2`. Establish `e12` using `congrFun (congrFun e 1) 2`. Establish `u01` using `hU 0 1 (by decide)`. Establish `u02` using `hU 0 2 (by decide)`.

Establish `u12` using `hU 1 2 (by decide)`. Establish `d10 : Δ 1 0 = 0` using `hΔ (by decide)`. Establish `d12 : Δ 1 2 = 0` using `hΔ (by decide)`. Establish `d02 : Δ 0 2 = 0` using `hΔ (by decide)`. Establish `d01 : Δ 0 1 = 0` using `hΔ (by decide)`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, d10, d12, d02, d01] at e01 e02 e12`. Establish `k12 : k 1 2 = 0` using `(hu 1 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e12)`. Establish `k02 : k 0 2 = 0` using `(hu 0 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e02)`. Establish `k01 : k 0 1 = 0` using `(hu 0 1 (by decide)).mul_right_eq_zero.1 (by`. Rewrite `e01` using `[k02]`.

Take the linear combination `e01)`. Introduce `a b hab`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)`.
-/
private theorem tc_low {R : Type} [CommRing R] (Δ k U : Matrix (Fin 3) (Fin 3) R) (e : Δ * k = k * U)
    (hΔ : Δ.IsDiag) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a b, a ≠ b → IsUnit (Δ a a - U b b)) :
    ∀ a b, 0 < wt a b → k a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have d10 : Δ 1 0 = 0 := hΔ (by decide)
  have d12 : Δ 1 2 = 0 := hΔ (by decide)
  have d02 : Δ 0 2 = 0 := hΔ (by decide)
  have d01 : Δ 0 1 = 0 := hΔ (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, d10, d12, d02, d01] at e01 e02 e12
  have k12 : k 1 2 = 0 := (hu 1 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e12)
  have k02 : k 0 2 = 0 := (hu 0 2 (by decide)).mul_right_eq_zero.1 (by linear_combination e02)
  have k01 : k 0 1 = 0 := (hu 0 1 (by decide)).mul_right_eq_zero.1 (by
    rw [k02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

/- English proof (translation)
Establish `e10` using `congrFun (congrFun e 1) 0`. Establish `e20` using `congrFun (congrFun e 2) 0`. Establish `e21` using `congrFun (congrFun e 2) 1`. Establish `e00` using `congrFun (congrFun e 0) 0`. Establish `e11` using `congrFun (congrFun e 1) 1`.

Establish `e22` using `congrFun (congrFun e 2) 2`. Establish `u10` using `hU 1 0 (by decide)`. Establish `u20` using `hU 2 0 (by decide)`. Establish `u21` using `hU 2 1 (by decide)`. Establish `k10` using `hk 1 0 (by decide)`.

Establish `k20` using `hk 2 0 (by decide)`. Establish `k21` using `hk 2 1 (by decide)`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, k10, k20, k21] at e10 e20 e21 e00 e11 e22`. Establish `m10 : M 1 0 = 0` using `(hu 0).mul_left_eq_zero.1 (by linear_combination e10)`. Establish `m20 : M 2 0 = 0` using `(hu 0).mul_left_eq_zero.1 (by linear_combination e20)`.

Establish `m21 : M 2 1 = 0` using `(hu 1).mul_left_eq_zero.1 (by rw [m20] at e21; linear_combination e21)`. Establish `m00 : M 0 0 = U 0 0` using `sub_eq_zero.1 ((hu 0).mul_left_eq_zero.1 (by linear_combination e00))`. Establish `m11 : M 1 1 = U 1 1` using `sub_eq_zero.1 ((hu 1).mul_left_eq_zero.1 (by`. Rewrite `e11` using `[m10]`. Take the linear combination `e11))`.

Establish `m22 : M 2 2 = U 2 2` using `sub_eq_zero.1 ((hu 2).mul_left_eq_zero.1 (by`. Rewrite `e22` using `[m20, m21]`. Take the linear combination `e22))`. Use `⟨fun a b hab => ?_, fun a => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)`.

Apply the tactic sequence `fin_cases a <;> assumption`.
-/
private theorem tc_up' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, wt a b < 0 → k a b = 0) (hU : ∀ a b, wt a b < 0 → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    (∀ a b, wt a b < 0 → M a b = 0) ∧ ∀ a, M a a = U a a := by
  have e10 := congrFun (congrFun e 1) 0
  have e20 := congrFun (congrFun e 2) 0
  have e21 := congrFun (congrFun e 2) 1
  have e00 := congrFun (congrFun e 0) 0
  have e11 := congrFun (congrFun e 1) 1
  have e22 := congrFun (congrFun e 2) 2
  have u10 := hU 1 0 (by decide)
  have u20 := hU 2 0 (by decide)
  have u21 := hU 2 1 (by decide)
  have k10 := hk 1 0 (by decide)
  have k20 := hk 2 0 (by decide)
  have k21 := hk 2 1 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u10, u20, u21, k10, k20, k21] at e10 e20 e21 e00 e11 e22
  have m10 : M 1 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e10)
  have m20 : M 2 0 = 0 := (hu 0).mul_left_eq_zero.1 (by linear_combination e20)
  have m21 : M 2 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m20] at e21; linear_combination e21)
  have m00 : M 0 0 = U 0 0 := sub_eq_zero.1 ((hu 0).mul_left_eq_zero.1 (by linear_combination e00))
  have m11 : M 1 1 = U 1 1 := sub_eq_zero.1 ((hu 1).mul_left_eq_zero.1 (by
    rw [m10] at e11; linear_combination e11))
  have m22 : M 2 2 = U 2 2 := sub_eq_zero.1 ((hu 2).mul_left_eq_zero.1 (by
    rw [m20, m21] at e22; linear_combination e22))
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)
  · fin_cases a <;> assumption

/- English proof (translation)
Establish `e01` using `congrFun (congrFun e 0) 1`. Establish `e02` using `congrFun (congrFun e 0) 2`. Establish `e12` using `congrFun (congrFun e 1) 2`. Establish `u01` using `hU 0 1 (by decide)`. Establish `u02` using `hU 0 2 (by decide)`.

Establish `u12` using `hU 1 2 (by decide)`. Establish `k01` using `hk 0 1 (by decide)`. Establish `k02` using `hk 0 2 (by decide)`. Establish `k12` using `hk 1 2 (by decide)`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, k01, k02, k12] at e01 e02 e12`.

Establish `m12 : M 1 2 = 0` using `(hu 2).mul_left_eq_zero.1 (by linear_combination e12)`. Establish `m02 : M 0 2 = 0` using `(hu 2).mul_left_eq_zero.1 (by linear_combination e02)`. Establish `m01 : M 0 1 = 0` using `(hu 1).mul_left_eq_zero.1 (by rw [m02] at e01; linear_combination e01)`. Introduce `a b hab`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)`.
-/
private theorem tc_low' {R : Type} [CommRing R] (M k U : Matrix (Fin 3) (Fin 3) R) (e : M * k = k * U)
    (hk : ∀ a b, 0 < wt a b → k a b = 0) (hU : ∀ a b, 0 < wt a b → U a b = 0) (hu : ∀ a, IsUnit (k a a)) :
    ∀ a b, 0 < wt a b → M a b = 0 := by
  have e01 := congrFun (congrFun e 0) 1
  have e02 := congrFun (congrFun e 0) 2
  have e12 := congrFun (congrFun e 1) 2
  have u01 := hU 0 1 (by decide)
  have u02 := hU 0 2 (by decide)
  have u12 := hU 1 2 (by decide)
  have k01 := hk 0 1 (by decide)
  have k02 := hk 0 2 (by decide)
  have k12 := hk 1 2 (by decide)
  simp only [Matrix.mul_apply, Fin.sum_univ_three, u01, u02, u12, k01, k02, k12] at e01 e02 e12
  have m12 : M 1 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e12)
  have m02 : M 0 2 = 0 := (hu 2).mul_left_eq_zero.1 (by linear_combination e02)
  have m01 : M 0 1 = 0 := (hu 1).mul_left_eq_zero.1 (by rw [m02] at e01; linear_combination e01)
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | assumption | exact absurd hab (by decide)

/- English proof (translation)
Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (h : Matrix (Fin 3) (Fin 3) R), ← Matrix.mul_assoc (h' : Matrix (Fin 3) (Fin 3) R), Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.one_mul]`.
-/
private theorem tc_rel {R : Type} [CommRing R] (h h' : GL (Fin 3) R) (X : Matrix (Fin 3) (Fin 3) R) :
    (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h) * (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') =
      (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') *
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * X * h') := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (h : Matrix (Fin 3) (Fin 3) R), ← Matrix.mul_assoc (h' : Matrix (Fin 3) (Fin 3) R),
    Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.one_mul]

end UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Introduce `O R D _ _ _ _ _ _ η Ψ I r x h hr hx hΨ hc`. Establish `cm : ∀ (h : GL (Fin 3) R) (g : D), η g = 1 → (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h` using `fun h g hg => tc_conj_mat r h g ((hr.mult g).trans hg)`. Establish `hX : ∀ a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O))`. Introduce `a`. Use `(residue_eq_zero_iff _).2 (hr.red x a a)` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[this]`. Simplify using `only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]`. Establish `hu : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a b, a ≠ b → IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h) a a - (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h') b b)`. Introduce `h' hh' a b hab`.

Rewrite using `[← residue_ne_zero_iff_isUnit, map_sub, tc_res_conj h hc.hat, tc_res_conj h' hh', hX, hX, ← map_sub, ← map_sub, residue_ne_zero_iff_isUnit]`. Conclude with `(tc_unit (Ψ x) hΨ a b hab).map _`. Establish `hk : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a, IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') a a)`. Introduce `h' hh' a`. Establish `: (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h').map (residue R) = 1`.

Rewrite using `[Matrix.map_mul, (tc_res h hc.hat).2, (tc_res h' hh').1, Matrix.one_mul]`. Use `congrFun (congrFun this a) a` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply, Matrix.one_apply_eq]`. Rewrite using `[← residue_ne_zero_iff_isUnit, this]`. Conclude with `one_ne_zero`.

Establish `hT : ∀ h' : GL (Fin 3) R, InHat h' → TriIn η Ψ I r h' → TriIn η Ψ I r h`. Introduce `h' hh' ht`. Establish `k1` using `tc_up _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.tri x hx) (hu h' hh')`. Establish `k2` using `fun g (hg : η g = 1) => tc_up' _ _ _ (tc_rel h h' (r g).mat) k1 (by rw [← cm h' g hg]; exact ht.tri g hg) (hk h' hh')`. Use `⟨fun g hg => ?_, fun s hs hg a => ?_⟩` and prove the remaining obligations.

Rewrite using `[cm h g hg]`. Conclude with `(k2 g hg).1`. Rewrite using `[cm h s hg, (k2 s hg).2, ← cm h' s hg]`. Conclude with `ht.ine s hs hg a`. Use `⟨⟨fun ⟨h', hh', ht⟩ => hT h' hh' ht, fun ht => ⟨h, hc.hat, ht⟩⟩, ⟨fun ⟨h', hh', ht⟩ => ⟨hT h' hh' ht.toTriIn, fun g hg => ?_⟩, fun ht => ⟨h, hc.hat, ht⟩⟩⟩` and prove the remaining obligations.

Establish `k1` using `tc_low _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.low x hx) (hu h' hh')`. Rewrite using `[cm h g hg]`. Conclude with `tc_low' _ _ _ (tc_rel h h' (r g).mat) k1 (by rw [← cm h' g hg]; exact ht.low g hg) (hk h' hh')`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.cond_iff_canon :
    ∀ {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Group D] (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (r : D →* GG 3 R) (x : D) (h : GL (Fin 3) R), Red η Ψ r → η x = 1 → IsUnit ((Ψ x : O) ^ 2 - 1) → Canon (r x).mat h →
      (CondT η Ψ I r ↔ TriIn η Ψ I r h) ∧ (CondD η Ψ I r ↔ DiagIn η Ψ I r h) := by
  intro O R D _ _ _ _ _ _ η Ψ I r x h hr hx hΨ hc
  have cm : ∀ (h : GL (Fin 3) R) (g : D), η g = 1 →
      (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h :=
    fun h g hg => tc_conj_mat r h g ((hr.mult g).trans hg)
  have hX : ∀ a, residue R ((r x).mat a a) = residue R (algebraMap O R ((Ψ x ^ wt1 a : Oˣ) : O)) := by
    intro a
    have := (residue_eq_zero_iff _).2 (hr.red x a a)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
    rw [this]
    simp only [GG.mat, unitaryThreeReflection_left, tor_val, Matrix.map_apply, Matrix.diagonal_apply_eq]
  have hu : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a b, a ≠ b →
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h) a a -
        (((h'⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r x).mat * h') b b) := by
    intro h' hh' a b hab
    rw [← residue_ne_zero_iff_isUnit, map_sub, tc_res_conj h hc.hat, tc_res_conj h' hh', hX, hX, ← map_sub,
      ← map_sub, residue_ne_zero_iff_isUnit]
    exact (tc_unit (Ψ x) hΨ a b hab).map _
  have hk : ∀ h' : GL (Fin 3) R, InHat h' → ∀ a,
      IsUnit ((((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h') a a) := by
    intro h' hh' a
    have : (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * h').map (residue R) = 1 := by
      rw [Matrix.map_mul, (tc_res h hc.hat).2, (tc_res h' hh').1, Matrix.one_mul]
    have := congrFun (congrFun this a) a
    rw [Matrix.map_apply, Matrix.one_apply_eq] at this
    rw [← residue_ne_zero_iff_isUnit, this]
    exact one_ne_zero
  have hT : ∀ h' : GL (Fin 3) R, InHat h' → TriIn η Ψ I r h' → TriIn η Ψ I r h := by
    intro h' hh' ht
    have k1 := tc_up _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.tri x hx) (hu h' hh')
    have k2 := fun g (hg : η g = 1) => tc_up' _ _ _ (tc_rel h h' (r g).mat) k1
      (by rw [← cm h' g hg]; exact ht.tri g hg) (hk h' hh')
    refine ⟨fun g hg => ?_, fun s hs hg a => ?_⟩
    · rw [cm h g hg]; exact (k2 g hg).1
    · rw [cm h s hg, (k2 s hg).2, ← cm h' s hg]; exact ht.ine s hs hg a
  refine ⟨⟨fun ⟨h', hh', ht⟩ => hT h' hh' ht, fun ht => ⟨h, hc.hat, ht⟩⟩,
    ⟨fun ⟨h', hh', ht⟩ => ⟨hT h' hh' ht.toTriIn, fun g hg => ?_⟩, fun ht => ⟨h, hc.hat, ht⟩⟩⟩
  have k1 := tc_low _ _ _ (tc_rel h h' (r x).mat) hc.diag (by rw [← cm h' x hx]; exact ht.low x hx) (hu h' hh')
  rw [cm h g hg]
  exact tc_low' _ _ _ (tc_rel h h' (r g).mat) k1 (by rw [← cm h' g hg]; exact ht.low g hg) (hk h' hh')
