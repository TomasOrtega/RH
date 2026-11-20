import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

/- English proof (translation)
Unfold `alt`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun w => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft]`. Rewrite using `[Units.smul_def, map_zsmul, rename_rename, ← Perm.coe_mul, Perm.sign_mul, mul_smul, smul_smul, Int.units_mul_self, one_smul, Units.smul_def]`.
-/
private theorem rename_alt {R : Type} [CommRing R] {n : ℕ} (u : Perm (Fin n)) (x : MvPolynomial (Fin n) R) :
    rename u (alt x) = Perm.sign u • alt x := by
  unfold alt
  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun w => ?_
  simp only [Equiv.coe_mulLeft]
  rw [Units.smul_def, map_zsmul, rename_rename, ← Perm.coe_mul, Perm.sign_mul, mul_smul, smul_smul,
    Int.units_mul_self, one_smul, Units.smul_def]

/- English proof (translation)
Simplify using `only [alt, map_add, smul_add, Finset.sum_add_distrib]`.
-/
private theorem antisymmetrizer_add {R : Type} [CommRing R] {n : ℕ} (x y : MvPolynomial (Fin n) R) :
    alt (x + y) = alt x + alt y := by
  simp only [alt, map_add, smul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [alt, map_mul, hz _, Finset.mul_sum, mul_smul_comm]`.
-/
private theorem antisymmetrizer_symmetric_mul {R : Type} [CommRing R] {n : ℕ} (z x : MvPolynomial (Fin n) R)
    (hz : z.IsSymmetric) : alt (z * x) = z * alt x := by
  simp only [alt, map_mul, hz _, Finset.mul_sum, mul_smul_comm]

/- English proof (translation)
The claim follows from `mul_left_cancel₀ (UpperTheory.V.AlgebraTools.hkDe R n).1 h`.
-/
private theorem eq_of_De_mul_eq_De_mul {R : Type} [CommRing R] [IsDomain R] {n : ℕ}
    (p q : MvPolynomial (Fin n) R) (h : De R n * p = De R n * q) : p = q :=
  mul_left_cancel₀ (UpperTheory.V.AlgebraTools.hkDe R n).1 h

/- English proof (translation)
Introduce `R _ _ n`. Establish `hadd : ∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y`. Introduce `x y`. Apply `eq_of_De_mul_eq_De_mul` to reduce the goal to its premises. Rewrite using `[mul_add, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_add]`.

Establish `hmul : ∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x`. Introduce `z x hz`. Apply `eq_of_De_mul_eq_De_mul` to reduce the goal to its premises. Rewrite using `[UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_symmetric_mul z x hz, mul_left_comm, UpperTheory.V.AlgebraTools.hkDdSpec]`. Establish `hsym : ∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric`.

Introduce `x w`. Apply `eq_of_De_mul_eq_De_mul` to reduce the goal to its premises. Establish `e1` using `congrArg (rename ⇑w) (UpperTheory.V.AlgebraTools.hkDdSpec R n x)`. Rewrite `e1` using `[map_mul, (UpperTheory.V.AlgebraTools.hkDe R n).2.1 w, rename_alt, ← UpperTheory.V.AlgebraTools.hkDdSpec R n x, smul_mul_assoc]`. Conclude with `(smul_left_cancel_iff _).mp e1`.

Use `⟨hadd, hmul, hsym, ?_⟩` and prove the remaining obligations. Use `⟨{ toFun := fun x => ⟨dd x, (mem_symmetricSubalgebra _).mpr (hsym x)⟩ map_add' := fun x y => Subtype.ext (hadd x y) map_smul' := fun c x => Subtype.ext ?_ }, fun x => rfl⟩` and prove the remaining obligations. Simplify using `only [RingHom.id_apply, Subalgebra.smul_def, SetLike.val_smul]`. Conclude with `hmul _ _ ((mem_symmetricSubalgebra _).mp c.2)`.
-/
theorem UpperTheory.V.AlgebraTools.hkDdProps :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), (∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y) ∧ (∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x) ∧
      (∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric) ∧
      ∃ D : MvPolynomial (Fin n) R →ₗ[symmetricSubalgebra (Fin n) R] symmetricSubalgebra (Fin n) R, ∀ x, (D x : MvPolynomial (Fin n) R) = dd x := by
  intro R _ _ n
  have hadd : ∀ x y : MvPolynomial (Fin n) R, dd (x + y) = dd x + dd y := by
    intro x y
    apply eq_of_De_mul_eq_De_mul
    rw [mul_add, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_add]
  have hmul : ∀ z x : MvPolynomial (Fin n) R, z.IsSymmetric → dd (z * x) = z * dd x := by
    intro z x hz
    apply eq_of_De_mul_eq_De_mul
    rw [UpperTheory.V.AlgebraTools.hkDdSpec, antisymmetrizer_symmetric_mul z x hz, mul_left_comm, UpperTheory.V.AlgebraTools.hkDdSpec]
  have hsym : ∀ x : MvPolynomial (Fin n) R, (dd x).IsSymmetric := by
    intro x w
    apply eq_of_De_mul_eq_De_mul
    have e1 := congrArg (rename ⇑w) (UpperTheory.V.AlgebraTools.hkDdSpec R n x)
    rw [map_mul, (UpperTheory.V.AlgebraTools.hkDe R n).2.1 w, rename_alt, ← UpperTheory.V.AlgebraTools.hkDdSpec R n x,
      smul_mul_assoc] at e1
    exact (smul_left_cancel_iff _).mp e1
  refine ⟨hadd, hmul, hsym, ?_⟩
  refine ⟨{ toFun := fun x => ⟨dd x, (mem_symmetricSubalgebra _).mpr (hsym x)⟩
            map_add' := fun x y => Subtype.ext (hadd x y)
            map_smul' := fun c x => Subtype.ext ?_ }, fun x => rfl⟩
  simp only [RingHom.id_apply, Subalgebra.smul_def, SetLike.val_smul]
  exact hmul _ _ ((mem_symmetricSubalgebra _).mp c.2)
