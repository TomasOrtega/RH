import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

section
variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R]
  [Algebra O R] (n : ℕ)

/- English proof (translation)
Simplify using `[GFrame.star]`.
-/
private theorem star_add' (y z : MonoidAlgebra R F.G₀) :
    F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
  simp [GFrame.star]

/- English proof (translation)
Simplify using `[GFrame.star]`.
-/
private theorem star_zero' : F.star O R n 0 = 0 := by
  simp [GFrame.star]

end

/- English proof (translation)
Simplify using `[GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]`.
-/
private theorem star_single_eq_single_conj_inv_mul_eps_zpow {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (r : R) :
    F.star O R n (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

/- English proof (translation)
Establish `hc : F.c⁻¹ = F.c` using `inv_eq_of_mul_eq_one_right F.c_sq`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[GFrame.conj, hc, ← mul_assoc, F.c_sq]`. Rewrite using `[mul_assoc, F.c_sq, mul_one]`.
-/
private theorem conjO_conjO_unimodular_class_representatives {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  apply Subtype.ext
  simp [GFrame.conj, hc, ← mul_assoc, F.c_sq]
  rw [mul_assoc, F.c_sq, mul_one]

/- English proof (translation)
Simplify using `[GFrame.eps, GFrame.conj]`.
-/
private theorem eps_conj' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp [GFrame.eps, GFrame.conj]

/- English proof (translation)
Establish `h : Units.map (f : R →* R') (F.eps O R g) = F.eps O R' g`. Use `ext`. Simplify using `[GFrame.eps, pushCh]`. Rewrite using `[← h, ← map_zpow (Units.map (f : R →* R')), Units.coe_map]`. Both sides reduce to the same expression.
-/
private theorem algHom_eps_zpow_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (R : Type) [CommRing R] [Algebra O R] (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R')
    (g : F.G₀) (k : ℤ) :
    f ((F.eps O R g ^ k : Rˣ) : R) = ((F.eps O R' g ^ k : R'ˣ) : R') := by
  have h : Units.map (f : R →* R') (F.eps O R g) = F.eps O R' g := by
    ext
    simp [GFrame.eps, pushCh]
  rw [← h, ← map_zpow (Units.map (f : R →* R')), Units.coe_map]
  rfl

/- English proof (translation)
Introduce `l _ F O _ _ R _ _ n`. Use `⟨?_, ?_, star_add' F O R n, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `y z`. Simplify using `only [GFrame.star, map_mul, MulOpposite.unop_mul]`. Simplify using `[GFrame.star, map_one]`.

Introduce `a y`. Simplify using `only [GFrame.star, map_smul, MulOpposite.unop_smul]`. Introduce `y`. Proceed by induction on `y using MonoidAlgebra.induction_linear`. Use `next => simp [star_zero']`.

Use `next y z hy hz => rw [star_add', star_add', hy, hz]`. Use `next g r =>`. Simplify using `only [star_single_eq_single_conj_inv_mul_eps_zpow, map_inv, inv_inv, conjO_conjO_unimodular_class_representatives, eps_conj', _root_.inv_zpow]`. Rewrite using `[mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]`. Introduce `R' _ _ f y`.

Proceed by induction on `y using MonoidAlgebra.induction_linear`. Use `next => simp [star_zero']`. Use `next y z hy hz => rw [map_add, star_add', star_add', map_add, hy, hz]`. Use `next g r =>`. Simplify using `only [star_single_eq_single_conj_inv_mul_eps_zpow, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, map_mul]`.

Rewrite using `[algHom_eps_zpow_eq]`.
-/
theorem UpperTheory.V.AlgebraTools.Det.starApi :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ),
    (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ F.star O R n 1 = 1 ∧
    (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (a : R) y, F.star O R n (a • y) = a • F.star O R n y) ∧
    (∀ y, F.star O R n (F.star O R n y) = y) ∧
    ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (y : MonoidAlgebra R F.G₀),
      F.star O R' n (MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') y) = MonoidAlgebra.mapRingHom F.G₀ (f : R →+* R') (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n
  refine ⟨?_, ?_, star_add' F O R n, ?_, ?_, ?_⟩
  · intro y z
    simp only [GFrame.star, map_mul, MulOpposite.unop_mul]
  · simp [GFrame.star, map_one]
  · intro a y
    simp only [GFrame.star, map_smul, MulOpposite.unop_smul]
  · intro y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [star_add', star_add', hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, map_inv, inv_inv, conjO_conjO_unimodular_class_representatives, eps_conj', _root_.inv_zpow]
      rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · intro R' _ _ f y
    induction y using MonoidAlgebra.induction_linear
    next => simp [star_zero']
    next y z hy hz => rw [map_add, star_add', star_add', map_add, hy, hz]
    next g r =>
      simp only [star_single_eq_single_conj_inv_mul_eps_zpow, MonoidAlgebra.mapRingHom_single, RingHom.coe_coe, map_mul]
      rw [algHom_eps_zpow_eq]
