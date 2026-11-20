import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

/- English proof (translation)
Establish `h : F.c⁻¹ = F.c` using `(eq_inv_of_mul_eq_one_left F.c_sq).symm`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, h]`. Simplify using `only [← mul_assoc, F.c_sq, one_mul]`. Rewrite using `[mul_assoc, F.c_sq, mul_one]`.
-/
private theorem conj_conj_of_isQuad {l : ℕ} [Fact l.Prime] (F : GFrame l) (g : F.G₀) : F.conj (F.conj g) = g := by
  have h : F.c⁻¹ = F.c := (eq_inv_of_mul_eq_one_left F.c_sq).symm
  apply Subtype.ext
  simp only [GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, h]
  simp only [← mul_assoc, F.c_sq, one_mul]
  rw [mul_assoc, F.c_sq, mul_one]

/- English proof (translation)
Simplify using `only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv]`. Rewrite using `[mul_right_comm, mul_inv_cancel, one_mul]`.
-/
private theorem eps_conj_eq_eps {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (g : F.G₀) : F.eps O R (F.conj g) = F.eps O R g := by
  simp only [GFrame.eps, pushCh, MonoidHom.comp_apply, Subgroup.coe_subtype, GFrame.conj, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_inv]
  rw [mul_right_comm, mul_inv_cancel, one_mul]

/- English proof (translation)
Simplify using `[GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]`.
-/
private theorem star_single_eq_single_conj_inv_mul_eps_zpow' {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (g : F.G₀) (b : R) : F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]

/- English proof (translation)
Introduce `l _ F n O _ _ R _ _`. Establish `hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z`. Introduce `y z`. Simplify using `[GFrame.star, map_add]`. Use `⟨?_, ?_, hadd, ?_, ?_, ?_, star_single_eq_single_conj_inv_mul_eps_zpow' F O R n⟩` and prove the remaining obligations.

Introduce `y`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp [GFrame.star]`. Consider the case `add y z hy hz => rw [hadd, hadd, hy, hz]`. Consider the case `single g b`.

Rewrite using `[star_single_eq_single_conj_inv_mul_eps_zpow', star_single_eq_single_conj_inv_mul_eps_zpow', map_inv, inv_inv, conj_conj_of_isQuad, map_inv, eps_conj_eq_eps, _root_.inv_zpow', mul_assoc, ← Units.val_mul, ← _root_.zpow_add]`. Simplify using the standard rewrite rules. Introduce `y z`. Simplify using `[GFrame.star, map_mul]`. Introduce `b y`.

Simplify using `[GFrame.star, map_smul]`. Simplify using `[GFrame.star, map_one]`. Introduce `y z`. Simplify using `[GFrame.star, map_sub]`.
-/
theorem UpperTheory.V.Pa.star_basic :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R], (∀ y, F.star O R n (F.star O R n y) = y) ∧ (∀ y z, F.star O R n (y * z) = F.star O R n z * F.star O R n y) ∧ (∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z) ∧ (∀ (b : R) y, F.star O R n (b • y) = b • F.star O R n y) ∧ F.star O R n 1 = 1 ∧ (∀ y z, F.star O R n (y - z) = F.star O R n y - F.star O R n z) ∧ ∀ g b, F.star O R n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
  intro l _ F n O _ _ R _ _
  have hadd : ∀ y z, F.star O R n (y + z) = F.star O R n y + F.star O R n z := by
    intro y z
    simp [GFrame.star, map_add]
  refine ⟨?_, ?_, hadd, ?_, ?_, ?_, star_single_eq_single_conj_inv_mul_eps_zpow' F O R n⟩
  · intro y
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add y z hy hz => rw [hadd, hadd, hy, hz]
    | single g b =>
      rw [star_single_eq_single_conj_inv_mul_eps_zpow', star_single_eq_single_conj_inv_mul_eps_zpow', map_inv, inv_inv, conj_conj_of_isQuad, map_inv, eps_conj_eq_eps, _root_.inv_zpow', mul_assoc, ← Units.val_mul, ← _root_.zpow_add]
      simp
  · intro y z
    simp [GFrame.star, map_mul]
  · intro b y
    simp [GFrame.star, map_smul]
  · simp [GFrame.star, map_one]
  · intro y z
    simp [GFrame.star, map_sub]
