import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.InjTest

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Proceed by induction.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Treat this case separately.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules.
-/
private theorem star_mapRingHom_eq_mapRingHom_star {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (B B' : Type) [CommRing B] [CommRing B'] [Algebra O B] [Algebra O B'] (n : ℕ) (φ : B →+* B') (hφ : φ.comp (algebraMap O B) = algebraMap O B') (y : MonoidAlgebra B F.G₀) :
    F.star O B' n (MonoidAlgebra.mapRingHom F.G₀ φ y) = MonoidAlgebra.mapRingHom F.G₀ φ (F.star O B n y) := by
  have h1 : ∀ (u : Bˣ) (k : ℤ), φ ((u ^ k : Bˣ) : B) = ((Units.map (φ : B →* B') u ^ k : B'ˣ) : B') := by
    intro u k
    rw [← map_zpow]
    rfl
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp [GFrame.star]
  | add a b ha hb =>
    simp only [map_add, GFrame.star, MulOpposite.unop_add] at *
    rw [ha, hb]
  | single g b =>
    simp only [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single, GFrame.eps, MonoidAlgebra.mapRingHom_single]
    simp
    rw [h1]
    congr 3
    ext
    simp [← hφ]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.Det.polarInj :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀) {X : Type} (K : X → Type) [∀ x, CommRing (K x)] [∀ x, Algebra O (K x)] (f : ∀ x, R →ₐ[O] K x),
    (∀ a, (∀ x, f x a = 0) → a = 0) → (∀ x, F.IsPolar O (D.map (f x : R →+* K x))) → F.IsPolar O D := by
  intro l _ F O _ _ R _ _ n D X K _ _ f hf h
  intro B _ _ _ _ y
  classical
  let u : MonoidAlgebra (MvPolynomial F.G₀ R) F.G₀ := y.coeff.support.sum fun g => MonoidAlgebra.single g (MvPolynomial.X g)
  let ev : MvPolynomial F.G₀ R →ₐ[R] B := MvPolynomial.aeval fun g => y.coeff g
  have hev : MonoidAlgebra.mapRingHom F.G₀ (ev : MvPolynomial F.G₀ R →+* B) u = y := by
    simp only [u, map_sum, MonoidAlgebra.mapRingHom_single]
    simp only [ev, AlgHom.coe_toRingHom, MvPolynomial.aeval_X]
    exact y.sum_single
  have hevO : (ev : MvPolynomial F.G₀ R →+* B).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O B := by
    ext o
    simp [ev, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply O R B]
  have key : D.D _ (F.star O _ n u) = D.D _ u := by
    rw [← sub_eq_zero]
    ext m
    rw [MvPolynomial.coeff_zero]
    apply hf
    intro x
    letI : Algebra R (MvPolynomial F.G₀ (K x)) := ((algebraMap (K x) (MvPolynomial F.G₀ (K x))).comp (f x : R →+* K x)).toAlgebra
    let φ : MvPolynomial F.G₀ R →ₐ[R] MvPolynomial F.G₀ (K x) := MvPolynomial.aeval MvPolynomial.X
    have hφ : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) = MvPolynomial.map (f x : R →+* K x) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [φ, RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
      · intro i
        simp [φ]
    have hφO : (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)).comp (algebraMap O (MvPolynomial F.G₀ R)) = algebraMap O (MvPolynomial F.G₀ (K x)) := by
      rw [hφ]
      refine RingHom.ext fun o => ?_
      rw [RingHom.comp_apply, MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_apply, MvPolynomial.map_C]
      congr 1
      exact (f x).commutes o
    have hz : MvPolynomial.map (f x : R →+* K x) (D.D _ (F.star O _ n u) - D.D _ u) = 0 := by
      rw [← hφ, map_sub, sub_eq_zero]
      have hx := h x (MvPolynomial F.G₀ (K x)) (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u)
      rw [star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hφO] at hx
      change D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) (F.star O _ n u)) = D.D _ (MonoidAlgebra.mapRingHom F.G₀ (φ : MvPolynomial F.G₀ R →+* MvPolynomial F.G₀ (K x)) u) at hx
      rw [D.nat _ _ φ, D.nat _ _ φ] at hx
      exact hx
    have hc := congrArg (MvPolynomial.coeff m) hz
    rw [MvPolynomial.coeff_map] at hc
    simpa using hc
  rw [← hev, star_mapRingHom_eq_mapRingHom_star F O _ _ n _ hevO, D.nat _ _ ev, D.nat _ _ ev, key]
