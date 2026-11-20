import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg

open Polynomial UpperTheory.V.W

/- English proof (translation)
Substitute using the available equality. Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.AlgebraTools.Det.mapApi_congr {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    (B : Type) [CommRing B] (i j : Algebra A B) (h : i = j) (x : MonoidAlgebra B G) :
    @GDet.D n A G _ _ D B _ i x = @GDet.D n A G _ _ D B _ j x := by
  subst h; rfl

/- English proof (translation)
Equip the data with the indicated structure. A detailed English derivation is pending.
-/
private theorem UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (B₀ : Type) [CommRing B₀] [Algebra A B₀]
    (B : Type) [CommRing B] [Algebra A' B] (φ : B₀ →+* B)
    (hφ : ∀ a, φ (algebraMap A B₀ a) = algebraMap A' B (f a)) (x : MonoidAlgebra B₀ G) :
    (D.map f).D B (MonoidAlgebra.mapRingHom G φ x) = φ (D.D B₀ x) := by
  letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
  exact D.nat B₀ B { φ with commutes' := hφ } x

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Both sides reduce to the same expression. Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.Det.mapApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A'),
    (∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f) ∧
    (∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y)) ∧
    (∀ i g, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1))) ∧
    (∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), (D.map f).D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) x) =
      MvPolynomial.map f (D.D (MvPolynomial σ A) x)) ∧
    (∀ (m : ℕ) (y : Fin m → MonoidAlgebra A G), (D.map f).D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.mapRingHom G f (y j)) =
      MvPolynomial.map f (D.D (MvPolynomial (Fin m) A) (GDet.gen y))) ∧
    (∀ y, D.Kills y → (D.map f).Kills (MonoidAlgebra.mapRingHom G f y)) ∧
    (∀ {A'' : Type} [CommRing A''] (f' : A' →+* A''), (D.map f).map f' = D.map (f'.comp f)) ∧ D.map (RingHom.id A) = D := by
  intro n A G _ _ D A' _ f
  have h1 : ∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
    intro y
    have e : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G f y) =
        MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
      rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
        ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
    show (D.map f).D A'[X] _ = _
    rw [e, UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq D f A[X] A'[X] (Polynomial.mapRingHom f) (fun a => by simp)]
    rfl
  have h2 : ∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
    intro i y
    simp only [GDet.lam, h1, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  have h4 : ∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), (D.map f).D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) x) =
      MvPolynomial.map f (D.D (MvPolynomial σ A) x) := fun σ x =>
    UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq D f _ _ (MvPolynomial.map f) (fun a => MvPolynomial.map_C f a) x
  refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_, ?_⟩
  · intro i g
    simpa using h2 i (MonoidAlgebra.single g 1)
  · intro m y
    rw [← h4]
    congr 1
    ext g
    simp [GDet.gen]
  · intro y hy B _ _ h
    letI : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
    have := hy B h
    rw [show MonoidAlgebra.mapRingHom G (algebraMap A B) y = MonoidAlgebra.mapRingHom G (algebraMap A' B) (MonoidAlgebra.mapRingHom G f y) from by
      rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]; rfl] at this
    exact this
  · intro A'' _ f'
    rfl
  · cases D
    simp only [GDet.map]
    congr 1
    funext B _ i
    congr 1
    exact Algebra.algebra_ext _ _ (fun r => rfl)
