import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.CA.d_toDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (y : MonoidAlgebra A G), D.toDet.chi y = D.chi y ∧ (∀ i, D.toDet.lam i y = D.lam i y) ∧ D.toDet.tr y = D.tr y ∧ (D.toDet.Kills y ↔ D.Kills y) := by
  intro n A G _ _ D y
  have hchi : D.toDet.chi y = D.chi y := by
    change D.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
      D.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
    congr 1
    rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def, MonoidAlgebra.smul_single,
      smul_eq_mul, mul_one]
    rfl
  have hlam : ∀ i, D.toDet.lam i y = D.lam i y := fun i => by
    unfold Det.lam GDet.lam
    rw [hchi]
  refine ⟨hchi, hlam, hlam 1, ?_⟩
  have key : ∀ (B : Type) [CommRing B] [Algebra A B] (h : B ⊗[A] MonoidAlgebra A G),
      D.toDet.D B (1 + h * (1 ⊗ₜ y)) =
        D.D B (1 + ofT A G B h * MonoidAlgebra.mapRingHom G (algebraMap A B) y) := by
    intro B _ _ h
    change D.D B (ofT A G B (1 + h * (1 ⊗ₜ y))) = _
    rw [map_add, map_one, map_mul, ofT_tmul, one_smul]
  constructor
  · intro hk B _ _ h
    have := hk B (toT A G B h)
    rwa [key, ofT_toT] at this
  · intro hk B _ _ h
    rw [key]
    exact hk B _
