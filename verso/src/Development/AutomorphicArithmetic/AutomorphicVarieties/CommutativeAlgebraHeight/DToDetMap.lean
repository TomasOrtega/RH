import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Introduce `n A G _ _ D B _ _`. Use `Det.ext' fun S _ _ x => ?_` and prove the remaining obligations. Use `letI : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra`. Use `haveI : IsScalarTower A B S := .of_algebraMap_eq fun _ => rfl`. Establish `h : ofT B G S x = ofT A G S (Det.cancel A (MonoidAlgebra A G) B S (Algebra.TensorProduct.map (AlgHom.id S S) (toT A G B) x))`.

Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul s y`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [tmul_add, map_add, ha, hb]`. Consider the case `single g b`. Rewrite using `[Algebra.TensorProduct.map_tmul, toT_single, Det.cancel_tmul, ofT_tmul, ofT_tmul, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single]`. Simplify using the standard rewrite rules.

Conclude with `congrArg (D.D S) h`.
-/
theorem UpperTheory.V.CA.d_toDet_map :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (B : Type) [CommRing B] [Algebra A B], (D.map (algebraMap A B)).toDet = (D.toDet.baseChange B).pull (toT A G B) := by
  intro n A G _ _ D B _ _
  refine Det.ext' fun S _ _ x => ?_
  letI : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A B S := .of_algebraMap_eq fun _ => rfl
  have h : ofT B G S x = ofT A G S (Det.cancel A (MonoidAlgebra A G) B S
      (Algebra.TensorProduct.map (AlgHom.id S S) (toT A G B) x)) := by
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s y =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | single g b =>
        rw [Algebra.TensorProduct.map_tmul, toT_single, Det.cancel_tmul, ofT_tmul, ofT_tmul,
          MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapRingHom_single]
        simp
  exact congrArg (D.D S) h
