import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Introduce `n A G _ _`. Use `⟨fun ρ => Det.ext' fun S _ _ x => ?_, fun D H _ φ => Det.ext' fun S _ _ x => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(GDet.repAlg ρ S (ofT A G S x)).det = (Det.repS (GDet.repAlg ρ A) S x).det`. Use `congr 1`. Proceed by induction on `x with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul s y`. Rewrite using `[ofT_tmul, Det.repS_tmul, map_smul]`. Use `congr 1`.

Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => ext i j`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add]`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Consider the case `single g r => ext i j`. Simplify using `[GDet.repAlg]`. Express the relevant statement in the definitionally equal form `D.D S (MonoidAlgebra.mapDomainRingHom S φ (ofT A H S x)) = D.D S (ofT A G S (Algebra.TensorProduct.map (AlgHom.id S S) (MonoidAlgebra.mapDomainAlgHom A A φ) x))`. Use `congr 1`.

Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul s y`. Proceed by induction on `y using MonoidAlgebra.induction_linear with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [tmul_add, map_add, ha, hb]`. Consider the case `single g r => simp [ofT_tmul]`.
-/
theorem UpperTheory.V.CA.d_toDet_ofRep :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G], (∀ ρ : G →* Matrix (Fin n) (Fin n) A, (GDet.ofRep ρ).toDet = Det.ofRep (Fintype.card_fin n) (GDet.repAlg ρ A)) ∧ ∀ (D : GDet n A G) (H : Type) [Group H] (φ : H →* G), (D.comap φ).toDet = D.toDet.pull (MonoidAlgebra.mapDomainAlgHom A A φ) := by
  intro n A G _ _
  refine ⟨fun ρ => Det.ext' fun S _ _ x => ?_, fun D H _ φ => Det.ext' fun S _ _ x => ?_⟩
  · change (GDet.repAlg ρ S (ofT A G S x)).det = (Det.repS (GDet.repAlg ρ A) S x).det
    congr 1
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]; ext i j; simp
      | single g r => ext i j; simp [GDet.repAlg]
  · change D.D S (MonoidAlgebra.mapDomainRingHom S φ (ofT A H S x)) =
      D.D S (ofT A G S (Algebra.TensorProduct.map (AlgHom.id S S) (MonoidAlgebra.mapDomainAlgHom A A φ) x))
    congr 1
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul s y =>
      induction y using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | single g r => simp [ofT_tmul]
