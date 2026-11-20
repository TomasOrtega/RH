import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.E.ChernClassEvaluation

variable {R : Type} [CommRing R]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  refine (HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl).trans ?_
  unfold chainsXIso
  congr 2
  simp [chainsN]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem freeGen_nat {P Q : PSh} (f : P ⟶ Q) (U : Scheme.{0}) (x : P.obj (op U)) :
    (((free R).map f).hom.app (op U)).hom (freeGen R P U x) = freeGen R Q U (f.app (op U) x) := by
  unfold freeGen
  change ((((toSheafify _ ((freeP R).obj P)) ≫ sheafifyMap _ ((freeP R).map f)).app (op U)).hom _) = _
  rw [← toSheafify_naturality, NatTrans.comp_app, ModuleCat.hom_comp]
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y)
    (by erw [ModuleCat.free_map_apply]; rfl)

def evH {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) : (A ⟶ B) →+ Sec B U where
  toFun f := (f.hom.app (op U)).hom y
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evH_apply {A B : Shv R} (U : Scheme.{0}) (y : Sec A U) (f : A ⟶ B) :
    (f.hom.app (op U)).hom y = evH U y f := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem evDelta_pf : ChernClassExistence.LeafEvDelta := by
  intro R _ E I n m hm α U
  constructor
  · intro x
    unfold ev
    rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) m (by simp) n 1 (by omega) (by simp)]
    have hz : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0 :=
      (HomologicalComplex.isZero_extend_X _ _ 1 (fun i => by show -(i : ℤ) ≠ 1; omega)).eq_of_tgt _ _
    rw [hz]
    simp [Sec.map]
  · intro p s t hs ht x
    unfold ev
    rw [δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by push_cast; omega), chains_d]
    simp only [Preadditive.comp_add, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]
    simp [Sec.map, Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul, freeGen_nat, Sx.face]
    rw [evH_apply, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    congr 1
    rw [← evH_apply]
    simp [freeGen_nat]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : ChernClassExistence.LeafEvMk) (h1 : ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural) (h2 : ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural)
    (c1 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) :
    LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists :=
  ChernClassExistence.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness hmk evDelta_pf h1 h2 c1 c2 c3

end LateralTheory.E.ChernClassEvaluation
