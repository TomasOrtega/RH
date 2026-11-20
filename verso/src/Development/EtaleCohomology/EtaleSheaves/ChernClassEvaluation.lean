import Development.EtaleCohomology.EtaleSheaves.ChernClassExistence

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
namespace LateralTheory.E.ChernClassEvaluation

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `(HomologicalComplex.extend_d_eq ((chainsN R).obj E) ComplexShape.embeddingDownNat (i := p + 1) (j := p) rfl rfl).trans ?_` and prove the remaining obligations. Unfold `chainsXIso`. Use `congr 2`. Simplify using `[chainsN]`. Both sides reduce to the same expression.
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
Unfold `freeGen`. Express the relevant statement in the definitionally equal form `((((toSheafify _ ((freeP R).obj P)) ≫ sheafifyMap _ ((freeP R).map f)).app (op U)).hom _) = _`. Rewrite using `[← toSheafify_naturality, NatTrans.comp_app, ModuleCat.hom_comp]`. Conclude with `congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj Q)).app (op U)).hom y) (by erw [ModuleCat.free_map_apply]; rfl)`.
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
Introduce `R _ E I n m hm α U`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Unfold `ev`. Rewrite using `[δ_v n m hm α (-((0 : ℕ) : ℤ)) m (by simp) n 1 (by omega) (by simp)]`.

Establish `hz : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) 1 = 0` using `(HomologicalComplex.isZero_extend_X _ _ 1 (fun i => by show -(i : ℤ) ≠ 1; omega)).eq_of_tgt _ _`. Rewrite using `[hz]`. Simplify using `[Sec.map]`. Introduce `p s t hs ht x`. Unfold `ev`.

Rewrite using `[δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by push_cast; omega), chains_d]`. Simplify using `only [Preadditive.comp_add, Preadditive.comp_zsmul, Category.assoc, Iso.inv_hom_id_assoc]`. Simplify using `[Sec.map, Units.smul_def, Preadditive.comp_sum, Preadditive.sum_comp, Preadditive.zsmul_comp, Preadditive.comp_zsmul, freeGen_nat, Sx.face]`. Rewrite using `[evH_apply, map_zsmul, map_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul]`. Use `congr 1`. Rewrite using `[← evH_apply]`. Simplify using `[freeGen_nat]`.
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
The claim follows from `ChernClassExistence.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness hmk evDelta_pf h1 h2 c1 c2 c3`.
-/
theorem etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness (hmk : ChernClassExistence.LeafEvMk) (h1 : ChernClassExistence.EtaleKummerChernEdgeValuesExistNatural) (h2 : ChernClassExistence.EtaleKummerChernTriangleValuesExistNatural)
    (c1 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges) (c2 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTriangles) (c3 : ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnTetrahedra) :
    LateralTheory.E.ChernCocycleExistenceAndUniqueness.EtaleKummerChernCocycleExists :=
  ChernClassExistence.etale_kummer_chern_cocycle_exists_of_evaluation_values_and_closedness hmk evDelta_pf h1 h2 c1 c2 c3

end LateralTheory.E.ChernClassEvaluation
