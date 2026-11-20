import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `T p`. Use `⟨AlgebraicClosure (T.residueField p), inferInstance, inferInstance, Spec.map (CommRingCat.ofHom (algebraMap (T.residueField p) (AlgebraicClosure (T.residueField p)))) ≫ T.fromSpecResidueField p, ?_⟩` and prove the remaining obligations. Take `⟨x⟩ : Nonempty (Sp (AlgebraicClosure (T.residueField p)))` from `inferInstance`. Use `⟨x, ?_⟩` and prove the remaining obligations. Use `show (T.fromSpecResidueField p).base _ = p`.

Conclude with `Scheme.fromSpecResidueField_apply p _`.
-/
theorem exists_geomPoint_through : ∀ (T : Scheme.{0}) (p : T), ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (s : Sp K ⟶ T), p ∈ Set.range s := by
  intro T p
  refine ⟨AlgebraicClosure (T.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField p) (AlgebraicClosure (T.residueField p)))) ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨x⟩ : Nonempty (Sp (AlgebraicClosure (T.residueField p))) := inferInstance
  refine ⟨x, ?_⟩
  show (T.fromSpecResidueField p).base _ = p
  exact Scheme.fromSpecResidueField_apply p _

end GlobalTheory
