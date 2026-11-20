import Development.EtaleCohomology.EtaleSheaves.DescentInduction

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
namespace LateralTheory.E.DescStepPf

/- English proof (translation)
Use `show CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0`. Use `infer_instance`.
-/
theorem bounds_le (R : Type) [CommRing R] (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 := by
  show CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0
  infer_instance

/- English proof (translation)
Introduce `R _ F E` and use `⟨bounds_le R E, by unfold res; infer_instance, fun m => by unfold res; exact InjectiveResolution.instInjectiveXIntCochainComplex (injectiveResolution F) m⟩`.
-/
theorem Bounds_holds : Bounds := fun R _ F E =>
  ⟨bounds_le R E, by unfold res; infer_instance,
    fun m => by unfold res; exact InjectiveResolution.instInjectiveXIntCochainComplex (injectiveResolution F) m⟩

/- English proof (translation)
The claim follows from `DescStep_of Bounds_holds hL hX`.
-/
theorem etale_descent_induction_of_levelwise_identity_and_complex_descent (hL : LevelIdent) (hX : CxDesc) : LateralTheory.E.t_E1Cut.DescStep :=
  DescStep_of Bounds_holds hL hX

end LateralTheory.E.DescStepPf
