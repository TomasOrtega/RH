import Development.EtaleCohomology.TateTwists.EtaleSheafSectionsSeparatedAndGlue

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Establish `: PreservesLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} R)))` using `preservesLimitsOfSize_shrink.{1, 0, 0, 1} _`. Conclude with `(isSheaf_iff_isSheaf_of_type _ _).1 (Presheaf.isSheaf_comp_of_isSheaf Scheme.etaleTopology.{0} F.obj (forget (ModuleCat.{1} (ULift.{1} R))) F.property)`.
-/
theorem sec_glue_forget_isSheaf (R : Type) [CommRing R] (F : Shv R) :
    Presieve.IsSheaf Scheme.etaleTopology.{0} (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) := by
  have : PreservesLimitsOfSize.{0, 1} (forget (ModuleCat.{1} (ULift.{1} R))) :=
    preservesLimitsOfSize_shrink.{1, 0, 0, 1} _
  exact (isSheaf_iff_isSheaf_of_type _ _).1
    (Presheaf.isSheaf_comp_of_isSheaf Scheme.etaleTopology.{0} F.obj
      (forget (ModuleCat.{1} (ULift.{1} R))) F.property)

/- English proof (translation)
Introduce `R _ F U`. Establish `hT` using `sec_glue_forget_isSheaf R F`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Take `⟨S, hS, h⟩` from `hab`.

Conclude with `(hT S hS).isSeparatedFor.ext (fun V g hg => h V g hg)`. Introduce `S hS s hs`. Set `x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows` to `fun V g hg => s V g hg`. Establish `hc : x.Compatible`. Rewrite using `[Presieve.compatible_iff_sieveCompatible]`.

Introduce `V W g k hg`. Conclude with `(hs V W g k hg).symm`. Take `⟨t, ht, -⟩` from `hT S hS x hc`. Conclude with `⟨t, fun V g hg => ht g hg⟩`.
-/
theorem etale_sheaf_sections_glue_of_forget_isSheaf : EtaleSheafSectionsSeparatedAndGlue := by
  intro R _ F U
  have hT := sec_glue_forget_isSheaf R F
  refine ⟨?_, ?_⟩
  · intro a b hab
    obtain ⟨S, hS, h⟩ := hab
    exact (hT S hS).isSeparatedFor.ext (fun V g hg => h V g hg)
  · intro S hS s hs
    let x : Presieve.FamilyOfElements (F.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) S.arrows :=
      fun V g hg => s V g hg
    have hc : x.Compatible := by
      rw [Presieve.compatible_iff_sieveCompatible]
      intro V W g k hg
      exact (hs V W g k hg).symm
    obtain ⟨t, ht, -⟩ := hT S hS x hc
    exact ⟨t, fun V g hg => ht g hg⟩

end LateralTheory.EtaleFoundations
