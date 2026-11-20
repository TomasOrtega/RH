import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityBaseChangeAffineCofilteredLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousConeDescendsEtaleSurjectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Take `⟨V, f, hV, hfe, hfs⟩` from `GlobalTheory.exists_affine_etale_surjective W`. Establish `hfa : IsAffineHom f`. Establish `: IsAffineHom (f ≫ terminal.from W)` using `isAffineHom_of_isAffine _`. Conclude with `IsAffineHom.of_comp f (terminal.from W)`. Use `GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs @IsAffineHom hfa ?_` and prove the remaining obligations.

Introduce `Z π hπ`. Establish `: IsAffine Z` using `isAffine_of_isAffineHom π`. Conclude with `GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit R F hF S I G c hc hG Z (π ≫ f ≫ r) inferInstance`.
-/
theorem contCone_bc_of_compact_separated (R : Type) [CommRing R] (F : Shv R) (hF : Finitary F)
    (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G)
    (hc : IsLimit c) (hG : ∀ i, IsAffineHom (G.obj i).hom) (W : Scheme.{0}) (r : W ⟶ S)
    [CompactSpace W] [W.IsSeparated] : ContCone R F ((bc (sch.map r)).mapCone c) := by
  obtain ⟨V, f, hV, hfe, hfs⟩ := GlobalTheory.exists_affine_etale_surjective W
  have hfa : IsAffineHom f := by
    have : IsAffineHom (f ≫ terminal.from W) := isAffineHom_of_isAffine _
    exact IsAffineHom.of_comp f (terminal.from W)
  refine GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs @IsAffineHom hfa ?_
  intro Z π hπ
  have : IsAffine Z := isAffine_of_isAffineHom π
  exact GlobalTheory.T.continuity_baseChange_affine_cofiltered_limit R F hF S I G c hc hG Z (π ≫ f ≫ r) inferInstance

/- English proof (translation)
Introduce `R _ F hF S I _ _ G c hc hG W r _ _`. Take `⟨V, f, hV, hfe, hfs⟩` from `GlobalTheory.exists_affine_etale_surjective W`. Establish `hqc : QuasiCompact f` using `inferInstance`. Establish `hsep : IsSeparated f`. Establish `: IsSeparated (f ≫ terminal.from W)`.

Rewrite using `[Subsingleton.elim (f ≫ terminal.from W) (terminal.from V)]`. Use `infer_instance`. Conclude with `IsSeparated.of_comp f (terminal.from W)`. Use `haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsStableUnderBaseChange := MorphismProperty.IsStableUnderBaseChange.inf`. Use `haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsMultiplicative := { id_mem := fun X => ⟨inferInstance, inferInstance⟩ comp_mem := fun f g hf hg => by`.

Take `⟨hf1, hf2⟩` from `hf`. Take `⟨hg1, hg2⟩` from `hg`. Conclude with `⟨inferInstance, inferInstance⟩ }`. Use `GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs (@QuasiCompact ⊓ @IsSeparated) ⟨hqc, hsep⟩ ?_` and prove the remaining obligations. Introduce `Z π hπ`.

Take `⟨h1, h2⟩` from `hπ`. Establish `: CompactSpace Z` using `QuasiCompact.compactSpace_of_compactSpace π`. Establish `: Z.IsSeparated`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Subsingleton.elim (terminal.from Z) (π ≫ terminal.from V)]`.

Use `infer_instance`. Conclude with `contCone_bc_of_compact_separated R F hF S I G c hc hG Z (π ≫ f ≫ r)`.
-/
theorem contCone_bc_of_qcqs : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), IsLimit c → (∀ i, IsAffineHom (G.obj i).hom) → ∀ (W : Scheme.{0}) (r : W ⟶ S) [CompactSpace W] [QuasiSeparatedSpace W], ContCone R F ((bc (sch.map r)).mapCone c) := by
  intro R _ F hF S I _ _ G c hc hG W r _ _
  obtain ⟨V, f, hV, hfe, hfs⟩ := GlobalTheory.exists_affine_etale_surjective W
  have hqc : QuasiCompact f := inferInstance
  have hsep : IsSeparated f := by
    have : IsSeparated (f ≫ terminal.from W) := by
      rw [Subsingleton.elim (f ≫ terminal.from W) (terminal.from V)]; infer_instance
    exact IsSeparated.of_comp f (terminal.from W)
  haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsStableUnderBaseChange :=
    MorphismProperty.IsStableUnderBaseChange.inf
  haveI : (@QuasiCompact ⊓ @IsSeparated : MorphismProperty Scheme.{0}).IsMultiplicative :=
    { id_mem := fun X => ⟨inferInstance, inferInstance⟩
      comp_mem := fun f g hf hg => by
        obtain ⟨hf1, hf2⟩ := hf
        obtain ⟨hg1, hg2⟩ := hg
        exact ⟨inferInstance, inferInstance⟩ }
  refine GlobalTheory.T.continuousCone_descends_etale_surjective R F S I G c W V r f hfe hfs (@QuasiCompact ⊓ @IsSeparated) ⟨hqc, hsep⟩ ?_
  intro Z π hπ
  obtain ⟨h1, h2⟩ := hπ
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace π
  have : Z.IsSeparated := by
    constructor
    rw [Subsingleton.elim (terminal.from Z) (π ≫ terminal.from V)]; infer_instance
  exact contCone_bc_of_compact_separated R F hF S I G c hc hG Z (π ≫ f ≫ r)

end GlobalTheory
