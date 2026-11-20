import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsAreConstantAbelianSchemeNoetheriaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDifferentialsFromGlobalFormsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafComparisonInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

/- English proof (translation)
Introduce `HC HH R _ _ A _ g hA hg`. Establish `hs : Smooth A.hom` using `hA.smooth`. Establish `hp : IsProper A.hom` using `hA.proper`. Establish `hsep : IsSeparated A.hom` using `inferInstance`. Establish `hqc : QuasiCompact A.hom` using `inferInstance`.

Establish `bij` using `HC.bijective_cechDeRhamComparison_degreeOne A.hom hs hsep hqc`. Take `⟨-, -, ⟨-, hproj, -⟩, -, ⟨hcl, hinj, -⟩, -⟩` from `HH R A g hA hg`. Establish `key : ∀ f : Form A.hom, cmp1 A.hom (Form.cl A.hom f) = clForm A.hom (cmpForm A.hom f)` using `comparison_formClass A.hom`. Use `⟨GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian R A hA, GlobalTheory.T.abelianScheme_differentials_from_globalForms HC HH R A g hA hg, hproj, fun w ↦ ?_, fun f ↦ ?_⟩` and prove the remaining obligations. Establish `hw : w ∈ ClosedForm A.hom` using `hcl ▸ Submodule.mem_top`.

Take `⟨c, hc⟩` from `bij.2 (clForm A.hom ⟨w, hw⟩)`. Establish `h1 : clForm A.hom ⟨w, hw⟩ ∈ CechHodgeFiltration A.hom` using `(cechHodgeFiltration_eq_range A.hom).symm ▸ ⟨_, rfl⟩`. Establish `h2 : c ∈ F1 A.hom`. Express the relevant statement in the definitionally equal form `toH1O A.hom c = 0`. Apply `cmpO_injective R A.left A.hom` to reduce the goal to its premises.

Rewrite using `[← structureSheaf_comparison_comm, hc, map_zero]`. Conclude with `h1`. Rewrite `h2` using `[hodgeFiltration_eq_range]`. Take `⟨f, rfl⟩` from `h2`. Use `⟨f, ?_⟩` and prove the remaining obligations.

Use `hinj ((key f).symm.trans hc)` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[← key, h, map_zero, map_zero]`. Introduce `h`. Apply `bij.1` to reduce the goal to its premises. Rewrite using `[key, h, map_zero, map_zero]`.
-/
theorem good_of_isAbelianScheme : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R]
    [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Good A.hom := by
  intro HC HH R _ _ A _ g hA hg
  have hs : Smooth A.hom := hA.smooth
  have hp : IsProper A.hom := hA.proper
  have hsep : IsSeparated A.hom := inferInstance
  have hqc : QuasiCompact A.hom := inferInstance
  have bij := HC.bijective_cechDeRhamComparison_degreeOne A.hom hs hsep hqc
  obtain ⟨-, -, ⟨-, hproj, -⟩, -, ⟨hcl, hinj, -⟩, -⟩ := HH R A g hA hg
  have key : ∀ f : Form A.hom, cmp1 A.hom (Form.cl A.hom f) = clForm A.hom (cmpForm A.hom f) :=
    comparison_formClass A.hom
  refine ⟨GlobalTheory.T.globalFunctionsAreConstant_abelianScheme_noetherian R A hA, GlobalTheory.T.abelianScheme_differentials_from_globalForms HC HH R A g hA hg, hproj, fun w ↦ ?_, fun f ↦ ?_⟩
  · have hw : w ∈ ClosedForm A.hom := hcl ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := bij.2 (clForm A.hom ⟨w, hw⟩)
    have h1 : clForm A.hom ⟨w, hw⟩ ∈ CechHodgeFiltration A.hom := (cechHodgeFiltration_eq_range A.hom).symm ▸ ⟨_, rfl⟩
    have h2 : c ∈ F1 A.hom := by
      change toH1O A.hom c = 0
      apply cmpO_injective R A.left A.hom
      rw [← structureSheaf_comparison_comm, hc, map_zero]
      exact h1
    rw [hodgeFiltration_eq_range] at h2
    obtain ⟨f, rfl⟩ := h2
    refine ⟨f, ?_⟩
    have := hinj ((key f).symm.trans hc)
    exact congrArg Subtype.val this
  · constructor
    · intro h
      apply hinj
      rw [← key, h, map_zero, map_zero]
    · intro h
      apply bij.1
      rw [key, h, map_zero, map_zero]

end GlobalTheory.LiftSys
