import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.CommonGen

/- English proof (translation)
Establish `: IsProper V₁.p` using `CommonModel.isProper_of_isProjOver V₁.ar.isProjOver`. Establish `: IsProper (V₁.π ≫ Y.str)` using `MorphismProperty.of_isPullback V₁.pb ‹IsProper V₁.p›`. Set `Q : Scheme.{0}` to `pullback V₁.π V₂.π`. Set `a : Q ⟶ V₁.G` to `pullback.fst V₁.π V₂.π`. Set `b : Q ⟶ V₂.G` to `pullback.snd V₁.π V₂.π`.

Establish `: IsFinite a` using `inferInstanceAs (IsFinite (pullback.fst V₁.π V₂.π))`. Establish `hs : Surjective a` using `inferInstanceAs (Surjective (pullback.fst V₁.π V₂.π))`. Take `⟨η, hη⟩` from `hs.surj (genericPoint V₁.G)`. Set `s : Q ⟶ Spec (.of F)` to `a ≫ V₁.π ≫ Y.str`. Establish `: IsProper s` using `inferInstanceAs (IsProper (a ≫ V₁.π ≫ Y.str))`.

Establish `: CharZero (Q.residueField η)` using `charZero_of_injective_ringHom ((Scheme.ΓSpecIso (.of F)).inv ≫ s.appTop ≫ Q.Γevaluation η).hom.injective`. Set `u : Spec (.of (Q.residueField η)) ⟶ Q` to `Spec.map (Q.residue η) ≫ Q.fromSpecStalk η`. Establish `hfin : IsFinite u.fromNormalization` using `GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η (L := Q.residueField η) (Q.residue η) (RingHom.FiniteType.of_surjective _ (Q.residue_surjective η)).essFiniteType`. Establish `hu : u (IsLocalRing.closedPoint (Q.residueField η)) = η` using `Scheme.fromSpecResidueField_apply η _`. Establish `: IsDominant (u ≫ a)` using `⟨(dense_iff_closure_eq.2 (genericPoint_spec V₁.G)).mono (Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint (Q.residueField η), by`.

Express the relevant statement in the definitionally equal form `a (u _) = _`. Rewrite using `[hu, hη]⟩)⟩`. Establish `hd : IsDominant (u.fromNormalization ≫ a)`. Establish `: IsDominant (u.toNormalization ≫ u.fromNormalization ≫ a)`. Rewrite using `[← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]`.

Use `infer_instance`. Conclude with `IsDominant.of_comp u.toNormalization _`. Use `⟨u.normalization, inferInstance, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u, u.fromNormalization ≫ a, u.fromNormalization ≫ b, inferInstance, hd, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, pullback.condition]`.
-/
theorem exists_common (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Mean4O.Cover Y) :
    ∃ (G : Scheme.{0}) (_ : IsIntegral G) (_ : GlobalTheory.IsNormalScheme G) (g : G ⟶ V₁.G) (k : G ⟶ V₂.G),
      IsFinite g ∧ IsDominant g ∧ k ≫ V₂.π = g ≫ V₁.π := by
  have : IsProper V₁.p := CommonModel.isProper_of_isProjOver V₁.ar.isProjOver
  have : IsProper (V₁.π ≫ Y.str) := MorphismProperty.of_isPullback V₁.pb ‹IsProper V₁.p›
  let Q : Scheme.{0} := pullback V₁.π V₂.π
  let a : Q ⟶ V₁.G := pullback.fst V₁.π V₂.π
  let b : Q ⟶ V₂.G := pullback.snd V₁.π V₂.π
  have : IsFinite a := inferInstanceAs (IsFinite (pullback.fst V₁.π V₂.π))
  have hs : Surjective a := inferInstanceAs (Surjective (pullback.fst V₁.π V₂.π))
  obtain ⟨η, hη⟩ := hs.surj (genericPoint V₁.G)
  let s : Q ⟶ Spec (.of F) := a ≫ V₁.π ≫ Y.str
  have : IsProper s := inferInstanceAs (IsProper (a ≫ V₁.π ≫ Y.str))
  have : CharZero (Q.residueField η) := charZero_of_injective_ringHom
    ((Scheme.ΓSpecIso (.of F)).inv ≫ s.appTop ≫ Q.Γevaluation η).hom.injective
  let u : Spec (.of (Q.residueField η)) ⟶ Q := Spec.map (Q.residue η) ≫ Q.fromSpecStalk η
  have hfin : IsFinite u.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk s η (L := Q.residueField η) (Q.residue η)
      (RingHom.FiniteType.of_surjective _ (Q.residue_surjective η)).essFiniteType
  have hu : u (IsLocalRing.closedPoint (Q.residueField η)) = η :=
    Scheme.fromSpecResidueField_apply η _
  have : IsDominant (u ≫ a) := ⟨(dense_iff_closure_eq.2 (genericPoint_spec V₁.G)).mono
    (Set.singleton_subset_iff.2 ⟨IsLocalRing.closedPoint (Q.residueField η), by
      change a (u _) = _
      rw [hu, hη]⟩)⟩
  have hd : IsDominant (u.fromNormalization ≫ a) := by
    have : IsDominant (u.toNormalization ≫ u.fromNormalization ≫ a) := by
      rw [← Category.assoc, Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp u.toNormalization _
  refine ⟨u.normalization, inferInstance, GlobalTheory.IsNormalScheme.normalization_of_isIntegral u,
    u.fromNormalization ≫ a, u.fromNormalization ≫ b, inferInstance, hd, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition]

end GlobalTheory.Mean4O.CommonGen
