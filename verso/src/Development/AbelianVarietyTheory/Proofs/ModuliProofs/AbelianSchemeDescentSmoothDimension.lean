import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgClosedJoinOfTwoFieldExtensions

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldDescentAb

set_option backward.isDefEq.respectTransparency.types false

/- English proof (translation)
Use `⟨⟨⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩` and prove the remaining obligations. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.Flat.of_isField (Field.toIsField K₀) _`.
-/
theorem fpqc_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (spMap i) := by
  refine ⟨⟨⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩, ?_⟩, inferInstance⟩
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.Flat.of_isField (Field.toIsField K₀) _

/- English proof (translation)
Establish `h : (MorphismProperty.diagonal @UniversallyClosed) p` using `MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.diagonal @UniversallyClosed) H.flip hf (show UniversallyClosed (pullback.diagonal q) from inferInstance)`. Establish `h' : UniversallyClosed (pullback.diagonal p)` using `h`. Conclude with `⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal p).isClosedMap.isClosed_range⟩`.
-/
theorem isSeparated_of_isPullback {X Y S T : Scheme.{0}} {f : T ⟶ S} {g : Y ⟶ X}
    {p : X ⟶ S} {q : Y ⟶ T} (H : IsPullback g q p f)
    (hf : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) f)
    [IsSeparated q] : IsSeparated p := by
  have h : (MorphismProperty.diagonal @UniversallyClosed) p :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.diagonal @UniversallyClosed) H.flip hf
      (show UniversallyClosed (pullback.diagonal q) from inferInstance)
  have h' : UniversallyClosed (pullback.diagonal p) := h
  exact ⟨IsClosedImmersion.of_isPreimmersion _ (pullback.diagonal p).isClosedMap.isClosed_range⟩

/- English proof (translation)
Use `⟨fun K' _ y Z fst snd h => ?_⟩` and prove the remaining obligations. Take `⟨ψ, rfl⟩` from `Spec.map_surjective y`. Take `⟨Ω, _, _, j, j', e⟩` from `GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i ψ.hom`. Establish `e' : spMap j ≫ spMap i = spMap j' ≫ Spec.map ψ`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`.

Use `congr 1`. Conclude with `CommRingCat.hom_ext e`. Establish `h₁ : IsPullback (pullback.fst snd (spMap j') ≫ fst) (pullback.snd snd (spMap j')) p (spMap j ≫ spMap i)`. Rewrite using `[e']`. Conclude with `(IsPullback.of_hasPullback snd (spMap j')).paste_horiz h`.

Establish `h₂ : IsPullback (H.lift (pullback.fst snd (spMap j') ≫ fst) (pullback.snd snd (spMap j') ≫ spMap j) (by rw [h₁.w, Category.assoc])) (pullback.snd snd (spMap j')) q (spMap j)` using `IsPullback.of_right (by rw [H.lift_fst]; exact h₁) (H.lift_snd _ _ _) H`. Establish `hc : ConnectedSpace ↥(pullback snd (spMap j'))` using `hq.geometrically_connectedSpace _ _ _ h₂`. Establish `: Surjective (spMap j')` using `(fpqc_spMap j').1.1`. Conclude with `(pullback.fst snd (spMap j')).surjective.connectedSpace (pullback.fst snd (spMap j')).continuous`.
-/
theorem geometricallyConnected_of_isPullback {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {X Y : Scheme.{0}} {g : Y ⟶ X} {p : X ⟶ Sp K₀} {q : Y ⟶ Sp K}
    (H : IsPullback g q p (spMap i)) [hq : GeometricallyConnected q] :
    GeometricallyConnected p := by
  refine ⟨fun K' _ y Z fst snd h => ?_⟩
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective y
  obtain ⟨Ω, _, _, j, j', e⟩ := GlobalTheory.exists_algClosed_join_of_two_field_extensions K₀ K K' i ψ.hom
  have e' : spMap j ≫ spMap i = spMap j' ≫ Spec.map ψ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext e
  have h₁ : IsPullback (pullback.fst snd (spMap j') ≫ fst) (pullback.snd snd (spMap j')) p
      (spMap j ≫ spMap i) := by
    rw [e']
    exact (IsPullback.of_hasPullback snd (spMap j')).paste_horiz h
  have h₂ : IsPullback (H.lift (pullback.fst snd (spMap j') ≫ fst)
      (pullback.snd snd (spMap j') ≫ spMap j) (by rw [h₁.w, Category.assoc]))
      (pullback.snd snd (spMap j')) q (spMap j) :=
    IsPullback.of_right (by rw [H.lift_fst]; exact h₁) (H.lift_snd _ _ _) H
  have hc : ConnectedSpace ↥(pullback snd (spMap j')) :=
    hq.geometrically_connectedSpace _ _ _ h₂
  have : Surjective (spMap j') := (fpqc_spMap j').1.1
  exact (pullback.fst snd (spMap j')).surjective.connectedSpace
    (pullback.fst snd (spMap j')).continuous

/- English proof (translation)
Establish `key : ∀ (T₀ : Over S) (x₀ y₀ : T₀ ⟶ A₀), x₀ * y₀ = y₀ * x₀`. Introduce `T₀ x₀ y₀`. Set `T : Over S'` to `Over.mk (pullback.snd T₀.hom f)`. Set `r : Over.mk (T.hom ≫ f) ⟶ T₀` to `Over.homMk (pullback.fst T₀.hom f) pullback.condition`. Set `up : (T₀ ⟶ A₀) → (T ⟶ A)` to `fun x => Over.homMk (H.1.lift (pullback.fst T₀.hom f ≫ x.left) (pullback.snd T₀.hom f) (by rw [Category.assoc, Over.w x, pullback.condition])) (H.1.lift_snd _ _ _)`.

Establish `hup : ∀ x : T₀ ⟶ A₀, (r ≫ x).left = (up x).left ≫ φ` using `fun x => (H.1.lift_fst _ _ _).symm`. Establish `h₁` using `H.2 T (up x₀) (up y₀) _ _ (hup x₀) (hup y₀)`. Establish `h₂` using `H.2 T (up y₀) (up x₀) _ _ (hup y₀) (hup x₀)`. Rewrite `h₂` using `[mul_comm (up y₀), ← h₁, ← MonObj.comp_mul, ← MonObj.comp_mul]`. Establish `: Epi (pullback.fst T₀.hom f)` using `Flat.epi_of_flat_of_surjective _`.

Use `ext1`. Rewrite using `[← cancel_epi (pullback.fst T₀.hom f)]`. Conclude with `h₂.symm`. Prove the components needed by the constructor for the conclusion. Use `key _ (fst A₀ A₀) (snd A₀ A₀)` as an intermediate fact.

Rewrite `this` using `[Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst]`. Conclude with `this.symm`.
-/
theorem isCommMonObj_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} (A₀ : Over S)
    (A : Over S') [GrpObj A₀] [GrpObj A] {φ : A.left ⟶ A₀.left} (H : IsGrpPullback A A₀ f φ)
    [Flat f] [Surjective f] [IsCommMonObj A] : IsCommMonObj A₀ := by
  have key : ∀ (T₀ : Over S) (x₀ y₀ : T₀ ⟶ A₀), x₀ * y₀ = y₀ * x₀ := by
    intro T₀ x₀ y₀
    let T : Over S' := Over.mk (pullback.snd T₀.hom f)
    let r : Over.mk (T.hom ≫ f) ⟶ T₀ :=
      Over.homMk (pullback.fst T₀.hom f) pullback.condition
    let up : (T₀ ⟶ A₀) → (T ⟶ A) := fun x => Over.homMk
      (H.1.lift (pullback.fst T₀.hom f ≫ x.left) (pullback.snd T₀.hom f)
        (by rw [Category.assoc, Over.w x, pullback.condition])) (H.1.lift_snd _ _ _)
    have hup : ∀ x : T₀ ⟶ A₀, (r ≫ x).left = (up x).left ≫ φ := fun x =>
      (H.1.lift_fst _ _ _).symm
    have h₁ := H.2 T (up x₀) (up y₀) _ _ (hup x₀) (hup y₀)
    have h₂ := H.2 T (up y₀) (up x₀) _ _ (hup y₀) (hup x₀)
    rw [mul_comm (up y₀), ← h₁, ← MonObj.comp_mul, ← MonObj.comp_mul] at h₂
    have : Epi (pullback.fst T₀.hom f) := Flat.epi_of_flat_of_surjective _
    ext1
    rw [← cancel_epi (pullback.fst T₀.hom f)]
    exact h₂.symm
  constructor
  have := key _ (fst A₀ A₀) (snd A₀ A₀)
  rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_snd_fst] at this
  exact this.symm

/- English proof (translation)
Introduce `K₀ K _ _ i A₀ A _ _ φ H hA`. Establish `hf` using `fpqc_spMap i`. Use `hf.1.1` as an intermediate fact. Use `hf.1.2` as an intermediate fact. Use `hA.comm` as an intermediate fact.

Use `hA.smooth` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Establish `hsep : IsSeparated A₀.hom` using `isSeparated_of_isPullback H.1 hf`. Establish `huc : UniversallyClosed A₀.hom` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.1.flip hf inferInstance`.

Establish `hsm : Smooth A₀.hom` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.1.flip hf inferInstance`. Establish `h₀ : IsAbelianScheme A₀` using `{ comm := isCommMonObj_of_isGrpPullback A₀ A H smooth := hsm proper := {} geomConnected := geometricallyConnected_of_isPullback i H.1 }`. Use `⟨h₀, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨g', hg'⟩` from `GlobalTheory.AbelianDim.exists_relDim K₀ A₀ h₀`. Establish `h' : SmoothOfRelativeDimension g' A.hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H.1 hg'`.

Take `⟨x, -⟩` from `A.hom.surjective (Nonempty.some inferInstance)`. Rewrite using `[ReciprocityTheory.ChartRestriction.G.H1.dim_unique A.hom hg h' x]`. Conclude with `hg'`.
-/
theorem isAbelianScheme_and_relDim_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (A₀ : Over (Sp K₀)) (A : Over (Sp K)) [GrpObj A₀] [GrpObj A] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap i) φ → IsAbelianScheme A → IsAbelianScheme A₀ ∧ ∀ g : ℕ, SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g A₀.hom := by
  intro K₀ K _ _ i A₀ A _ _ φ H hA
  have hf := fpqc_spMap i
  have := hf.1.1
  have := hf.1.2
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hsep : IsSeparated A₀.hom := isSeparated_of_isPullback H.1 hf
  have huc : UniversallyClosed A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) H.1.flip hf
      inferInstance
  have hsm : Smooth A₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) H.1.flip hf inferInstance
  have h₀ : IsAbelianScheme A₀ :=
    { comm := isCommMonObj_of_isGrpPullback A₀ A H
      smooth := hsm
      proper := {}
      geomConnected := geometricallyConnected_of_isPullback i H.1 }
  refine ⟨h₀, fun g hg => ?_⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim K₀ A₀ h₀
  have h' : SmoothOfRelativeDimension g' A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g').of_isPullback H.1 hg'
  obtain ⟨x, -⟩ := A.hom.surjective (Nonempty.some inferInstance)
  rw [ReciprocityTheory.ChartRestriction.G.H1.dim_unique A.hom hg h' x]
  exact hg'

end GlobalTheory.FieldDescentAb
