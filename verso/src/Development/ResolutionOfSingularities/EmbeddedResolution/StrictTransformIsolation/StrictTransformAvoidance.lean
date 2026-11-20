import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsOpenImmersion
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GenericPointsAvoidCenter
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DetachedLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem comp_base_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (x : ↥A) :
    (f ≫ g).base x = g.base (f.base x) := by simp

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

def AvoidsCenters (S : EmbeddedBlowupSequence k Y pY) : ∀ (i : ℕ), ↥(S.schemeAt i) → Prop
  | 0 => fun _ => True
  | (i + 1) => fun x =>
      (S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) ∧
        AvoidsCenters S i ((S.blowdown i).base x)

/- English proof (translation)
Discharge the goal by the elementary cases of `trivial`.
-/
@[simp] theorem avoidsCenters_zero (S : EmbeddedBlowupSequence k Y pY) (x : ↥(S.schemeAt 0)) : S.AvoidsCenters 0 x := trivial

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
@[simp] theorem avoidsCenters_succ_iff (S : EmbeddedBlowupSequence k Y pY) (i : ℕ) (x : ↥(S.schemeAt (i + 1))) :
    S.AvoidsCenters (i + 1) x ↔
      ((S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) ∧
        S.AvoidsCenters i ((S.blowdown i).base x)) :=
  Iff.rfl

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ _ _ _ _`. Conclude with `S.avoidsCenters_zero _`.

Consider the case `succ i ih`. Introduce `hi C hC ξ hξ`. Establish `hi' : i < S.length` using `Nat.lt_of_succ_le hi`. Take `⟨C', hC', hη', hfr⟩` from `S.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC ξ hξ`. Establish `key : (S.strictTransformι i).base ((S.strictTransformMap i).base ξ) = (S.blowdown i).base ((S.strictTransformι (i + 1)).base ξ)`.

Establish `h : (S.strictTransformMap i ≫ S.strictTransformι i).base ξ = (S.strictTransformι (i + 1) ≫ S.blowdown i).base ξ`. Rewrite using `[S.strictTransformMap_comp_strictTransformι i]`. Simplify using `using h`. Use `(S.avoidsCenters_succ_iff i _).mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← key]`.

Conclude with `S.notMem_ambientCenter_support_of_isGenericPoint i C' hC' hfr _ hη'`. Rewrite using `[← key]`. Conclude with `ih (Nat.le_of_succ_le hi) C' hC' _ hη'`.
-/
private theorem forall_avoidsCenters_strictTransformι_of_isGenericPoint [AlgebraicGeometry.IsReduced Y]
    (S : EmbeddedBlowupSequence k Y pY)
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j)) :
    ∀ (i : ℕ), i ≤ S.length → ∀ C : Set ↥(S.strictTransform i),
      C ∈ irreducibleComponents ↥(S.strictTransform i) →
      ∀ ξ : ↥(S.strictTransform i), IsGenericPoint ξ C →
      S.AvoidsCenters i ((S.strictTransformι i).base ξ) := by
  intro i
  induction i with
  | zero =>
    intro _ _ _ _ _
    exact S.avoidsCenters_zero _
  | succ i ih =>
    intro hi C hC ξ hξ
    have hi' : i < S.length := Nat.lt_of_succ_le hi
    obtain ⟨C', hC', hη', hfr⟩ := S.exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC ξ hξ
    have key : (S.strictTransformι i).base ((S.strictTransformMap i).base ξ)
        = (S.blowdown i).base ((S.strictTransformι (i + 1)).base ξ) := by
      have h : (S.strictTransformMap i ≫ S.strictTransformι i).base ξ
          = (S.strictTransformι (i + 1) ≫ S.blowdown i).base ξ := by
        rw [S.strictTransformMap_comp_strictTransformι i]
      simpa using h
    refine (S.avoidsCenters_succ_iff i _).mpr ⟨?_, ?_⟩
    · rw [← key]
      exact S.notMem_ambientCenter_support_of_isGenericPoint i C' hC' hfr _ hη'
    · rw [← key]
      exact ih (Nat.le_of_succ_le hi) C' hC' _ hη'

/- English proof (translation)
The claim follows from `forall_avoidsCenters_strictTransformι_of_isGenericPoint S hN i hi C hC ξ hξ`.
-/
theorem avoidsCenters_strictTransformι_of_isGenericPoint [AlgebraicGeometry.IsReduced Y] (S : EmbeddedBlowupSequence k Y pY)
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i ≤ S.length)
    (C : Set ↥(S.strictTransform i)) (hC : C ∈ irreducibleComponents ↥(S.strictTransform i))
    (ξ : ↥(S.strictTransform i)) (hξ : IsGenericPoint ξ C) :
    S.AvoidsCenters i ((S.strictTransformι i).base ξ) :=
  forall_avoidsCenters_strictTransformι_of_isGenericPoint S hN i hi C hC ξ hξ

/- English proof (translation)
Establish `: CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i)` using `S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi`. Establish `: AlgebraicGeometry.IsOpenImmersion (S.blowdown i ∣_ S.ambientCenterSupportCompl i)` using `inferInstance`. Establish `hle : U ≤ (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i)`. Introduce `x hx`. Conclude with `hU hx`.

Establish `key : (S.schemeAt (i + 1)).homOfLE hle ≫ ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫ (S.ambientCenterSupportCompl i).ι) = U.ι ≫ S.blowdown i`. Rewrite using `[AlgebraicGeometry.morphismRestrict_ι, ← CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.homOfLE_ι]`. Rewrite using `[← key]`. Use `infer_instance`.
-/
theorem isOpenImmersion_ι_comp_blowdown (S : EmbeddedBlowupSequence k Y pY) (i : ℕ) (hi : i < S.length)
    (U : (S.schemeAt (i + 1)).Opens)
    (hU : (U : Set ↥(S.schemeAt (i + 1))) ⊆
      ⇑(S.blowdown i).base ⁻¹' ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i))) :
    AlgebraicGeometry.IsOpenImmersion (U.ι ≫ S.blowdown i) := by
  have : CategoryTheory.IsIso (S.blowdown i ∣_ S.ambientCenterSupportCompl i) :=
    S.isIso_blowdown_restrict_ambientCenterSupportCompl i hi
  have : AlgebraicGeometry.IsOpenImmersion (S.blowdown i ∣_ S.ambientCenterSupportCompl i) := inferInstance
  have hle : U ≤ (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) := by
    intro x hx
    exact hU hx
  have key : (S.schemeAt (i + 1)).homOfLE hle ≫
      ((S.blowdown i ∣_ S.ambientCenterSupportCompl i) ≫ (S.ambientCenterSupportCompl i).ι) = U.ι ≫ S.blowdown i := by
    rw [AlgebraicGeometry.morphismRestrict_ι, ← CategoryTheory.Category.assoc,
      AlgebraicGeometry.Scheme.homOfLE_ι]
  rw [← key]
  infer_instance

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `hx`. Establish `hcont : Continuous ⇑(S.strictTransformMap i).base` using `(S.strictTransformMap i).base.hom.continuous`. Establish `hηC : closure ({η} : Set ↥(S.strictTransform (i + 1))) = C` using `hη`. Establish `hηC' : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)) = C'` using `hη'`. Establish `hclosed : IsClosed (⇑(S.strictTransformMap i).base ⁻¹' C')`.

Rewrite using `[← hηC']`. Conclude with `isClosed_closure.preimage hcont`. Establish `hsub : C ⊆ ⇑(S.strictTransformMap i).base ⁻¹' C'`. Rewrite using `[← hηC]`. Use `closure_minimal ?_ hclosed` and prove the remaining obligations.

Introduce `z hz`. Establish `hz' : z = η` using `hz`. Substitute `hz'` using the available equality. Rewrite using `[Set.mem_preimage, ← hηC']`. Conclude with `subset_closure rfl`.

Use `⟨(S.strictTransformMap i).base c, hsub hc, ?_⟩` and prove the remaining obligations. Establish `key : ((S.strictTransformMap i) ≫ (S.strictTransformι i)).base c = ((S.strictTransformι (i + 1)) ≫ (S.blowdown i)).base c`. Rewrite using `[S.strictTransformMap_comp_strictTransformι i]`. Simplify using `using key`.
-/
theorem mem_image_strictTransformι_of_mem_image_succ (S : EmbeddedBlowupSequence k Y pY) (i : ℕ)
    (C : Set ↥(S.strictTransform (i + 1))) (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C)
    (C' : Set ↥(S.strictTransform i)) (hη' : IsGenericPoint ((S.strictTransformMap i).base η) C')
    (x : ↥(S.schemeAt (i + 1))) (hx : x ∈ ⇑(S.strictTransformι (i + 1)).base '' C) :
    (S.blowdown i).base x ∈ ⇑(S.strictTransformι i).base '' C' := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hcont : Continuous ⇑(S.strictTransformMap i).base := (S.strictTransformMap i).base.hom.continuous
  have hηC : closure ({η} : Set ↥(S.strictTransform (i + 1))) = C := hη
  have hηC' : closure ({(S.strictTransformMap i).base η} : Set ↥(S.strictTransform i)) = C' := hη'
  have hclosed : IsClosed (⇑(S.strictTransformMap i).base ⁻¹' C') := by
    rw [← hηC']
    exact isClosed_closure.preimage hcont
  have hsub : C ⊆ ⇑(S.strictTransformMap i).base ⁻¹' C' := by
    rw [← hηC]
    refine closure_minimal ?_ hclosed
    intro z hz
    have hz' : z = η := hz
    subst hz'
    rw [Set.mem_preimage, ← hηC']
    exact subset_closure rfl
  refine ⟨(S.strictTransformMap i).base c, hsub hc, ?_⟩
  have key : ((S.strictTransformMap i) ≫ (S.strictTransformι i)).base c
      = ((S.strictTransformι (i + 1)) ≫ (S.blowdown i)).base c := by
    rw [S.strictTransformMap_comp_strictTransformι i]
  simpa using key

/- English proof (translation)
Establish `hvx : V.ι.base (⟨x, hx⟩ : ↥V) = x` using `rfl`. Establish `hvy : V.ι.base (⟨y, hy⟩ : ↥V) = y` using `rfl`. Establish `h' : (V.ι ≫ π).base (⟨y, hy⟩ : ↥V) ⤳ (V.ι ≫ π).base (⟨x, hx⟩ : ↥V)`. Rewrite using `[comp_base_apply V.ι π (⟨x, hx⟩ : ↥V), comp_base_apply V.ι π (⟨y, hy⟩ : ↥V), hvx, hvy]`. Conclude with `specializes_iff_mem_closure.mpr h`.

Establish `hspec : (⟨y, hy⟩ : ↥V) ⤳ (⟨x, hx⟩ : ↥V)` using `hoe.isInducing.specializes_iff.mp h'`. Establish `hfin` using `hspec.map V.ι.base.hom.continuous`. Rewrite `hfin` using `[hvx, hvy]`. Conclude with `specializes_iff_mem_closure.mp hfin`.
-/
private theorem mem_closure_singleton_of_base_mem {X₀ X₁ : Scheme.{u}}
    (π : X₁ ⟶ X₀) (V : X₁.Opens)
    (hoe : Topology.IsOpenEmbedding ⇑(V.ι ≫ π).base)
    {x y : ↥X₁} (hx : x ∈ V) (hy : y ∈ V)
    (h : π.base x ∈ closure ({π.base y} : Set ↥X₀)) :
    x ∈ closure ({y} : Set ↥X₁) := by
  have hvx : V.ι.base (⟨x, hx⟩ : ↥V) = x := rfl
  have hvy : V.ι.base (⟨y, hy⟩ : ↥V) = y := rfl
  have h' : (V.ι ≫ π).base (⟨y, hy⟩ : ↥V) ⤳ (V.ι ≫ π).base (⟨x, hx⟩ : ↥V) := by
    rw [comp_base_apply V.ι π (⟨x, hx⟩ : ↥V), comp_base_apply V.ι π (⟨y, hy⟩ : ↥V), hvx, hvy]
    exact specializes_iff_mem_closure.mpr h
  have hspec : (⟨y, hy⟩ : ↥V) ⤳ (⟨x, hx⟩ : ↥V) := hoe.isInducing.specializes_iff.mp h'
  have hfin := hspec.map V.ι.base.hom.continuous
  rw [hvx, hvy] at hfin
  exact specializes_iff_mem_closure.mp hfin

/- English proof (translation)
Establish `hgenericImage : IsGenericPoint ((S.strictTransformι (i + 1)).base η) (⇑(S.strictTransformι (i + 1)).base '' C)` using `FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformι (i + 1)) hη`. Establish `hgenericImagePrev : IsGenericPoint ((S.strictTransformι i).base ((S.strictTransformMap i).base η)) (⇑(S.strictTransformι i).base '' C')` using `FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformι i) hη'`. Establish `hclA : closure ({(S.strictTransformι (i + 1)).base η} : Set ↥(S.schemeAt (i + 1))) = ⇑(S.strictTransformι (i + 1)).base '' C` using `hgenericImage`. Establish `hclB : closure ({(S.strictTransformι i).base ((S.strictTransformMap i).base η)} : Set ↥(S.schemeAt i)) = ⇑(S.strictTransformι i).base '' C'` using `hgenericImagePrev`. Establish `key : (S.strictTransformι i).base ((S.strictTransformMap i).base η) = (S.blowdown i).base ((S.strictTransformι (i + 1)).base η)`.

Establish `h : (S.strictTransformMap i ≫ S.strictTransformι i).base η = (S.strictTransformι (i + 1) ≫ S.blowdown i).base η`. Rewrite using `[S.strictTransformMap_comp_strictTransformι i]`. Simplify using `using h`. Establish `hclosure : (S.blowdown i).base x ∈ closure ({(S.blowdown i).base ((S.strictTransformι (i + 1)).base η)} : Set ↥(S.schemeAt i))`. Rewrite using `[← key, hclB]`.

Conclude with `hmem`. Establish `hy₀ : (S.blowdown i).base ((S.strictTransformι (i + 1)).base η) ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i))`. Introduce `hmemc`. Conclude with `hx (closure_minimal (Set.singleton_subset_iff.mpr hmemc) ((S.ambientCenter i).support).2 hclosure)`. Take `⟨V, hVdef⟩ : ∃ V : (S.schemeAt (i + 1)).Opens, V = (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i)` from `⟨_, rfl⟩`.

Establish `hVsub : (V : Set ↥(S.schemeAt (i + 1))) ⊆ ⇑(S.blowdown i).base ⁻¹' ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i))`. Rewrite using `[hVdef]`. Introduce `y hy`. Conclude with `hy`. Establish `hoi : AlgebraicGeometry.IsOpenImmersion (V.ι ≫ S.blowdown i)` using `S.isOpenImmersion_ι_comp_blowdown i hi V hVsub`.

Establish `hxV : x ∈ V`. Rewrite using `[hVdef]`. Conclude with `hx`. Establish `hyV : (S.strictTransformι (i + 1)).base η ∈ V`. Rewrite using `[hVdef]`.

Conclude with `hy₀`. Establish `hmain` using `mem_closure_singleton_of_base_mem (S.blowdown i) V (V.ι ≫ S.blowdown i).isOpenEmbedding hxV hyV hclosure`. Rewrite using `[← hclA]`. Conclude with `hmain`.
-/
private theorem mem_image_strictTransformι_succ_of_mem_image [AlgebraicGeometry.IsReduced Y]
    (S : EmbeddedBlowupSequence k Y pY) (i : ℕ) (hi : i < S.length)
    (C : Set ↥(S.strictTransform (i + 1))) (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C)
    (C' : Set ↥(S.strictTransform i)) (hη' : IsGenericPoint ((S.strictTransformMap i).base η) C')
    (x : ↥(S.schemeAt (i + 1)))
    (hx : (S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))
    (hmem : (S.blowdown i).base x ∈ ⇑(S.strictTransformι i).base '' C') :
    x ∈ ⇑(S.strictTransformι (i + 1)).base '' C := by
  have hgenericImage : IsGenericPoint ((S.strictTransformι (i + 1)).base η) (⇑(S.strictTransformι (i + 1)).base '' C) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformι (i + 1)) hη
  have hgenericImagePrev : IsGenericPoint ((S.strictTransformι i).base ((S.strictTransformMap i).base η))
      (⇑(S.strictTransformι i).base '' C') :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding (S.isClosedEmbedding_strictTransformι i) hη'
  have hclA : closure ({(S.strictTransformι (i + 1)).base η} : Set ↥(S.schemeAt (i + 1)))
      = ⇑(S.strictTransformι (i + 1)).base '' C := hgenericImage
  have hclB : closure ({(S.strictTransformι i).base ((S.strictTransformMap i).base η)} : Set ↥(S.schemeAt i))
      = ⇑(S.strictTransformι i).base '' C' := hgenericImagePrev
  have key : (S.strictTransformι i).base ((S.strictTransformMap i).base η)
      = (S.blowdown i).base ((S.strictTransformι (i + 1)).base η) := by
    have h : (S.strictTransformMap i ≫ S.strictTransformι i).base η
        = (S.strictTransformι (i + 1) ≫ S.blowdown i).base η := by
      rw [S.strictTransformMap_comp_strictTransformι i]
    simpa using h
  have hclosure : (S.blowdown i).base x ∈
      closure ({(S.blowdown i).base ((S.strictTransformι (i + 1)).base η)} : Set ↥(S.schemeAt i)) := by
    rw [← key, hclB]
    exact hmem
  have hy₀ : (S.blowdown i).base ((S.strictTransformι (i + 1)).base η) ∉
      ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
    intro hmemc
    exact hx (closure_minimal (Set.singleton_subset_iff.mpr hmemc)
      ((S.ambientCenter i).support).2 hclosure)
  obtain ⟨V, hVdef⟩ : ∃ V : (S.schemeAt (i + 1)).Opens,
      V = (TopologicalSpace.Opens.map (S.blowdown i).base).obj (S.ambientCenterSupportCompl i) := ⟨_, rfl⟩
  have hVsub : (V : Set ↥(S.schemeAt (i + 1))) ⊆
      ⇑(S.blowdown i).base ⁻¹'
        ((S.ambientCenterSupportCompl i : (S.schemeAt i).Opens) : Set ↥(S.schemeAt i)) := by
    rw [hVdef]
    intro y hy
    exact hy
  have hoi : AlgebraicGeometry.IsOpenImmersion (V.ι ≫ S.blowdown i) :=
    S.isOpenImmersion_ι_comp_blowdown i hi V hVsub
  have hxV : x ∈ V := by
    rw [hVdef]
    exact hx
  have hyV : (S.strictTransformι (i + 1)).base η ∈ V := by
    rw [hVdef]
    exact hy₀
  have hmain := mem_closure_singleton_of_base_mem (S.blowdown i) V
    (V.ι ≫ S.blowdown i).isOpenEmbedding hxV hyV hclosure
  rw [← hclA]
  exact hmain

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hmem => mem_image_strictTransformι_succ_of_mem_image S i hi C η hη C' hη' x hx hmem, fun hxC => mem_image_strictTransformι_of_mem_image_succ S i C η hη C' hη' x hxC⟩`.
-/
theorem mem_image_strictTransformι_iff_of_notMem_ambientCenter [AlgebraicGeometry.IsReduced Y]
    (S : EmbeddedBlowupSequence k Y pY)
    (_hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j)) (i : ℕ) (hi : i < S.length)
    (C : Set ↥(S.strictTransform (i + 1))) (η : ↥(S.strictTransform (i + 1))) (hη : IsGenericPoint η C)
    (C' : Set ↥(S.strictTransform i)) (hη' : IsGenericPoint ((S.strictTransformMap i).base η) C')
    (x : ↥(S.schemeAt (i + 1)))
    (hx : (S.blowdown i).base x ∉ ((S.ambientCenter i).support : Set ↥(S.schemeAt i))) :
    ((S.blowdown i).base x ∈ ⇑(S.strictTransformι i).base '' C') ↔ (x ∈ ⇑(S.strictTransformι (i + 1)).base '' C) :=
  ⟨fun hmem => mem_image_strictTransformι_succ_of_mem_image S i hi C η hη C' hη' x hx hmem,
    fun hxC => mem_image_strictTransformι_of_mem_image_succ S i C η hη C' hη' x hxC⟩

end EmbeddedBlowupSequence

namespace OpenImmersionRestriction

/- English proof (translation)
Rewrite `hx` using `[FunctorialResolution.EmbeddedResolution.support_comap_eq]`. Conclude with `hx`.
-/
theorem mem_support_of_mem_support_comap {X Z : Scheme.{u}} (f : X ⟶ Z) (I : Z.IdealSheafData)
    (x : ↥X) (hx : x ∈ ((I.comap f).support : Set ↥X)) :
    f.base x ∈ (I.support : Set ↥Z) := by
  rw [FunctorialResolution.EmbeddedResolution.support_comap_eq] at hx
  exact hx

def reducedVanishingAssignment : VanishingAssignment.{u} :=
  fun _ T => Scheme.IdealSheafData.vanishingIdeal T

/- English proof (translation)
Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce `ha`. Establish `h2 : g a ∈ (Z₁ : Set ↥W) ∩ (U : Set ↥W)` using `⟨ha, hg a⟩`. Rewrite `h2` using `[h]`.

Conclude with `h2.1`. Introduce `ha`. Establish `h2 : g a ∈ (Z₂ : Set ↥W) ∩ (U : Set ↥W)` using `⟨ha, hg a⟩`. Rewrite `h2` using `[← h]`. Conclude with `h2.1`.
-/
private theorem preimage_congr_of_inter_eq {W : Scheme.{u}} {Z₁ Z₂ : TopologicalSpace.Closeds ↥W}
    {U : W.Opens} (h : (Z₁ : Set ↥W) ∩ (U : Set ↥W) = (Z₂ : Set ↥W) ∩ (U : Set ↥W))
    {A : Type u} (g : A → ↥W) (hg : ∀ a, g a ∈ (U : Set ↥W)) :
    g ⁻¹' (Z₁ : Set ↥W) = g ⁻¹' (Z₂ : Set ↥W) := by
  ext a
  constructor
  · intro ha
    have h2 : g a ∈ (Z₁ : Set ↥W) ∩ (U : Set ↥W) := ⟨ha, hg a⟩
    rw [h] at h2
    exact h2.1
  · intro ha
    have h2 : g a ∈ (Z₂ : Set ↥W) ∩ (U : Set ↥W) := ⟨ha, hg a⟩
    rw [← h] at h2
    exact h2.1

/- English proof (translation)
Establish `hg : ∀ a, (V.2.fromSpec).base a ∈ (U : Set ↥W)`. Introduce `a`. Establish `ha : (V.2.fromSpec).base a ∈ (V.1 : Set ↥W)`. Rewrite using `[← IsAffineOpen.range_fromSpec V.2]`. Conclude with `Set.mem_range_self a`.

Conclude with `hV ha`. Conclude with `congrArg PrimeSpectrum.vanishingIdeal (preimage_congr_of_inter_eq h (fun a => (V.2.fromSpec).base a) hg)`.
-/
private theorem vanishingIdeal_ideal_eq_of_inter_eq {W : Scheme.{u}}
    (Z₁ Z₂ : TopologicalSpace.Closeds ↥W) (U : W.Opens)
    (h : (Z₁ : Set ↥W) ∩ (U : Set ↥W) = (Z₂ : Set ↥W) ∩ (U : Set ↥W))
    (V : W.affineOpens) (hV : (V.1 : Set ↥W) ⊆ (U : Set ↥W)) :
    (Scheme.IdealSheafData.vanishingIdeal Z₁).ideal V
      = (Scheme.IdealSheafData.vanishingIdeal Z₂).ideal V := by
  have hg : ∀ a, (V.2.fromSpec).base a ∈ (U : Set ↥W) := by
    intro a
    have ha : (V.2.fromSpec).base a ∈ (V.1 : Set ↥W) := by
      rw [← IsAffineOpen.range_fromSpec V.2]
      exact Set.mem_range_self a
    exact hV ha
  exact congrArg PrimeSpectrum.vanishingIdeal
    (preimage_congr_of_inter_eq h (fun a => (V.2.fromSpec).base a) hg)

/- English proof (translation)
Use `(agreeNear_iff _ _ _).mpr ⟨U, hx, ?_⟩` and prove the remaining obligations. Use `Scheme.IdealSheafData.ext (funext fun V => ?_)` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]`. Use `congrArg _ ?_` and prove the remaining obligations. Use `vanishingIdeal_ideal_eq_of_inter_eq Z₁ Z₂ U h _ ?_` and prove the remaining obligations.

Introduce `y hy`. Take `⟨z, -, rfl⟩` from `hy`. Conclude with `z.2`.
-/
theorem agreeNear_vanishingIdeal_of_inter_eq {W : Scheme.{u}}
    (Z₁ Z₂ : TopologicalSpace.Closeds ↥W) (U : W.Opens) (x : ↥W) (hx : x ∈ (U : Set ↥W))
    (h : (Z₁ : Set ↥W) ∩ (U : Set ↥W) = (Z₂ : Set ↥W) ∩ (U : Set ↥W)) :
    AgreeNear (Scheme.IdealSheafData.vanishingIdeal Z₁)
      (Scheme.IdealSheafData.vanishingIdeal Z₂) x := by
  refine (agreeNear_iff _ _ _).mpr ⟨U, hx, ?_⟩
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  refine congrArg _ ?_
  refine vanishingIdeal_ideal_eq_of_inter_eq Z₁ Z₂ U h _ ?_
  intro y hy
  obtain ⟨z, -, rfl⟩ := hy
  exact z.2

/- English proof (translation)
Establish `h1 : (1 : A) ∈ Ideal.comap φ P`. Rewrite using `[hP]`. Conclude with `Submodule.mem_top`. Establish `h2 : φ (1 : A) ∈ P` using `Ideal.mem_comap.mp h1`. Rewrite `h2` using `[map_one]`.

Establish `hPtop : P = ⊤` using `Submodule.eq_top_iff'.mpr fun x => by`. Simplify using `using Ideal.mul_mem_left P x h2`. Rewrite using `[hPtop, ← Ideal.one_eq_top, one_mul]`.
-/
private theorem comap_eq_comap_mul_of_comap_eq_top {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (P Q : Ideal B) (hP : Ideal.comap φ P = ⊤) :
    Ideal.comap φ Q = Ideal.comap φ (P * Q) := by
  have h1 : (1 : A) ∈ Ideal.comap φ P := by
    rw [hP]
    exact Submodule.mem_top
  have h2 : φ (1 : A) ∈ P := Ideal.mem_comap.mp h1
  rw [map_one] at h2
  have hPtop : P = ⊤ := Submodule.eq_top_iff'.mpr fun x => by
    simpa using Ideal.mul_mem_left P x h2
  rw [hPtop, ← Ideal.one_eq_top, one_mul]

/- English proof (translation)
Establish `hcomp : K.comap (U.ι ≫ f) = (K.comap f).comap U.ι`. Simplify using `[Scheme.IdealSheafData.comap_comp]`. Rewrite using `[hcomp, ← hmul]`. Use `Scheme.IdealSheafData.ext (funext fun V => ?_)` and prove the remaining obligations. Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J U.ι V, AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I * J) U.ι V]`.

Simplify using `only [AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]`. Use `comap_eq_comap_mul_of_comap_eq_top _ _ _ ?_` and prove the remaining obligations. Rewrite using `[← AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I U.ι V, hI]`. Simplify using the standard rewrite rules.
-/
theorem comap_eq_comap_comp_of_mul_eq {X Z : Scheme.{u}} (f : X ⟶ Z) (U : X.Opens)
    (I J : X.IdealSheafData) (K : Z.IdealSheafData)
    (hmul : I * J = K.comap f) (hI : I.comap U.ι = ⊤) :
    J.comap U.ι = K.comap (U.ι ≫ f) := by
  have hcomp : K.comap (U.ι ≫ f) = (K.comap f).comap U.ι := by
    simp [Scheme.IdealSheafData.comap_comp]
  rw [hcomp, ← hmul]
  refine Scheme.IdealSheafData.ext (funext fun V => ?_)
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion J U.ι V,
    AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion (I * J) U.ι V]
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  refine comap_eq_comap_mul_of_comap_eq_top _ _ _ ?_
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion I U.ι V, hI]
  simp

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  [AlgebraicGeometry.QuasiCompact pY]

omit [AlgebraicGeometry.QuasiCompact pY] in
/- English proof (translation)
Introduce `i hi` and use `(D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt i hi`.
-/
theorem isNoetherian_schemeAt_toEmbeddedBlowupSequence (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    ∀ i ≤ (D.toEmbeddedBlowupSequence A).length,
      AlgebraicGeometry.IsNoetherian ((D.toEmbeddedBlowupSequence A).schemeAt i) :=
  fun i hi => (D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt i hi

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`. Introduce `_ E hE x hx hcl`. Rewrite `hE` using `[(principalizationOfEmbedding k Y pY D A).boundary_zero]`.

Simplify using `at hE`. Consider the case `succ i ih`. Introduce `hi E hE x hx hcl`. Establish `hilt : i < (principalizationOfEmbedding k Y pY D A).length` using `hi`. Rewrite `hE` using `[(principalizationOfEmbedding k Y pY D A).boundary_succ_eq_map_strictTransform_append i hilt, List.mem_append]`.

Establish `hcl'` using `((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x).mp hcl`. Break down `hE with hE | hE` into its components or cases. Take `⟨E', hE', rfl⟩` from `List.mem_map.mp hE`. Establish `hmem : x ∈ ((E'.comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i)).support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt (i + 1)))` using `AlgebraicGeometry.Scheme.IdealSheafData.support_antitone (FunctorialResolution.EmbeddedResolution.comap_le_strictTransform ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) ((principalizationOfEmbedding k Y pY D A).center i) E') hx`. Establish `hmem2 : ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i).base x ∈ (E'.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))` using `mem_support_of_mem_support_comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) E' x hmem`.

Conclude with `ih (Nat.le_of_succ_le hi) E' hE' _ hmem2 hcl'.2`. Rewrite `hE` using `[List.mem_singleton]`. Substitute `hE` using the available equality. Rewrite `hx` using `[(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i]`. Establish `hmem2 : ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i).base x ∈ (((principalizationOfEmbedding k Y pY D A).center i).support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))` using `mem_support_of_mem_support_comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) ((principalizationOfEmbedding k Y pY D A).center i) x hx`.

Conclude with `hcl'.1 hmem2`.
-/
private theorem forall_not_avoidsCenters_of_mem_boundary_support (D : EmbeddingDatum k Y pY)
    (A : PrincipalizationAlgorithm.{u}) :
    ∀ (i : ℕ), i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ E : ((principalizationOfEmbedding k Y pY D A).schemeAt i).IdealSheafData,
        E ∈ (principalizationOfEmbedding k Y pY D A).boundary i →
        ∀ x : ↥((D.toEmbeddedBlowupSequence A).schemeAt i),
          x ∈ (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) →
          ¬ (D.toEmbeddedBlowupSequence A).AvoidsCenters i x := by
  intro i
  induction i with
  | zero =>
      intro _ E hE x hx hcl
      rw [(principalizationOfEmbedding k Y pY D A).boundary_zero] at hE
      simp at hE
  | succ i ih =>
      intro hi E hE x hx hcl
      have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi
      rw [(principalizationOfEmbedding k Y pY D A).boundary_succ_eq_map_strictTransform_append i hilt, List.mem_append] at hE
      have hcl' := ((D.toEmbeddedBlowupSequence A).avoidsCenters_succ_iff i x).mp hcl
      rcases hE with hE | hE
      · obtain ⟨E', hE', rfl⟩ := List.mem_map.mp hE
        have hmem : x ∈ ((E'.comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i)).support :
            Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt (i + 1))) :=
          AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
            (FunctorialResolution.EmbeddedResolution.comap_le_strictTransform
              ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i)
              ((principalizationOfEmbedding k Y pY D A).center i) E') hx
        have hmem2 : ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i).base x ∈
            (E'.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) :=
          mem_support_of_mem_support_comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) E' x hmem
        exact ih (Nat.le_of_succ_le hi) E' hE' _ hmem2 hcl'.2
      · rw [List.mem_singleton] at hE
        subst hE
        rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hx
        have hmem2 : ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i).base x ∈
            (((principalizationOfEmbedding k Y pY D A).center i).support :
              Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) :=
          mem_support_of_mem_support_comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i)
            ((principalizationOfEmbedding k Y pY D A).center i) x hx
        exact hcl'.1 hmem2

/- English proof (translation)
The claim follows from `forall_not_avoidsCenters_of_mem_boundary_support D A i hi E hE x hx`.
-/
theorem not_avoidsCenters_of_mem_boundary_support (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (i : ℕ) (hi : i ≤ (D.toEmbeddedBlowupSequence A).length)
    (E : ((principalizationOfEmbedding k Y pY D A).schemeAt i).IdealSheafData)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D A).boundary i)
    (x : ↥((D.toEmbeddedBlowupSequence A).schemeAt i))
    (hx : x ∈ (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))) :
    ¬ (D.toEmbeddedBlowupSequence A).AvoidsCenters i x :=
  forall_not_avoidsCenters_of_mem_boundary_support D A i hi E hE x hx

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
private theorem ker_congr {A B : Scheme.{u}} {f g : A ⟶ B}
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.QuasiCompact g] (h : f = g) :
    AlgebraicGeometry.Scheme.Hom.ker f = AlgebraicGeometry.Scheme.Hom.ker g := by
  subst h
  rfl

/- English proof (translation)
Establish `h2 : (j ≫ e.inv) ≫ e.hom = j` using `by simp`. Establish `: AlgebraicGeometry.QuasiCompact ((j ≫ e.inv) ≫ e.hom)`. Rewrite using `[h2]`. Use `infer_instance`. Establish `h3 : AlgebraicGeometry.Scheme.Hom.ker j = AlgebraicGeometry.Scheme.Hom.ker ((j ≫ e.inv) ≫ e.hom)` using `ker_congr h2.symm`.

Rewrite using `[h3]`. Conclude with `FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (j ≫ e.inv) e.hom`.
-/
private theorem ker_comap_iso_hom_eq_ker_comp_inv {W B X : Scheme.{u}} (j : W ⟶ B) (e : X ≅ B)
    [AlgebraicGeometry.QuasiCompact j] [AlgebraicGeometry.QuasiCompact (j ≫ e.inv)] :
    (AlgebraicGeometry.Scheme.Hom.ker j).comap e.hom
      = AlgebraicGeometry.Scheme.Hom.ker (j ≫ e.inv) := by
  have h2 : (j ≫ e.inv) ≫ e.hom = j := by simp
  have : AlgebraicGeometry.QuasiCompact ((j ≫ e.inv) ≫ e.hom) := by
    rw [h2]
    infer_instance
  have h3 : AlgebraicGeometry.Scheme.Hom.ker j
      = AlgebraicGeometry.Scheme.Hom.ker ((j ≫ e.inv) ≫ e.hom) := ker_congr h2.symm
  rw [h3]
  exact FunctorialResolution.Blowup.comap_ker_comp_of_isOpenImmersion (j ≫ e.inv) e.hom

/- English proof (translation)
Establish `hle : (AlgebraicGeometry.Scheme.Hom.ker f).radical ≤ AlgebraicGeometry.Scheme.Hom.ker f` using `by show (AlgebraicGeometry.Scheme.Hom.ker f).radical ≤ AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals (fun U : Z.affineOpens => RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)))`. Rewrite using `[AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff]`. Introduce `U`. Establish `h1 : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U ≤ RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1))` using `AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le _ U`. Establish `hrad : (RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1))).IsRadical`.

Rewrite using `[RingHom.ker_eq_comap_bot]`. Conclude with `Ideal.isRadical_bot.comap _`. Conclude with `le_trans (Ideal.radical_mono h1) hrad`. Conclude with `le_antisymm hle (AlgebraicGeometry.Scheme.IdealSheafData.le_radical _)`.
-/
private theorem radical_ker_eq_of_isReduced {W Z : Scheme.{u}} [AlgebraicGeometry.IsReduced W]
    (f : W ⟶ Z) :
    (AlgebraicGeometry.Scheme.Hom.ker f).radical = AlgebraicGeometry.Scheme.Hom.ker f := by
  have hle : (AlgebraicGeometry.Scheme.Hom.ker f).radical
      ≤ AlgebraicGeometry.Scheme.Hom.ker f := by
    show (AlgebraicGeometry.Scheme.Hom.ker f).radical ≤
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdeals
        (fun U : Z.affineOpens =>
          RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)))
    rw [AlgebraicGeometry.Scheme.IdealSheafData.le_ofIdeals_iff]
    intro U
    have h1 : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U ≤
        RingHom.ker (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1)) :=
      AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le _ U
    have hrad : (RingHom.ker
        (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f U.1))).IsRadical := by
      rw [RingHom.ker_eq_comap_bot]
      exact Ideal.isRadical_bot.comap _
    exact le_trans (Ideal.radical_mono h1) hrad
  exact le_antisymm hle (AlgebraicGeometry.Scheme.IdealSheafData.le_radical _)

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `radical_ker_eq_of_isReduced f`.
-/
private theorem radical_eq_of_eq_ker {Z W : Scheme.{u}} [AlgebraicGeometry.IsReduced W]
    (I : Z.IdealSheafData) (f : W ⟶ Z)
    (h : I = AlgebraicGeometry.Scheme.Hom.ker f) : I.radical = I := by
  subst h
  exact radical_ker_eq_of_isReduced f

/- English proof (translation)
Establish `hB : (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0 = AlgebraicGeometry.Scheme.Hom.ker (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv)` using `EmbeddedBlowupSequence.strictTransformIdeal_zero (D.toEmbeddedBlowupSequence A)`. Establish `hA : (principalizationOfEmbedding k Y pY D A).ideal 0 = AlgebraicGeometry.Scheme.Hom.ker (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv)`. Rewrite using `[IdealBlowupSequence.ideal_zero, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero]`. Conclude with `ker_comap_iso_hom_eq_ker_comp_inv D.emb (principalizationOfEmbedding k Y pY D A).isoZero`. Establish `hsupp : (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ : TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0)) = ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).support` using `TopologicalSpace.Closeds.ext (Scheme.IdealSheafData.range_subschemeι ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0))`.

Establish `hrad : ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).radical = (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0` using `radical_eq_of_eq_ker ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0) (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) hB`. Establish `key : Scheme.IdealSheafData.vanishingIdeal (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ : TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0)) = (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0`. Rewrite using `[hsupp, Scheme.IdealSheafData.vanishingIdeal_support]`. Conclude with `hrad`. Conclude with `hA.trans (hB.symm.trans key.symm)`.
-/
theorem principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal [AlgebraicGeometry.IsReduced Y]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (hcl : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base)) :
    (principalizationOfEmbedding k Y pY D A).ideal 0 =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0)) := by
  have hB : (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) :=
    EmbeddedBlowupSequence.strictTransformIdeal_zero (D.toEmbeddedBlowupSequence A)
  have hA : (principalizationOfEmbedding k Y pY D A).ideal 0
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) := by
    rw [IdealBlowupSequence.ideal_zero, FunctorialResolution.EmbeddedResolution.SequenceOfBlowups.projectionToBase_zero]
    exact ker_comap_iso_hom_eq_ker_comp_inv D.emb (principalizationOfEmbedding k Y pY D A).isoZero
  have hsupp : (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ :
      TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0))
      = ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).support :=
    TopologicalSpace.Closeds.ext
      (Scheme.IdealSheafData.range_subschemeι ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0))
  have hrad : ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).radical = (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0 :=
    radical_eq_of_eq_ker ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0)
      (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) hB
  have key : Scheme.IdealSheafData.vanishingIdeal
      (⟨Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base, hcl⟩ :
        TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt 0))
      = (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0 := by
    rw [hsupp, Scheme.IdealSheafData.vanishingIdeal_support]
    exact hrad
  exact hA.trans (hB.symm.trans key.symm)

def AgreesWithComponentsOrderOne (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (i : ℕ) : Prop :=
  ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
  ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
  ∀ hC : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C),
    AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal i)
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C, hC⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i)))
        (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) ∧
      orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
        (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) = 1

/- English proof (translation)
Establish `hrange : Set.range ⇑(X.fromSpecStalk x).base = {z : ↥X | z ⤳ x}`. Rewrite using `[AlgebraicGeometry.Scheme.range_fromSpecStalk]`. Establish `hy' : y ∈ Set.range ⇑(X.fromSpecStalk x).base`. Rewrite using `[hrange]`. Conclude with `hy`.

Establish `hx' : x ∈ Set.range ⇑(X.fromSpecStalk x).base`. Rewrite using `[hrange]`. Conclude with `specializes_refl x`. Take `⟨a, ha⟩` from `hy'`. Take `⟨b, hb⟩` from `hx'`.

Establish `hab : a = b`. Set `: Field ↑(X.presheaf.stalk x)` to `hfield.toField`. Establish `key : ∀ p q : PrimeSpectrum ↑(X.presheaf.stalk x), p = q` using `fun p q => Subsingleton.elim p q`. Conclude with `key a b`. Conclude with `ha.symm.trans ((congrArg (fun t => (X.fromSpecStalk x).base t) hab).trans hb)`.
-/
private theorem eq_of_specializes_of_isField_stalk {X : Scheme.{u}} (x : ↥X)
    (hfield : IsField ↑(X.presheaf.stalk x)) (y : ↥X) (hy : y ⤳ x) : y = x := by
  have hrange : Set.range ⇑(X.fromSpecStalk x).base = {z : ↥X | z ⤳ x} := by
    rw [AlgebraicGeometry.Scheme.range_fromSpecStalk]
  have hy' : y ∈ Set.range ⇑(X.fromSpecStalk x).base := by
    rw [hrange]; exact hy
  have hx' : x ∈ Set.range ⇑(X.fromSpecStalk x).base := by
    rw [hrange]; exact specializes_refl x
  obtain ⟨a, ha⟩ := hy'
  obtain ⟨b, hb⟩ := hx'
  have hab : a = b := by
    let : Field ↑(X.presheaf.stalk x) := hfield.toField
    have key : ∀ p q : PrimeSpectrum ↑(X.presheaf.stalk x), p = q := fun p q =>
      Subsingleton.elim p q
    exact key a b
  exact ha.symm.trans ((congrArg (fun t => (X.fromSpecStalk x).base t) hab).trans hb)

/- English proof (translation)
Use `⟨isIrreducible_singleton.closure, ?_⟩` and prove the remaining obligations. Introduce `S hS hsub`. Take `⟨y, hy⟩` from `QuasiSober.sober hS.closure isClosed_closure`. Establish `hy2 : closure ({y} : Set ↥X) = closure S` using `hy`. Establish `hxS : x ∈ closure S` using `subset_closure (hsub (subset_closure rfl))`.

Establish `hyx : y = x`. Use `h y (specializes_iff_mem_closure.mpr ?_)` and prove the remaining obligations. Rewrite using `[hy2]`. Conclude with `hxS`. Rewrite `hy2` using `[hyx]`.

Rewrite using `[hy2]`. Conclude with `subset_closure`.
-/
private theorem closure_singleton_mem_irreducibleComponents {X : Scheme.{u}} (x : ↥X)
    (h : ∀ y : ↥X, y ⤳ x → y = x) :
    closure ({x} : Set ↥X) ∈ irreducibleComponents ↥X := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro S hS hsub
  obtain ⟨y, hy⟩ := QuasiSober.sober hS.closure isClosed_closure
  have hy2 : closure ({y} : Set ↥X) = closure S := hy
  have hxS : x ∈ closure S := subset_closure (hsub (subset_closure rfl))
  have hyx : y = x := by
    refine h y (specializes_iff_mem_closure.mpr ?_)
    rw [hy2]
    exact hxS
  rw [hyx] at hy2
  rw [hy2]
  exact subset_closure

/- English proof (translation)
Establish `hcont : Continuous ⇑e.inv.base` using `e.inv.base.hom.continuous`. Establish `h1 : e.inv.base w ⤳ e.inv.base (e.hom.base x)` using `hw.map hcont`. Establish `h2 : e.inv.base (e.hom.base x) = x`. Rewrite using `[← comp_base_apply e.hom e.inv x, e.hom_inv_id]`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[h2]`. Establish `h3` using `h _ h1`. Establish `h4 : e.hom.base (e.inv.base w) = w`. Rewrite using `[← comp_base_apply e.inv e.hom w, e.inv_hom_id]`. Simplify using the standard rewrite rules.

Rewrite using `[← h4, h3]`.
-/
private theorem eq_of_specializes_iso_hom {X B : Scheme.{u}} (e : X ≅ B) (x : ↥X)
    (h : ∀ y : ↥X, y ⤳ x → y = x) (w : ↥B) (hw : w ⤳ e.hom.base x) :
    w = e.hom.base x := by
  have hcont : Continuous ⇑e.inv.base := e.inv.base.hom.continuous
  have h1 : e.inv.base w ⤳ e.inv.base (e.hom.base x) := hw.map hcont
  have h2 : e.inv.base (e.hom.base x) = x := by
    rw [← comp_base_apply e.hom e.inv x, e.hom_inv_id]
    simp
  rw [h2] at h1
  have h3 := h _ h1
  have h4 : e.hom.base (e.inv.base w) = w := by
    rw [← comp_base_apply e.inv e.hom w, e.inv_hom_id]
    simp
  rw [← h4, h3]

/- English proof (translation)
Introduce `hfield`. Establish `hB : (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0 = AlgebraicGeometry.Scheme.Hom.ker (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv)` using `EmbeddedBlowupSequence.strictTransformIdeal_zero (D.toEmbeddedBlowupSequence A)`. Establish `hcomap : (AlgebraicGeometry.Scheme.Hom.ker D.emb).comap (principalizationOfEmbedding k Y pY D A).isoZero.hom = AlgebraicGeometry.Scheme.Hom.ker (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv)` using `ker_comap_iso_hom_eq_ker_comp_inv D.emb (principalizationOfEmbedding k Y pY D A).isoZero`. Establish `hxsupp : ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ ∈ ((((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).support) : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0))`. Rewrite using `[← Scheme.IdealSheafData.range_subschemeι ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0)]`.

Conclude with `⟨ξ, rfl⟩`. Establish `hz : (principalizationOfEmbedding k Y pY D A).isoZero.hom.base (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ) ∈ ((AlgebraicGeometry.Scheme.Hom.ker D.emb).support : Set ↥D.ambient)`. Use `mem_support_of_mem_support_comap (principalizationOfEmbedding k Y pY D A).isoZero.hom (AlgebraicGeometry.Scheme.Hom.ker D.emb) _ ?_` and prove the remaining obligations. Rewrite using `[hcomap, ← hB]`. Conclude with `hxsupp`.

Establish `hnogen : ∀ y, y ⤳ ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ → y = ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ` using `fun y hy => eq_of_specializes_of_isField_stalk _ hfield y hy`. Establish `hcomp` using `closure_singleton_mem_irreducibleComponents ((principalizationOfEmbedding k Y pY D A).isoZero.hom.base (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ)) (eq_of_specializes_iso_hom (principalizationOfEmbedding k Y pY D A).isoZero (((D.toEmbeddedBlowupSequence A).strict …`. Conclude with `D.nonzeroOnComponents_ker _ hcomp (closure_minimal (Set.singleton_subset_iff.mpr hz) (AlgebraicGeometry.Scheme.Hom.ker D.emb).support.2)`.
-/
private theorem not_isField_stalk_strictTransformι_zero {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform 0)) :
    ¬ IsField ↑(((D.toEmbeddedBlowupSequence A).schemeAt 0).presheaf.stalk
      (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ)) := by
  intro hfield
  have hB : (D.toEmbeddedBlowupSequence A).strictTransformIdeal 0
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) :=
    EmbeddedBlowupSequence.strictTransformIdeal_zero (D.toEmbeddedBlowupSequence A)
  have hcomap : (AlgebraicGeometry.Scheme.Hom.ker D.emb).comap
        (principalizationOfEmbedding k Y pY D A).isoZero.hom
      = AlgebraicGeometry.Scheme.Hom.ker
          (D.emb ≫ (principalizationOfEmbedding k Y pY D A).isoZero.inv) :=
    ker_comap_iso_hom_eq_ker_comp_inv D.emb (principalizationOfEmbedding k Y pY D A).isoZero
  have hxsupp : ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ ∈
      ((((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0).support) : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι ((D.toEmbeddedBlowupSequence A).strictTransformIdeal 0)]
    exact ⟨ξ, rfl⟩
  have hz : (principalizationOfEmbedding k Y pY D A).isoZero.hom.base
        (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ)
      ∈ ((AlgebraicGeometry.Scheme.Hom.ker D.emb).support : Set ↥D.ambient) := by
    refine mem_support_of_mem_support_comap (principalizationOfEmbedding k Y pY D A).isoZero.hom
      (AlgebraicGeometry.Scheme.Hom.ker D.emb) _ ?_
    rw [hcomap, ← hB]
    exact hxsupp
  have hnogen : ∀ y, y ⤳ ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ
      → y = ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ :=
    fun y hy => eq_of_specializes_of_isField_stalk _ hfield y hy
  have hcomp := closure_singleton_mem_irreducibleComponents
    ((principalizationOfEmbedding k Y pY D A).isoZero.hom.base (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ))
    (eq_of_specializes_iso_hom (principalizationOfEmbedding k Y pY D A).isoZero
      (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ) hnogen)
  exact D.nonzeroOnComponents_ker _ hcomp
    (closure_minimal (Set.singleton_subset_iff.mpr hz)
      (AlgebraicGeometry.Scheme.Hom.ker D.emb).support.2)

/- English proof (translation)
Introduce `C hC ξ hξ hCcl`. Establish `: AlgebraicGeometry.IsLocallyNoetherian ((principalizationOfEmbedding k Y pY D A).schemeAt 0)` using `((D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt 0 (Nat.zero_le _)).toIsLocallyNoetherian`. Establish `: TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform 0)` using `(D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0 (Nat.zero_le _)`. Establish `hemb` using `(D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι 0`. Establish `hclr : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base)` using `hemb.isClosed_range`.

Establish `hid0` using `principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hclr`. Use `set Bad : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0) := ⋃ C'' ∈ (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}), ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C'' with hBaddef`. Establish `hfin : (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}).Finite` using `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset`. Establish `hBadcl : IsClosed Bad`. Rewrite using `[hBaddef]`.

Conclude with `hfin.isClosed_biUnion (fun C'' hC'' => hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents C'' hC''.1))`. Establish `hxU : ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ ∈ Badᶜ`. Introduce `hmem`. Rewrite `hmem` using `[hBaddef]`. Take `⟨C'', hC''D, hxim⟩` from `Set.mem_iUnion₂.mp hmem`.

Take `⟨z, hzC'', hz⟩` from `hxim`. Establish `hzξ : z = ξ` using `hemb.injective hz`. Substitute `hzξ` using the available equality. Establish `hsub : C ⊆ C''`. Rewrite using `[← hξ.def]`.

Conclude with `closure_minimal (Set.singleton_subset_iff.mpr hzC'') (isClosed_of_mem_irreducibleComponents C'' hC''D.1)`. Conclude with `hC''D.2 (subset_antisymm (hC.2 hC''D.1.1 hsub) hsub)`. Establish `hinter : (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) ∩ Badᶜ = (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) ∩ Badᶜ`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨z, rfl⟩, hy⟩`. Use `⟨?_, hy⟩` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ C`. Conclude with `⟨z, hz, rfl⟩`. Use `absurd ?_ hy` and prove the remaining obligations.

Rewrite using `[hBaddef]`. Use `Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩ ⟨z, mem_irreducibleComponent, rfl⟩` and prove the remaining obligations. Introduce `h`. Conclude with `hz (h ▸ mem_irreducibleComponent)`. Introduce and unpack `⟨⟨z, hzC, rfl⟩, hy⟩`.

Conclude with `⟨⟨z, rfl⟩, hy⟩`. Establish `hgen : IsGenericPoint (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ) (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C)` using `FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hξ`. Establish `hmax : Maximal (fun s => IsIrreducible s ∧ s ⊆ (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base)) (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C)`. Prove the components needed by the constructor for the conclusion. Conclude with `⟨hC.1.image _ hemb.continuous.continuousOn, Set.image_subset_range _ _⟩`.

Introduce and unpack `b ⟨hbirr, hbr⟩ hsub y hy`. Establish `hpre : IsIrreducible (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ⁻¹' b)` using `FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding hemb.isEmbedding hbirr hbr`. Establish `hCsub : C ⊆ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ⁻¹' b` using `fun z hz => hsub ⟨z, hz, rfl⟩`. Establish `hle` using `hC.2 hpre hCsub`. Take `⟨z, rfl⟩` from `hbr hy`.

Conclude with `⟨z, hle hy, rfl⟩`. Establish `hfield` using `not_isField_stalk_strictTransformι_zero D A ξ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hid0]`. Conclude with `agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter`.

Rewrite using `[hid0]`. Conclude with `FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one_of_not_isField _ _ _ hmax hgen hfield`.
-/
private theorem agreesWithComponentsOrderOne_zero {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    AgreesWithComponentsOrderOne D A 0 := by
  classical
  intro C hC ξ hξ hCcl
  have : AlgebraicGeometry.IsLocallyNoetherian ((principalizationOfEmbedding k Y pY D A).schemeAt 0) :=
    ((D.toEmbeddedBlowupSequence A).isNoetherian_schemeAt 0 (Nat.zero_le _)).toIsLocallyNoetherian
  have : TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) :=
    (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) 0
      (Nat.zero_le _)
  have hemb := (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι 0
  have hclr : IsClosed (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) := hemb.isClosed_range
  have hid0 := principalizationOfEmbedding_ideal_zero_eq_vanishingIdeal D A hclr
  set Bad : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt 0) :=
    ⋃ C'' ∈ (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}),
      ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C'' with hBaddef
  have hfin : (irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform 0) \ {C}).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
  have hBadcl : IsClosed Bad := by
    rw [hBaddef]
    exact hfin.isClosed_biUnion (fun C'' hC'' =>
      hemb.isClosedMap _ (isClosed_of_mem_irreducibleComponents C'' hC''.1))
  have hxU : ((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ ∈ Badᶜ := by
    intro hmem
    rw [hBaddef] at hmem
    obtain ⟨C'', hC''D, hxim⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨z, hzC'', hz⟩ := hxim
    have hzξ : z = ξ := hemb.injective hz
    subst hzξ
    have hsub : C ⊆ C'' := by
      rw [← hξ.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr hzC'')
        (isClosed_of_mem_irreducibleComponents C'' hC''D.1)
    exact hC''D.2 (subset_antisymm (hC.2 hC''D.1.1 hsub) hsub)
  have hinter : (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base) ∩ Badᶜ
      = (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) ∩ Badᶜ := by
    ext y
    constructor
    · rintro ⟨⟨z, rfl⟩, hy⟩
      refine ⟨?_, hy⟩
      by_cases hz : z ∈ C
      · exact ⟨z, hz, rfl⟩
      · refine absurd ?_ hy
        rw [hBaddef]
        refine Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents z, ?_⟩
          ⟨z, mem_irreducibleComponent, rfl⟩
        intro h
        exact hz (h ▸ mem_irreducibleComponent)
    · rintro ⟨⟨z, hzC, rfl⟩, hy⟩
      exact ⟨⟨z, rfl⟩, hy⟩
  have hgen : IsGenericPoint (((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ξ)
      (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) :=
    FunctorialResolution.EmbeddedResolution.isGenericPoint_image_of_isClosedEmbedding hemb hξ
  have hmax : Maximal (fun s => IsIrreducible s ∧
      s ⊆ (Set.range ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base))
      (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base '' C) := by
    constructor
    · exact ⟨hC.1.image _ hemb.continuous.continuousOn, Set.image_subset_range _ _⟩
    · rintro b ⟨hbirr, hbr⟩ hsub y hy
      have hpre : IsIrreducible (⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ⁻¹' b) :=
        FunctorialResolution.EmbeddedResolution.isIrreducible_preimage_of_isEmbedding hemb.isEmbedding hbirr hbr
      have hCsub : C ⊆ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι 0).base ⁻¹' b :=
        fun z hz => hsub ⟨z, hz, rfl⟩
      have hle := hC.2 hpre hCsub
      obtain ⟨z, rfl⟩ := hbr hy
      exact ⟨z, hle hy, rfl⟩
  have hfield := not_isField_stalk_strictTransformι_zero D A ξ
  refine ⟨?_, ?_⟩
  · rw [hid0]
    exact agreeNear_vanishingIdeal_of_inter_eq _ _ ⟨Badᶜ, hBadcl.isOpen_compl⟩ _ hxU hinter
  · rw [hid0]
    exact FunctorialResolution.EmbeddedResolution.orderAt_vanishingIdeal_eq_one_of_not_isField _ _ _ hmax hgen hfield

/- English proof (translation)
Introduce `C hC η hηgen hCcl`. Establish `hN` using `isNoetherian_schemeAt_toEmbeddedBlowupSequence D A`. Establish `hi' : i < (D.toEmbeddedBlowupSequence A).length` using `Nat.lt_of_succ_le hi`. Establish `hilt : i < (principalizationOfEmbedding k Y pY D A).length` using `hi'`. Take `⟨C', hC'm, hη', hfr⟩` from `(D.toEmbeddedBlowupSequence A).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC η hηgen`.

Establish `hC'cl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C')` using `((D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i).isClosedMap _ (isClosed_of_mem_irreducibleComponents C' hC'm)`. Take `⟨hag, hord⟩` from `ih C' hC'm _ hη' hC'cl`. Take `⟨V, hxV, hVeq⟩` from `(agreeNear_iff _ _ _).mp hag`. Take `⟨V', hV'⟩ : ∃ V' : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens, V' = V` from `⟨V, rfl⟩`. Establish `hkey : ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η) = ((D.toEmbeddedBlowupSequence A).blowdown i).base (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η)`.

Establish `h : ((D.toEmbeddedBlowupSequence A).strictTransformMap i ≫ (D.toEmbeddedBlowupSequence A).strictTransformι i).base η = ((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1) ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base η`. Rewrite using `[(D.toEmbeddedBlowupSequence A).strictTransformMap_comp_strictTransformι i]`. Simplify using `using h`. Establish `hnot` using `(D.toEmbeddedBlowupSequence A).notMem_ambientCenter_support_of_isGenericPoint i C' hC'm hfr _ hη'`. Establish `hxV' : ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η) ∈ V'`.

Rewrite using `[hV']`. Conclude with `hxV`. Establish `hV'eq : ((principalizationOfEmbedding k Y pY D A).ideal i).comap V'.ι = (Scheme.IdealSheafData.vanishingIdeal (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ : TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap V'.ι`. Rewrite using `[hV']`. Conclude with `hVeq`.

Take `⟨U, hUdef⟩ : ∃ U : ((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)).Opens, U = (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i)` from `⟨_, rfl⟩`. Establish `hUsub : (U : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1))) ⊆ ⇑((D.toEmbeddedBlowupSequence A).blowdown i).base ⁻¹' (((D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens) : Set ↥((D.toEmbeddedBlowupSequence A).sc …`. Rewrite using `[hUdef]`. Introduce `y hy`. Conclude with `hy.2`.

Establish `hmemU : ∀ y : ↥U, ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y) ∉ (((D.toEmbeddedBlowupSequence A).ambientCenter i).support : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i))`. Introduce `y`. Conclude with `hUsub y.2`. Establish `hxU : ((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η ∈ U`. Rewrite using `[hUdef]`.

Establish `h1 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η) ∈ V'`. Rewrite using `[← hkey]`. Conclude with `hxV'`. Establish `h2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η) ∈ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i`. Rewrite using `[← hkey]`.

Conclude with `hnot`. Conclude with `⟨h1, h2⟩`. Establish `: AlgebraicGeometry.IsOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)` using `EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub`. Establish `hexc : ((principalizationOfEmbedding k Y pY D A).exceptionalIdeal i).comap U.ι = ⊤`. Use `FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint _ _ ?_` and prove the remaining obligations.

Rewrite using `[Set.disjoint_left]`. Introduce `y hy hmem`. Rewrite `hmem` using `[(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i]`. Conclude with `absurd (mem_support_of_mem_support_comap ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) _ y hmem) (hUsub hy)`. Establish `hJ : ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι = ((principalizationOfEmbedding k Y pY D A).ideal i).comap (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)` using `comap_eq_comap_comp_of_mul_eq _ U _ _ _ ((principalizationOfEmbedding k Y pY D A).ideal_succ i hilt) hexc`.

Establish `hle : U ≤ (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj V'`. Rewrite using `[hUdef]`. Introduce `y hy`. Conclude with `hy.1`. Establish `hcomapφ : ((principalizationOfEmbedding k Y pY D A).ideal i).comap (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) = (Scheme.IdealSheafData.vanishingIdeal (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ : TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupS …` using `AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_comp_eq_of_comap_ι_eq ((D.toEmbeddedBlowupSequence A).blowdown i) V' U hle _ _ hV'eq`.

Establish `hLHS : (Scheme.IdealSheafData.vanishingIdeal (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ : TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) = Scheme.IdealSheafData.vanishi …`. Use `FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) _ _ ?_` and prove the remaining obligations. Use extensionality with `y`. Establish `hcb` using `comp_base_apply U.ι ((D.toEmbeddedBlowupSequence A).blowdown i) y`. Establish `hiff` using `EmbeddedBlowupSequence.mem_image_strictTransformι_iff_of_notMem_ambientCenter (D.toEmbeddedBlowupSequence A) hN i hi' C η hηgen C' hη' (U.ι.base y) (hmemU y)`.

Prove the components needed by the constructor for the conclusion. Introduce `hy`. Establish `hy1 : U.ι.base y ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C` using `hy`. Establish `hy2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y) ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C'` using `hiff.mpr hy1`. Establish `hy3 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base y ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C'`.

Rewrite using `[hcb]`. Conclude with `hy2`. Conclude with `hy3`. Introduce `hy`. Establish `hy1 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base y ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C'` using `hy`.

Establish `hy2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y) ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C'`. Rewrite using `[← hcb]`. Conclude with `hy1`. Conclude with `hiff.mp hy2`. Use `⟨(agreeNear_iff _ _ _).mpr ⟨U, hxU, ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `hJ.trans (hcomapφ.trans (hLHS.trans (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.ι (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ : TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))).s …`. Establish `e1` using `FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion U.ι ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)) (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)`. Establish `e2` using `FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) ((principalizationOfEmbedding k Y pY D A).ideal i) (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)`. Establish `hφp : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U) = ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η)`. Rewrite using `[comp_base_apply U.ι ((D.toEmbeddedBlowupSequence A).blowdown i) (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)]`.

Conclude with `hkey.symm`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem agreesWithComponentsOrderOne_succ {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u})
    (i : ℕ) (hi : i + 1 ≤ (D.toEmbeddedBlowupSequence A).length) (ih : AgreesWithComponentsOrderOne D A i) :
    AgreesWithComponentsOrderOne D A (i + 1) := by
  classical
  intro C hC η hηgen hCcl
  have hN := isNoetherian_schemeAt_toEmbeddedBlowupSequence D A
  have hi' : i < (D.toEmbeddedBlowupSequence A).length := Nat.lt_of_succ_le hi
  have hilt : i < (principalizationOfEmbedding k Y pY D A).length := hi'
  obtain ⟨C', hC'm, hη', hfr⟩ :=
    (D.toEmbeddedBlowupSequence A).exists_irreducibleComponent_isGenericPoint_strictTransformMap hN i hi' C hC η hηgen
  have hC'cl : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C') :=
    ((D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i).isClosedMap _
      (isClosed_of_mem_irreducibleComponents C' hC'm)
  obtain ⟨hag, hord⟩ := ih C' hC'm _ hη' hC'cl
  obtain ⟨V, hxV, hVeq⟩ := (agreeNear_iff _ _ _).mp hag
  obtain ⟨V', hV'⟩ : ∃ V' : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens, V' = V := ⟨V, rfl⟩
  have hkey : ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η)
      = ((D.toEmbeddedBlowupSequence A).blowdown i).base (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η) := by
    have h : ((D.toEmbeddedBlowupSequence A).strictTransformMap i ≫ (D.toEmbeddedBlowupSequence A).strictTransformι i).base η
        = ((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1) ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base η := by
      rw [(D.toEmbeddedBlowupSequence A).strictTransformMap_comp_strictTransformι i]
    simpa using h
  have hnot :=
    (D.toEmbeddedBlowupSequence A).notMem_ambientCenter_support_of_isGenericPoint i C' hC'm hfr _ hη'
  have hxV' : ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η)
      ∈ V' := by
    rw [hV']; exact hxV
  have hV'eq : ((principalizationOfEmbedding k Y pY D A).ideal i).comap V'.ι
      = (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap V'.ι := by
    rw [hV']; exact hVeq
  obtain ⟨U, hUdef⟩ : ∃ U : ((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)).Opens,
      U = (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj
        (V' ⊓ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i) := ⟨_, rfl⟩
  have hUsub : (U : Set ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1))) ⊆
      ⇑((D.toEmbeddedBlowupSequence A).blowdown i).base ⁻¹'
        (((D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i : ((D.toEmbeddedBlowupSequence A).schemeAt i).Opens) :
          Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
    rw [hUdef]
    intro y hy
    exact hy.2
  have hmemU : ∀ y : ↥U, ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y) ∉
      (((D.toEmbeddedBlowupSequence A).ambientCenter i).support :
        Set ↥((D.toEmbeddedBlowupSequence A).schemeAt i)) := by
    intro y
    exact hUsub y.2
  have hxU : ((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η ∈ U := by
    rw [hUdef]
    have h1 : ((D.toEmbeddedBlowupSequence A).blowdown i).base
        (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η) ∈ V' := by
      rw [← hkey]; exact hxV'
    have h2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base
        (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η)
        ∈ (D.toEmbeddedBlowupSequence A).ambientCenterSupportCompl i := by
      rw [← hkey]; exact hnot
    exact ⟨h1, h2⟩
  have : AlgebraicGeometry.IsOpenImmersion (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
    EmbeddedBlowupSequence.isOpenImmersion_ι_comp_blowdown (D.toEmbeddedBlowupSequence A) i hi' U hUsub
  have hexc : ((principalizationOfEmbedding k Y pY D A).exceptionalIdeal i).comap U.ι = ⊤ := by
    refine FunctorialResolution.EmbeddedResolution.comap_ι_eq_top_of_disjoint _ _ ?_
    rw [Set.disjoint_left]
    intro y hy hmem
    rw [(principalizationOfEmbedding k Y pY D A).exceptionalIdeal_eq i] at hmem
    exact absurd (mem_support_of_mem_support_comap
      ((principalizationOfEmbedding k Y pY D A).transitionMapSucc i) _ y hmem) (hUsub hy)
  have hJ : ((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι
      = ((principalizationOfEmbedding k Y pY D A).ideal i).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
    comap_eq_comap_comp_of_mul_eq _ U _ _ _
      ((principalizationOfEmbedding k Y pY D A).ideal_succ i hilt) hexc
  have hle : U ≤ (TopologicalSpace.Opens.map ((D.toEmbeddedBlowupSequence A).blowdown i).base).obj V' := by
    rw [hUdef]
    intro y hy
    exact hy.1
  have hcomapφ : ((principalizationOfEmbedding k Y pY D A).ideal i).comap
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
      = (Scheme.IdealSheafData.vanishingIdeal
          (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
            TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
          (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) :=
    AlgebraicGeometry.Scheme.IdealSheafData.comap_ι_comp_eq_of_comap_ι_eq
      ((D.toEmbeddedBlowupSequence A).blowdown i) V' U hle _ _ hV'eq
  have hLHS : (Scheme.IdealSheafData.vanishingIdeal
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C', hC'cl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt i))).comap
        (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i)
      = Scheme.IdealSheafData.vanishingIdeal
          (FunctorialResolution.EmbeddedResolution.closedPreimage U.ι
            (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
              TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))) := by
    refine FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion_of_coe_eq
      (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) _ _ ?_
    ext y
    have hcb := comp_base_apply U.ι ((D.toEmbeddedBlowupSequence A).blowdown i) y
    have hiff := EmbeddedBlowupSequence.mem_image_strictTransformι_iff_of_notMem_ambientCenter
      (D.toEmbeddedBlowupSequence A) hN i hi' C η hηgen C' hη' (U.ι.base y) (hmemU y)
    constructor
    · intro hy
      have hy1 : U.ι.base y ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C := hy
      have hy2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y)
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hiff.mpr hy1
      have hy3 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base y
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
        rw [hcb]; exact hy2
      exact hy3
    · intro hy
      have hy1 : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base y
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := hy
      have hy2 : ((D.toEmbeddedBlowupSequence A).blowdown i).base (U.ι.base y)
          ∈ ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C' := by
        rw [← hcb]; exact hy1
      exact hiff.mp hy2
  refine ⟨(agreeNear_iff _ _ _).mpr ⟨U, hxU, ?_⟩, ?_⟩
  · exact hJ.trans (hcomapφ.trans (hLHS.trans
      (FunctorialResolution.EmbeddedResolution.comap_vanishingIdeal_of_isOpenImmersion U.ι
        (⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base '' C, hCcl⟩ :
          TopologicalSpace.Closeds ↥((D.toEmbeddedBlowupSequence A).schemeAt (i + 1)))).symm))
  · have e1 := FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion U.ι
      ((principalizationOfEmbedding k Y pY D A).ideal (i + 1))
      (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)
    have e2 := FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion
      (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i) ((principalizationOfEmbedding k Y pY D A).ideal i)
      (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)
    have hφp : (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base
        (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)
        = ((D.toEmbeddedBlowupSequence A).strictTransformι i).base (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η) := by
      rw [comp_base_apply U.ι ((D.toEmbeddedBlowupSequence A).blowdown i)
        (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)]
      exact hkey.symm
    calc FunctorialResolution.EmbeddedResolution.orderAt ((principalizationOfEmbedding k Y pY D A).ideal (i + 1))
          (((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η)
        = FunctorialResolution.EmbeddedResolution.orderAt (((principalizationOfEmbedding k Y pY D A).ideal (i + 1)).comap U.ι)
            (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U) := e1.symm
      _ = FunctorialResolution.EmbeddedResolution.orderAt (((principalizationOfEmbedding k Y pY D A).ideal i).comap
            (U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i))
            (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U) := by rw [hJ]
      _ = FunctorialResolution.EmbeddedResolution.orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            ((U.ι ≫ (D.toEmbeddedBlowupSequence A).blowdown i).base
              (⟨((D.toEmbeddedBlowupSequence A).strictTransformι (i + 1)).base η, hxU⟩ : ↥U)) := e2
      _ = FunctorialResolution.EmbeddedResolution.orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base
              (((D.toEmbeddedBlowupSequence A).strictTransformMap i).base η)) := by rw [hφp]
      _ = 1 := hord

/- English proof (translation)
Introduce `i`. Proceed by induction on `i with`. Consider the case `zero => intro _`. Conclude with `agreesWithComponentsOrderOne_zero D A`. Consider the case `succ i ih => intro hi`.

Conclude with `agreesWithComponentsOrderOne_succ D A i hi (ih (Nat.le_of_succ_le hi))`.
-/
private theorem forall_agreesWithComponentsOrderOne {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    ∀ i : ℕ, i ≤ (D.toEmbeddedBlowupSequence A).length → AgreesWithComponentsOrderOne D A i := by
  intro i
  induction i with
  | zero => intro _; exact agreesWithComponentsOrderOne_zero D A
  | succ i ih => intro hi; exact agreesWithComponentsOrderOne_succ D A i hi (ih (Nat.le_of_succ_le hi))

/- English proof (translation)
The claim follows from `forall_agreesWithComponentsOrderOne D A i hi`.
-/
theorem agreesWithComponentsOrderOne_of_le [AlgebraicGeometry.IsReduced Y] (D : EmbeddingDatum k Y pY)
    (A : PrincipalizationAlgorithm.{u}) (i : ℕ) (hi : i ≤ (D.toEmbeddedBlowupSequence A).length) :
    AgreesWithComponentsOrderOne D A i :=
  forall_agreesWithComponentsOrderOne D A i hi

/- English proof (translation)
Introduce `k _ _ Y _ _ pY _ _ D i hi`. Conclude with `(D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) i hi`.
-/
theorem noetherianSpace_strictTransform (A : PrincipalizationAlgorithm.{u}) :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        TopologicalSpace.NoetherianSpace ↥((D.toEmbeddedBlowupSequence A).strictTransform i) := by
  intro k _ _ Y _ _ pY _ _ D i hi
  exact (D.toEmbeddedBlowupSequence A).noetherianSpace_strictTransform_of_isNoetherian (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) i hi

/- English proof (translation)
Introduce `k _ _ Y _ _ pY _ _ D i _`. Conclude with `(D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i`.
-/
theorem isClosedEmbedding_strictTransformι (A : PrincipalizationAlgorithm.{u}) :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
        Topology.IsClosedEmbedding ⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base := by
  intro k _ _ Y _ _ pY _ _ D i _
  exact (D.toEmbeddedBlowupSequence A).isClosedEmbedding_strictTransformι i

/- English proof (translation)
Introduce `k _ _ Y _ _ pY _ _ D i hi C hC ξ hξ E hE hx`. Conclude with `not_avoidsCenters_of_mem_boundary_support D A i hi E hE _ hx (EmbeddedBlowupSequence.avoidsCenters_strictTransformι_of_isGenericPoint (D.toEmbeddedBlowupSequence A) (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) i hi C hC ξ hξ)`.
-/
theorem genericPoint_notMem_boundary_support (A : PrincipalizationAlgorithm.{u}) :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ E ∈ (principalizationOfEmbedding k Y pY D A).boundary i,
        ((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ ∉
          (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i)) := by
  intro k _ _ Y _ _ pY _ _ D i hi C hC ξ hξ E hE hx
  exact not_avoidsCenters_of_mem_boundary_support D A i hi E hE _ hx
    (EmbeddedBlowupSequence.avoidsCenters_strictTransformι_of_isGenericPoint (D.toEmbeddedBlowupSequence A)
      (isNoetherian_schemeAt_toEmbeddedBlowupSequence D A) i hi C hC ξ hξ)

/- English proof (translation)
Introduce `k _ _ Y _ _ pY _ _ D i hi C hC ξ hξ hCcl`. Conclude with `agreesWithComponentsOrderOne_of_le D A i hi C hC ξ hξ hCcl`.
-/
theorem agreeNear_and_orderAt_eq_one_reducedVanishingAssignment (A : PrincipalizationAlgorithm.{u}) :
    ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
      (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
      [AlgebraicGeometry.QuasiCompact pY] (D : EmbeddingDatum k Y pY) (i : ℕ),
      i ≤ (D.toEmbeddedBlowupSequence A).length →
      ∀ C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i),
      ∀ ξ : ↥((D.toEmbeddedBlowupSequence A).strictTransform i), IsGenericPoint ξ C →
      ∀ hC : IsClosed (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C),
        AgreeNear ((principalizationOfEmbedding k Y pY D A).ideal i)
            (reducedVanishingAssignment ((D.toEmbeddedBlowupSequence A).schemeAt i)
              ⟨⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C, hC⟩)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) ∧
          orderAt ((principalizationOfEmbedding k Y pY D A).ideal i)
            (((D.toEmbeddedBlowupSequence A).strictTransformι i).base ξ) = 1 := by
  intro k _ _ Y _ _ pY _ _ D i hi C hC ξ hξ hCcl
  exact agreesWithComponentsOrderOne_of_le D A i hi C hC ξ hξ hCcl

/- English proof (translation)
The claim follows from `{ noetherianSpace_alive := noetherianSpace_strictTransform A isClosedEmbedding_aliveι := isClosedEmbedding_strictTransformι A generic_not_mem_member := genericPoint_notMem_boundary_support A agreeNear_orderAt_eq_one := agreeNear_and_orderAt_eq_one_reducedVanishingAssignment A }`.
-/
theorem chartIsolationHypotheses_reducedVanishingAssignment (A : PrincipalizationAlgorithm.{u}) :
    ChartIsolationHypotheses reducedVanishingAssignment A :=
  { noetherianSpace_alive := noetherianSpace_strictTransform A
    isClosedEmbedding_aliveι := isClosedEmbedding_strictTransformι A
    generic_not_mem_member := genericPoint_notMem_boundary_support A
    agreeNear_orderAt_eq_one := agreeNear_and_orderAt_eq_one_reducedVanishingAssignment A }

/- English proof (translation)
Introduce `hsub`. Take `⟨ξ, hξ⟩` from `QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)`. Conclude with `genericPoint_notMem_boundary_support A k Y pY D i hi C hC ξ hξ E hE (hsub ⟨ξ, hξ.mem, rfl⟩)`.
-/
theorem not_image_irreducibleComponent_subset_boundary_support [AlgebraicGeometry.IsReduced Y]
    (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) (i : ℕ) (hi : i ≤ (D.toEmbeddedBlowupSequence A).length)
    (C : Set ↥((D.toEmbeddedBlowupSequence A).strictTransform i))
    (hC : C ∈ irreducibleComponents ↥((D.toEmbeddedBlowupSequence A).strictTransform i))
    (E : ((principalizationOfEmbedding k Y pY D A).schemeAt i).IdealSheafData)
    (hE : E ∈ (principalizationOfEmbedding k Y pY D A).boundary i) :
    ¬ (⇑((D.toEmbeddedBlowupSequence A).strictTransformι i).base '' C ⊆
        (E.support : Set ↥((principalizationOfEmbedding k Y pY D A).schemeAt i))) := by
  intro hsub
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  exact genericPoint_notMem_boundary_support A k Y pY D i hi C hC ξ hξ E hE
    (hsub ⟨ξ, hξ.mem, rfl⟩)

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution

end
