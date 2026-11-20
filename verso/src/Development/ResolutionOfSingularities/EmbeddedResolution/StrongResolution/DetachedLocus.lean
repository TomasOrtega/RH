import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ClopenSubscheme
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ReducedSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

/- English proof (authored)
The field spectrum is Noetherian, and the ambient scheme is quasi-compact and locally of finite type over it, so the ambient scheme is Noetherian. Stage zero is isomorphic to it. At each successor the ambient transition is a blowup of the preceding Noetherian scheme, which gives a Noetherian source. Induction proves the property through the final stage.
-/
theorem isNoetherian_schemeAt (i : ℕ) (hi : i ≤ S.length) :
    AlgebraicGeometry.IsNoetherian (S.schemeAt i) := by
  have hring : IsNoetherianRing ↥(CommRingCat.of k) := by
    show IsNoetherianRing k
    infer_instance
  have hspec : AlgebraicGeometry.IsNoetherian (Spec (CommRingCat.of k)) :=
    AlgebraicGeometry.isNoetherian_Spec.mpr hring
  have hamb : AlgebraicGeometry.IsNoetherian S.ambient :=
    isNoetherian_of_locallyOfFiniteType S.ambientStruct
  have h0 : AlgebraicGeometry.IsNoetherian (S.ambientSeq.schemeAt 0) :=
    isNoetherian_of_iso S.ambientSeq.isoZero.symm
  revert hi
  induction i with
  | zero =>
    intro _
    exact h0
  | succ n ih =>
    intro hi
    have hn : AlgebraicGeometry.IsNoetherian (S.ambientSeq.schemeAt n) :=
      ih (Nat.le_of_succ_le hi)
    exact isNoetherian_of_isBlowupAlongIdealSheaf (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hi)

/- English proof (authored)
By construction the strict transform is the closed subscheme of its strict-transform ideal, so its inclusion is the closed immersion defined by that ideal.
-/
theorem strictTransformι_eq_subschemeι (j : ℕ) :
    S.strictTransformι j = (S.strictTransformIdeal j).subschemeι := rfl

/- English proof (authored)
The closed immersion identifies its source with a closed subspace of the target. A subspace of a Noetherian space is Noetherian, giving the assertion.
-/
private theorem noetherianSpace_of_isClosedImmersion
    {Z X : Scheme.{u}} (f : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion f]
    (h : TopologicalSpace.NoetherianSpace ↥X) :
    TopologicalSpace.NoetherianSpace ↥Z := by
  have := h
  have hcl := AlgebraicGeometry.Scheme.Hom.isClosedEmbedding f
  exact hcl.toIsEmbedding.toIsInducing.noetherianSpace

/- English proof (authored)
Apply preservation of Noetherianity under taking a closed subspace to the strict-transform inclusion at the given stage.
-/
theorem noetherianSpace_strictTransform_of_noetherianSpace_schemeAt (j : ℕ)
    (h : TopologicalSpace.NoetherianSpace ↥(S.schemeAt j)) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform j) :=
  noetherianSpace_of_isClosedImmersion (S.strictTransformIdeal j).subschemeι h

/- English proof (authored)
The new ambient space is Noetherian. The strict-transform immersion is an embedding into that space and its source is Noetherian. Its inverse images of quasi-compact opens are consequently quasi-compact.
-/
theorem quasiCompact_strictTransformι_blowdown (i : ℕ)
    (h : TopologicalSpace.NoetherianSpace ↥(S.schemeAt (i + 1))) :
    AlgebraicGeometry.QuasiCompact
      (EmbeddedResolution.strictTransformι (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)) := by
  have := h
  exact quasiCompact_strictTransformι_of_noetherianSpace _ _ _

def detachedOpens (i : ℕ) (h : IsOpen (S.detachedLocus i)) : (S.strictTransform i).Opens :=
  ⟨S.detachedLocus i, h⟩

/- English proof (authored)
The detached open is the detached locus equipped with a proof that it is open. Its underlying set is therefore that locus.
-/
theorem coe_detachedOpens (i : ℕ) (h : IsOpen (S.detachedLocus i)) :
    ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      S.detachedLocus i := rfl

/- English proof (authored)
Every point of the detached locus also belongs to its closure. Thus it cannot lie in the complement of that closure, and the two opens are disjoint.
-/
theorem disjoint_detachedOpens_detachedClosureCompl (i : ℕ) (h : IsOpen (S.detachedLocus i))
    (_hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)) :
    Disjoint ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have h1 : x ∈ S.detachedLocus i := hx
  have h2 : x ∈ closure (S.detachedLocus i) := subset_closure h1
  exact hx' h2

/- English proof (authored)
In the Noetherian strict transform the detached locus is closed, so its closure equals the locus. The two opens are the locus and its complement, whose union is the whole space.
-/
theorem union_detachedOpens_detachedClosureCompl (i : ℕ) (h : IsOpen (S.detachedLocus i))
    (hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i)) :
    ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) ∪
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) = Set.univ := by
  have := hn
  rw [S.coe_detachedOpens i h, S.detachedClosureCompl_coe i, S.detachedClosure_coe i]
  exact Set.union_compl_self _

/- English proof (authored)
The underlying set of the open complement of the detached closure is the ordinary set complement of that closed subset.
-/
theorem coe_detachedClosureCompl (i : ℕ) :
    ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      ((S.detachedClosure i : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i))ᶜ := rfl

/- English proof (authored)
Noetherianity makes the detached locus equal to its closure. The stated open is therefore the complement of that locus. Since the locus is open by hypothesis, its complement is closed.
-/
theorem isClosed_detachedClosureCompl (i : ℕ)
    (hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (h : IsOpen (S.detachedLocus i)) :
    IsClosed ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have := hn
  have hc : ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
      = (S.detachedLocus i)ᶜ := by
    rw [S.coe_detachedClosureCompl i, S.detachedClosure_coe i]
  rw [hc]
  exact isClosed_compl_iff.mpr h

/- English proof (authored)
A point of the detached locus lies in a detached component. Each such component is defined by requiring its entire ambient image to lie in the center support, so the point’s image lies there.
-/
theorem image_detachedLocus_subset_ambientCenter_support (i : ℕ) :
    ⇑(S.strictTransformι i).base '' (S.detachedLocus i) ⊆
      ((S.ambientCenter i).support : Set ↥(S.schemeAt i)) := by
  rintro x ⟨y, hy, rfl⟩
  rw [S.detachedLocus_eq_sUnion i, Set.mem_sUnion] at hy
  obtain ⟨C, hC, hyC⟩ := hy
  exact ((S.mem_detachedComponents i C).mp hC).2 ⟨y, hyC, rfl⟩

/- English proof (authored)
The center off the detached locus has ideal equal to the kernel of the closed subscheme on the complement followed by the open inclusion. This source is Noetherian, so the composite is quasi-compact and the support of its kernel is the closure of the image. The image lies in the complement of the detached locus, which is closed because the locus is open. Its closure therefore lies in that same complement.
-/
theorem support_centerOffDetached_subset_detachedClosureCompl (i : ℕ)
    (hn : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i))
    (h : IsOpen (S.detachedLocus i)) :
    ((S.centerOffDetached i).support : Set ↥(S.strictTransform i)) ⊆
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
  have := hn
  have hco : ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) =
      (S.detachedLocus i)ᶜ := by
    rw [S.detachedClosureCompl_coe i, S.detachedClosure_coe i]
  have hoe := (S.detachedClosureCompl i).ι.isOpenEmbedding
  have hnU := hoe.toIsEmbedding.toIsInducing.noetherianSpace
  have hnW := noetherianSpace_of_isClosedImmersion
    ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι hnU
  have hqc : AlgebraicGeometry.QuasiCompact
      (((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι ≫
        (S.detachedClosureCompl i).ι) :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hr : Set.range ⇑(S.detachedClosureCompl i).ι.base =
      ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
    (S.detachedClosureCompl i).range_ι
  rw [S.centerOffDetached_eq i, Scheme.Hom.support_ker, hco]
  refine closure_minimal ?_ h.isClosed_compl
  rintro y ⟨z, rfl⟩
  rw [← hco, ← hr]
  exact ⟨_, rfl⟩

/- English proof (authored)
At zero the strict transform is defined by the kernel of the original reduced scheme’s closed immersion, transported through the ambient isomorphism. This kernel defines a reduced subscheme. At a successor, the preceding strict transform is reduced by induction and the strict-transform immersion is quasi-compact in the Noetherian new ambient stage. The strict transform of a reduced closed subscheme under this blowup is reduced, completing the induction.
-/
theorem isReduced_strictTransform_of_isNoetherian [AlgebraicGeometry.IsReduced Y]
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j))
    (i : ℕ) (hi : i ≤ S.length) :
    AlgebraicGeometry.IsReduced (S.strictTransform i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    have hq : AlgebraicGeometry.QuasiCompact S.emb := inferInstance
    have hq2 : AlgebraicGeometry.QuasiCompact (S.emb ≫ S.ambientSeq.isoZero.inv) :=
      inferInstance
    exact isReduced_subscheme_ker (S.emb ≫ S.ambientSeq.isoZero.inv)
  | succ n ih =>
    intro hi
    have hred : AlgebraicGeometry.IsReduced (S.strictTransformIdeal n).subscheme :=
      ih (Nat.le_of_succ_le hi)
    have hno : AlgebraicGeometry.IsNoetherian (S.schemeAt (n + 1)) := hN (n + 1) hi
    have hqc : AlgebraicGeometry.QuasiCompact
        (EmbeddedResolution.strictTransformι (S.blowdown n) (S.ambientCenter n) (S.strictTransformIdeal n)) :=
      FunctorialResolution.EmbeddedResolution.quasiCompact_strictTransformι_of_isLocallyNoetherian
        (S.blowdown n) (S.ambientCenter n) (S.strictTransformIdeal n)
    exact isReduced_subscheme_strictTransform (S.blowdown n) (S.ambientCenter n)
      (S.strictTransformIdeal n) (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hi)

/- English proof (authored)
Every point of the first summand maps into the first target set. Conversely, a point mapping into that set cannot belong to the second summand, whose image lies in the disjoint second target set. Since the two summands cover the source, it belongs to the first.
-/
private theorem range_coprod_inl_eq_preimage {A B X : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    (V W : Set ↥X) (hdisj : Disjoint V W)
    (ha : ∀ x : ↥A, a.base x ∈ V) (hb : ∀ y : ↥B, b.base y ∈ W) :
    Set.range ⇑(coprod.inl : A ⟶ A ⨿ B).base = ⇑(coprod.desc a b).base ⁻¹' V := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    have h1 : (coprod.desc a b).base ((coprod.inl : A ⟶ A ⨿ B).base z) = a.base z := by
      have h := congrArg (fun f : A ⟶ X => f.base z) (coprod.inl_desc a b)
      simpa using h
    rw [Set.mem_preimage, h1]
    exact ha z
  · intro z hz
    by_contra hzn
    have hz2 : z ∈ Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base := by
      rw [Blowup.range_coprod_inr_eq_compl]
      exact hzn
    obtain ⟨y, rfl⟩ := hz2
    have h1 : (coprod.desc a b).base ((coprod.inr : B ⟶ A ⨿ B).base y) = b.base y := by
      have h := congrArg (fun f : B ⟶ X => f.base y) (coprod.inr_desc a b)
      simpa using h
    rw [Set.mem_preimage, h1] at hz
    exact Set.disjoint_left.mp hdisj hz (hb y)

/- English proof (authored)
Every point of the second summand maps into the second target set. If a point mapping into that set were in the first summand, its image would also lie in the first target set, contradicting disjointness. It therefore lies in the second summand.
-/
private theorem range_coprod_inr_eq_preimage {A B X : Scheme.{u}} (a : A ⟶ X) (b : B ⟶ X)
    (V W : Set ↥X) (hdisj : Disjoint V W)
    (ha : ∀ x : ↥A, a.base x ∈ V) (hb : ∀ y : ↥B, b.base y ∈ W) :
    Set.range ⇑(coprod.inr : B ⟶ A ⨿ B).base = ⇑(coprod.desc a b).base ⁻¹' W := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩
    have h1 : (coprod.desc a b).base ((coprod.inr : B ⟶ A ⨿ B).base y) = b.base y := by
      have h := congrArg (fun f : B ⟶ X => f.base y) (coprod.inr_desc a b)
      simpa using h
    rw [Set.mem_preimage, h1]
    exact hb y
  · intro z hz
    rw [Blowup.range_coprod_inr_eq_compl]
    intro hzl
    obtain ⟨x, rfl⟩ := hzl
    have h1 : (coprod.desc a b).base ((coprod.inl : A ⟶ A ⨿ B).base x) = a.base x := by
      have h := congrArg (fun f : A ⟶ X => f.base x) (coprod.inl_desc a b)
      simpa using h
    rw [Set.mem_preimage, h1] at hz
    exact Set.disjoint_left.mp hdisj (ha x) hz

/- English proof (authored)
Substitute the vanishing ideal for the given equal ideal. In a reduced scheme the reduced closed subscheme of a closed open set is isomorphic over the ambient scheme to the open subscheme on that set.
-/
private theorem exists_iso_subscheme_of_eq_vanishingIdeal {X : Scheme.{u}}
    [AlgebraicGeometry.IsReduced X] (C : X.Opens)
    (hC : IsClosed ((C : Set ↥X))) (J : X.IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.vanishingIdeal
      (⟨(C : Set ↥X), hC⟩ : TopologicalSpace.Closeds ↥X)) :
    ∃ e : J.subscheme ≅ C.toScheme, e.hom ≫ C.ι = J.subschemeι := by
  subst hJ
  exact exists_iso_subscheme_vanishingIdeal_of_isClosed C hC

/- English proof (authored)
The given closed immersion has the ideal used to define the strict transform as its kernel. The canonical lift of the strict transform to the original closed subscheme has the same composite to the ambient scheme as the prescribed map. The closed immersion is a monomorphism, so the two lifts are equal. The blowup result for the canonical lift gives the desired property.
-/
private theorem isBlowupAlongIdealSheaf_lift_of_comp_eq {X X₁ S₀ : Scheme.{u}} (j : S₀ ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion j] [Mono j]
    [AlgebraicGeometry.IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (D : X.IdealSheafData) (hD : Scheme.Hom.ker j = D)
    (q : (Blowup.strictTransform π Z D).subscheme ⟶ S₀)
    (hq : q ≫ j = (Blowup.strictTransform π Z D).subschemeι ≫ π) :
    Blowup.IsBlowupAlongIdealSheaf q (Z.comap j) := by
  subst hD
  have h2 := strictTransformLiftOfClosedImmersion_comp j π Z
  have h3 : q = strictTransformLiftOfClosedImmersion j π Z := by
    rw [← cancel_mono j, hq, h2]
  rw [h3]
  exact isBlowupAlongIdealSheaf_strictTransformLiftOfClosedImmersion j π Z hπ

/- English proof (authored)
Because the two target opens are disjoint and the summands map into their respective opens, the inverse image of each open in the coproduct is exactly its source summand. The comparison isomorphisms commute with the restricted maps. Over the first open this identifies the restriction with the given blowup. Over the second it identifies the restriction with the given isomorphism, which is the blowup along the unit ideal there. These two opens cover the target, and the blowup property is local for this cover.
-/
private theorem isBlowupAlongIdealSheaf_coprod_desc_of_disjoint_cover {A A' F : Scheme.{u}} (g : A' ⟶ A) (j : F ⟶ A)
    (I : A.IdealSheafData) (V W : A.Opens)
    (hdisj : Disjoint ((V : Set ↥A)) ((W : Set ↥A)))
    (hcov : (V : Set ↥A) ∪ (W : Set ↥A) = Set.univ)
    (hgV : ∀ x : ↥A', g.base x ∈ (V : Set ↥A))
    (hjW : ∀ y : ↥F, j.base y ∈ (W : Set ↥A))
    (e : F ≅ W.toScheme) (he : e.hom ≫ W.ι = j)
    (hIW : I.comap W.ι = ⊤)
    (gV : A' ⟶ V.toScheme) (hgv : gV ≫ V.ι = g)
    (hblow : Blowup.IsBlowupAlongIdealSheaf gV (I.comap V.ι)) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc g j) I := by
  have hrl : Set.range ⇑(coprod.inl : A' ⟶ A' ⨿ F).base
      = Set.range ⇑(coprod.desc g j ⁻¹ᵁ V).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact range_coprod_inl_eq_preimage g j _ _ hdisj hgV hjW
  have hrr : Set.range ⇑(coprod.inr : F ⟶ A' ⨿ F).base
      = Set.range ⇑(coprod.desc g j ⁻¹ᵁ W).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact range_coprod_inr_eq_preimage g j _ _ hdisj hgV hjW
  obtain ⟨δ, hδ⟩ : ∃ δ : A' ≅ (coprod.desc g j ⁻¹ᵁ V).toScheme,
      δ.hom ≫ (coprod.desc g j ⁻¹ᵁ V).ι = (coprod.inl : A' ⟶ A' ⨿ F) :=
    ⟨IsOpenImmersion.isoOfRangeEq _ _ hrl, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : F ≅ (coprod.desc g j ⁻¹ᵁ W).toScheme,
      ε.hom ≫ (coprod.desc g j ⁻¹ᵁ W).ι = (coprod.inr : F ⟶ A' ⨿ F) :=
    ⟨IsOpenImmersion.isoOfRangeEq _ _ hrr, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrr⟩
  have key1 : δ.hom ≫ (coprod.desc g j ∣_ V) = gV := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hδ,
      coprod.inl_desc, hgv]
  have key2 : ε.hom ≫ (coprod.desc g j ∣_ W) = e.hom := by
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hε,
      coprod.inr_desc, he]
  have hV : Blowup.IsBlowupAlongIdealSheaf (coprod.desc g j ∣_ V) (I.comap V.ι) := by
    have hb := hblow.iso_hom_comp δ.symm
    rw [← key1, Iso.symm_hom, Iso.inv_hom_id_assoc] at hb
    exact hb
  have hisoW : IsIso (coprod.desc g j ∣_ W) := by
    have hw : (coprod.desc g j ∣_ W) = ε.inv ≫ e.hom := by
      rw [← key2, Iso.inv_hom_id_assoc]
    rw [hw]
    infer_instance
  have hW : Blowup.IsBlowupAlongIdealSheaf (coprod.desc g j ∣_ W) (I.comap W.ι) := by
    rw [hIW]
    exact Blowup.IsBlowupAlongIdealSheaf.of_isIso _
  have hoi : ∀ b : Bool,
      IsOpenImmersion (Bool.rec (motive := fun b =>
        (Bool.rec (motive := fun _ => Scheme.{u}) V.toScheme W.toScheme b) ⟶ A) V.ι W.ι b) := by
    intro b
    cases b
    · exact (inferInstance : IsOpenImmersion V.ι)
    · exact (inferInstance : IsOpenImmersion W.ι)
  refine Blowup.IsBlowupAlongIdealSheaf.of_comap_of_isOpenImmersion_cover (coprod.desc g j) I
      (fun b : Bool => Bool.rec (motive := fun _ => Scheme.{u}) V.toScheme W.toScheme b)
      (fun b : Bool => Bool.rec (motive := fun b =>
        (Bool.rec (motive := fun _ => Scheme.{u}) V.toScheme W.toScheme b) ⟶ A) V.ι W.ι b) ?_ ?_
  · intro x
    by_cases hx : x ∈ (V : Set ↥A)
    · refine ⟨false, ?_⟩
      show x ∈ Set.range ⇑V.ι.base
      rw [Scheme.Opens.range_ι]
      exact hx
    · refine ⟨true, ?_⟩
      show x ∈ Set.range ⇑W.ι.base
      rw [Scheme.Opens.range_ι]
      have hxu : x ∈ (V : Set ↥A) ∪ (W : Set ↥A) := by rw [hcov]; trivial
      exact hxu.resolve_left hx
  · intro b
    cases b
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc g j) V.ι) (I.comap V.ι)
      have hb := hV.iso_hom_comp (pullbackRestrictIsoRestrict (coprod.desc g j) V)
      rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict] at hb
    · show Blowup.IsBlowupAlongIdealSheaf (pullback.snd (coprod.desc g j) W.ι) (I.comap W.ι)
      have hb := hW.iso_hom_comp (pullbackRestrictIsoRestrict (coprod.desc g j) W)
      rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict] at hb

/- English proof (authored)
The current strict transform is reduced and Noetherian, so the open detached locus is also closed and its reduced subscheme agrees with that open subscheme. The map from the next strict transform is the blowup along the pulled-back ambient center by the strict-transform lift theorem. Its range lies in the complement of the detached locus. Indeed, the preceding support away from the center lies in the ambient image of this complement, and that image is closed. The closure formula for the next support and the commuting blowdown square therefore put every image point in the complement. Restricting the blowup to this open keeps its whole source and restricts its center to the center off the detached locus. On the detached open the latter center is the unit ideal because its support lies in the closed complement. The map on that summand is an isomorphism. The local blowup criterion on these two disjoint opens now gives the result.
-/
theorem isBlowupAlongIdealSheaf_coprod_desc_centerOffDetached [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.QuasiCompact pY] (i : ℕ) (hi : i < S.length)
    (h : IsOpen (S.detachedLocus i))
    (hN : ∀ j ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt j)) :
    Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.detachedι i)) (S.centerOffDetached i) := by
  have hn0 : AlgebraicGeometry.IsNoetherian (S.schemeAt i) := hN i hi.le
  have hn1 : AlgebraicGeometry.IsNoetherian (S.schemeAt (i + 1)) := hN (i + 1) hi
  have hns0 : TopologicalSpace.NoetherianSpace ↥(S.schemeAt i) := inferInstance
  have hns1 : TopologicalSpace.NoetherianSpace ↥(S.schemeAt (i + 1)) := inferInstance
  have hnsA : TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) :=
    S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i hns0
  have hnsA1 : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (i + 1)) :=
    S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt (i + 1) hns1
  have hred : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
    S.isReduced_strictTransform_of_isNoetherian hN i hi.le
  have hqcst : AlgebraicGeometry.QuasiCompact
      (EmbeddedResolution.strictTransformι (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)) :=
    S.quasiCompact_strictTransformι_blowdown i hns1
  have hUc : IsClosed ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    rw [S.coe_detachedOpens i h]
    exact S.isClosed_detachedLocus i
  have hdetached : S.detachedIdeal i
      = Scheme.IdealSheafData.vanishingIdeal
          (⟨((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)), hUc⟩ :
            TopologicalSpace.Closeds ↥(S.strictTransform i)) := by
    rw [S.detachedIdeal_eq i]
    congr 1
    refine TopologicalSpace.Closeds.ext ?_
    show ((S.detachedClosure i : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
        Set ↥(S.strictTransform i)) =
      ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))
    rw [S.detachedClosure_coe i, S.coe_detachedOpens i h]
  obtain ⟨e, he⟩ := exists_iso_subscheme_of_eq_vanishingIdeal (S.detachedOpens i h) hUc
    (S.detachedIdeal i) hdetached
  have hblowA : Blowup.IsBlowupAlongIdealSheaf (S.strictTransformMap i) (S.comapAmbientCenter i) := by
    have hln : AlgebraicGeometry.IsLocallyNoetherian (S.schemeAt (i + 1)) := inferInstance
    have hmono : Mono (S.strictTransformι i) := inferInstance
    exact isBlowupAlongIdealSheaf_lift_of_comp_eq (S.strictTransformι i) (S.blowdown i) (S.ambientCenter i)
      (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism i hi) (S.strictTransformIdeal i) (by simp) (S.strictTransformMap i)
      (S.strictTransformMap_comp_strictTransformι i)
  have hstrict : ∀ x : ↥(S.strictTransform (i + 1)),
      (S.strictTransformMap i).base x ∈
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
    have hVcl : IsClosed ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
      S.isClosed_detachedClosureCompl i hnsA h
    have himV : IsClosed (⇑(S.strictTransformι i).base ''
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
      (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (S.strictTransformι i)).isClosedMap _ hVcl
    have hsub : (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
          ((S.ambientCenter i).support : Set ↥(S.schemeAt i)))
        ⊆ ⇑(S.strictTransformι i).base ''
            ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rintro y ⟨hy, hy2⟩
      rw [← Scheme.IdealSheafData.range_subschemeι] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨z, ?_, rfl⟩
      by_contra hz
      refine absurd (S.image_detachedLocus_subset_ambientCenter_support i ⟨z, ?_, rfl⟩) hy2
      have hz' : z ∈ ((S.detachedClosure i : TopologicalSpace.Closeds ↥(S.strictTransform i)) :
          Set ↥(S.strictTransform i)) := by
        by_contra hz2
        exact hz (by rw [S.detachedClosureCompl_coe i]; exact hz2)
      rw [S.detachedClosure_coe i] at hz'
      exact hz'
    intro x
    have h1 : (S.strictTransformι (i + 1)).base x ∈
        ((S.strictTransformIdeal (i + 1)).support : Set ↥(S.schemeAt (i + 1))) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨x, rfl⟩
    rw [S.strictTransformIdeal_succ i,
      support_strictTransform_eq_closure_preimage (S.blowdown i) (S.ambientCenter i) (S.strictTransformIdeal i)] at h1
    have h2 : closure (⇑(S.blowdown i).base ⁻¹'
          (((S.strictTransformIdeal i).support : Set ↥(S.schemeAt i)) \
            ((S.ambientCenter i).support : Set ↥(S.schemeAt i))))
        ⊆ ⇑(S.blowdown i).base ⁻¹' (⇑(S.strictTransformι i).base ''
            ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i))) :=
      closure_minimal (Set.preimage_mono hsub)
        (himV.preimage (S.blowdown i).base.hom.continuous)
    obtain ⟨v, hv, hveq⟩ := h2 h1
    have h3 : (S.strictTransformι i).base ((S.strictTransformMap i).base x)
        = (S.blowdown i).base ((S.strictTransformι (i + 1)).base x) := by
      have hc := congrArg (fun f : S.strictTransform (i + 1) ⟶ S.schemeAt i => f.base x)
        (S.strictTransformMap_comp_strictTransformι i)
      simpa using hc
    have h4 : (S.strictTransformι i).base v = (S.strictTransformι i).base ((S.strictTransformMap i).base x) := by
      rw [h3, hveq]
    have h5 := (AlgebraicGeometry.Scheme.Hom.isClosedEmbedding (S.strictTransformι i)).injective h4
    rw [← h5]
    exact hv
  have hζr : Set.range ⇑(𝟙 (S.strictTransform (i + 1))).base
      = Set.range ⇑(S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)).ι.base := by
    rw [Scheme.Opens.range_ι]
    have hA : Set.range ⇑(𝟙 (S.strictTransform (i + 1))).base = Set.univ := by simp
    rw [hA]
    symm
    rw [Set.eq_univ_iff_forall]
    intro z
    exact hstrict z
  obtain ⟨ζ, hζ⟩ : ∃ ζ : S.strictTransform (i + 1) ≅ (S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)).toScheme,
      ζ.hom ≫ (S.strictTransformMap i ⁻¹ᵁ (S.detachedClosureCompl i)).ι = 𝟙 (S.strictTransform (i + 1)) :=
    ⟨IsOpenImmersion.isoOfRangeEq _ _ hζr, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hζr⟩
  have hgv : (ζ.hom ≫ (S.strictTransformMap i ∣_ (S.detachedClosureCompl i))) ≫ (S.detachedClosureCompl i).ι
      = S.strictTransformMap i := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hζ, Category.id_comp]
  have hnU : TopologicalSpace.NoetherianSpace ↥((S.detachedClosureCompl i).toScheme) :=
    ((S.detachedClosureCompl i).ι.isOpenEmbedding).toIsEmbedding.toIsInducing.noetherianSpace
  have hnW : TopologicalSpace.NoetherianSpace
      ↥(((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subscheme) :=
    noetherianSpace_of_isClosedImmersion
      ((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι hnU
  have hq1 : AlgebraicGeometry.QuasiCompact
      (((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι) :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hq2 : AlgebraicGeometry.QuasiCompact
      ((((S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι).subschemeι) ≫
        (S.detachedClosureCompl i).ι) :=
    ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
  have hWeq : (S.centerOffDetached i).comap (S.detachedClosureCompl i).ι
      = (S.comapAmbientCenter i).comap (S.detachedClosureCompl i).ι := by
    rw [S.centerOffDetached_eq i]
    exact comap_ker_subschemeι_comp _ _
  have hblowV : Blowup.IsBlowupAlongIdealSheaf (ζ.hom ≫ (S.strictTransformMap i ∣_ (S.detachedClosureCompl i)))
      ((S.centerOffDetached i).comap (S.detachedClosureCompl i).ι) := by
    rw [hWeq]
    exact (hblowA.restrict (S.detachedClosureCompl i)).iso_hom_comp ζ
  have hIW : (S.centerOffDetached i).comap (S.detachedOpens i h).ι = ⊤ := by
    refine Blowup.comap_eq_top_of_notMem_support _ _ ?_
    intro x hx
    have h1 : (S.detachedOpens i h).ι.base x ∈
        ((S.detachedClosureCompl i : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) :=
      S.support_centerOffDetached_subset_detachedClosureCompl i hnsA h hx
    have h2 : (S.detachedOpens i h).ι.base x ∈
        ((S.detachedOpens i h : (S.strictTransform i).Opens) : Set ↥(S.strictTransform i)) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨x, rfl⟩
    exact Set.disjoint_left.mp (S.disjoint_detachedOpens_detachedClosureCompl i h hnsA) h2 h1
  refine isBlowupAlongIdealSheaf_coprod_desc_of_disjoint_cover (S.strictTransformMap i) (S.detachedι i) (S.centerOffDetached i)
      (S.detachedClosureCompl i) (S.detachedOpens i h) ((S.disjoint_detachedOpens_detachedClosureCompl i h hnsA).symm)
      ?_ hstrict ?_ e he hIW (ζ.hom ≫ (S.strictTransformMap i ∣_ (S.detachedClosureCompl i))) hgv hblowV
  · rw [Set.union_comm]
    exact S.union_detachedOpens_detachedClosureCompl i h hnsA
  · intro y
    have hy : (S.detachedι i).base y ∈ Set.range ⇑(S.detachedOpens i h).ι.base := by
      refine ⟨e.hom.base y, ?_⟩
      have hc := congrArg (fun f : (S.detachedIdeal i).subscheme ⟶ S.strictTransform i => f.base y) he
      simpa using hc
    rwa [Scheme.Opens.range_ι] at hy

private def coprodSwapAssocHom (A F T : Scheme.{u}) : A ⨿ (T ⨿ F) ⟶ (A ⨿ F) ⨿ T :=
  coprod.desc ((coprod.inl : A ⟶ A ⨿ F) ≫ (coprod.inl : A ⨿ F ⟶ (A ⨿ F) ⨿ T))
    (coprod.desc (coprod.inr : T ⟶ (A ⨿ F) ⨿ T)
      ((coprod.inr : F ⟶ A ⨿ F) ≫ (coprod.inl : A ⨿ F ⟶ (A ⨿ F) ⨿ T)))

private def coprodSwapAssocInv (A F T : Scheme.{u}) : (A ⨿ F) ⨿ T ⟶ A ⨿ (T ⨿ F) :=
  coprod.desc
    (coprod.desc (coprod.inl : A ⟶ A ⨿ (T ⨿ F))
      ((coprod.inr : F ⟶ T ⨿ F) ≫ (coprod.inr : T ⨿ F ⟶ A ⨿ (T ⨿ F))))
    ((coprod.inl : T ⟶ T ⨿ F) ≫ (coprod.inr : T ⨿ F ⟶ A ⨿ (T ⨿ F)))

private def coprodSwapAssocIso (A F T : Scheme.{u}) : A ⨿ (T ⨿ F) ≅ (A ⨿ F) ⨿ T where
  hom := coprodSwapAssocHom A F T
  inv := coprodSwapAssocInv A F T
  hom_inv_id := by
    refine coprod.hom_ext ?_ ?_
    · simp [coprodSwapAssocHom, coprodSwapAssocInv, coprod.inl_desc, coprod.inr_desc]
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocHom, coprodSwapAssocInv, coprod.inl_desc, coprod.inr_desc]
  inv_hom_id := by
    refine coprod.hom_ext ?_ ?_
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocHom, coprodSwapAssocInv, coprod.inl_desc, coprod.inr_desc]
    · simp [coprodSwapAssocHom, coprodSwapAssocInv, coprod.inl_desc, coprod.inr_desc]

/- English proof (authored)
The forward morphism of the isomorphism was defined to be the map that rearranges and reassociates the three coproduct summands.
-/
private theorem coprodSwapAssocIso_hom (A F T : Scheme.{u}) :
    (coprodSwapAssocIso A F T).hom = coprodSwapAssocHom A F T := rfl

/- English proof (authored)
The total center is supported in the previous strict-transform summand. Its pullback to that summand is the center off the detached locus, and its pullback to the already detached summand is the unit ideal. Thus the given blowup on the first summand and the identity on the second form a blowup of the full center. The total transition equals this coproduct map after the canonical rearrangement of the three source summands, as seen by checking each summand. Precomposition with that source isomorphism preserves the blowup property.
-/
theorem isBlowupAlongIdealSheaf_totalTransition_of_coprod_desc (i : ℕ)
    (h : Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.detachedι i)) (S.centerOffDetached i)) :
    Blowup.IsBlowupAlongIdealSheaf (S.totalTransition i) (S.totalCenter i) := by
  have hq1 : AlgebraicGeometry.QuasiCompact (S.centerOffDetached i).subschemeι := inferInstance
  have hq2 : AlgebraicGeometry.QuasiCompact
      ((S.centerOffDetached i).subschemeι ≫
        (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := inferInstance
  have hker : Scheme.Hom.ker (S.centerOffDetached i).subschemeι = S.centerOffDetached i := by simp
  have hl : (S.totalCenter i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)
      = S.centerOffDetached i := by
    rw [S.totalCenter_eq i,
      Blowup.ker_comp_coprod_inl_comap_inl (Y := S.detachedCoprod i) (S.centerOffDetached i).subschemeι, hker]
  have hr : (S.totalCenter i).comap (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i) = ⊤ := by
    rw [S.totalCenter_eq i,
      Blowup.ker_comp_coprod_inl_comap_inr (Y := S.detachedCoprod i) (S.centerOffDetached i).subschemeι]
  have h₁ : Blowup.IsBlowupAlongIdealSheaf (coprod.desc (S.strictTransformMap i) (S.detachedι i))
      ((S.totalCenter i).comap (coprod.inl : S.strictTransform i ⟶ S.totalSpace i)) := by
    rw [hl]; exact h
  have h₂ : Blowup.IsBlowupAlongIdealSheaf (𝟙 (S.detachedCoprod i))
      ((S.totalCenter i).comap (coprod.inr : S.detachedCoprod i ⟶ S.totalSpace i)) := by
    rw [hr]; exact Blowup.isBlowupAlongIdealSheaf_id_top _
  have hmap := Blowup.IsBlowupAlongIdealSheaf.coprod h₁ h₂
  have hcomp :
      (coprodSwapAssocIso (S.strictTransform (i + 1)) (S.detachedScheme i) (S.detachedCoprod i)).hom ≫
          coprod.map (coprod.desc (S.strictTransformMap i) (S.detachedι i)) (𝟙 (S.detachedCoprod i)) =
        S.totalTransition i := by
    refine coprod.hom_ext ?_ ?_
    · simp [coprodSwapAssocIso_hom, coprodSwapAssocHom, EmbeddedBlowupSequence.totalTransition,
        coprod.inl_desc, coprod.inr_desc]
    · refine coprod.hom_ext ?_ ?_ <;>
        simp [coprodSwapAssocIso_hom, coprodSwapAssocHom, EmbeddedBlowupSequence.totalTransition,
          coprod.inl_desc, coprod.inr_desc]
  have hfin := hmap.iso_hom_comp
    (coprodSwapAssocIso (S.strictTransform (i + 1)) (S.detachedScheme i) (S.detachedCoprod i))
  rw [hcomp] at hfin
  exact hfin

end EmbeddedBlowupSequence

def EmbeddedBlowupSequence.DetachedLocusIsOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY) : Prop :=
  ∀ i < S.length, IsOpen (S.detachedLocus i)

def EmbeddedBlowupSequence.AllLevelsNoetherian {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : EmbeddedBlowupSequence k Y pY) : Prop :=
  ∀ i ≤ S.length, AlgebraicGeometry.IsNoetherian (S.schemeAt i)

/- English proof (authored)
For a stage within the sequence, openness of the detached locus and Noetherianity give the blowup description on the strict-transform summand. The coproduct argument extends it to the full total transition. The successor arrow of the tower is this transition, so each such arrow is the required blowup.
-/
theorem transitionsAreBlowups_of_detachedLocusIsOpen {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsReduced Y]
    {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] (S : EmbeddedBlowupSequence k Y pY)
    (hOpen : EmbeddedBlowupSequence.DetachedLocusIsOpen S) (hnoeth : EmbeddedBlowupSequence.AllLevelsNoetherian S) :
    S.TransitionsAreBlowups := by
  intro i hi
  rw [S.totalTower_map_succ i]
  exact EmbeddedBlowupSequence.isBlowupAlongIdealSheaf_totalTransition_of_coprod_desc S i
    (EmbeddedBlowupSequence.isBlowupAlongIdealSheaf_coprod_desc_centerOffDetached S i hi (hOpen i hi) hnoeth)

def DetachedLocusIsOpenForEmbeddings (A : PrincipalizationAlgorithm.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y pY),
    EmbeddedBlowupSequence.DetachedLocusIsOpen (D.toEmbeddedBlowupSequence A)

/- English proof (authored)
The finite-stage Noetherianity theorem applies to the embedded blowup sequence obtained from the given embedding and algorithm. It gives the required result at every stage at or below the length.
-/
theorem allLevelsNoetherian_toEmbeddedBlowupSequence (A : PrincipalizationAlgorithm.{u}) (k : Type u) [Field k] [CharZero k]
    (Y : Scheme.{u}) (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    (D : EmbeddingDatum k Y pY) :
    EmbeddedBlowupSequence.AllLevelsNoetherian (D.toEmbeddedBlowupSequence A) := by
  intro i hi
  exact EmbeddedBlowupSequence.isNoetherian_schemeAt (D.toEmbeddedBlowupSequence A) i hi

/- English proof (authored)
For any embedding datum the assumed openness holds at every stage. The embedded sequence from the algorithm also has Noetherian ambient stages. The preceding blowup construction applies to these two facts and identifies its transitions as blowups.
-/
theorem transitionsAreBlowupsForEmbeddings_of_detachedLocusIsOpen (A : PrincipalizationAlgorithm.{u}) (h : DetachedLocusIsOpenForEmbeddings A) :
    TransitionsAreBlowupsForEmbeddings A := by
  intro k _ _ Y pY _ _ _ _ D
  exact transitionsAreBlowups_of_detachedLocusIsOpen (D.toEmbeddedBlowupSequence A) (h k Y pY D)
    (allLevelsNoetherian_toEmbeddedBlowupSequence A k Y pY D)

def vanishingIdealClosureImage {X Z : Scheme.{u}} (f : Z ⟶ X) (C : Set ↥Z) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    (⟨closure (⇑f.base '' C), isClosed_closure⟩ : TopologicalSpace.Closeds ↥X)

/- English proof (authored)
The named ideal is defined by taking the topological closure of the set’s image and then its vanishing ideal.
-/
theorem vanishingIdealClosureImage_eq {X Z : Scheme.{u}} (f : Z ⟶ X) (C : Set ↥Z) :
    vanishingIdealClosureImage f C =
      Scheme.IdealSheafData.vanishingIdeal
        (⟨closure (⇑f.base '' C), isClosed_closure⟩ : TopologicalSpace.Closeds ↥X) := rfl

/- English proof (authored)
Smoothness over the field gives regular local rings, so distinct irreducible components are disjoint. The scheme is locally Noetherian, so the irreducible components are locally finite. Each component is closed, and its complement is a union of the other components, which is closed by local finiteness. Thus the component is also open.
-/
theorem isClopen_of_mem_irreducibleComponents_of_smooth {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (C : Set ↥X)
    (hC : C ∈ irreducibleComponents ↥X) : IsClopen C :=
  isClopen_irreducibleComponent_of_smooth p inferInstance hC

/- English proof (authored)
The original smooth scheme is reduced. Its reduced vanishing subscheme on the given clopen set is isomorphic over the ambient scheme to the open subscheme on that set. The open subscheme has smooth structural morphism by restriction. The identification of the immersions transports smoothness to the vanishing subscheme.
-/
theorem smooth_subschemeι_vanishingIdeal_comp_of_isClopen {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (C : Set ↥X) (hC : IsClopen C) :
    AlgebraicGeometry.Smooth
      ((Scheme.IdealSheafData.vanishingIdeal
        (⟨C, hC.isClosed⟩ : TopologicalSpace.Closeds ↥X)).subschemeι ≫ p) := by
  have hredX : AlgebraicGeometry.IsReduced X := isReduced_of_smooth p
  obtain ⟨e, he⟩ := exists_iso_subscheme_vanishingIdeal_of_isClosed
    (⟨C, hC.isOpen⟩ : X.Opens) hC.isClosed
  have key : AlgebraicGeometry.Smooth
      ((e.hom ≫ Scheme.Opens.ι (⟨C, hC.isOpen⟩ : X.Opens)) ≫ p) := inferInstance
  rw [he] at key
  exact key

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

variable (S : EmbeddedBlowupSequence k Y pY)

def schemeAtToSpec (i : ℕ) : S.schemeAt i ⟶ Spec (CommRingCat.of k) :=
  S.ambientSeq.projectionToBase i ≫ S.ambientStruct

/- English proof (authored)
The structural map at a stage is defined by its ambient projection to the original ambient scheme followed by that scheme’s structural map to the field.
-/
theorem schemeAtToSpec_eq (i : ℕ) :
    S.schemeAtToSpec i = S.ambientSeq.projectionToBase i ≫ S.ambientStruct := rfl

def strictTransformToSpec (i : ℕ) : S.strictTransform i ⟶ Spec (CommRingCat.of k) :=
  S.strictTransformι i ≫ S.schemeAtToSpec i

/- English proof (authored)
The strict-transform structural morphism is obtained by composing its ambient inclusion with the ambient stage’s structural map.
-/
theorem strictTransformToSpec_eq (i : ℕ) :
    S.strictTransformToSpec i = S.strictTransformι i ≫ S.schemeAtToSpec i := rfl

/- English proof (authored)
Induct on the stage for the projection to the original ambient scheme. The first projection is an isomorphism. Each successor factor is the blowup of a Noetherian scheme and is proper, hence locally of finite type. Composing with the preceding projection preserves this property. Composing each stage projection with the original ambient structure map to the field preserves it once more.
-/
theorem locallyOfFiniteType_schemeAtToSpec (i : ℕ) (hi : i ≤ S.length) :
    AlgebraicGeometry.LocallyOfFiniteType (S.schemeAtToSpec i) := by
  have key : ∀ j : ℕ, j ≤ S.length →
      AlgebraicGeometry.LocallyOfFiniteType (S.ambientSeq.projectionToBase j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [SequenceOfBlowups.projectionToBase_zero]
      infer_instance
    | succ n ih =>
      intro hn
      have hft : AlgebraicGeometry.LocallyOfFiniteType (S.ambientSeq.projectionToBase n) :=
        ih (Nat.le_of_succ_le hn)
      have hno : AlgebraicGeometry.IsNoetherian (S.schemeAt n) :=
        S.isNoetherian_schemeAt n (Nat.le_of_succ_le hn)
      have hprop : AlgebraicGeometry.IsProper (S.ambientSeq.transitionMapSucc n) :=
        Blowup.blowupIsProper (S.schemeAt n) (S.schemeAt (n + 1)) (S.ambientSeq.transitionMapSucc n)
          (S.ambientCenter n) (S.ambientSeq.isBlowupAlongIdealSheaf_blowupMorphism n hn)
      have hftb : AlgebraicGeometry.LocallyOfFiniteType (S.ambientSeq.transitionMapSucc n) :=
        inferInstance
      rw [SequenceOfBlowups.projectionToBase_succ]
      infer_instance
  have := key i hi
  rw [S.schemeAtToSpec_eq i]
  infer_instance

/- English proof (authored)
The strict-transform inclusion is a closed immersion and hence locally of finite type. The ambient stage’s structural map is locally of finite type as well, so their composite has the property.
-/
theorem locallyOfFiniteType_strictTransformToSpec (i : ℕ) (hi : i ≤ S.length) :
    AlgebraicGeometry.LocallyOfFiniteType (S.strictTransformToSpec i) := by
  have hlev : AlgebraicGeometry.LocallyOfFiniteType (S.schemeAtToSpec i) :=
    S.locallyOfFiniteType_schemeAtToSpec i hi
  have hι : AlgebraicGeometry.LocallyOfFiniteType (S.strictTransformι i) := inferInstance
  rw [S.strictTransformToSpec_eq i]
  infer_instance

end EmbeddedBlowupSequence

end FunctorialResolution.EmbeddedResolution

end
