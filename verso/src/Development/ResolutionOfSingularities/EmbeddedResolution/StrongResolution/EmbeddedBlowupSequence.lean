import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.RemoveIsoBlowups
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure EmbeddedBlowupSequence (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    [AlgebraicGeometry.IsAffine Y] (pY : Y ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] : Type (u + 1) where
  ambient : Scheme.{u}
  ambientStruct : ambient ⟶ Spec (CommRingCat.of k)
  isAffine_ambient : AlgebraicGeometry.IsAffine ambient
  smooth_ambientStruct : AlgebraicGeometry.Smooth ambientStruct
  locallyOfFiniteType_ambientStruct : AlgebraicGeometry.LocallyOfFiniteType ambientStruct
  quasiCompact_ambientStruct : AlgebraicGeometry.QuasiCompact ambientStruct
  emb : Y ⟶ ambient
  isClosedImmersion_emb : AlgebraicGeometry.IsClosedImmersion emb
  emb_comp : emb ≫ ambientStruct = pY
  ambientSeq : SequenceOfBlowups ambient

namespace EmbeddedBlowupSequence

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

instance instIsAffineAmbient (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.IsAffine T.ambient := T.isAffine_ambient

instance instSmoothAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.Smooth T.ambientStruct := T.smooth_ambientStruct

instance instLocallyOfFiniteTypeAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.LocallyOfFiniteType T.ambientStruct :=
  T.locallyOfFiniteType_ambientStruct

instance instQuasiCompactAmbientStruct (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.QuasiCompact T.ambientStruct := T.quasiCompact_ambientStruct

instance instIsClosedImmersionEmb (T : EmbeddedBlowupSequence k Y pY) :
    AlgebraicGeometry.IsClosedImmersion T.emb := T.isClosedImmersion_emb

variable (T : EmbeddedBlowupSequence k Y pY)

abbrev length : ℕ := T.ambientSeq.length

abbrev schemeAt (i : ℕ) : Scheme.{u} := T.ambientSeq.schemeAt i

abbrev blowdown (i : ℕ) : T.schemeAt (i + 1) ⟶ T.schemeAt i := T.ambientSeq.transitionMapSucc i

abbrev ambientCenter (i : ℕ) : (T.schemeAt i).IdealSheafData := T.ambientSeq.center i

def strictTransformIdeal (i : ℕ) : (T.schemeAt i).IdealSheafData :=
  Nat.rec (motive := fun j => (T.schemeAt j).IdealSheafData)
    (Scheme.Hom.ker (T.emb ≫ T.ambientSeq.isoZero.inv))
    (fun j ih => Blowup.strictTransform (T.blowdown j) (T.ambientCenter j) ih) i

/- English proof (authored)
The recursive strict-transform construction starts from the ideal of the original closed immersion transported into stage zero. This is the kernel of the original embedding followed by the inverse of the initial ambient isomorphism.
-/
@[simp] theorem strictTransformIdeal_zero :
    T.strictTransformIdeal 0 = Scheme.Hom.ker (T.emb ≫ T.ambientSeq.isoZero.inv) := rfl

/- English proof (authored)
The recursive successor step takes the strict transform of the preceding ideal under the current blowdown, using the current center.
-/
@[simp] theorem strictTransformIdeal_succ (i : ℕ) :
    T.strictTransformIdeal (i + 1) =
      Blowup.strictTransform (T.blowdown i) (T.ambientCenter i) (T.strictTransformIdeal i) := rfl

abbrev strictTransform (i : ℕ) : Scheme.{u} := (T.strictTransformIdeal i).subscheme

abbrev strictTransformι (i : ℕ) : T.strictTransform i ⟶ T.schemeAt i := (T.strictTransformIdeal i).subschemeι

/- English proof (authored)
The total transform is cut out by the pulled-back ideal on the new ambient stage. Its open part away from the center defines the strict transform by scheme-theoretic closure. A section vanishing on the whole total transform vanishes on that open part, giving inclusion in the strict-transform ideal.
-/
theorem comap_strictTransformIdeal_le (i : ℕ) :
    (T.strictTransformIdeal i).comap (T.blowdown i) ≤ T.strictTransformIdeal (i + 1) :=
  Blowup.comap_le_strictTransform _ _ _

/- English proof (authored)
The strict-transform ideal contains the pullback of the preceding ideal. Thus the ambient blowdown restricted to the successor strict transform kills the preceding defining ideal. It factors through the preceding strict transform by the universal property of a closed immersion, giving the commuting square.
-/
theorem exists_strictTransformMap (i : ℕ) :
    ∃ f : T.strictTransform (i + 1) ⟶ T.strictTransform i,
      f ≫ T.strictTransformι i = T.strictTransformι (i + 1) ≫ T.blowdown i := by
  have hle : T.strictTransformIdeal i ≤ (T.strictTransformIdeal (i + 1)).map (T.blowdown i) :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr (T.comap_strictTransformIdeal_le i)
  exact ⟨(T.strictTransformIdeal (i + 1)).subschemeMap (T.strictTransformIdeal i) (T.blowdown i) hle,
    Scheme.IdealSheafData.subschemeMap_subschemeι (T.strictTransformIdeal (i + 1)) (T.strictTransformIdeal i)
      (T.blowdown i) hle⟩

def strictTransformMap (i : ℕ) : T.strictTransform (i + 1) ⟶ T.strictTransform i := (T.exists_strictTransformMap i).choose

/- English proof (authored)
The strict-transform map was chosen as a factorization of the restriction of blowdown through the preceding strict-transform immersion. Its factorization equation is the asserted equality.
-/
theorem strictTransformMap_comp_strictTransformι (i : ℕ) :
    T.strictTransformMap i ≫ T.strictTransformι i = T.strictTransformι (i + 1) ≫ T.blowdown i :=
  (T.exists_strictTransformMap i).choose_spec

def detachedComponents (i : ℕ) : Set (Set ↥(T.strictTransform i)) :=
  {C | C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
    (T.strictTransformι i).base '' C ⊆ ((T.ambientCenter i).support : Set ↥(T.schemeAt i))}

/- English proof (authored)
A detached component is defined to be an irreducible component of the strict transform whose entire ambient image lies in the support of the current center. Membership is exactly the conjunction of these conditions.
-/
theorem mem_detachedComponents (i : ℕ) (C : Set ↥(T.strictTransform i)) :
    C ∈ T.detachedComponents i ↔
      C ∈ irreducibleComponents ↥(T.strictTransform i) ∧
        (T.strictTransformι i).base '' C ⊆ ((T.ambientCenter i).support : Set ↥(T.schemeAt i)) := Iff.rfl

def detachedLocus (i : ℕ) : Set ↥(T.strictTransform i) := ⋃₀ (T.detachedComponents i)

/- English proof (authored)
The detached locus is defined as the union of all the detached components.
-/
theorem detachedLocus_eq_sUnion (i : ℕ) : T.detachedLocus i = ⋃₀ (T.detachedComponents i) := rfl

/- English proof (authored)
The Noetherian strict transform has finitely many irreducible components. Each of them is closed, so the union of the subfamily of detached components is a finite union of closed sets and is closed.
-/
theorem isClosed_detachedLocus (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(T.strictTransform i)] :
    IsClosed (T.detachedLocus i) := by
  have hfinComp : (irreducibleComponents ↥(T.strictTransform i)).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hsub : T.detachedComponents i ⊆ irreducibleComponents ↥(T.strictTransform i) :=
    fun C hC => ((T.mem_detachedComponents i C).mp hC).1
  have hfin : (T.detachedComponents i).Finite := hfinComp.subset hsub
  rw [T.detachedLocus_eq_sUnion i, Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion fun C hC => isClosed_of_mem_irreducibleComponents _ (hsub hC)

def detachedClosure (i : ℕ) : TopologicalSpace.Closeds ↥(T.strictTransform i) :=
  ⟨closure (T.detachedLocus i), isClosed_closure⟩

/- English proof (authored)
The detached locus is already closed by Noetherianity and finiteness of the component family. Its closure therefore equals the locus itself.
-/
theorem detachedClosure_coe (i : ℕ)
    [TopologicalSpace.NoetherianSpace ↥(T.strictTransform i)] :
    (T.detachedClosure i : Set ↥(T.strictTransform i)) = T.detachedLocus i := by
  show closure (T.detachedLocus i) = T.detachedLocus i
  exact (T.isClosed_detachedLocus i).closure_eq

def detachedIdeal (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (T.detachedClosure i)

/- English proof (authored)
The detached ideal is the reduced vanishing ideal of the closure of the detached locus by definition.
-/
theorem detachedIdeal_eq (i : ℕ) :
    T.detachedIdeal i = Scheme.IdealSheafData.vanishingIdeal (T.detachedClosure i) := rfl

abbrev detachedScheme (i : ℕ) : Scheme.{u} := (T.detachedIdeal i).subscheme

abbrev detachedι (i : ℕ) : T.detachedScheme i ⟶ T.strictTransform i := (T.detachedIdeal i).subschemeι

def detachedClosureCompl (i : ℕ) : (T.strictTransform i).Opens := (T.detachedClosure i).compl

/- English proof (authored)
The open complement of the detached closure consists of all points outside the underlying closed set. This is exactly the set-theoretic complement on the right.
-/
theorem detachedClosureCompl_coe (i : ℕ) :
    ((T.detachedClosureCompl i : (T.strictTransform i).Opens) : Set ↥(T.strictTransform i)) =
      (T.detachedClosure i : Set ↥(T.strictTransform i))ᶜ := rfl

def comapAmbientCenter (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  (T.ambientCenter i).comap (T.strictTransformι i)

/- English proof (authored)
The center on the strict transform is defined by pulling the ambient center ideal back along the strict-transform inclusion.
-/
theorem comapAmbientCenter_eq (i : ℕ) :
    T.comapAmbientCenter i = (T.ambientCenter i).comap (T.strictTransformι i) := rfl

def centerOffDetached (i : ℕ) : (T.strictTransform i).IdealSheafData :=
  Scheme.Hom.ker
    (((T.comapAmbientCenter i).comap (T.detachedClosureCompl i).ι).subschemeι ≫ (T.detachedClosureCompl i).ι)

/- English proof (authored)
Restrict the pulled-back center ideal to the open complement of the detached closure. Take the inclusion of the resulting closed subscheme into that open, then include the open into the strict transform. The center off the detached locus is defined as the kernel ideal of this composite.
-/
theorem centerOffDetached_eq (i : ℕ) :
    T.centerOffDetached i =
      Scheme.Hom.ker
        (((T.comapAmbientCenter i).comap (T.detachedClosureCompl i).ι).subschemeι ≫
          (T.detachedClosureCompl i).ι) := rfl

def detachedCoprod (i : ℕ) : Scheme.{u} :=
  Nat.rec (motive := fun _ => Scheme.{u}) (⊥_ Scheme.{u})
    (fun j ih => ih ⨿ T.detachedScheme j) i

/- English proof (authored)
At the initial stage there are no detached schemes from earlier stages, so their coproduct is the initial, empty scheme.
-/
@[simp] theorem detachedCoprod_zero : T.detachedCoprod 0 = ⊥_ Scheme.{u} := rfl

/- English proof (authored)
At the successor, the recursive coproduct adds the scheme detached at the preceding stage to the coproduct of all schemes already detached.
-/
@[simp] theorem detachedCoprod_succ (i : ℕ) :
    T.detachedCoprod (i + 1) = (T.detachedCoprod i ⨿ T.detachedScheme i) := rfl

abbrev totalSpace (i : ℕ) : Scheme.{u} := T.strictTransform i ⨿ T.detachedCoprod i

def totalTransition (i : ℕ) : T.totalSpace (i + 1) ⟶ T.totalSpace i :=
  coprod.desc (T.strictTransformMap i ≫ coprod.inl)
    (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
        (T.detachedι i ≫ coprod.inl) :
      T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i)

/- English proof (authored)
The total transition is defined on the new strict-transform summand as the strict-transform transition followed by inclusion of the preceding strict-transform summand. The coproduct projection rule gives exactly this restriction of the total map.
-/
theorem inl_totalTransition_eq_strictTransformMap_inl (i : ℕ) :
    (coprod.inl : T.strictTransform (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      T.strictTransformMap i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) := by
  exact coprod.inl_desc (T.strictTransformMap i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i))
    (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
      (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
      T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i)

/- English proof (authored)
The old detached coproduct is the first summand of the enlarged detached coproduct, which is the second summand of the new total space. Restrict the new transition first to the enlarged detached coproduct and then to its first summand. The two coproduct identities give inclusion of the old detached coproduct in the preceding total space.
-/
theorem inl_inr_totalTransition (i : ℕ) :
    (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod (i + 1)) ≫
        (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i) := by
  have h : (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  exact Eq.trans
    (congrArg
      (fun f : T.detachedCoprod (i + 1) ⟶ T.totalSpace i =>
        (coprod.inl : T.detachedCoprod i ⟶ T.detachedCoprod (i + 1)) ≫ f) h)
    (coprod.inl_desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
      (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)))

/- English proof (authored)
The newly detached scheme is the second summand of the enlarged detached coproduct. Restrict the total transition to that coproduct and then to its second summand. By the defining coproduct identities the map goes through the newly detached scheme’s inclusion into the preceding strict transform and then into the preceding total space.
-/
theorem inr_inr_totalTransition (i : ℕ) :
    (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫
        (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) := by
  have h1 : (coprod.inr : T.detachedCoprod (i + 1) ⟶ T.totalSpace (i + 1)) ≫ T.totalTransition i =
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  have h2 : (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod i ⨿ T.detachedScheme i) ≫
      (coprod.desc (coprod.inr : T.detachedCoprod i ⟶ T.totalSpace i)
          (T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) :
        T.detachedCoprod i ⨿ T.detachedScheme i ⟶ T.totalSpace i) =
      T.detachedι i ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i) :=
    coprod.inr_desc _ _
  exact Eq.trans
    (congrArg
      (fun f : T.detachedCoprod (i + 1) ⟶ T.totalSpace i =>
        (coprod.inr : T.detachedScheme i ⟶ T.detachedCoprod (i + 1)) ≫ f) h1)
    h2

def totalCenter (i : ℕ) : (T.totalSpace i).IdealSheafData :=
  Scheme.Hom.ker
    ((T.centerOffDetached i).subschemeι ≫ (coprod.inl : T.strictTransform i ⟶ T.totalSpace i))

/- English proof (authored)
The total-space center is the closed subscheme given by the center off the detached locus in the strict-transform summand. Its ideal is defined as the kernel of the closed subscheme inclusion followed by that summand inclusion.
-/
theorem totalCenter_eq (i : ℕ) :
    T.totalCenter i =
      Scheme.Hom.ker
        ((T.centerOffDetached i).subschemeι ≫
          (coprod.inl : T.strictTransform i ⟶ T.totalSpace i)) := rfl

/- English proof (authored)
For a closed immersion, the induced morphism from the source to its scheme-theoretic image is an isomorphism. The image is the closed subscheme of the kernel ideal. Take the inverse isomorphism and use the image factorization to obtain the stated equation.
-/
private theorem exists_kerSubschemeIso_of_isClosedImmersion {X Z : Scheme.{u}} (g : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion g] :
    ∃ u : (Scheme.Hom.ker g).subscheme ≅ Z, u.hom ≫ g = (Scheme.Hom.ker g).subschemeι :=
  ⟨(asIso g.toImage).symm, by
    rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]⟩

/- English proof (authored)
Define the forward map on the first summand by the given isomorphism and on the initial summand by its unique map. The inverse is the inverse of the given isomorphism followed by the first inclusion. Their composite on the target is the identity by cancellation. In the other order the composite is the identity on the first summand by the same cancellation, and on the initial summand by uniqueness. The coproduct property gives the identity on the whole source.
-/
private theorem exists_coprodIso_of_isInitial {A B Z : Scheme.{u}}
    (hB : IsInitial B) (u : A ≅ Z) :
    ∃ e : (A ⨿ B) ≅ Z, (coprod.inl : A ⟶ A ⨿ B) ≫ e.hom = u.hom := by
  refine ⟨⟨coprod.desc u.hom (hB.to Z), u.inv ≫ coprod.inl, ?_, ?_⟩, coprod.inl_desc _ _⟩
  · refine coprod.hom_ext ?_ ?_
    · calc (coprod.inl : A ⟶ A ⨿ B) ≫ (coprod.desc u.hom (hB.to Z) ≫ (u.inv ≫ coprod.inl))
          = ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc u.hom (hB.to Z)) ≫
              (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) := (Category.assoc _ _ _).symm
        _ = u.hom ≫ (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) :=
            congrArg (fun t => t ≫ (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B))) (coprod.inl_desc _ _)
        _ = (u.hom ≫ u.inv) ≫ (coprod.inl : A ⟶ A ⨿ B) := (Category.assoc _ _ _).symm
        _ = 𝟙 A ≫ (coprod.inl : A ⟶ A ⨿ B) :=
            congrArg (fun t => t ≫ (coprod.inl : A ⟶ A ⨿ B)) u.hom_inv_id
        _ = (coprod.inl : A ⟶ A ⨿ B) := Category.id_comp _
        _ = (coprod.inl : A ⟶ A ⨿ B) ≫ 𝟙 (A ⨿ B) := (Category.comp_id _).symm
    · exact hB.hom_ext _ _
  · calc (u.inv ≫ (coprod.inl : A ⟶ A ⨿ B)) ≫ coprod.desc u.hom (hB.to Z)
        = u.inv ≫ ((coprod.inl : A ⟶ A ⨿ B) ≫ coprod.desc u.hom (hB.to Z)) :=
          Category.assoc _ _ _
      _ = u.inv ≫ u.hom := congrArg (fun t => u.inv ≫ t) (coprod.inl_desc _ _)
      _ = 𝟙 Z := u.inv_hom_id

/- English proof (authored)
The stage-zero strict transform is the kernel subscheme of the original closed immersion transported into the initial ambient stage. Its identification with the original scheme commutes with that immersion. The stage-zero detached coproduct is initial, so taking its coproduct with the strict transform preserves this identification and yields the required isomorphism of total spaces.
-/
theorem exists_totalSpaceZeroIso :
    ∃ e : T.totalSpace 0 ≅ Y,
      (coprod.inl : T.strictTransform 0 ⟶ T.totalSpace 0) ≫ e.hom ≫
          (T.emb ≫ T.ambientSeq.isoZero.inv) = T.strictTransformι 0 := by
  have : AlgebraicGeometry.IsClosedImmersion (T.emb ≫ T.ambientSeq.isoZero.inv) := inferInstance
  obtain ⟨u, hu⟩ := exists_kerSubschemeIso_of_isClosedImmersion
    (T.emb ≫ T.ambientSeq.isoZero.inv)
  have hB : IsInitial (T.detachedCoprod 0) := initialIsInitial
  obtain ⟨e, he⟩ :=
    exists_coprodIso_of_isInitial (A := T.strictTransform 0) (B := T.detachedCoprod 0) (Z := Y) hB u
  refine ⟨e, ?_⟩
  refine Eq.trans ?_ hu
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact congrArg (fun t => t ≫ (T.emb ≫ T.ambientSeq.isoZero.inv)) he

def totalSpaceZeroIso : T.totalSpace 0 ≅ Y := T.exists_totalSpaceZeroIso.choose

/- English proof (authored)
The chosen stage-zero isomorphism satisfies the compatibility equation from its construction. Restricting it to the strict-transform summand and then applying the original embedding transported to the initial ambient stage gives the stage-zero strict-transform inclusion.
-/
theorem totalSpaceZeroIso_spec :
    (coprod.inl : T.strictTransform 0 ⟶ T.totalSpace 0) ≫ T.totalSpaceZeroIso.hom ≫
        (T.emb ≫ T.ambientSeq.isoZero.inv) = T.strictTransformι 0 :=
  T.exists_totalSpaceZeroIso.choose_spec

def totalTower : ℕᵒᵖ ⥤ Scheme.{u} :=
  (Functor.ofSequence (fun i => (T.totalTransition i).op)).leftOp

/- English proof (authored)
The tower is built from the sequence of total transitions. Its object at the given index is the total space from which those transitions are formed.
-/
theorem totalTower_obj (i : ℕ) : T.totalTower.obj (Opposite.op i) = T.totalSpace i := rfl

/- English proof (authored)
The functor constructed from consecutive transitions sends each successor order arrow to its specified consecutive map in the opposite category. Passing back to the original category gives the given total transition.
-/
theorem totalTower_map_succ (i : ℕ) :
    T.totalTower.map (homOfLE (Nat.le_succ i)).op = T.totalTransition i := by
  show ((Functor.ofSequence (fun j => (T.totalTransition j).op)).map
      (homOfLE (Nat.le_succ i))).unop = T.totalTransition i
  rw [Functor.ofSequence_map_homOfLE_succ]
  rfl

def TransitionsAreBlowups : Prop :=
  ∀ i, i < T.length → Blowup.IsBlowupAlongIdealSheaf (T.totalTower.map (homOfLE (Nat.le_succ i)).op) (T.totalCenter i)

def inducedBlowups (h : T.TransitionsAreBlowups) : SequenceOfBlowups Y where
  length := T.length
  tower := T.totalTower
  isoZero := T.totalSpaceZeroIso
  center := T.totalCenter
  isBlowup := h

/- English proof (authored)
The induced sequence is constructed with one step per ambient stage before the end, so its length is assigned the ambient sequence length.
-/
@[simp] theorem inducedBlowups_length (h : T.TransitionsAreBlowups) : (T.inducedBlowups h).length = T.length := rfl

/- English proof (authored)
The induced sequence is built with the tower of total spaces and total transitions as its underlying functor.
-/
@[simp] theorem inducedBlowups_tower (h : T.TransitionsAreBlowups) : (T.inducedBlowups h).tower = T.totalTower := rfl

/- English proof (authored)
The initial object of the induced blowup sequence is identified with the original scheme using the chosen stage-zero isomorphism of total spaces.
-/
theorem inducedBlowups_isoObjZero (h : T.TransitionsAreBlowups) : (T.inducedBlowups h).isoZero = T.totalSpaceZeroIso := rfl

/- English proof (authored)
At every stage the induced sequence is assigned the total-space center, which is supported on the strict-transform summand.
-/
@[simp] theorem inducedBlowups_center (h : T.TransitionsAreBlowups) (i : ℕ) :
    (T.inducedBlowups h).center i = T.totalCenter i := rfl

def inducedBlowupsWithoutIso (h : T.TransitionsAreBlowups) : SequenceOfBlowups Y := (T.inducedBlowups h).withoutIsoBlowups

end EmbeddedBlowupSequence

/- English proof (authored)
The structure map of finite-dimensional affine space is induced by the inclusion of the field in a finitely generated polynomial algebra. It is therefore locally of finite type.
-/
private theorem locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift (k : Type u) [Field k] (n : ℕ) :
    AlgebraicGeometry.LocallyOfFiniteType (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

/- English proof (authored)
Finite-dimensional affine space is affine and its morphism to the field spectrum is an affine morphism. Such a morphism is quasi-compact.
-/
private theorem quasiCompact_affineSpaceIndexedByToSpec_ulift (k : Type u) [Field k] (n : ℕ) :
    AlgebraicGeometry.QuasiCompact (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n))) := by
  unfold affineSpaceIndexedByToSpec
  infer_instance

namespace AffineSpacePrincipalizationData

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

def toEmbeddedBlowupSequence (S : AffineSpacePrincipalizationData k Y pY) : EmbeddedBlowupSequence k Y pY where
  ambient := S.ambient
  ambientStruct := S.ambientToSpec
  isAffine_ambient := inferInstance
  smooth_ambientStruct := S.ambient_smooth
  locallyOfFiniteType_ambientStruct := locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift k S.dim
  quasiCompact_ambientStruct := quasiCompact_affineSpaceIndexedByToSpec_ulift k S.dim
  emb := S.emb
  isClosedImmersion_emb := S.emb_closedImmersion
  emb_comp := S.emb_comp
  ambientSeq := S.ambientBlowups

/- English proof (authored)
When the affine-space principalization data are viewed as an embedded blowup sequence, the original affine ambient scheme is assigned directly as its ambient scheme.
-/
theorem toEmbeddedBlowupSequence_ambient (S : AffineSpacePrincipalizationData k Y pY) :
    S.toEmbeddedBlowupSequence.ambient = S.ambient := rfl

/- English proof (authored)
The conversion from affine-space principalization data uses the original closed immersion into the chosen affine ambient space as the embedding of the sequence.
-/
theorem toEmbeddedBlowupSequence_emb (S : AffineSpacePrincipalizationData k Y pY) :
    S.toEmbeddedBlowupSequence.emb = S.emb := rfl

/- English proof (authored)
The ambient tower of the converted sequence is the ambient blowup sequence supplied by the affine-space principalization data.
-/
theorem embeddedAmbientBlowups_eq (S : AffineSpacePrincipalizationData k Y pY) :
    S.toEmbeddedBlowupSequence.ambientSeq = S.ambientBlowups := rfl

/- English proof (authored)
The ambient blowup sequence is unchanged in the construction from affine-space data. Its scheme at the given stage is the ambient level of those data.
-/
theorem toEmbeddedBlowupSequence_schemeAt (S : AffineSpacePrincipalizationData k Y pY) (i : ℕ) :
    S.toEmbeddedBlowupSequence.schemeAt i = S.ambientLevel i := rfl

/- English proof (authored)
Both constructions begin with the same embedding kernel transported to stage zero and take strict transforms under the same ambient blowdowns and centers. The recursive strict-transform ideals therefore agree at the specified stage.
-/
theorem toEmbeddedBlowupSequence_strictTransformIdeal (S : AffineSpacePrincipalizationData k Y pY) (i : ℕ) :
    S.toEmbeddedBlowupSequence.strictTransformIdeal i = S.strictTransformIdeal i := rfl

/- English proof (authored)
The two descriptions use the same total-space transition maps and the same total-space center ideals at each stage. Thus the assertion that each transition is the blowup along its center is identical in both.
-/
theorem toEmbeddedBlowupSequence_transitionsAreBlowups_iff (S : AffineSpacePrincipalizationData k Y pY) :
    S.toEmbeddedBlowupSequence.TransitionsAreBlowups ↔ S.TransitionsAreBlowups := Iff.rfl

/- English proof (authored)
The two induced sequences use the same length, total-space tower, initial isomorphism, and centers. Their blowup certificates establish the same propositions and do not affect the sequence data. Hence the sequences agree.
-/
theorem embeddedInducedBlowups_eq (S : AffineSpacePrincipalizationData k Y pY) (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowups ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h) = S.blowupSequence h := rfl

/- English proof (authored)
The unshortened induced sequences agree by the preceding comparison. Apply the operation that removes unit-center blowups to both sequences to obtain equality after shortening.
-/
theorem embeddedInducedBlowupsWithoutIso_eq (S : AffineSpacePrincipalizationData k Y pY) (h : S.TransitionsAreBlowups) :
    S.toEmbeddedBlowupSequence.inducedBlowupsWithoutIso ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h) = S.blowupSequenceWithoutIsos h := by
  show (S.toEmbeddedBlowupSequence.inducedBlowups ((toEmbeddedBlowupSequence_transitionsAreBlowups_iff S).mpr h)).withoutIsoBlowups
      = (S.blowupSequence h).withoutIsoBlowups
  exact congrArg SequenceOfBlowups.withoutIsoBlowups (embeddedInducedBlowups_eq S h)

end AffineSpacePrincipalizationData

namespace EmbeddingDatum

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]

def toEmbeddedBlowupSequence (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) : EmbeddedBlowupSequence k Y pY where
  ambient := D.ambient
  ambientStruct := D.ambientStruct
  isAffine_ambient := D.isAffine_ambient
  smooth_ambientStruct := D.smooth_ambientStruct
  locallyOfFiniteType_ambientStruct := D.locallyOfFiniteType_ambientStruct
  quasiCompact_ambientStruct := D.quasiCompact_ambientStruct
  emb := D.emb
  isClosedImmersion_emb := D.isClosedImmersion_emb
  emb_comp := D.comp_eq
  ambientSeq :=
    (A k D.ambient D.ambientStruct (Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker
      ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups

/- English proof (authored)
The construction from an embedding datum takes the smooth ambient scheme specified by that datum and uses it as the ambient scheme of the embedded blowup sequence.
-/
theorem toEmbeddedBlowupSequence_ambient (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    (D.toEmbeddedBlowupSequence A).ambient = D.ambient := rfl

/- English proof (authored)
The construction retains the given closed immersion from the original affine scheme into the ambient scheme as its embedding.
-/
theorem toEmbeddedBlowupSequence_emb (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    (D.toEmbeddedBlowupSequence A).emb = D.emb := rfl

/- English proof (authored)
The construction assigns the ambient sequence by running principalization on the kernel ideal of the given embedding, with the empty boundary and the specified nonvanishing condition. Its underlying blowup sequence is the stated ambient tower.
-/
theorem ambientBlowups_eq_toSequenceOfBlowups (D : EmbeddingDatum k Y pY) (A : PrincipalizationAlgorithm.{u}) :
    (D.toEmbeddedBlowupSequence A).ambientSeq =
      (A k D.ambient D.ambientStruct (Scheme.Hom.ker D.emb) D.nonzeroOnComponents_ker
        ([] : List D.ambient.IdealSheafData) D.sncEmpty).toSequenceOfBlowups := rfl

end EmbeddingDatum

def TransitionsAreBlowupsForEmbeddings (A : PrincipalizationAlgorithm.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y pY),
    (D.toEmbeddedBlowupSequence A).TransitionsAreBlowups

def embeddedResolutionRuleOfPrincipalization (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A) : EmbeddedResolutionRule.{u} := by
  intro k _ _ Y pY _ _ _ _ D
  exact (D.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso (h k Y pY D)

/- English proof (authored)
By definition the embedded resolution rule constructs the embedded sequence from the given datum and then takes its induced blowups with the isomorphism steps removed.
-/
theorem embeddedResolutionRuleOfPrincipalization_apply (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (D : EmbeddingDatum k Y pY) :
    embeddedResolutionRuleOfPrincipalization A h k Y pY D = (D.toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso (h k Y pY D) := rfl

def affineSpaceEmbeddingDatum (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    EmbeddingDatum k Y pY where
  ambient := affineSpaceIndexedBy k (ULift.{u} (Fin (hemb k Y pY).choose))
  ambientStruct := affineSpaceIndexedByToSpec k (ULift.{u} (Fin (hemb k Y pY).choose))
  emb := (hemb k Y pY).choose_spec.choose
  isAffine_ambient := inferInstance
  smooth_ambientStruct := hsm k ((hemb k Y pY).choose)
  locallyOfFiniteType_ambientStruct :=
    locallyOfFiniteType_affineSpaceIndexedByToSpec_ulift k ((hemb k Y pY).choose)
  quasiCompact_ambientStruct :=
    quasiCompact_affineSpaceIndexedByToSpec_ulift k ((hemb k Y pY).choose)
  isClosedImmersion_emb := (hemb k Y pY).choose_spec.choose_spec.1
  nonzeroOnComponents_ker := (hemb k Y pY).choose_spec.choose_spec.2.1
  comp_eq := (hemb k Y pY).choose_spec.choose_spec.2.2
  sncEmpty := hsnc k ((hemb k Y pY).choose)

/- English proof (authored)
Both constructions use the same closed embedding into the chosen affine space, the same structural map, and the same principalization of the embedding kernel with empty boundary. The resulting embedded blowup sequences agree.
-/
theorem affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A =
      (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence := rfl

def affineSpaceEmbeddingChoice (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    EmbeddingChoice.{u} := by
  intro k _ _ Y pY _ _ _ _
  exact affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY

/- English proof (authored)
The embedding choice assigns to each affine input exactly the datum obtained from the chosen embedding into affine space and its ambient smoothness and empty-boundary properties.
-/
theorem affineSpaceEmbeddingChoice_eq_affineSpaceEmbeddingDatum (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    affineSpaceEmbeddingChoice hemb hsnc hsm k Y pY = affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY := rfl

/- English proof (authored)
Expand the embedded rule as the shortened induced sequence for the chosen embedding datum. The embedded sequence for this datum agrees with the one obtained from the affine-space principalization data. The comparison identifies their shortened induced sequences, since the proofs that transitions are blowups do not change the underlying data. The latter sequence is exactly the affine resolution rule on the given input.
-/
theorem embeddedResolutionRuleOfPrincipalization_affineSpaceEmbeddingDatum (A : PrincipalizationAlgorithm.{u}) (h : TransitionsAreBlowupsForEmbeddings A)
    (hemb : AffineEmbedsIntoAffineSpace.{u}) (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u})
    (hsm : AffineSpaceIsSmooth.{u}) (hw : EmbeddedPrincipalizationYieldsBlowups A hemb hsnc hsm)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY]
    [AlgebraicGeometry.QuasiCompact pY] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    embeddedResolutionRuleOfPrincipalization A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) =
      affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw k Y pY := by
  have hT := affineSpaceEmbeddingDatum_toEmbeddedBlowupSequence A hemb hsnc hsm k Y pY
  have key : ∀ (T₁ T₂ : EmbeddedBlowupSequence k Y pY), T₁ = T₂ →
      ∀ (h₁ : T₁.TransitionsAreBlowups) (h₂ : T₂.TransitionsAreBlowups),
        T₁.inducedBlowupsWithoutIso h₁ = T₂.inducedBlowupsWithoutIso h₂ := by
    rintro T₁ T₂ rfl h₁ h₂
    rfl
  calc embeddedResolutionRuleOfPrincipalization A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)
      = ((affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence A).inducedBlowupsWithoutIso
          (h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)) :=
        embeddedResolutionRuleOfPrincipalization_apply A h k Y pY (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY)
    _ = ((AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).toEmbeddedBlowupSequence).inducedBlowupsWithoutIso
          ((AffineSpacePrincipalizationData.toEmbeddedBlowupSequence_transitionsAreBlowups_iff
            (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)).mpr (hw k Y pY)) :=
        key _ _ hT _ _
    _ = (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY).blowupSequenceWithoutIsos (hw k Y pY) :=
        AffineSpacePrincipalizationData.embeddedInducedBlowupsWithoutIso_eq (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)
          (hw k Y pY)
    _ = affineResolutionRuleOfPrincipalization A hemb hsnc hsm hw k Y pY := rfl

end FunctorialResolution.EmbeddedResolution

end
