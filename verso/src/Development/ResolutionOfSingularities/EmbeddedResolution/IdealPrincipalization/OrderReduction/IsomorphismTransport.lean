import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `: IsIso (Limits.pullback.snd f I.subschemeι)` using `(IsPullback.of_hasPullback f I.subschemeι).flip.isIso_fst_of_isIso`. Establish `hw : Limits.pullback.fst f I.subschemeι = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ inv f`. Rewrite using `[← Category.assoc, ← Limits.pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]`. Unfold `AlgebraicGeometry.Scheme.IdealSheafData.comap`. Rewrite using `[hw, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]`.
-/
private theorem comap_eq_ker_subschemeι_comp_inv {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (I : B.IdealSheafData) :
    I.comap f = (I.subschemeι ≫ inv f).ker := by
  have : IsIso (Limits.pullback.snd f I.subschemeι) :=
    (IsPullback.of_hasPullback f I.subschemeι).flip.isIso_fst_of_isIso
  have hw : Limits.pullback.fst f I.subschemeι
      = Limits.pullback.snd f I.subschemeι ≫ I.subschemeι ≫ inv f := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  unfold AlgebraicGeometry.Scheme.IdealSheafData.comap
  rw [hw, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

/- English proof (translation)
Rewrite using `[imageIdealSheaf_eq_ker, comap_eq_ker_subschemeι_comp_inv (inv f) J, IsIso.inv_inv]`.
-/
theorem imageIdealSheaf_eq_comap_inv {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    imageIdealSheaf f J = J.comap (inv f) := by
  rw [imageIdealSheaf_eq_ker, comap_eq_ker_subschemeι_comp_inv (inv f) J, IsIso.inv_inv]

/- English proof (translation)
Rewrite using `[imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
theorem imageIdealSheaf_comap {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (I : B.IdealSheafData) :
    imageIdealSheaf f (I.comap f) = I := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (translation)
Rewrite using `[imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, IsIso.hom_inv_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]`.
-/
theorem comap_imageIdealSheaf {A B : Scheme.{u}} (f : A ⟶ B) [IsIso f]
    (J : A.IdealSheafData) :
    (imageIdealSheaf f J).comap f = J := by
  rw [imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
    IsIso.hom_inv_id, AlgebraicGeometry.Scheme.IdealSheafData.comap_id]

/- English proof (translation)
Rewrite using `[imageIdealSheaf_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_comp, AlgebraicGeometry.Scheme.Hom.ker_comp, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]`.
-/
theorem ker_comp_eq_imageIdealSheaf_ker {W A B : Scheme.{u}} (g : W ⟶ A) (w : A ⟶ B) :
    (g ≫ w).ker = imageIdealSheaf w g.ker := by
  rw [imageIdealSheaf_eq_ker, AlgebraicGeometry.Scheme.Hom.ker_comp,
    AlgebraicGeometry.Scheme.Hom.ker_comp, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]

/- English proof (translation)
Establish `e1 : ((I.comap w).subschemeι ≫ w).ker = I`. Rewrite using `[ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, imageIdealSheaf_comap]`. Establish `e2 : (I.subschemeι ≫ inv w).ker = I.comap w`. Rewrite using `[ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι, imageIdealSheaf_eq_comap_inv, IsIso.inv_inv]`. Establish `h1 : I.subschemeι.ker ≤ ((I.comap w).subschemeι ≫ w).ker` using `le_of_eq (by rw [e1, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])`.

Establish `h2 : (I.comap w).subschemeι.ker ≤ (I.subschemeι ≫ inv w).ker` using `le_of_eq (by rw [e2, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])`. Use `⟨⟨IsClosedImmersion.lift I.subschemeι ((I.comap w).subschemeι ≫ w) h1, IsClosedImmersion.lift (I.comap w).subschemeι (I.subschemeι ≫ inv w) h2, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono (I.comap w).subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.hom_inv_id, Category.comp_id, Category.id_comp]`. Rewrite using `[← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac, ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.id_comp]`. Conclude with `IsClosedImmersion.lift_fac ..`.
-/
private theorem exists_iso_subscheme_comap_of_isIso {A B : Scheme.{u}} (w : A ⟶ B) [IsIso w]
    (I : B.IdealSheafData) :
    ∃ θ : (I.comap w).subscheme ≅ I.subscheme,
      θ.hom ≫ I.subschemeι = (I.comap w).subschemeι ≫ w := by
  have e1 : ((I.comap w).subschemeι ≫ w).ker = I := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_comap]
  have e2 : (I.subschemeι ≫ inv w).ker = I.comap w := by
    rw [ker_comp_eq_imageIdealSheaf_ker, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι,
      imageIdealSheaf_eq_comap_inv, IsIso.inv_inv]
  have h1 : I.subschemeι.ker ≤ ((I.comap w).subschemeι ≫ w).ker :=
    le_of_eq (by rw [e1, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  have h2 : (I.comap w).subschemeι.ker ≤ (I.subschemeι ≫ inv w).ker :=
    le_of_eq (by rw [e2, AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι])
  refine ⟨⟨IsClosedImmersion.lift I.subschemeι ((I.comap w).subschemeι ≫ w) h1,
    IsClosedImmersion.lift (I.comap w).subschemeι (I.subschemeι ≫ inv w) h2, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono (I.comap w).subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id, Category.id_comp]
  · rw [← cancel_mono I.subschemeι, Category.assoc, IsClosedImmersion.lift_fac,
      ← Category.assoc, IsClosedImmersion.lift_fac, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · exact IsClosedImmersion.lift_fac ..

/- English proof (translation)
Take `⟨θ, hθ⟩` from `exists_iso_subscheme_comap_of_isIso w I`. Rewrite using `[imageIdealSheaf_eq_ker (w ≫ g) (I.comap w), imageIdealSheaf_eq_ker g I, ← Category.assoc, ← hθ, Category.assoc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]`.
-/
theorem imageIdealSheaf_comp_comap_of_isIso {A B C : Scheme.{u}} (w : A ⟶ B) [IsIso w] (g : B ⟶ C)
    (I : B.IdealSheafData) :
    imageIdealSheaf (w ≫ g) (I.comap w) = imageIdealSheaf g I := by
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso w I
  rw [imageIdealSheaf_eq_ker (w ≫ g) (I.comap w), imageIdealSheaf_eq_ker g I, ← Category.assoc, ← hθ,
    Category.assoc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

/- English proof (translation)
Use extensionality with `x`. Simplify using `[AlgebraicGeometry.Scheme.IdealSheafData.support_comap]`.
-/
private theorem compl_support_comap {A B : Scheme.{u}} (v : A ⟶ B) (I : B.IdealSheafData) :
    (I.comap v).support.compl = (TopologicalSpace.Opens.map v.base).obj I.support.compl := by
  ext x
  simp [AlgebraicGeometry.Scheme.IdealSheafData.support_comap]

/- English proof (translation)
Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
private theorem opens_map_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C) (U : C.Opens) :
    (TopologicalSpace.Opens.map (f ≫ g).base).obj U
      = (TopologicalSpace.Opens.map f.base).obj ((TopologicalSpace.Opens.map g.base).obj U) := by
  ext x
  simp

/- English proof (translation)
Use extensionality with `x`. Conclude with `Iff.rfl`.
-/
private theorem opens_map_id {B : Scheme.{u}} (W : B.Opens) :
    (TopologicalSpace.Opens.map (𝟙 B : B ⟶ B).base).obj W = W := by
  ext x
  exact Iff.rfl

/- English proof (translation)
Establish `hcomp : (TopologicalSpace.Opens.map θ.inv.base).obj V' = (TopologicalSpace.Opens.map (θ.inv ≫ θ.hom).base).obj V`. Rewrite using `[hVV', opens_map_comp]`. Establish `hle : V ≤ (TopologicalSpace.Opens.map θ.inv.base).obj V'` using `le_of_eq (by rw [hcomp, Iso.inv_hom_id, opens_map_id])`. Use `⟨⟨Scheme.Hom.resLE θ.hom V V' (le_of_eq hVV'), Scheme.Hom.resLE θ.inv V' V hle, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← cancel_mono V'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]`.

Rewrite using `[← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]`. Conclude with `Scheme.Hom.resLE_comp_ι ..`.
-/
private theorem exists_iso_opens_preimage {A B : Scheme.{u}} (θ : A ≅ B) (V' : A.Opens) (V : B.Opens)
    (hVV' : V' = (TopologicalSpace.Opens.map θ.hom.base).obj V) :
    ∃ c : (↑V' : Scheme.{u}) ≅ (↑V : Scheme.{u}), c.hom ≫ V.ι = V'.ι ≫ θ.hom := by
  have hcomp : (TopologicalSpace.Opens.map θ.inv.base).obj V'
      = (TopologicalSpace.Opens.map (θ.inv ≫ θ.hom).base).obj V := by
    rw [hVV', opens_map_comp]
  have hle : V ≤ (TopologicalSpace.Opens.map θ.inv.base).obj V' :=
    le_of_eq (by rw [hcomp, Iso.inv_hom_id, opens_map_id])
  refine ⟨⟨Scheme.Hom.resLE θ.hom V V' (le_of_eq hVV'),
    Scheme.Hom.resLE θ.inv V' V hle, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono V'.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← cancel_mono V.ι, Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · exact Scheme.Hom.resLE_comp_ι ..

/- English proof (translation)
Rewrite using `[← hc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]`.
-/
private theorem ker_eq_of_iso_comp {P Q T : Scheme.{u}} (c : Q ≅ P) (h₁ : P ⟶ T) (h₂ : Q ⟶ T)
    (hc : c.hom ≫ h₁ = h₂) : h₁.ker = h₂.ker := by
  rw [← hc, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]

/- English proof (translation)
Establish `hψ : ψ = inv u₁ ≫ φ ≫ u`. Rewrite using `[← hsq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]`. Establish `hmaps : ψ ≫ inv u = inv u₁ ≫ φ`. Rewrite using `[hψ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]`. Establish `hcm : ∀ I : X.IdealSheafData, (imageIdealSheaf u I).comap ψ = (I.comap φ).comap (inv u₁)`.

Introduce `I`. Rewrite using `[imageIdealSheaf_eq_comap_inv, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hmaps]`. Take `⟨θ, hθ⟩` from `exists_iso_subscheme_comap_of_isIso (inv u₁) (D.comap φ)`. Establish `hVV' : (TopologicalSpace.Opens.map ((D.comap φ).comap (inv u₁)).subschemeι.base).obj ((Z.comap φ).comap (inv u₁)).support.compl = (TopologicalSpace.Opens.map θ.hom.base).obj ((TopologicalSpace.Opens.map (D.comap φ).subschemeι.base).obj (Z.comap φ).support.compl)`. Rewrite using `[compl_support_comap, ← opens_map_comp, ← opens_map_comp, hθ]`.

Take `⟨c, hc⟩` from `exists_iso_opens_preimage θ _ _ hVV'`. Rewrite using `[Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq, Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq, hcm Z, hcm D, ← ker_comp_eq_imageIdealSheaf_ker]`. Use `ker_eq_of_iso_comp c _ _ ?_` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Rewrite using `[← Category.assoc c.hom, hc, Category.assoc, reassoc_of% hθ]`.

Simplify using the standard rewrite rules.
-/
theorem imageIdealSheaf_strictTransform_of_comm_sq {X X₁ Y Y₁ : Scheme.{u}}
    (φ : X₁ ⟶ X) (ψ : Y₁ ⟶ Y) (u : X ⟶ Y) (u₁ : X₁ ⟶ Y₁) [IsIso u] [IsIso u₁]
    (hsq : u₁ ≫ ψ = φ ≫ u) (Z D : X.IdealSheafData) :
    imageIdealSheaf u₁ (Blowup.strictTransform φ Z D)
      = Blowup.strictTransform ψ (imageIdealSheaf u Z) (imageIdealSheaf u D) := by
  have hψ : ψ = inv u₁ ≫ φ ≫ u := by
    rw [← hsq, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  have hmaps : ψ ≫ inv u = inv u₁ ≫ φ := by
    rw [hψ, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcm : ∀ I : X.IdealSheafData,
      (imageIdealSheaf u I).comap ψ = (I.comap φ).comap (inv u₁) := by
    intro I
    rw [imageIdealSheaf_eq_comap_inv,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      ← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hmaps]
  obtain ⟨θ, hθ⟩ := exists_iso_subscheme_comap_of_isIso (inv u₁) (D.comap φ)
  have hVV' : (TopologicalSpace.Opens.map ((D.comap φ).comap (inv u₁)).subschemeι.base).obj
        ((Z.comap φ).comap (inv u₁)).support.compl
      = (TopologicalSpace.Opens.map θ.hom.base).obj
        ((TopologicalSpace.Opens.map (D.comap φ).subschemeι.base).obj
          (Z.comap φ).support.compl) := by
    rw [compl_support_comap, ← opens_map_comp, ← opens_map_comp, hθ]
  obtain ⟨c, hc⟩ := exists_iso_opens_preimage θ _ _ hVV'
  rw [Blowup.strictTransform_eq_ker, Blowup.strictTransform_eq_ker, Blowup.strictTransformImmersion_eq,
    Blowup.strictTransformImmersion_eq, Blowup.strictTransformOpens_eq, Blowup.strictTransformOpens_eq,
    hcm Z, hcm D, ← ker_comp_eq_imageIdealSheaf_ker]
  refine ker_eq_of_iso_comp c _ _ ?_
  simp only [Category.assoc]
  rw [← Category.assoc c.hom, hc, Category.assoc, reassoc_of% hθ]
  simp

namespace IsPushforwardBlowupSeq

/- English proof (translation)
Take `⟨hlen, σ, hci, h0, hstep, hcent, hker⟩` from `h`. Take `⟨hlen2, e, he0, hestep, hecent⟩` from `he`. Establish `hestep' : ∀ (i : ℕ) (hp : i + 1 ≤ B.length) (hq : i ≤ B.length), (e (i + 1) hp).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hq).hom` using `fun i hp _ => hestep i hp`. Establish `hecent' : ∀ (i : ℕ) (hp : i < B.length) (hq : i ≤ B.length), (B'.center i).comap (e i hq).hom = B.center i` using `fun i hp _ => hecent i hp`. Use `⟨by omega, fun i hi => σ i hi ≫ (e i (by omega)).hom, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Use `hci i hi` as an intermediate fact. Use `infer_instance`. Establish `hgoal : (σ 0 (Nat.zero_le _) ≫ (e 0 (Nat.zero_le _)).hom) ≫ B'.isoZero.hom = BS.isoZero.hom ≫ j`. Rewrite using `[Category.assoc, he0, h0]`.

Conclude with `hgoal`. Introduce `i hi`. Establish `hiB : i < B.length` using `by omega`. Establish `hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom) ≫ B'.transitionMapSucc i = BS.transitionMapSucc i ≫ (σ i hi.le ≫ (e i hiB.le).hom)`. Rewrite using `[Category.assoc, hestep' i hiB hiB.le, ← Category.assoc, hstep i hi, Category.assoc]`.

Conclude with `hgoal`. Introduce `i hi`. Establish `hiB : i < B.length` using `by omega`. Establish `hgoal : imageIdealSheaf (σ i hi.le ≫ (e i hiB.le).hom) (BS.center i) = B'.center i`. Rewrite using `[imageIdealSheaf_comp, ← hcent i hi, ← hecent' i hiB hiB.le, imageIdealSheaf_comap]`.

Conclude with `hgoal.symm`. Introduce `i hi`. Establish `hiB : i < B.length` using `by omega`. Establish `hcen : imageIdealSheaf (e i hiB.le).hom (B.center i) = B'.center i`. Rewrite using `[← hecent' i hiB hiB.le, imageIdealSheaf_comap]`.

Establish `hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom).ker = Blowup.strictTransform (B'.transitionMapSucc i) (B'.center i) ((σ i hi.le ≫ (e i hiB.le).hom).ker)`. Rewrite using `[ker_comp_eq_imageIdealSheaf_ker, hker i hi, imageIdealSheaf_strictTransform_of_comm_sq (B.transitionMapSucc i) (B'.transitionMapSucc i) (e i hiB.le).hom (e (i + 1) hiB).hom (hestep' i hiB hiB.le) (B.center i) ((σ i hi.le).ker), hcen, ker_comp_eq_imageIdealSheaf_ker]`. Conclude with `hgoal`.
-/
theorem of_isomorphic {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    {BS : SequenceOfBlowups S} {B B' : SequenceOfBlowups X}
    (h : IsPushforwardBlowupSeq j BS B) (he : B.Isomorphic B') :
    IsPushforwardBlowupSeq j BS B' := by
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  obtain ⟨hlen2, e, he0, hestep, hecent⟩ := he
  have hestep' : ∀ (i : ℕ) (hp : i + 1 ≤ B.length) (hq : i ≤ B.length),
      (e (i + 1) hp).hom ≫ B'.transitionMapSucc i = B.transitionMapSucc i ≫ (e i hq).hom :=
    fun i hp _ => hestep i hp
  have hecent' : ∀ (i : ℕ) (hp : i < B.length) (hq : i ≤ B.length),
      (B'.center i).comap (e i hq).hom = B.center i := fun i hp _ => hecent i hp
  refine ⟨by omega, fun i hi => σ i hi ≫ (e i (by omega)).hom, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hci i hi
    infer_instance
  · have hgoal : (σ 0 (Nat.zero_le _) ≫ (e 0 (Nat.zero_le _)).hom) ≫ B'.isoZero.hom
        = BS.isoZero.hom ≫ j := by
      rw [Category.assoc, he0, h0]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom) ≫ B'.transitionMapSucc i
        = BS.transitionMapSucc i ≫ (σ i hi.le ≫ (e i hiB.le).hom) := by
      rw [Category.assoc, hestep' i hiB hiB.le, ← Category.assoc, hstep i hi, Category.assoc]
    exact hgoal
  · intro i hi
    have hiB : i < B.length := by omega
    have hgoal : imageIdealSheaf (σ i hi.le ≫ (e i hiB.le).hom) (BS.center i) = B'.center i := by
      rw [imageIdealSheaf_comp, ← hcent i hi, ← hecent' i hiB hiB.le,
        imageIdealSheaf_comap]
    exact hgoal.symm
  · intro i hi
    have hiB : i < B.length := by omega
    have hcen : imageIdealSheaf (e i hiB.le).hom (B.center i) = B'.center i := by
      rw [← hecent' i hiB hiB.le, imageIdealSheaf_comap]
    have hgoal : (σ (i + 1) hi ≫ (e (i + 1) hiB).hom).ker
        = Blowup.strictTransform (B'.transitionMapSucc i) (B'.center i)
            ((σ i hi.le ≫ (e i hiB.le).hom).ker) := by
      rw [ker_comp_eq_imageIdealSheaf_ker, hker i hi,
        imageIdealSheaf_strictTransform_of_comm_sq (B.transitionMapSucc i) (B'.transitionMapSucc i)
          (e i hiB.le).hom (e (i + 1) hiB).hom (hestep' i hiB hiB.le) (B.center i)
          ((σ i hi.le).ker),
        hcen, ker_comp_eq_imageIdealSheaf_ker]
    exact hgoal

/- English proof (translation)
Take `⟨hlen2, τ, hτ0, hτsq, hτcent⟩` from `hpb`. Take `⟨hlen, σ, hci, h0, hstep, hcent, hker⟩` from `h`. Establish `hτ0' : ∀ hp : (0 : ℕ) ≤ BS'.length, τ 0 hp ≫ BS.isoZero.hom = BS'.isoZero.hom ≫ e` using `fun _ => hτ0`. Establish `hiso : ∀ (i : ℕ) (hi : i ≤ BS'.length), IsIso (τ i hi)`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero`. Introduce `hi`. Establish `hzz : τ 0 hi = BS'.isoZero.hom ≫ e ≫ BS.isoZero.inv`. Rewrite using `[← Category.assoc, ← hτ0' hi]`.

Simplify using the standard rewrite rules. Rewrite using `[hzz]`. Use `infer_instance`. Consider the case `succ n ih`. Introduce `hi`.

Establish `hn : n < BS'.length` using `by omega`. Use `ih (by omega)` as an intermediate fact. Conclude with `(hτsq n hn).isIso_fst_of_isIso`. Use `⟨by omega, fun i hi => τ i hi ≫ σ i (by omega), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`.

Use `hiso i hi` as an intermediate fact. Use `hci i (by omega)` as an intermediate fact. Use `infer_instance`. Establish `hgoal : (τ 0 (Nat.zero_le _) ≫ σ 0 (Nat.zero_le _)) ≫ B.isoZero.hom = BS'.isoZero.hom ≫ j'`. Rewrite using `[hj, Category.assoc, h0, ← Category.assoc, hτ0, Category.assoc]`.

Conclude with `hgoal`. Introduce `i hi`. Establish `hiS : i < BS.length` using `by omega`. Establish `hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS) ≫ B.transitionMapSucc i = BS'.transitionMapSucc i ≫ (τ i hi.le ≫ σ i hiS.le)`. Rewrite using `[Category.assoc, hstep i hiS, ← Category.assoc, (hτsq i hi).w, Category.assoc]`.

Conclude with `hgoal`. Introduce `i hi`. Establish `hiS : i < BS.length` using `by omega`. Use `hiso i hi.le` as an intermediate fact. Establish `hgoal : imageIdealSheaf (τ i hi.le ≫ σ i hiS.le) (BS'.center i) = B.center i`.

Rewrite using `[hτcent i hi, hcent i hiS]`. Conclude with `imageIdealSheaf_comp_comap_of_isIso (τ i hi.le) (σ i hiS.le) (BS.center i)`. Conclude with `hgoal.symm`. Introduce `i hi`. Establish `hiS : i < BS.length` using `by omega`.

Use `hiso (i + 1) hi` as an intermediate fact. Use `hiso i hi.le` as an intermediate fact. Establish `hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS).ker = Blowup.strictTransform (B.transitionMapSucc i) (B.center i) ((τ i hi.le ≫ σ i hiS.le).ker)`. Rewrite using `[AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]`. Conclude with `hker i hiS`.

Conclude with `hgoal`.
-/
theorem isIso_comp {S' S X : Scheme.{u}} (e : S' ⟶ S) [IsIso e]
    (j : S ⟶ X) [IsClosedImmersion j] (j' : S' ⟶ X) [IsClosedImmersion j']
    (hj : j' = e ≫ j)
    {BS' : SequenceOfBlowups S'} {BS : SequenceOfBlowups S} {B : SequenceOfBlowups X}
    (hpb : IsStrictPullbackBlowupSeq e BS' BS) (h : IsPushforwardBlowupSeq j BS B) :
    IsPushforwardBlowupSeq j' BS' B := by
  obtain ⟨hlen2, τ, hτ0, hτsq, hτcent⟩ := hpb
  obtain ⟨hlen, σ, hci, h0, hstep, hcent, hker⟩ := h
  have hτ0' : ∀ hp : (0 : ℕ) ≤ BS'.length,
      τ 0 hp ≫ BS.isoZero.hom = BS'.isoZero.hom ≫ e := fun _ => hτ0
  have hiso : ∀ (i : ℕ) (hi : i ≤ BS'.length), IsIso (τ i hi) := by
    intro i
    induction i with
    | zero =>
        intro hi
        have hzz : τ 0 hi = BS'.isoZero.hom ≫ e ≫ BS.isoZero.inv := by
          rw [← Category.assoc, ← hτ0' hi]
          simp
        rw [hzz]
        infer_instance
    | succ n ih =>
        intro hi
        have hn : n < BS'.length := by omega
        have := ih (by omega)
        exact (hτsq n hn).isIso_fst_of_isIso
  refine ⟨by omega, fun i hi => τ i hi ≫ σ i (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have := hiso i hi
    have := hci i (by omega)
    infer_instance
  · have hgoal : (τ 0 (Nat.zero_le _) ≫ σ 0 (Nat.zero_le _)) ≫ B.isoZero.hom
        = BS'.isoZero.hom ≫ j' := by
      rw [hj, Category.assoc, h0, ← Category.assoc, hτ0, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS) ≫ B.transitionMapSucc i
        = BS'.transitionMapSucc i ≫ (τ i hi.le ≫ σ i hiS.le) := by
      rw [Category.assoc, hstep i hiS, ← Category.assoc, (hτsq i hi).w, Category.assoc]
    exact hgoal
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso i hi.le
    have hgoal : imageIdealSheaf (τ i hi.le ≫ σ i hiS.le) (BS'.center i) = B.center i := by
      rw [hτcent i hi, hcent i hiS]
      exact imageIdealSheaf_comp_comap_of_isIso (τ i hi.le) (σ i hiS.le) (BS.center i)
    exact hgoal.symm
  · intro i hi
    have hiS : i < BS.length := by omega
    have := hiso (i + 1) hi
    have := hiso i hi.le
    have hgoal : (τ (i + 1) hi ≫ σ (i + 1) hiS).ker
        = Blowup.strictTransform (B.transitionMapSucc i) (B.center i) ((τ i hi.le ≫ σ i hiS.le).ker) := by
      rw [AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso,
        AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso]
      exact hker i hiS
    exact hgoal

/- English proof (translation)
Establish `key : ∀ i : ℕ, i ≤ BS.length → i = 0` using `fun i hi => by omega`. Use `⟨by omega, fun i hi => eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ j ≫ B.isoZero.inv ≫ eqToHom (congrArg B.schemeAt (key i hi).symm), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i hi infer_instance`. Simplify using the standard rewrite rules. Introduce `i hi`.

Conclude with `absurd hi (by omega)`. Introduce `i hi`. Conclude with `absurd hi (by omega)`. Introduce `i hi`. Conclude with `absurd hi (by omega)`.
-/
theorem of_length_eq_zero {S X : Scheme.{u}} (j : S ⟶ X) [IsClosedImmersion j]
    (BS : SequenceOfBlowups S) (B : SequenceOfBlowups X)
    (hS : BS.length = 0) (hX : B.length = 0) :
    IsPushforwardBlowupSeq j BS B := by
  have key : ∀ i : ℕ, i ≤ BS.length → i = 0 := fun i hi => by omega
  refine ⟨by omega, fun i hi =>
      eqToHom (congrArg BS.schemeAt (key i hi)) ≫ BS.isoZero.hom ≫ j ≫ B.isoZero.inv ≫
        eqToHom (congrArg B.schemeAt (key i hi).symm), ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    infer_instance
  · simp
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)
  · intro i hi
    exact absurd hi (by omega)

end IsPushforwardBlowupSeq

end FunctorialResolution.EmbeddedResolution
