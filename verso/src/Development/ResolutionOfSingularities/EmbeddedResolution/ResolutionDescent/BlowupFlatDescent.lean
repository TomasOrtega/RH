import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev pullbackFstSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (i : ℕ) : Scheme.{u} :=
  pullback (pullback.fst g g) (t.projectionToBase i)

abbrev pullbackSndSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (i : ℕ) : Scheme.{u} :=
  pullback (pullback.snd g g) (t.projectionToBase i)

/- English proof (authored)
The first projection in the pullback is obtained by base change of the given flat morphism. Flatness is preserved by base change.
-/
private theorem flat_fst_of_isPullback {A B C D : Scheme.{u}} {p : A ⟶ B} {q : A ⟶ C}
    {f : B ⟶ D} {h : C ⟶ D} (H : IsPullback p q f h) [AlgebraicGeometry.Flat h] :
    AlgebraicGeometry.Flat p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Flat) H.flip inferInstance

/- English proof (authored)
Precompose both projections with the given isomorphism of their source. This identifies the new square with the original pullback square, so it still satisfies the same universal property.
-/
private theorem isPullback_iso_hom_comp {P P' A B C : Scheme.{u}} {pf : P' ⟶ A} {ps : P' ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (H : IsPullback pf ps f g) (e : P ≅ P') :
    IsPullback (e.hom ≫ pf) (e.hom ≫ ps) f g := by
  have E : IsPullback e.hom (e.hom ≫ ps) ps (𝟙 B) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := E.paste_horiz H
  rwa [Category.id_comp] at h

/- English proof (authored)
Use the overlap isomorphism to write the second overlap pullback on the first overlap object. Its compatibility with the overlap base maps allows pasting with the self-pullback square of the cover. The stage comparison square is a pullback, and the comparison maps agree on the overlap by hypothesis. Cancelling the stage square gives a self-pullback square for the stage comparison map. The center pulls back to the same ideal along the two projections of this square by the center compatibility. Flat ideal descent now shows that the pullback of its image along the stage comparison is exactly the original center.
-/
theorem comap_map_center_eq_center_of_isPullback {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (n : ℕ) {X : Scheme.{u}} (π : X ⟶ Y)
    (γ : t.schemeAt n ⟶ X) [AlgebraicGeometry.Flat γ] [AlgebraicGeometry.QuasiCompact γ]
    (hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (hcenter : ((t.center n).comap (pullback.snd (pullback.snd g g) (t.projectionToBase n))).comap e.hom
      = (t.center n).comap (pullback.snd (pullback.fst g g) (t.projectionToBase n)))
    (hbase : e.hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase n)
      = pullback.fst (pullback.fst g g) (t.projectionToBase n))
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    ((t.center n).map γ).comap γ = t.center n := by
  have hpbSnd : IsPullback (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n))
      (pullback.fst (pullback.fst g g) (t.projectionToBase n)) (t.projectionToBase n) (pullback.snd g g) := by
    have h := isPullback_iso_hom_comp
      (IsPullback.of_hasPullback (pullback.snd g g) (t.projectionToBase n)).flip e
    rwa [hbase] at h
  have Big := hpbSnd.paste_vert (IsPullback.of_hasPullback g g).flip
  have hcond : pullback.fst (pullback.fst g g) (t.projectionToBase n) ≫ pullback.fst g g
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ t.projectionToBase n := pullback.condition
  rw [hcond, ← hsq.w] at Big
  have comm : (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n)) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ := by
    rw [Category.assoc]
    exact hgamma
  have key : IsPullback (e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n))
      (pullback.snd (pullback.fst g g) (t.projectionToBase n)) γ γ :=
    IsPullback.of_bot Big comm hsq
  refine comap_map_eq_self_of_isPullback γ key (t.center n) ?_
  rw [Scheme.IdealSheafData.comap_comp]
  exact hcenter

/- English proof (authored)
The original stage transition blows up the original center, which is the pullback of the image center by hypothesis. The canonical blowup of the image center pulls back along the flat comparison map to a blowup of that same original center. By the universal property, the two blowups are isomorphic over the stage. The comparison map furnished by this identification has the stated commuting equation and pullback square.
-/
theorem exists_isPullback_blowup_proj_map_center {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    ∃ q : t.schemeAt (n + 1) ⟶ Blowup.blowup ((t.center n).map γ),
      q ≫ Blowup.blowup.proj ((t.center n).map γ) = t.transitionMapSucc n ≫ γ ∧
        IsPullback q (t.transitionMapSucc n) (Blowup.blowup.proj ((t.center n).map γ)) γ := by
  have := hflat
  have h' : Blowup.IsBlowupAlongIdealSheaf (t.transitionMapSucc n) (((t.center n).map γ).comap γ) := by
    rw [hc]
    exact t.isBlowupAlongIdealSheaf_blowupMorphism n hn
  exact (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)).exists_isPullback_of_flat γ h'

def toBlowupOfMapCenter {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    t.schemeAt (n + 1) ⟶ Blowup.blowup ((t.center n).map γ) :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose

/- English proof (authored)
The comparison was chosen with a commuting square over the original stage. Its composite with the descended blowup projection is the original blowup transition followed by the stage comparison.
-/
theorem toBlowupOfMapCenter_comp_proj {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    toBlowupOfMapCenter hn hflat hc ≫ Blowup.blowup.proj ((t.center n).map γ) = t.transitionMapSucc n ≫ γ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.1

/- English proof (authored)
The comparison map was chosen to exhibit the original blowup as the pullback of the image-center blowup along the stage comparison. The asserted pullback square is that property.
-/
theorem isPullback_toBlowupOfMapCenter {W X : Scheme.{u}} {t : SequenceOfBlowups W} {n : ℕ}
    (hn : n < t.length) {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n) :
    IsPullback (toBlowupOfMapCenter hn hflat hc) (t.transitionMapSucc n)
      (Blowup.blowup.proj ((t.center n).map γ)) γ :=
  (exists_isPullback_blowup_proj_map_center hn hflat hc).choose_spec.2

/- English proof (authored)
Paste the pullback square comparing the blowups with the earlier pullback square comparing their bases. The resulting maps to the original and new bases are the successor projections, because each transition followed by the preceding projection equals the successor projection. Hence the pasted square is the asserted one.
-/
theorem isPullback_toBlowupOfMapCenter_projectionToBase {W Y X : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    {n : ℕ} (hn : n < t.length) (π : X ⟶ Y) {γ : t.schemeAt n ⟶ X}
    (hflat : AlgebraicGeometry.Flat γ) (hc : ((t.center n).map γ).comap γ = t.center n)
    (hsq : IsPullback γ (t.projectionToBase n) π g) :
    IsPullback (toBlowupOfMapCenter hn hflat hc) (t.projectionToBase (n + 1))
      (Blowup.blowup.proj ((t.center n).map γ) ≫ π) g := by
  have h := (isPullback_toBlowupOfMapCenter hn hflat hc).paste_vert hsq
  rwa [← t.projectionToBase_succ n] at h

/- English proof (authored)
Compare the two overlap maps to the blowup of the descended center. Their composites with its projection coincide, since the overlap comparisons commute with the successor transitions and the preceding comparisons agree as maps to the descended stage. The descended center becomes locally generated by a non-zero-divisor on the blowup. It remains so after pulling back through the flat comparison to the local successor and then through the flat overlap projection. The uniqueness part of the blowup universal property therefore makes the two maps to the descended blowup equal.
-/
theorem toBlowupOfMapCenter_cocycle {W Y X : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) {n : ℕ} (hn : n < t.length) (π : X ⟶ Y)
    {γ : t.schemeAt n ⟶ X} (hflat : AlgebraicGeometry.Flat γ)
    (hc : ((t.center n).map γ).comap γ = t.center n)
    (_hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1))
    (hee : e'.hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n) ≫ e.hom)
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    e'.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ toBlowupOfMapCenter hn hflat hc
      = pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ toBlowupOfMapCenter hn hflat hc := by
  have := hflat
  have hfst : AlgebraicGeometry.Flat (pullback.fst g g) :=
    flat_fst_of_isPullback (IsPullback.of_hasPullback g g)
  have hdc : AlgebraicGeometry.Flat (toBlowupOfMapCenter hn hflat hc) :=
    flat_fst_of_isPullback (isPullback_toBlowupOfMapCenter hn hflat hc)
  have hsnd1 : pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.fst g g) (t.projectionToBase n) :=
    (t.pullbackTransitionMap_snd (pullback.fst g g) (Nat.le_succ n)).symm
  have hsnd2 : pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n
      = t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) :=
    (t.pullbackTransitionMap_snd (pullback.snd g g) (Nat.le_succ n)).symm
  have hsnd1' : pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n ≫ γ
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ := by
    rw [← Category.assoc, ← Category.assoc, hsnd1]
  have hsnd2' : pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ t.transitionMapSucc n ≫ γ
      = t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
        ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ := by
    rw [← Category.assoc, ← Category.assoc, hsnd2]
  have hk : Blowup.IsLocallyGeneratedByNonZeroDivisor (((t.center n).map γ).comap
      (pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫
        toBlowupOfMapCenter hn hflat hc ≫ Blowup.blowup.proj ((t.center n).map γ))) := by
    rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat
      (Blowup.IsLocallyGeneratedByNonZeroDivisor.comap_of_flat (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)).1
        (toBlowupOfMapCenter hn hflat hc)) _
  refine Blowup.IsBlowupAlongIdealSheaf.hom_ext_of_comp_eq (Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)) hk ?_ ?_
  · simp only [Category.assoc]
    rw [toBlowupOfMapCenter_comp_proj hn hflat hc, hsnd2', hsnd1', ← Category.assoc, hee,
      Category.assoc, hgamma]
  · rw [Category.assoc]

structure DescendedBlowupData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) (n : ℕ)
    {X : Scheme.{u}} (π : X ⟶ Y) (γ : t.schemeAt n ⟶ X)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1)) where
  total : Scheme.{u}
  totalStruct : total ⟶ Y
  down : total ⟶ X
  totalCenter : X.IdealSheafData
  totalComparison : t.schemeAt (n + 1) ⟶ total
  center_comap : totalCenter.comap γ = t.center n
  isBlowup_down : Blowup.IsBlowupAlongIdealSheaf down totalCenter
  sq_comm : totalComparison ≫ down = t.transitionMapSucc n ≫ γ
  isPullback_sq : IsPullback totalComparison (t.transitionMapSucc n) down γ
  isPullback_base : IsPullback totalComparison (t.projectionToBase (n + 1)) totalStruct g
  hom_comparison :
    e'.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase (n + 1)) ≫ totalComparison
      = pullback.snd (pullback.fst g g) (t.projectionToBase (n + 1)) ≫ totalComparison
  structY_eq : totalStruct = down ≫ π

def descendedBlowupData {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) {n : ℕ} (hn : n < t.length)
    {X : Scheme.{u}} (π : X ⟶ Y) (γ : t.schemeAt n ⟶ X)
    (hsq : IsPullback γ (t.projectionToBase n) π g)
    (e : pullbackFstSchemeAt g t n ≅ pullbackSndSchemeAt g t n)
    (e' : pullbackFstSchemeAt g t (n + 1) ≅ pullbackSndSchemeAt g t (n + 1))
    (hee : e'.hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ n)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ n) ≫ e.hom)
    (hcenter : ((t.center n).comap (pullback.snd (pullback.snd g g) (t.projectionToBase n))).comap e.hom
      = (t.center n).comap (pullback.snd (pullback.fst g g) (t.projectionToBase n)))
    (hbase : e.hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase n)
      = pullback.fst (pullback.fst g g) (t.projectionToBase n))
    (hgamma : e.hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ γ
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ γ) :
    DescendedBlowupData g t n π γ e' :=
  haveI hfl : AlgebraicGeometry.Flat γ := flat_fst_of_isPullback hsq
  haveI _hqc : AlgebraicGeometry.QuasiCompact γ := quasiCompact_of_isPullback hsq.flip
  have hc : ((t.center n).map γ).comap γ = t.center n :=
    comap_map_center_eq_center_of_isPullback g t n π γ hsq e hcenter hbase hgamma
  { total := Blowup.blowup ((t.center n).map γ)
    totalStruct := Blowup.blowup.proj ((t.center n).map γ) ≫ π
    down := Blowup.blowup.proj ((t.center n).map γ)
    totalCenter := (t.center n).map γ
    totalComparison := toBlowupOfMapCenter hn hfl hc
    center_comap := hc
    isBlowup_down := Blowup.blowup.isBlowupAlongIdealSheaf_proj ((t.center n).map γ)
    sq_comm := toBlowupOfMapCenter_comp_proj hn hfl hc
    isPullback_sq := isPullback_toBlowupOfMapCenter hn hfl hc
    isPullback_base := isPullback_toBlowupOfMapCenter_projectionToBase g t hn π hfl hc hsq
    hom_comparison := toBlowupOfMapCenter_cocycle g t hn π hfl hc hsq e e' hee hgamma
    structY_eq := rfl }

end FunctorialResolution.EmbeddedResolution
