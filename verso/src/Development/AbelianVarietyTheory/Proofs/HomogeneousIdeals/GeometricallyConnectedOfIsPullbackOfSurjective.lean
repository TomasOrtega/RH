import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsaRos
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Use `⟨fun K _ t Z fst snd hZ => ?_⟩` and prove the remaining obligations. Take `⟨z, -⟩` from `(pullback.snd s t).surjective (Nonempty.some inferInstance)`. Set `e` to `(pullback s t).fromSpecResidueField z`. Set `u` to `e ≫ pullback.fst s t`. Set `v` to `e ≫ pullback.snd s t`.

Establish `huv : v ≫ t = u ≫ s` using `by simp only [u, v, Category.assoc, pullback.condition]`. Establish `hbig : IsPullback (pullback.fst snd v ≫ fst) (pullback.snd snd v) q (u ≫ s)` using `huv ▸ (IsPullback.of_hasPullback snd v).paste_horiz hZ`. Establish `hsmall` using `IsPullback.of_right (h₁₁ := h.lift (pullback.fst snd v ≫ fst) (pullback.snd snd v ≫ u) (by simpa only [Category.assoc] using hbig.w)) (by simpa using hbig) (by simp) h`. Establish `hc : ConnectedSpace ↥(pullback snd v)` using `GeometricallyConnected.geometrically_connectedSpace u _ _ hsmall`. Establish `hv : Surjective v` using `⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩`.

Conclude with `(pullback.fst snd v).surjective.connectedSpace (pullback.fst snd v).continuous`.
-/
theorem GlobalTheory.geometricallyConnected_of_isPullback_of_surjective {X Y X' Y' : Scheme.{0}}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {q : X ⟶ Y} {s : Y' ⟶ Y} (h : IsPullback a p q s)
    [Surjective s] [GeometricallyConnected p] : GeometricallyConnected q := by
  refine ⟨fun K _ t Z fst snd hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.snd s t).surjective (Nonempty.some inferInstance)
  let e := (pullback s t).fromSpecResidueField z
  let u := e ≫ pullback.fst s t
  let v := e ≫ pullback.snd s t
  have huv : v ≫ t = u ≫ s := by simp only [u, v, Category.assoc, pullback.condition]
  have hbig : IsPullback (pullback.fst snd v ≫ fst) (pullback.snd snd v) q (u ≫ s) :=
    huv ▸ (IsPullback.of_hasPullback snd v).paste_horiz hZ
  have hsmall := IsPullback.of_right
    (h₁₁ := h.lift (pullback.fst snd v ≫ fst) (pullback.snd snd v ≫ u)
      (by simpa only [Category.assoc] using hbig.w))
    (by simpa using hbig) (by simp) h
  have hc : ConnectedSpace ↥(pullback snd v) :=
    GeometricallyConnected.geometrically_connectedSpace u _ _ hsmall
  have hv : Surjective v := ⟨fun x => ⟨Nonempty.some inferInstance, Subsingleton.elim _ _⟩⟩
  exact (pullback.fst snd v).surjective.connectedSpace (pullback.fst snd v).continuous

/- English proof (translation)
Use `letI := E.addCommGroup`. Use `letI := E.grpB`. Use `haveI := E.free`. Use `haveI := E.finite`. Use `haveI := E.q_hom`.

Use `haveI := E.i_hom`. Use `haveI := E.q_flat`. Use `haveI := E.q_surjective`. Use `haveI := E.q_quasiCompact`. Use `haveI : Smooth E.B.hom := E.isAbelian.smooth`.

Use `haveI : GeometricallyConnected E.B.hom := E.isAbelian.geomConnected`. Use `haveI : IsProper E.B.hom := E.isAbelian.proper`. Establish `hTc : GeometricallyConnected (splitTorus (Spec (CommRingCat.of K)) E.X).hom` using `((GlobalTheory.splitTorus_properties (Spec (CommRingCat.of K))).1 E.X).2.2.2.2.2.2.2.1`. Establish `hiq : E.i ≫ E.q = 1` using `E.isKernel.w`. Establish `key : ∀ {W : Over (Spec (CommRingCat.of K))} (a b : W ⟶ G), a ≫ E.q = b ≫ E.q → (a⁻¹ * b) ≫ E.q = toUnit W ≫ (η : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.B)`.

Introduce `W a b hab`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, hab, _root_.inv_mul_cancel]`. Apply the tactic sequence `try exact rfl`. Set `m : G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X ⟶ G` to `fst _ _ * (snd _ _ ≫ E.i)`. Establish `hm : ∀ {W : Over (Spec (CommRingCat.of K))} (l : W ⟶ G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X), l ≫ m = (l ≫ fst _ _) * ((l ≫ snd _ _) ≫ E.i)`.

Introduce `W l`. Simplify using `only [m, MonObj.comp_mul, Category.assoc]`. Establish `hw : fst _ _ ≫ E.q = m ≫ E.q`. Simplify using `only [m, MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]`. Establish `hsq : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)) m E.q E.q` using `IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw (fun c => lift c.fst (E.isKernel.lift (c.fst⁻¹ * c.snd) (toUnit _) (key _ _ c.condition))) (fun c => by rw [lift_fst]) (fun c => by rw [hm, lift_fst, lift_snd, IsPullback.lift_fst, mul_inv_cancel_left]) (fun c l h1 h2 => by`.

Use `CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, h1]) ?_` and prove the remaining obligations. Rewrite using `[lift_snd]`. Use `E.isKernel.hom_ext ?_ (toUnit_unique _ _)` and prove the remaining obligations. Rewrite using `[IsPullback.lift_fst]`. Rewrite `h2` using `[hm, h1]`.

Conclude with `eq_inv_mul_of_mul_eq h2))`. Establish `hsqS : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left m.left E.q.left E.q.left` using `hsq.map (Over.forget _)`. Establish `hprod : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left (snd G (splitTorus (Spec (CommRingCat.of K)) E.X)).left G.hom (splitTorus (Spec (CommRingCat.of K)) E.X).hom` using `IsPullback.of_hasPullback _ _`. Establish `hfs : Smooth (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left` using `MorphismProperty.of_isPullback (P := @Smooth) hprod.flip inferInstance`. Establish `hfc : GeometricallyConnected (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left` using `MorphismProperty.of_isPullback (P := @GeometricallyConnected) hprod.flip hTc`.

Establish `hqs : Smooth E.q.left` using `MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsqS ⟨⟨E.q_surjective, E.q_flat⟩, E.q_quasiCompact⟩ hfs`. Establish `hqc : GeometricallyConnected E.q.left` using `GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hsqS.flip`. Establish `hqa : IsAffineHom E.q.left` using `GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel _ G E.B _ E.q E.i E.q_hom E.i_hom E.q_flat E.q_surjective E.q_quasiCompact E.isKernel inferInstance`. Rewrite using `[← Over.w E.q]`. Use `⟨hqs, hqc, inferInstance, GeometricallyConnected.comp _ _, inferInstance⟩` and prove the remaining obligations.
-/
theorem GlobalTheory.torusExtension_smooth_geometricallyConnected {K : Type} [Field K] (G : Over (Spec (CommRingCat.of K))) [GrpObj G] (E : TorusExtension G) : Smooth E.q.left ∧ GeometricallyConnected E.q.left ∧ Smooth G.hom ∧ GeometricallyConnected G.hom ∧ IsSeparated G.hom := by
  letI := E.addCommGroup
  letI := E.grpB
  haveI := E.free
  haveI := E.finite
  haveI := E.q_hom
  haveI := E.i_hom
  haveI := E.q_flat
  haveI := E.q_surjective
  haveI := E.q_quasiCompact
  haveI : Smooth E.B.hom := E.isAbelian.smooth
  haveI : GeometricallyConnected E.B.hom := E.isAbelian.geomConnected
  haveI : IsProper E.B.hom := E.isAbelian.proper
  have hTc : GeometricallyConnected (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    ((GlobalTheory.splitTorus_properties (Spec (CommRingCat.of K))).1 E.X).2.2.2.2.2.2.2.1
  have hiq : E.i ≫ E.q = 1 := E.isKernel.w
  have key : ∀ {W : Over (Spec (CommRingCat.of K))} (a b : W ⟶ G), a ≫ E.q = b ≫ E.q →
      (a⁻¹ * b) ≫ E.q = toUnit W ≫ (η : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ E.B) := by
    intro W a b hab
    rw [MonObj.mul_comp, GrpObj.inv_comp, hab, _root_.inv_mul_cancel]
    try exact rfl
  let m : G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X ⟶ G := fst _ _ * (snd _ _ ≫ E.i)
  have hm : ∀ {W : Over (Spec (CommRingCat.of K))} (l : W ⟶ G ⊗ splitTorus (Spec (CommRingCat.of K)) E.X),
      l ≫ m = (l ≫ fst _ _) * ((l ≫ snd _ _) ≫ E.i) := by
    intro W l
    simp only [m, MonObj.comp_mul, Category.assoc]
  have hw : fst _ _ ≫ E.q = m ≫ E.q := by
    simp only [m, MonObj.mul_comp, Category.assoc, hiq, MonObj.comp_one, _root_.mul_one]
  have hsq : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)) m E.q E.q :=
    IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
      (fun c => lift c.fst (E.isKernel.lift (c.fst⁻¹ * c.snd) (toUnit _) (key _ _ c.condition)))
      (fun c => by rw [lift_fst])
      (fun c => by rw [hm, lift_fst, lift_snd, IsPullback.lift_fst, mul_inv_cancel_left])
      (fun c l h1 h2 => by
        refine CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, h1]) ?_
        rw [lift_snd]
        refine E.isKernel.hom_ext ?_ (toUnit_unique _ _)
        rw [IsPullback.lift_fst]
        rw [hm, h1] at h2
        exact eq_inv_mul_of_mul_eq h2))
  have hsqS : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left m.left
      E.q.left E.q.left := hsq.map (Over.forget _)
  have hprod : IsPullback (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left
      (snd G (splitTorus (Spec (CommRingCat.of K)) E.X)).left G.hom
      (splitTorus (Spec (CommRingCat.of K)) E.X).hom :=
    IsPullback.of_hasPullback _ _
  have hfs : Smooth (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @Smooth) hprod.flip inferInstance
  have hfc : GeometricallyConnected (fst G (splitTorus (Spec (CommRingCat.of K)) E.X)).left :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hprod.flip hTc
  have hqs : Smooth E.q.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hsqS
      ⟨⟨E.q_surjective, E.q_flat⟩, E.q_quasiCompact⟩ hfs
  have hqc : GeometricallyConnected E.q.left :=
    GlobalTheory.geometricallyConnected_of_isPullback_of_surjective hsqS.flip
  have hqa : IsAffineHom E.q.left :=
    GlobalTheory.isAffineHom_of_flatQuotient_of_affine_kernel _ G E.B _ E.q E.i E.q_hom E.i_hom
      E.q_flat E.q_surjective E.q_quasiCompact E.isKernel inferInstance
  rw [← Over.w E.q]
  refine ⟨hqs, hqc, inferInstance, GeometricallyConnected.comp _ _, inferInstance⟩
