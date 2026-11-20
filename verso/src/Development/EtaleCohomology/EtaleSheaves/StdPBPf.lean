import Development.EtaleCohomology.EtaleSheaves.PullInjOfIso

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StandardPushout

variable {S : Type} [CommRing S] (f g : S)

def descR {T : Type} [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (h : a.comp (algebraMap S _) = b.comp (algebraMap S _)) : Localization.Away (f * g) →+* T :=
  IsLocalization.Away.lift (f * g) (g := a.comp (algebraMap S _)) (by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit f).map a
    · rw [h]; exact (IsLocalization.Away.algebraMap_isUnit g).map b)

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ _`.
-/
theorem descR_alg {T : Type} [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (h : a.comp (algebraMap S _) = b.comp (algebraMap S _)) (s : S) :
    descR f g a b h (algebraMap S _ s) = a (algebraMap S _ s) :=
  IsLocalization.lift_eq _ _

/- English proof (translation)
The claim follows from `IsLocalization.Away.awayToAwayRight_eq f g s`.
-/
theorem rL_alg (s : S) : LateralTheory.E.t_E1Cut.rL f g (algebraMap S _ s) = algebraMap S _ s :=
  IsLocalization.Away.awayToAwayRight_eq f g s

/- English proof (translation)
The claim follows from `IsLocalization.Away.awayToAwayLeft_eq g f s`.
-/
theorem rR_alg (s : S) : LateralTheory.E.t_E1Cut.rR f g (algebraMap S _ s) = algebraMap S _ s :=
  IsLocalization.Away.awayToAwayLeft_eq g f s

/- English proof (translation)
Establish `hw : CommRingCat.ofHom (algebraMap S (Localization.Away f)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rL f g) = CommRingCat.ofHom (algebraMap S (Localization.Away g)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rR f g)`. Use extensionality with `x`. Simplify using `[rL_alg, rR_alg]`. Use `IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw) ?_` and prove the remaining obligations. Establish `hc : ∀ s : PushoutCocone (CommRingCat.ofHom (algebraMap S (Localization.Away f))) (CommRingCat.ofHom (algebraMap S (Localization.Away g))), s.inl.hom.comp (algebraMap S _) = s.inr.hom.comp (algebraMap S _)` using `fun s => by`.

Use `congrArg CommRingCat.Hom.hom s.condition` as an intermediate fact. Simplify using `using this`. Use `PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom (descR f g s.inl.hom s.inr.hom (hc s))) ?_ ?_ ?_` and prove the remaining obligations. Introduce `s ext1`. Apply `IsLocalization.ringHom_ext (Submonoid.powers f)` to reduce the goal to its premises.

Use extensionality with `x`. Simplify using `[rL_alg, descR_alg]`. Introduce `s ext1`. Apply `IsLocalization.ringHom_ext (Submonoid.powers g)` to reduce the goal to its premises. Use extensionality with `x`.

Use `congrArg (fun φ => φ x) (hc s)` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`. Simplify using `[rR_alg, descR_alg, this]`. Introduce `s m h1 _ ext1`. Apply `IsLocalization.ringHom_ext (Submonoid.powers (f * g))` to reduce the goal to its premises.

Use extensionality with `x`. Use `congrArg (fun φ => (CommRingCat.Hom.hom φ) (algebraMap S (Localization.Away f) x)) h1` as an intermediate fact. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, rL_alg] at this`. Simplify using `[descR_alg, this]`.
-/
theorem isPushout_away :
    IsPushout (CommRingCat.ofHom (algebraMap S (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
      (CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rL f g)) (CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rR f g)) := by
  have hw : CommRingCat.ofHom (algebraMap S (Localization.Away f)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rL f g)
      = CommRingCat.ofHom (algebraMap S (Localization.Away g)) ≫ CommRingCat.ofHom (LateralTheory.E.t_E1Cut.rR f g) := by
    ext x
    simp [rL_alg, rR_alg]
  refine IsPushout.of_isColimit (c := PushoutCocone.mk _ _ hw) ?_
  have hc : ∀ s : PushoutCocone (CommRingCat.ofHom (algebraMap S (Localization.Away f)))
      (CommRingCat.ofHom (algebraMap S (Localization.Away g))),
      s.inl.hom.comp (algebraMap S _) = s.inr.hom.comp (algebraMap S _) := fun s => by
    have := congrArg CommRingCat.Hom.hom s.condition
    simpa using this
  refine PushoutCocone.IsColimit.mk _ (fun s => CommRingCat.ofHom (descR f g s.inl.hom s.inr.hom (hc s)))
    ?_ ?_ ?_
  · intro s
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp [rL_alg, descR_alg]
  · intro s
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext x
    have := congrArg (fun φ => φ x) (hc s)
    simp only [RingHom.comp_apply] at this
    simp [rR_alg, descR_alg, this]
  · intro s m h1 _
    ext1
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (algebraMap S (Localization.Away f) x)) h1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, rL_alg] at this
    simp [descR_alg, this]

instance constPreserves (J : Type) [SmallCategory J] :
    PreservesLimitsOfShape J (SimplicialObject.const PSh) := by
  apply preservesLimitsOfShape_of_evaluation
  intro k
  exact preservesLimitsOfShape_of_natIso
    (NatIso.ofComponents (fun X => Iso.refl X) (by intros; rfl) :
      𝟭 PSh ≅ SimplicialObject.const PSh ⋙ (evaluation _ _).obj k)

instance schPreserves (J : Type) [SmallCategory J] : PreservesLimitsOfShape J sch := by
  unfold sch
  infer_instance

/- English proof (translation)
The claim follows from `(isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_away f g)).map sch`.
-/
theorem isPullback_sp :
    IsPullback (spMap (LateralTheory.E.t_E1Cut.rL f g)) (spMap (LateralTheory.E.t_E1Cut.rR f g))
      (spMap (algebraMap S (Localization.Away f))) (spMap (algebraMap S (Localization.Away g))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_away f g)).map sch

end LateralTheory.E.StandardPushout

open LateralTheory.E.StandardPushout in
/- English proof (translation)
Introduce `S _ f g`. Establish `h` using `isPullback_sp f g`. Conclude with `⟨h.isoPullback.hom, inferInstance, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩`.
-/
theorem LateralTheory.E.MVPf.StdPB_of : LateralTheory.E.MVPf.StdPB := by
  intro S _ f g
  have h := isPullback_sp f g
  exact ⟨h.isoPullback.hom, inferInstance, h.isoPullback_hom_fst, h.isoPullback_hom_snd⟩
