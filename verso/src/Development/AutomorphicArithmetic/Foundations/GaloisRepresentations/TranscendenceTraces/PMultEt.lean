import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
Establish `hpb` using `pullback_lift_diagonal_isPullback s f`. Establish `hgr` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb (inferInstance : IsOpenImmersion (pullback.diagonal f))`. Establish `hsnd : IsOpenImmersion (pullback.snd (s ≫ f) f)`. Establish `: IsIso (s ≫ f)` using `by rw [h]; infer_instance`. Use `infer_instance`.

Establish `hs : s = pullback.lift (𝟙 Y) s (by simp [h]) ≫ pullback.snd (s ≫ f) f` using `(pullback.lift_snd _ _ _).symm`. Rewrite using `[hs]`. Conclude with `IsOpenImmersion.comp _ _`.
-/
private theorem isOpenImmersion_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ X) [Etale f] (h : s ≫ f = 𝟙 Y) :
    IsOpenImmersion s := by
  have hpb := pullback_lift_diagonal_isPullback s f
  have hgr := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hpb
    (inferInstance : IsOpenImmersion (pullback.diagonal f))
  have hsnd : IsOpenImmersion (pullback.snd (s ≫ f) f) := by
    have : IsIso (s ≫ f) := by rw [h]; infer_instance
    infer_instance
  have hs : s = pullback.lift (𝟙 Y) s (by simp [h]) ≫ pullback.snd (s ≫ f) f :=
    (pullback.lift_snd _ _ _).symm
  rw [hs]
  exact IsOpenImmersion.comp _ _

/- English proof (translation)
Rewrite using `[Module.length_eq_one_iff, isSimpleModule_self_iff_isUnit]`. Take `⟨a, b, hab⟩` from `h.exists_pair_ne`. Use `⟨⟨a, b, hab⟩, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h.mul_inv_cancel hx`. Conclude with `⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩`.
-/
private theorem length_self_of_isField (R : Type) [CommRing R] (h : IsField R) : Module.length R R = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_self_iff_isUnit]
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  refine ⟨⟨a, b, hab⟩, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
  exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩

/- English proof (translation)
Establish `hK : IsField ((Spec (CommRingCat.of Ω)).presheaf.stalk (IsLocalRing.closedPoint Ω))`. Establish `e : (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω)) = genericPoint _` using `Subsingleton.elim _ _`. Rewrite using `[e]`. Conclude with `(inferInstance : Field (Spec (CommRingCat.of Ω)).functionField).toIsField`. Use `haveI := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion s›).2 (IsLocalRing.closedPoint Ω)`.

Establish `hV : IsField (V.presheaf.stalk (pt s))` using `MulEquiv.isField hK (asIso (s.stalkMap (IsLocalRing.closedPoint Ω))).commRingCatIsoToRingEquiv.toMulEquiv`. Conclude with `length_self_of_isField _ hV`.
-/
private theorem length_stalk_pt {V : Scheme.{0}} {Ω : Type} [Field Ω] (s : gp Ω ⟶ V) [IsOpenImmersion s] :
    Module.length (V.presheaf.stalk (pt s)) (V.presheaf.stalk (pt s)) = 1 := by
  have hK : IsField ((Spec (CommRingCat.of Ω)).presheaf.stalk (IsLocalRing.closedPoint Ω)) := by
    have e : (IsLocalRing.closedPoint Ω : Spec (CommRingCat.of Ω)) = genericPoint _ :=
      Subsingleton.elim _ _
    rw [e]
    exact (inferInstance : Field (Spec (CommRingCat.of Ω)).functionField).toIsField
  haveI := (IsOpenImmersion.iff_isIso_stalkMap.mp ‹IsOpenImmersion s›).2 (IsLocalRing.closedPoint Ω)
  have hV : IsField (V.presheaf.stalk (pt s)) :=
    MulEquiv.isField hK (asIso (s.stalkMap (IsLocalRing.closedPoint Ω))).commRingCatIsoToRingEquiv.toMulEquiv
  exact length_self_of_isField _ hV

/- English proof (translation)
Introduce `Z S p _`. Use function extensionality and compare the values at `Ω _ _ z`. Express the relevant statement in the definitionally equal form `mult p Ω z = (1 : ℤ)`. Establish `hσ : IsOpenImmersion (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p))` using `isOpenImmersion_of_section (pullback.snd p (z ≫ p)) _ (pullback.lift_snd _ _ _)`. Establish `hl` using `length_stalk_pt (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p))`.

Simplify using `only [mult]`. Rewrite using `[hl]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.TranscendenceTraces.multEt_of :
    MultEt := by
  intro Z S p _
  funext Ω _ _ z
  change mult p Ω z = (1 : ℤ)
  have hσ : IsOpenImmersion (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p)) :=
    isOpenImmersion_of_section (pullback.snd p (z ≫ p)) _ (pullback.lift_snd _ _ _)
  have hl := length_stalk_pt (pullback.lift z (𝟙 (gp Ω)) (Category.id_comp _).symm : gp Ω ⟶ pullback p (z ≫ p))
  simp only [mult]
  rw [hl]
  rfl
