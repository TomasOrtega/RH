import Mathlib

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

namespace GlobalTheory.FinEt

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

/- English proof (translation)
Rewrite using `[← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]`.
-/
theorem range_of_isPullback {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

/- English proof (translation)
Use `⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance, Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫ X.fromSpecResidueField x, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Rewrite using `[← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]`.

Conclude with `⟨_, rfl⟩`. Introduce and unpack `rfl`. Take `⟨z⟩ : Nonempty (Spec (.of (AlgebraicClosure (X.residueField y))))` from `inferInstance`. Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]`.

Conclude with `⟨_, rfl⟩`.
-/
theorem exists_algClosed_point (X : Scheme.{u}) (x : X) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (a : Spec (.of k) ⟶ X),
      Set.range a = {x} := by
  refine ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) _)) ≫ X.fromSpecResidueField x, ?_⟩
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    rw [← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  · rintro rfl
    obtain ⟨z⟩ : Nonempty (Spec (.of (AlgebraicClosure (X.residueField y)))) := inferInstance
    refine ⟨z, ?_⟩
    rw [← Set.mem_singleton_iff, ← Scheme.range_fromSpecResidueField, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

variable {S : Scheme.{u}} {X Y : Over S}

/- English proof (translation)
The claim follows from `(isIso_iff_of_reflects_iso f (Over.forget S)).symm`.
-/
theorem isIso_iff_isIso_left (f : X ⟶ Y) : IsIso f ↔ IsIso f.left :=
  (isIso_iff_of_reflects_iso f (Over.forget S)).symm

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := pullback.snd Y.hom t) (v₁₃ := t) (h₂₂ := Y.hom) ?_ (by simp) (IsPullback.of_hasPullback Y.hom t).flip` and prove the remaining obligations. Simplify using `using (IsPullback.of_hasPullback X.hom t).flip`.
-/
theorem isPullback_pullback_map {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y) :
    IsPullback ((Over.pullback t).map f).left (pullback.fst X.hom t) (pullback.fst Y.hom t)
      f.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd Y.hom t) (v₁₃ := t) (h₂₂ := Y.hom) ?_ (by simp)
    (IsPullback.of_hasPullback Y.hom t).flip
  simpa using (IsPullback.of_hasPullback X.hom t).flip

/- English proof (translation)
Establish `: IsFinite (f.left ≫ Y.hom)` using `by rw [Over.w]; infer_instance`. Conclude with `IsFinite.of_comp f.left Y.hom`.
-/
theorem isFinite_left (f : X ⟶ Y) [IsFinite X.hom] [IsSeparated Y.hom] : IsFinite f.left := by
  have : IsFinite (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  exact IsFinite.of_comp f.left Y.hom

/- English proof (translation)
Establish `: Etale (f.left ≫ Y.hom)` using `by rw [Over.w]; infer_instance`. Conclude with `Etale.of_comp f.left Y.hom`.
-/
theorem etale_left (f : X ⟶ Y) [Etale X.hom] [LocallyOfFiniteType Y.hom]
    [FormallyUnramified Y.hom] : Etale f.left := by
  have : Etale (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  exact Etale.of_comp f.left Y.hom

def isoLocus (f : X ⟶ Y) : Set S :=
  {s | IsIso ((Over.pullback (S.fromSpecResidueField s)).map f)}

/- English proof (translation)
Establish `H` using `isPullback_pullback_map t f`. Establish `h1 : IsFinite ((Over.pullback t).map f).left` using `MorphismProperty.of_isPullback (P := @IsFinite) H.flip inferInstance`. Establish `h2 : Flat ((Over.pullback t).map f).left` using `MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance`. Rewrite using `[isIso_iff_isIso_left, Scheme.Hom.isIso_iff_finrank_eq]`. Establish `h3` using `Scheme.Hom.finrank_of_isPullback _ _ _ _ H.flip`.

Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Establish `: y ∈ Set.range (pullback.fst Y.hom t)` using `by rwa [Scheme.Pullback.range_fst]`. Take `⟨z, rfl⟩` from `this`. Rewrite using `[← h3, h, Pi.one_apply]`.

Introduce `h`. Use function extensionality and compare the values at `z`. Rewrite using `[h3, Pi.one_apply]`. Apply `h` to reduce the goal to its premises. Rewrite using `[← Set.mem_preimage, ← Scheme.Pullback.range_fst]`.

Conclude with `⟨z, rfl⟩`.
-/
theorem isIso_pullback_map_iff_finrank {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite f.left] [Flat f.left] :
    IsIso ((Over.pullback t).map f) ↔
      ∀ y : Y.left, Y.hom y ∈ Set.range t → f.left.finrank y = 1 := by
  have H := isPullback_pullback_map t f
  have h1 : IsFinite ((Over.pullback t).map f).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) H.flip inferInstance
  have h2 : Flat ((Over.pullback t).map f).left :=
    MorphismProperty.of_isPullback (P := @Flat) H.flip inferInstance
  rw [isIso_iff_isIso_left, Scheme.Hom.isIso_iff_finrank_eq]
  have h3 := Scheme.Hom.finrank_of_isPullback _ _ _ _ H.flip
  constructor
  · intro h y hy
    have : y ∈ Set.range (pullback.fst Y.hom t) := by rwa [Scheme.Pullback.range_fst]
    obtain ⟨z, rfl⟩ := this
    rw [← h3, h, Pi.one_apply]
  · intro h
    funext z
    rw [h3, Pi.one_apply]
    apply h
    rw [← Set.mem_preimage, ← Scheme.Pullback.range_fst]
    exact ⟨z, rfl⟩

/- English proof (translation)
Rewrite using `[isoLocus, Set.mem_setOf_eq, isIso_pullback_map_iff_finrank, Scheme.range_fromSpecResidueField]`. Both sides reduce to the same expression.
-/
theorem mem_isoLocus_iff (f : X ⟶ Y) [IsFinite f.left] [Flat f.left] (s : S) :
    s ∈ isoLocus f ↔ ∀ y : Y.left, Y.hom y = s → f.left.finrank y = 1 := by
  rw [isoLocus, Set.mem_setOf_eq, isIso_pullback_map_iff_finrank,
    Scheme.range_fromSpecResidueField]
  rfl

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[Set.mem_compl_iff, mem_isoLocus_iff]`. Simplify using `only [not_forall, Set.mem_image, Set.mem_setOf_eq]`. The claim follows by propositional logic.
-/
theorem compl_isoLocus (f : X ⟶ Y) [IsFinite f.left] [Flat f.left] :
    (isoLocus f)ᶜ = Y.hom '' {y | f.left.finrank y ≠ 1} := by
  ext s
  rw [Set.mem_compl_iff, mem_isoLocus_iff]
  simp only [not_forall, Set.mem_image, Set.mem_setOf_eq]
  tauto

/- English proof (translation)
Use `isFinite_left f` as an intermediate fact. Use `etale_left f` as an intermediate fact. Rewrite using `[isIso_pullback_map_iff_finrank]`. Prove the components needed by the constructor for the conclusion. Introduce `h s hs`.

Rewrite using `[mem_isoLocus_iff]`. Introduce and unpack `y rfl`. Conclude with `h y hs`. Introduce `h y hy`. Conclude with `(mem_isoLocus_iff f _).mp (h hy) y rfl`.
-/
theorem isIso_pullback_map_iff {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso ((Over.pullback t).map f) ↔ Set.range t ⊆ isoLocus f := by
  have := isFinite_left f
  have := etale_left f
  rw [isIso_pullback_map_iff_finrank]
  constructor
  · intro h s hs
    rw [mem_isoLocus_iff]
    rintro y rfl
    exact h y hs
  · intro h y hy
    exact (mem_isoLocus_iff f _).mp (h hy) y rfl

/- English proof (translation)
Use `isFinite_left f` as an intermediate fact. Use `etale_left f` as an intermediate fact. Establish `h : IsClopen {y | f.left.finrank y ≠ 1}` using `(f.left.isLocallyConstant_finrank.isClopen_fiber 1).compl`. Rewrite using `[← isClopen_compl_iff, compl_isoLocus]`. Conclude with `⟨Y.hom.isClosedMap _ h.isClosed, Y.hom.isOpenMap _ h.isOpen⟩`.
-/
theorem isClopen_isoLocus (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] : IsClopen (isoLocus f) := by
  have := isFinite_left f
  have := etale_left f
  have h : IsClopen {y | f.left.finrank y ≠ 1} :=
    (f.left.isLocallyConstant_finrank.isClopen_fiber 1).compl
  rw [← isClopen_compl_iff, compl_isoLocus]
  exact ⟨Y.hom.isClosedMap _ h.isClosed, Y.hom.isOpenMap _ h.isOpen⟩

/- English proof (translation)
Use `isFinite_left f` as an intermediate fact. Use `etale_left f` as an intermediate fact. Rewrite using `[isIso_iff_isIso_left, Scheme.Hom.isIso_iff_finrank_eq, Set.eq_univ_iff_forall]`. Prove the components needed by the constructor for the conclusion. Introduce `h s`.

Rewrite using `[mem_isoLocus_iff]`. Introduce `y _`. Rewrite using `[h, Pi.one_apply]`. Introduce `h`. Use function extensionality and compare the values at `y`.

Conclude with `(mem_isoLocus_iff f _).mp (h _) y rfl`.
-/
theorem isIso_iff_isoLocus_eq_univ (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso f ↔ isoLocus f = Set.univ := by
  have := isFinite_left f
  have := etale_left f
  rw [isIso_iff_isIso_left, Scheme.Hom.isIso_iff_finrank_eq, Set.eq_univ_iff_forall]
  constructor
  · intro h s
    rw [mem_isoLocus_iff]
    intro y _
    rw [h, Pi.one_apply]
  · intro h
    funext y
    exact (mem_isoLocus_iff f _).mp (h _) y rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `_ k _ _`. Conclude with `⟨fun a b h ↦ (cancel_mono f).mp h, fun y ↦ ⟨y ≫ inv f, by simp⟩⟩`. Introduce `h`. Establish `hsurj : Function.Surjective f`.

Introduce `y`. Take `⟨k, _, _, a, ha⟩` from `exists_algClosed_point Y y`. Take `⟨b, rfl⟩` from `(h k).2 a`. Take `⟨z⟩ : Nonempty (Spec (.of k))` from `inferInstance`. Use `⟨b z, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Set.mem_singleton_iff, ← ha, ← Scheme.Hom.comp_apply]`. Conclude with `⟨_, rfl⟩`. Establish `hdiag : IsIso (pullback.diagonal f)`. Apply `isIso_of_isOpenImmersion_of_opensRange_eq_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff]`.

Introduce `z _`. Take `⟨k, _, _, a, ha⟩` from `exists_algClosed_point _ z`. Establish `e : a ≫ pullback.fst f f = a ≫ pullback.snd f f` using `(h k).1 (by simp [pullback.condition])`. Establish `e' : a = (a ≫ pullback.fst f f) ≫ pullback.diagonal f`. Apply the tactic sequence `apply pullback.hom_ext <;> simp [e]`.

Establish `: z ∈ Set.range a` using `by simp [ha]`. Take `⟨w, rfl⟩` from `this`. Use `⟨(a ≫ pullback.fst f f) w, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, ← e']`. Establish `hsnd : IsIso (pullback.snd f f)` using `IsIso.of_isIso_fac_left (pullback.diagonal_snd f)`.

Rewrite using `[Scheme.Hom.isIso_iff_finrank_eq]`. Use function extensionality and compare the values at `y`. Take `⟨x, rfl⟩` from `hsurj y`. Rewrite using `[← Scheme.Hom.finrank_pullback_snd, Scheme.Hom.finrank_eq_one_of_isIso]`. Both sides reduce to the same expression.
-/
theorem isIso_iff_bijective_algClosed {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Etale f] :
    IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k],
      Function.Bijective fun x : Spec (.of k) ⟶ X ↦ x ≫ f := by
  constructor
  · intro _ k _ _
    exact ⟨fun a b h ↦ (cancel_mono f).mp h, fun y ↦ ⟨y ≫ inv f, by simp⟩⟩
  intro h
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨k, _, _, a, ha⟩ := exists_algClosed_point Y y
    obtain ⟨b, rfl⟩ := (h k).2 a
    obtain ⟨z⟩ : Nonempty (Spec (.of k)) := inferInstance
    refine ⟨b z, ?_⟩
    rw [← Set.mem_singleton_iff, ← ha, ← Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have hdiag : IsIso (pullback.diagonal f) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [eq_top_iff]
    intro z _
    obtain ⟨k, _, _, a, ha⟩ := exists_algClosed_point _ z
    have e : a ≫ pullback.fst f f = a ≫ pullback.snd f f :=
      (h k).1 (by simp [pullback.condition])
    have e' : a = (a ≫ pullback.fst f f) ≫ pullback.diagonal f := by
      apply pullback.hom_ext <;> simp [e]
    have : z ∈ Set.range a := by simp [ha]
    obtain ⟨w, rfl⟩ := this
    refine ⟨(a ≫ pullback.fst f f) w, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← e']
  have hsnd : IsIso (pullback.snd f f) :=
    IsIso.of_isIso_fac_left (pullback.diagonal_snd f)
  rw [Scheme.Hom.isIso_iff_finrank_eq]
  funext y
  obtain ⟨x, rfl⟩ := hsurj y
  rw [← Scheme.Hom.finrank_pullback_snd, Scheme.Hom.finrank_eq_one_of_isIso]
  rfl

/- English proof (translation)
Use `isFinite_left f` as an intermediate fact. Use `etale_left f` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `_ k _ _ s`. Conclude with `⟨fun a b h ↦ (cancel_mono f).mp h, fun y ↦ ⟨y ≫ inv f, by simp⟩⟩`.

Introduce `h`. Rewrite using `[isIso_iff_isIso_left, isIso_iff_bijective_algClosed]`. Introduce `k _ _`. Prove the components needed by the constructor for the conclusion. Introduce `a b (hab : a ≫ f.left = b ≫ f.left)`.

Establish `hb : b ≫ X.hom = a ≫ X.hom`. Rewrite using `[← Over.w f, ← Category.assoc, ← hab, Category.assoc]`. Use `(h k (a ≫ X.hom)).1 (a₁ := Over.homMk a rfl) (a₂ := Over.homMk b hb) (Over.OverMorphism.ext hab)` as an intermediate fact. Conclude with `congr(($this).left)`. Introduce `y`.

Take `⟨x, hx⟩` from `(h k (y ≫ Y.hom)).2 (Over.homMk y rfl)`. Conclude with `⟨x.left, congr(($hx).left)⟩`.
-/
theorem isIso_iff_bijective_over_algClosed (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ S),
      Function.Bijective fun x : Over.mk s ⟶ X ↦ x ≫ f := by
  have := isFinite_left f
  have := etale_left f
  constructor
  · intro _ k _ _ s
    exact ⟨fun a b h ↦ (cancel_mono f).mp h, fun y ↦ ⟨y ≫ inv f, by simp⟩⟩
  intro h
  rw [isIso_iff_isIso_left, isIso_iff_bijective_algClosed]
  intro k _ _
  constructor
  · intro a b (hab : a ≫ f.left = b ≫ f.left)
    have hb : b ≫ X.hom = a ≫ X.hom := by
      rw [← Over.w f, ← Category.assoc, ← hab, Category.assoc]
    have := (h k (a ≫ X.hom)).1 (a₁ := Over.homMk a rfl) (a₂ := Over.homMk b hb)
      (Over.OverMorphism.ext hab)
    exact congr(($this).left)
  · intro y
    obtain ⟨x, hx⟩ := (h k (y ≫ Y.hom)).2 (Over.homMk y rfl)
    exact ⟨x.left, congr(($hx).left)⟩

def eqLocus (f g : X ⟶ Y) : Set S :=
  {s | (Over.pullback (S.fromSpecResidueField s)).map f =
    (Over.pullback (S.fromSpecResidueField s)).map g}

def agreeι (f g : X ⟶ Y) :
    pullback (pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm))
      (pullback.diagonal Y.hom) ⟶ X.left :=
  pullback.fst _ _

instance (f g : X ⟶ Y) [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    IsOpenImmersion (agreeι f g) := by
  unfold agreeι; infer_instance

instance (f g : X ⟶ Y) [IsSeparated Y.hom] : IsClosedImmersion (agreeι f g) := by
  unfold agreeι; infer_instance

/- English proof (translation)
Establish `h` using `pullback.condition (f := pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm)) (g := pullback.diagonal Y.hom)`. Establish `h1` using `h =≫ pullback.fst _ _`. Establish `h2` using `h =≫ pullback.snd _ _`. Simplify using `only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h1 h2`. Conclude with `h1.trans h2.symm`.
-/
theorem agreeι_condition (f g : X ⟶ Y) : agreeι f g ≫ f.left = agreeι f g ≫ g.left := by
  have h := pullback.condition
    (f := pullback.lift f.left g.left ((Over.w f).trans (Over.w g).symm))
    (g := pullback.diagonal Y.hom)
  have h1 := h =≫ pullback.fst _ _
  have h2 := h =≫ pullback.snd _ _
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
    pullback.diagonal_snd, Category.comp_id] at h1 h2
  exact h1.trans h2.symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Apply the tactic sequence `have : pullback.lift a (a ≫ f.left) (by apply pullback.hom_ext <;> simp [h]) ≫ agreeι f g = a := pullback.lift_fst _ _ _`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `⟨_, by rw [← Scheme.Hom.comp_apply, this]⟩`.

Introduce `h`. Rewrite using `[← IsOpenImmersion.lift_fac (agreeι f g) a h, Category.assoc, Category.assoc, agreeι_condition]`.
-/
theorem comp_eq_comp_iff_range (f g : X ⟶ Y) [LocallyOfFiniteType Y.hom]
    [FormallyUnramified Y.hom] {Z : Scheme.{u}} (a : Z ⟶ X.left) :
    a ≫ f.left = a ≫ g.left ↔ Set.range a ⊆ Set.range (agreeι f g) := by
  constructor
  · intro h
    have : pullback.lift a (a ≫ f.left) (by apply pullback.hom_ext <;> simp [h]) ≫ agreeι f g
        = a := pullback.lift_fst _ _ _
    rintro _ ⟨z, rfl⟩
    exact ⟨_, by rw [← Scheme.Hom.comp_apply, this]⟩
  · intro h
    rw [← IsOpenImmersion.lift_fac (agreeι f g) a h, Category.assoc, Category.assoc,
      agreeι_condition]

/- English proof (translation)
Rewrite using `[← Scheme.Pullback.range_fst, ← comp_eq_comp_iff_range]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← (isPullback_pullback_map t f).w, ← (isPullback_pullback_map t g).w, h]`. Introduce `h ext1`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[(isPullback_pullback_map t f).w, (isPullback_pullback_map t g).w, h]`. Simplify using the standard rewrite rules.
-/
theorem pullback_map_eq_iff_preimage {T : Scheme.{u}} (t : T ⟶ S) (f g : X ⟶ Y)
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    (Over.pullback t).map f = (Over.pullback t).map g ↔
      X.hom ⁻¹' Set.range t ⊆ Set.range (agreeι f g) := by
  rw [← Scheme.Pullback.range_fst, ← comp_eq_comp_iff_range]
  constructor
  · intro h
    rw [← (isPullback_pullback_map t f).w, ← (isPullback_pullback_map t g).w, h]
  · intro h
    ext1
    apply pullback.hom_ext
    · rw [(isPullback_pullback_map t f).w, (isPullback_pullback_map t g).w, h]
    · simp

/- English proof (translation)
Use extensionality with `s`. Rewrite using `[Set.mem_compl_iff, eqLocus, Set.mem_setOf_eq, pullback_map_eq_iff_preimage, Scheme.range_fromSpecResidueField, Set.not_subset]`. Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Set.mem_compl_iff]`. The claim follows by propositional logic.
-/
theorem compl_eqLocus (f g : X ⟶ Y) [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    (eqLocus f g)ᶜ = X.hom '' (Set.range (agreeι f g))ᶜ := by
  ext s
  rw [Set.mem_compl_iff, eqLocus, Set.mem_setOf_eq, pullback_map_eq_iff_preimage,
    Scheme.range_fromSpecResidueField, Set.not_subset]
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, Set.mem_compl_iff]
  tauto

/- English proof (translation)
Rewrite using `[pullback_map_eq_iff_preimage, ← Set.compl_subset_compl (s := eqLocus f g), compl_eqLocus, Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl]`.
-/
theorem pullback_map_eq_iff {T : Scheme.{u}} (t : T ⟶ S) (f g : X ⟶ Y)
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    (Over.pullback t).map f = (Over.pullback t).map g ↔ Set.range t ⊆ eqLocus f g := by
  rw [pullback_map_eq_iff_preimage, ← Set.compl_subset_compl (s := eqLocus f g), compl_eqLocus,
    Set.image_subset_iff, Set.preimage_compl, Set.compl_subset_compl]

/- English proof (translation)
Establish `h : IsClopen (Set.range (agreeι f g))ᶜ` using `IsClopen.compl ⟨(agreeι f g).isClosedEmbedding.isClosed_range, (agreeι f g).isOpenEmbedding.isOpen_range⟩`. Rewrite using `[← isClopen_compl_iff, compl_eqLocus]`. Conclude with `⟨X.hom.isClosedMap _ h.isClosed, X.hom.isOpenMap _ h.isOpen⟩`.
-/
theorem isClopen_eqLocus (f g : X ⟶ Y) [UniversallyOpen X.hom] [UniversallyClosed X.hom]
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] [IsSeparated Y.hom] :
    IsClopen (eqLocus f g) := by
  have h : IsClopen (Set.range (agreeι f g))ᶜ :=
    IsClopen.compl ⟨(agreeι f g).isClosedEmbedding.isClosed_range,
      (agreeι f g).isOpenEmbedding.isOpen_range⟩
  rw [← isClopen_compl_iff, compl_eqLocus]
  exact ⟨X.hom.isClosedMap _ h.isClosed, X.hom.isOpenMap _ h.isOpen⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `Set.eq_univ_of_forall fun _ ↦ rfl`. Introduce `h`. Establish `h1` using `compl_eqLocus f g`.

Rewrite `h1` using `[h, Set.compl_univ, eq_comm, Set.image_eq_empty, Set.compl_empty_iff]`. Use `(comp_eq_comp_iff_range f g (𝟙 _)).mpr (by simp [h1])` as an intermediate fact. Use `ext1`. Simplify using `using this`.
-/
theorem eq_iff_eqLocus_eq_univ (f g : X ⟶ Y)
    [LocallyOfFiniteType Y.hom] [FormallyUnramified Y.hom] :
    f = g ↔ eqLocus f g = Set.univ := by
  constructor
  · rintro rfl
    exact Set.eq_univ_of_forall fun _ ↦ rfl
  · intro h
    have h1 := compl_eqLocus f g
    rw [h, Set.compl_univ, eq_comm, Set.image_eq_empty, Set.compl_empty_iff] at h1
    have := (comp_eq_comp_iff_range f g (𝟙 _)).mpr (by simp [h1])
    ext1
    simpa using this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨IsOpenImmersion.lift U.ι t (by simpa using h), IsOpenImmersion.lift_fac _ _ _⟩`. Introduce and unpack `⟨t', rfl⟩ _ ⟨x, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]`.

Conclude with `⟨_, rfl⟩`.
-/
theorem range_subset_iff_factors {T : Scheme.{u}} (t : T ⟶ S) (U : S.Opens) :
    Set.range t ⊆ U ↔ ∃ t' : T ⟶ U, t' ≫ U.ι = t := by
  constructor
  · intro h
    exact ⟨IsOpenImmersion.lift U.ι t (by simpa using h), IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨t', rfl⟩ _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩

/- English proof (translation)
Take `⟨hc⟩` from `nonempty_isColimit_binaryCofanMk_of_isCompl i j (by`. Rewrite using `[isCompl_iff, disjoint_iff, codisjoint_iff]`. Apply the tactic sequence `constructor <;> ext1 <;> simp [h])`. Establish `: coprod.desc i j = ((coprodIsCoprod _ _).coconePointUniqueUpToIso hc).hom`. Apply `coprod.hom_ext` to reduce the goal to its premises.

Rewrite using `[coprod.inl_desc]`. Conclude with `((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨.left⟩).symm`. Rewrite using `[coprod.inr_desc]`. Conclude with `((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨.right⟩).symm`. Rewrite using `[this]`.

Conclude with `Iso.isIso_hom _`.
-/
theorem isIso_coprodDesc {U V X : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i]
    [IsOpenImmersion j] (h : Set.range j = (Set.range i)ᶜ) : IsIso (coprod.desc i j) := by
  obtain ⟨hc⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl i j (by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff]
    constructor <;> ext1 <;> simp [h])
  have : coprod.desc i j = ((coprodIsCoprod _ _).coconePointUniqueUpToIso hc).hom := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      exact ((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨.left⟩).symm
    · rw [coprod.inr_desc]
      exact ((coprodIsCoprod _ _).comp_coconePointUniqueUpToIso_hom hc ⟨.right⟩).symm
  rw [this]
  exact Iso.isIso_hom _

/- English proof (translation)
Establish `hi : IsClosedImmersion i` using `.of_isPreimmersion _ (by`. Rewrite using `[← isOpen_compl_iff, ← h]`. Conclude with `j.isOpenEmbedding.isOpen_range)`. Establish `hj : IsClosedImmersion j` using `.of_isPreimmersion _ (by`. Rewrite using `[h, isClosed_compl_iff]`.

Conclude with `i.isOpenEmbedding.isOpen_range)`. Use `wlog hS : ∃ R, S = Spec R generalizing U V X S`. Take `⟨R, g, _, s, rfl⟩` from `S.exists_Spec_apply_eq s`. Establish `H` using `IsPullback.of_hasPullback p g`. Establish `Hi` using `IsPullback.of_hasPullback i (pullback.fst p g)`.

Establish `Hj` using `IsPullback.of_hasPullback j (pullback.fst p g)`. Rewrite using `[← Scheme.Hom.finrank_of_isPullback _ _ _ _ H, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (Hi.paste_vert H), ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (Hj.paste_vert H)]`. Use `this _ _ ?_ _ _ inferInstance inferInstance ⟨_, rfl⟩` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, h, Set.preimage_compl]`. Take `⟨R, rfl⟩` from `hS`.

Use `wlog hU : ∃ A, U = Spec A generalizing U`. Establish `_ : IsAffine U` using `isAffine_of_isAffineHom (i ≫ p)`. Rewrite using `[← Scheme.Hom.finrank_comp_left_of_isIso U.isoSpec.inv (i ≫ p), ← Category.assoc]`. Use `this _ ?_ inferInstance ⟨_, rfl⟩` and prove the remaining obligations. Rewrite using `[h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, U.isoSpec.inv.surjective.range_eq, Set.image_univ]`.

Take `⟨A, rfl⟩` from `hU`. Use `wlog hV : ∃ B, V = Spec B generalizing V`. Establish `_ : IsAffine V` using `isAffine_of_isAffineHom (j ≫ p)`. Rewrite using `[← Scheme.Hom.finrank_comp_left_of_isIso V.isoSpec.inv (j ≫ p), ← Category.assoc]`. Use `this _ inferInstance ?_ ⟨_, rfl⟩` and prove the remaining obligations.

Rewrite using `[← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, V.isoSpec.inv.surjective.range_eq, Set.image_univ]`. Take `⟨B, rfl⟩` from `hV`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (i ≫ p)`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (j ≫ p)`. Establish `hφ1 : φ.hom.Finite` using `by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance`.

Establish `hφ2 : φ.hom.Flat` using `by rw [← Flat.SpecMap_iff, hφ]; infer_instance`. Establish `hψ1 : ψ.hom.Finite` using `by rw [← IsFinite.SpecMap_iff, hψ]; infer_instance`. Establish `hψ2 : ψ.hom.Flat` using `by rw [← Flat.SpecMap_iff, hψ]; infer_instance`. Establish `hiso` using `isIso_coprodDesc i j h`. Use `algebraize [φ.hom, ψ.hom]`.

Establish `e : coprod.desc i j ≫ p = coprodSpec A B ≫ Spec.map (CommRingCat.ofHom (algebraMap R (A × B)))`. Apply `coprod.hom_ext` to reduce the goal to its premises. Rewrite using `[coprod.inl_desc_assoc, ← hφ, coprodSpec_inl_assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[coprod.inr_desc_assoc, ← hψ, coprodSpec_inr_assoc, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `: IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (A × B))))`. Rewrite using `[IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.mpr inferInstance`. Establish `hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (A × B))))`.

Rewrite using `[← (IsIso.inv_comp_eq _).mpr e]`. Use `infer_instance`. Establish `: Module.Flat R (A × B)` using `RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hfl)`. Rewrite using `[← Scheme.Hom.finrank_comp_left_of_isIso (coprod.desc i j) p, e, Scheme.Hom.finrank_comp_left_of_isIso, ← hφ, ← hψ]`. Establish `e1` using `Scheme.Hom.finrank_SpecMap_algebraMap R (A × B) s`.

Establish `e2` using `Scheme.Hom.finrank_SpecMap_algebraMap R A s`. Establish `e3` using `Scheme.Hom.finrank_SpecMap_algebraMap R B s`. Rewrite `e1` using `[Module.rankAtStalk_prod]`. Conclude with `e1.trans (congrArg₂ (· + ·) e2.symm e3.symm)`.
-/
theorem finrank_eq_add {U V X S : Scheme.{u}} (i : U ⟶ X) (j : V ⟶ X) [IsOpenImmersion i]
    [IsOpenImmersion j] (h : Set.range j = (Set.range i)ᶜ) (p : X ⟶ S) [IsFinite p] [Flat p]
    (s : S) : p.finrank s = (i ≫ p).finrank s + (j ≫ p).finrank s := by
  have hi : IsClosedImmersion i := .of_isPreimmersion _ (by
    rw [← isOpen_compl_iff, ← h]; exact j.isOpenEmbedding.isOpen_range)
  have hj : IsClosedImmersion j := .of_isPreimmersion _ (by
    rw [h, isClosed_compl_iff]; exact i.isOpenEmbedding.isOpen_range)
  wlog hS : ∃ R, S = Spec R generalizing U V X S
  · obtain ⟨R, g, _, s, rfl⟩ := S.exists_Spec_apply_eq s
    have H := IsPullback.of_hasPullback p g
    have Hi := IsPullback.of_hasPullback i (pullback.fst p g)
    have Hj := IsPullback.of_hasPullback j (pullback.fst p g)
    rw [← Scheme.Hom.finrank_of_isPullback _ _ _ _ H,
      ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (Hi.paste_vert H),
      ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (Hj.paste_vert H)]
    refine this _ _ ?_ _ _ inferInstance inferInstance ⟨_, rfl⟩
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, h, Set.preimage_compl]
  obtain ⟨R, rfl⟩ := hS
  wlog hU : ∃ A, U = Spec A generalizing U
  · have _ : IsAffine U := isAffine_of_isAffineHom (i ≫ p)
    rw [← Scheme.Hom.finrank_comp_left_of_isIso U.isoSpec.inv (i ≫ p), ← Category.assoc]
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rw [h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      U.isoSpec.inv.surjective.range_eq, Set.image_univ]
  obtain ⟨A, rfl⟩ := hU
  wlog hV : ∃ B, V = Spec B generalizing V
  · have _ : IsAffine V := isAffine_of_isAffineHom (j ≫ p)
    rw [← Scheme.Hom.finrank_comp_left_of_isIso V.isoSpec.inv (j ≫ p), ← Category.assoc]
    refine this _ inferInstance ?_ ⟨_, rfl⟩
    rw [← h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      V.isoSpec.inv.surjective.range_eq, Set.image_univ]
  obtain ⟨B, rfl⟩ := hV
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ p)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (j ≫ p)
  have hφ1 : φ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hφ]; infer_instance
  have hφ2 : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  have hψ1 : ψ.hom.Finite := by rw [← IsFinite.SpecMap_iff, hψ]; infer_instance
  have hψ2 : ψ.hom.Flat := by rw [← Flat.SpecMap_iff, hψ]; infer_instance
  have hiso := isIso_coprodDesc i j h
  algebraize [φ.hom, ψ.hom]
  have e : coprod.desc i j ≫ p =
      coprodSpec A B ≫ Spec.map (CommRingCat.ofHom (algebraMap R (A × B))) := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, ← hφ, coprodSpec_inl_assoc, ← Spec.map_comp]; rfl
    · rw [coprod.inr_desc_assoc, ← hψ, coprodSpec_inr_assoc, ← Spec.map_comp]; rfl
  have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R (A × B)))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap R (A × B)))) := by
    rw [← (IsIso.inv_comp_eq _).mpr e]
    infer_instance
  have : Module.Flat R (A × B) := RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hfl)
  rw [← Scheme.Hom.finrank_comp_left_of_isIso (coprod.desc i j) p, e,
    Scheme.Hom.finrank_comp_left_of_isIso, ← hφ, ← hψ]
  have e1 := Scheme.Hom.finrank_SpecMap_algebraMap R (A × B) s
  have e2 := Scheme.Hom.finrank_SpecMap_algebraMap R A s
  have e3 := Scheme.Hom.finrank_SpecMap_algebraMap R B s
  rw [Module.rankAtStalk_prod] at e1
  exact e1.trans (congrArg₂ (· + ·) e2.symm e3.symm)

def IsSplitOfRank {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ) : Prop :=
  ∃ s : Fin n → (S ⟶ X), (∀ i, s i ≫ p = 𝟙 S) ∧ Nonempty (IsColimit (Cofan.mk X s))

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i, fun i ↦ by simp, ⟨coproductIsCoproduct _⟩⟩`.
-/
theorem isSplitOfRank_sigmaDesc (S : Scheme.{u}) (n : ℕ) :
    IsSplitOfRank (Sigma.desc fun _ : Fin n ↦ 𝟙 S) n :=
  ⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i, fun i ↦ by simp, ⟨coproductIsCoproduct _⟩⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hc⟩`. Establish `: IsIso (Sigma.desc s)` using `(Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hc`. Conclude with `⟨asIso (Sigma.desc s), Sigma.hom_ext _ _ fun i ↦ by simp [hs]⟩`. Introduce and unpack `⟨e, he⟩`.

Use `⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom, fun i ↦ by simp [he], ?_⟩` and prove the remaining obligations. Rewrite using `[Cofan.nonempty_isColimit_iff_isIso_sigmaDesc]`. Establish `: Sigma.desc (fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom) = e.hom` using `Sigma.hom_ext _ _ fun i ↦ by simp`. Express the relevant statement in the definitionally equal form `IsIso (Sigma.desc fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom)`. Rewrite using `[this]`.

Use `infer_instance`.
-/
theorem isSplitOfRank_iff_exists_iso {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ) :
    IsSplitOfRank p n ↔
      ∃ e : (∐ fun _ : Fin n ↦ S) ≅ X, e.hom ≫ p = Sigma.desc fun _ : Fin n ↦ 𝟙 S := by
  constructor
  · rintro ⟨s, hs, hc⟩
    have : IsIso (Sigma.desc s) := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hc
    exact ⟨asIso (Sigma.desc s), Sigma.hom_ext _ _ fun i ↦ by simp [hs]⟩
  · rintro ⟨e, he⟩
    refine ⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom, fun i ↦ by simp [he], ?_⟩
    rw [Cofan.nonempty_isColimit_iff_isIso_sigmaDesc]
    have : Sigma.desc (fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom) = e.hom :=
      Sigma.hom_ext _ _ fun i ↦ by simp
    change IsIso (Sigma.desc fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom)
    rw [this]
    infer_instance

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[isSplitOfRank_iff_exists_iso]`. Introduce and unpack `⟨e, he⟩`. Use `⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom, fun i ↦ by simp [he], fun i ↦ inferInstance, fun x ↦ ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `e.hom.surjective x`.

Take `⟨i, y, hy⟩` from `(sigmaOpenCover fun _ : Fin n ↦ S).exists_eq x`. Take `rfl : Sigma.ι (fun _ : Fin n ↦ S) i y = x` from `hy`. Use `⟨i, ⟨y, Scheme.Hom.comp_apply _ _ _⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `j ⟨z, hz⟩`. Rewrite `hz` using `[Scheme.Hom.comp_apply]`.

Use `(sigmaι_eq_iff _ _ _ _ _).mp (e.hom.isOpenEmbedding.injective hz)` as an intermediate fact. Conclude with `congr(($this).1)`. Introduce and unpack `⟨s, hs, ho, hx⟩`. Use `⟨s, hs, nonempty_isColimit_cofanMk_of s ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Take `⟨i, hi⟩` from `(hx x).exists`. Conclude with `Opens.mem_iSup.mpr ⟨i, hi⟩`. Introduce `i j hij`. Rewrite using `[Function.onFun, disjoint_iff, eq_bot_iff]`.

Introduce and unpack `x ⟨hi, hj⟩`. Conclude with `(hij ((hx x).unique hi hj)).elim`.
-/
theorem isSplitOfRank_iff {X S : Scheme.{u}} (p : X ⟶ S) (n : ℕ) :
    IsSplitOfRank p n ↔ ∃ s : Fin n → (S ⟶ X), (∀ i, s i ≫ p = 𝟙 S) ∧
      (∀ i, IsOpenImmersion (s i)) ∧ ∀ x : X, ∃! i, x ∈ Set.range (s i) := by
  constructor
  · rw [isSplitOfRank_iff_exists_iso]
    rintro ⟨e, he⟩
    refine ⟨fun i ↦ Sigma.ι (fun _ : Fin n ↦ S) i ≫ e.hom, fun i ↦ by simp [he],
      fun i ↦ inferInstance, fun x ↦ ?_⟩
    obtain ⟨x, rfl⟩ := e.hom.surjective x
    obtain ⟨i, y, hy⟩ := (sigmaOpenCover fun _ : Fin n ↦ S).exists_eq x
    obtain rfl : Sigma.ι (fun _ : Fin n ↦ S) i y = x := hy
    refine ⟨i, ⟨y, Scheme.Hom.comp_apply _ _ _⟩, ?_⟩
    rintro j ⟨z, hz⟩
    rw [Scheme.Hom.comp_apply] at hz
    have := (sigmaι_eq_iff _ _ _ _ _).mp (e.hom.isOpenEmbedding.injective hz)
    exact congr(($this).1)
  · rintro ⟨s, hs, ho, hx⟩
    refine ⟨s, hs, nonempty_isColimit_cofanMk_of s ?_ ?_⟩
    · rw [eq_top_iff]
      intro x _
      obtain ⟨i, hi⟩ := (hx x).exists
      exact Opens.mem_iSup.mpr ⟨i, hi⟩
    · intro i j hij
      rw [Function.onFun, disjoint_iff, eq_bot_iff]
      rintro x ⟨hi, hj⟩
      exact (hij ((hx x).unique hi hj)).elim

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := q) (v₁₃ := t) (h₂₂ := p) ?_ (by simp) H.flip` and prove the remaining obligations. Rewrite using `[H.lift_snd, hσ]`. Conclude with `IsPullback.of_horiz_isIso ⟨by simp⟩`.
-/
theorem isPullback_section {X S X' S' : Scheme.{u}} {a : X' ⟶ X} {q : X' ⟶ S'} {p : X ⟶ S}
    {t : S' ⟶ S} (H : IsPullback a q p t) (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S) :
    IsPullback (H.lift (t ≫ σ) (𝟙 S') (by simp [hσ])) t a σ := by
  refine IsPullback.of_right (h₁₂ := q) (v₁₃ := t) (h₂₂ := p) ?_ (by simp) H.flip
  rw [H.lift_snd, hσ]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

/- English proof (translation)
Rewrite `h`, the goal using `[isSplitOfRank_iff]`. Take `⟨s, hs, ho, hx⟩` from `h`. Use `⟨fun i ↦ H.lift (t ≫ s i) (𝟙 S') (by simp [hs]), fun i ↦ H.lift_snd _ _ _, fun i ↦ MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_section H (s i) (hs i)).flip (ho i), fun x ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [range_of_isPullback (isPullback_section H _ (hs _)), Set.mem_preimage]`. Conclude with `hx (a x)`.
-/
theorem IsSplitOfRank.of_isPullback {X S X' S' : Scheme.{u}} {a : X' ⟶ X} {q : X' ⟶ S'}
    {p : X ⟶ S} {t : S' ⟶ S} (H : IsPullback a q p t) {n : ℕ} (h : IsSplitOfRank p n) :
    IsSplitOfRank q n := by
  rw [isSplitOfRank_iff] at h ⊢
  obtain ⟨s, hs, ho, hx⟩ := h
  refine ⟨fun i ↦ H.lift (t ≫ s i) (𝟙 S') (by simp [hs]), fun i ↦ H.lift_snd _ _ _,
    fun i ↦ MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (isPullback_section H (s i) (hs i)).flip (ho i), fun x ↦ ?_⟩
  simp only [range_of_isPullback (isPullback_section H _ (hs _)), Set.mem_preimage]
  exact hx (a x)

/- English proof (translation)
The claim follows from `h.of_isPullback (IsPullback.of_hasPullback p t)`.
-/
theorem IsSplitOfRank.pullback_snd {X S S' : Scheme.{u}} {p : X ⟶ S} {n : ℕ}
    (h : IsSplitOfRank p n) (t : S' ⟶ S) : IsSplitOfRank (pullback.snd p t) n :=
  h.of_isPullback (IsPullback.of_hasPullback p t)

/- English proof (translation)
The claim follows from `h.of_isPullback (a := (H'.isoIsPullback _ _ H).hom) (t := 𝟙 _) (IsPullback.of_horiz_isIso ⟨by simp⟩)`.
-/
theorem IsSplitOfRank.of_isPullback_of_isPullback {X S X' X'' S' : Scheme.{u}} {a : X' ⟶ X}
    {q : X' ⟶ S'} {a' : X'' ⟶ X} {q' : X'' ⟶ S'} {p : X ⟶ S} {t : S' ⟶ S}
    (H : IsPullback a q p t) (H' : IsPullback a' q' p t) {n : ℕ} (h : IsSplitOfRank q n) :
    IsSplitOfRank q' n :=
  h.of_isPullback (a := (H'.isoIsPullback _ _ H).hom) (t := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

/- English proof (translation)
Rewrite using `[isSplitOfRank_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, -, -, hx⟩`. Conclude with `⟨fun x ↦ (hx x).exists.choose.elim0⟩`. Introduce `h`.

Conclude with `⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun x ↦ h.elim x⟩`.
-/
theorem isSplitOfRank_zero_iff {X S : Scheme.{u}} (p : X ⟶ S) :
    IsSplitOfRank p 0 ↔ IsEmpty X := by
  rw [isSplitOfRank_iff]
  constructor
  · rintro ⟨s, -, -, hx⟩
    exact ⟨fun x ↦ (hx x).exists.choose.elim0⟩
  · intro h
    exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun x ↦ h.elim x⟩

/- English proof (translation)
Rewrite `h`, the goal using `[isSplitOfRank_iff]`. Take `⟨s, hs, ho, hx⟩` from `h`. Use `⟨Fin.cons σ fun i ↦ s i ≫ j, fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩` and prove the remaining obligations. Apply the tactic sequence `induction i using Fin.cases <;> simp [hσ, hs]`. Proceed by induction on `i using Fin.cases`.

Use `simpa`. Simplify using `only [Fin.cons_succ]`. Use `infer_instance`. Distinguish the cases in `hxσ : x ∈ Set.range σ`. Use `⟨0, by simpa using hxσ, fun i hi ↦ ?_⟩` and prove the remaining obligations.

Proceed by induction on `i using Fin.cases`. Both sides reduce to the same expression. Simplify using `only [Fin.cons_succ] at hi`. Take `⟨y, rfl⟩` from `hi`. Rewrite `hxσ` using `[Scheme.Hom.comp_apply]`.

Conclude with `((hj.le ⟨_, rfl⟩) hxσ).elim`. Take `⟨v, rfl⟩` from `hj.ge hxσ`. Take `⟨i, ⟨y, rfl⟩, hi⟩` from `hx v`. Use `⟨i.succ, ?_, fun k hk ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [Fin.cons_succ]`.

Conclude with `⟨y, Scheme.Hom.comp_apply _ _ _⟩`. Proceed by induction on `k using Fin.cases`. Conclude with `(hxσ (by simpa using hk)).elim`. Simplify using `only [Fin.cons_succ] at hk`. Take `⟨z, hz⟩` from `hk`.

Rewrite `hz` using `[Scheme.Hom.comp_apply]`. Rewrite using `[hi _ ⟨z, j.isOpenEmbedding.injective hz⟩]`.
-/
theorem IsSplitOfRank.succ {X V S : Scheme.{u}} {p : X ⟶ S} (σ : S ⟶ X) (hσ : σ ≫ p = 𝟙 S)
    [IsOpenImmersion σ] (j : V ⟶ X) [IsOpenImmersion j] (hj : Set.range j = (Set.range σ)ᶜ)
    {n : ℕ} (h : IsSplitOfRank (j ≫ p) n) : IsSplitOfRank p (n + 1) := by
  rw [isSplitOfRank_iff] at h ⊢
  obtain ⟨s, hs, ho, hx⟩ := h
  refine ⟨Fin.cons σ fun i ↦ s i ≫ j, fun i ↦ ?_, fun i ↦ ?_, fun x ↦ ?_⟩
  · induction i using Fin.cases <;> simp [hσ, hs]
  · induction i using Fin.cases
    · simpa
    · simp only [Fin.cons_succ]; infer_instance
  by_cases hxσ : x ∈ Set.range σ
  · refine ⟨0, by simpa using hxσ, fun i hi ↦ ?_⟩
    induction i using Fin.cases
    · rfl
    · simp only [Fin.cons_succ] at hi
      obtain ⟨y, rfl⟩ := hi
      rw [Scheme.Hom.comp_apply] at hxσ
      exact ((hj.le ⟨_, rfl⟩) hxσ).elim
  · obtain ⟨v, rfl⟩ := hj.ge hxσ
    obtain ⟨i, ⟨y, rfl⟩, hi⟩ := hx v
    refine ⟨i.succ, ?_, fun k hk ↦ ?_⟩
    · simp only [Fin.cons_succ]
      exact ⟨y, Scheme.Hom.comp_apply _ _ _⟩
    induction k using Fin.cases
    · exact (hxσ (by simpa using hk)).elim
    · simp only [Fin.cons_succ] at hk
      obtain ⟨z, hz⟩ := hk
      rw [Scheme.Hom.comp_apply] at hz
      rw [hi _ ⟨z, j.isOpenEmbedding.injective hz⟩]

def complOpen {X S : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ] : X.Opens :=
  ⟨(Set.range σ)ᶜ, σ.isClosedEmbedding.isClosed_range.isOpen_compl⟩

/- English proof (translation)
The claim follows from `Scheme.Opens.range_ι _`.
-/
theorem range_complOpen_ι {X S : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ] :
    Set.range (complOpen σ).ι = (Set.range σ)ᶜ := Scheme.Opens.range_ι _

instance {X S : Scheme.{u}} (σ : S ⟶ X) [IsClosedImmersion σ] [IsOpenImmersion σ] :
    IsClosedImmersion (complOpen σ).ι := .of_isPreimmersion _ (by
  rw [range_complOpen_ι, isClosed_compl_iff]; exact σ.isOpenEmbedding.isOpen_range)

/- English proof (translation)
Rewrite `h` using `[isSplitOfRank_iff]`. Take `⟨s, hs, ho, hx⟩` from `h`. Set `V : X.Opens` to `⨆ i : Fin n, (s i.succ).opensRange`. Establish `hV (x : X) : x ∈ Set.range V.ι ↔ ∃ i : Fin n, x ∈ Set.range (s i.succ)`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `Opens.mem_iSup`. Establish `hle (i : Fin n) : Set.range (s i.succ) ⊆ Set.range V.ι` using `fun x hx ↦ (hV x).mpr ⟨i, hx⟩`. Establish `hfac (i : Fin n)` using `IsOpenImmersion.lift_fac V.ι (s i.succ) (hle i)`. Use `⟨s 0, ho 0, V, hs 0, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Rewrite using `[hV]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi⟩ h0`. Conclude with `Fin.succ_ne_zero i ((hx x).unique hi h0)`. Introduce `h0`.

Take `⟨i, hi⟩` from `(hx x).exists`. Proceed by induction on `i using Fin.cases`. Conclude with `(h0 hi).elim`. Conclude with `⟨_, hi⟩`. Rewrite using `[isSplitOfRank_iff]`.

Use `⟨fun i ↦ IsOpenImmersion.lift V.ι (s i.succ) (hle i), fun i ↦ ?_, fun i ↦ ?_, fun v ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hfac, hs]`. Establish `: IsOpenImmersion (IsOpenImmersion.lift V.ι (s i.succ) (hle i) ≫ V.ι)`. Rewrite using `[hfac]`. Conclude with `ho _`.

Conclude with `IsOpenImmersion.of_comp _ V.ι`. Establish `key (i : Fin n) : v ∈ Set.range (IsOpenImmersion.lift V.ι (s i.succ) (hle i)) ↔ V.ι v ∈ Set.range (s i.succ)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, by rw [← Scheme.Hom.comp_apply, hfac]⟩`.

Introduce and unpack `⟨y, hy⟩`. Use `⟨y, V.ι.isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hfac, hy]`. Simplify using `only [key]`. Take `⟨i, hi⟩` from `(hV _).mp ⟨v, rfl⟩`.

Conclude with `⟨i, hi, fun j hj ↦ Fin.succ_injective _ ((hx _).unique hj hi)⟩`.
-/
theorem IsSplitOfRank.exists_of_succ {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ}
    (h : IsSplitOfRank p (n + 1)) :
    ∃ (σ : S ⟶ X) (_ : IsOpenImmersion σ) (V : X.Opens), σ ≫ p = 𝟙 S ∧
      Set.range V.ι = (Set.range σ)ᶜ ∧ IsSplitOfRank (V.ι ≫ p) n := by
  rw [isSplitOfRank_iff] at h
  obtain ⟨s, hs, ho, hx⟩ := h
  let V : X.Opens := ⨆ i : Fin n, (s i.succ).opensRange
  have hV (x : X) : x ∈ Set.range V.ι ↔ ∃ i : Fin n, x ∈ Set.range (s i.succ) := by
    rw [Scheme.Opens.range_ι]
    exact Opens.mem_iSup
  have hle (i : Fin n) : Set.range (s i.succ) ⊆ Set.range V.ι := fun x hx ↦ (hV x).mpr ⟨i, hx⟩
  have hfac (i : Fin n) := IsOpenImmersion.lift_fac V.ι (s i.succ) (hle i)
  refine ⟨s 0, ho 0, V, hs 0, ?_, ?_⟩
  · ext x
    rw [hV]
    constructor
    · rintro ⟨i, hi⟩ h0
      exact Fin.succ_ne_zero i ((hx x).unique hi h0)
    · intro h0
      obtain ⟨i, hi⟩ := (hx x).exists
      induction i using Fin.cases
      · exact (h0 hi).elim
      · exact ⟨_, hi⟩
  rw [isSplitOfRank_iff]
  refine ⟨fun i ↦ IsOpenImmersion.lift V.ι (s i.succ) (hle i), fun i ↦ ?_, fun i ↦ ?_,
    fun v ↦ ?_⟩
  · rw [← Category.assoc, hfac, hs]
  · have : IsOpenImmersion (IsOpenImmersion.lift V.ι (s i.succ) (hle i) ≫ V.ι) := by
      rw [hfac]; exact ho _
    exact IsOpenImmersion.of_comp _ V.ι
  have key (i : Fin n) : v ∈ Set.range (IsOpenImmersion.lift V.ι (s i.succ) (hle i)) ↔
      V.ι v ∈ Set.range (s i.succ) := by
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [← Scheme.Hom.comp_apply, hfac]⟩
    · rintro ⟨y, hy⟩
      refine ⟨y, V.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hfac, hy]
  simp only [key]
  obtain ⟨i, hi⟩ := (hV _).mp ⟨v, rfl⟩
  exact ⟨i, hi, fun j hj ↦ Fin.succ_injective _ ((hx _).unique hj hi)⟩

/- English proof (translation)
Take `⟨e, he⟩` from `(isSplitOfRank_iff_exists_iso p n).mp h`. Establish `: IsZariskiLocalAtSource @Etale` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Establish `: Etale (Sigma.desc fun _ : Fin n ↦ 𝟙 S)` using `IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance`. Rewrite using `[← e.inv_hom_id_assoc p, he]`. Use `infer_instance`.
-/
theorem IsSplitOfRank.etale {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n) :
    Etale p := by
  obtain ⟨e, he⟩ := (isSplitOfRank_iff_exists_iso p n).mp h
  have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  have : Etale (Sigma.desc fun _ : Fin n ↦ 𝟙 S) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun _ ↦ inferInstance
  rw [← e.inv_hom_id_assoc p, he]
  infer_instance

/- English proof (translation)
Proceed by induction on `n generalizing X with`. Consider the case `zero`. Use `(isSplitOfRank_zero_iff p).mp h` as an intermediate fact. Use `infer_instance`. Consider the case `succ n ih`.

Take `⟨σ, _, V, hσ, hV, h'⟩` from `h.exists_of_succ`. Use `ih h'` as an intermediate fact. Use `isIso_coprodDesc σ V.ι hV` as an intermediate fact. Establish `e : coprod.desc σ V.ι ≫ p = coprod.desc (𝟙 S) (V.ι ≫ p)`. Rewrite using `[coprod.desc_comp, hσ]`.

Rewrite using `[← IsIso.inv_hom_id_assoc (coprod.desc σ V.ι) p, e]`. Use `infer_instance`.
-/
theorem IsSplitOfRank.isFinite {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n) :
    IsFinite p := by
  induction n generalizing X with
  | zero =>
    have := (isSplitOfRank_zero_iff p).mp h
    infer_instance
  | succ n ih =>
    obtain ⟨σ, _, V, hσ, hV, h'⟩ := h.exists_of_succ
    have := ih h'
    have := isIso_coprodDesc σ V.ι hV
    have e : coprod.desc σ V.ι ≫ p = coprod.desc (𝟙 S) (V.ι ≫ p) := by
      rw [coprod.desc_comp, hσ]
    rw [← IsIso.inv_hom_id_assoc (coprod.desc σ V.ι) p, e]
    infer_instance

/- English proof (translation)
Use `h.isFinite` as an intermediate fact. Use `h.etale` as an intermediate fact. Proceed by induction on `n generalizing X with`. Consider the case `zero`. Use `(isSplitOfRank_zero_iff p).mp h` as an intermediate fact.

Use `finrank_eq_add (𝟙 X) (𝟙 X) (Subsingleton.elim _ _) p s` as an intermediate fact. Rewrite `this` using `[Category.id_comp]`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Take `⟨σ, _, V, hσ, hV, h'⟩` from `h.exists_of_succ`.

Rewrite using `[finrank_eq_add σ V.ι hV p s, hσ, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 S), ih h' h'.isFinite h'.etale, Pi.one_apply, add_comm]`.
-/
theorem IsSplitOfRank.finrank_eq {X S : Scheme.{u}} {p : X ⟶ S} {n : ℕ} (h : IsSplitOfRank p n)
    (s : S) : p.finrank s = n := by
  have := h.isFinite
  have := h.etale
  induction n generalizing X with
  | zero =>
    have := (isSplitOfRank_zero_iff p).mp h
    have := finrank_eq_add (𝟙 X) (𝟙 X) (Subsingleton.elim _ _) p s
    rw [Category.id_comp] at this
    omega
  | succ n ih =>
    obtain ⟨σ, _, V, hσ, hV, h'⟩ := h.exists_of_succ
    rw [finrank_eq_add σ V.ι hV p s, hσ, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 S),
      ih h' h'.isFinite h'.etale, Pi.one_apply, add_comm]

/- English proof (translation)
Proceed by induction on `n generalizing X S with`. Consider the case `zero`. Use `⟨S, X, 𝟙 S, 𝟙 X, p, inferInstance, inferInstance, inferInstance, IsPullback.of_horiz_isIso ⟨by simp⟩, (isSplitOfRank_zero_iff p).mpr ⟨fun x ↦ ?_⟩⟩` and prove the remaining obligations. Use `p.one_le_finrank_map x` as an intermediate fact. Rewrite `this` using `[hn]`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Establish `hp : Surjective p` using `p.one_le_finrank_iff_surjective.mp fun s ↦ by simp [hn]`. Set `σ` to `pullback.diagonal p`. Establish `hσ : σ ≫ pullback.snd p p = 𝟙 X` using `pullback.diagonal_snd p`.

Take `⟨S', X', t, a, q, h1, h2, h3, H, hq⟩` from `ih ((complOpen σ).ι ≫ pullback.snd p p) fun x ↦ by`. Use `finrank_eq_add σ (complOpen σ).ι (range_complOpen_ι σ) (pullback.snd p p) x` as an intermediate fact. Rewrite `this` using `[hσ, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 X), Scheme.Hom.finrank_pullback_snd, hn, Pi.one_apply]`. Use linear arithmetic over natural numbers and integers. Establish `G` using `IsPullback.of_hasPullback (pullback.snd p p) t`.

Establish `Gσ` using `isPullback_section G σ hσ`. Establish `Gj` using `IsPullback.of_hasPullback (complOpen σ).ι (pullback.fst (pullback.snd p p) t)`. Use `⟨S', _, t ≫ p, _, _, inferInstance, inferInstance, inferInstance, G.paste_horiz (IsPullback.of_hasPullback p p), ?_⟩` and prove the remaining obligations. Use `MorphismProperty.of_isPullback (P := @IsOpenImmersion) Gσ.flip inferInstance` as an intermediate fact. Use `IsSplitOfRank.succ (G.lift (t ≫ σ) (𝟙 _) _) (G.lift_snd _ _ _) (pullback.snd (complOpen σ).ι _) ?_ (hq.of_isPullback_of_isPullback H (Gj.paste_vert G))` and prove the remaining obligations.

Rewrite using `[Scheme.Pullback.range_snd, range_of_isPullback Gσ, range_complOpen_ι, Set.preimage_compl]`.
-/
theorem exists_isPullback_isSplitOfRank (n : ℕ) {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p]
    [Etale p] (hn : ∀ s, p.finrank s = n) :
    ∃ (S' X' : Scheme.{u}) (t : S' ⟶ S) (a : X' ⟶ X) (q : X' ⟶ S'),
      IsFinite t ∧ Etale t ∧ Surjective t ∧ IsPullback a q p t ∧ IsSplitOfRank q n := by
  induction n generalizing X S with
  | zero =>
    refine ⟨S, X, 𝟙 S, 𝟙 X, p, inferInstance, inferInstance, inferInstance,
      IsPullback.of_horiz_isIso ⟨by simp⟩, (isSplitOfRank_zero_iff p).mpr ⟨fun x ↦ ?_⟩⟩
    have := p.one_le_finrank_map x
    rw [hn] at this
    omega
  | succ n ih =>
    have hp : Surjective p := p.one_le_finrank_iff_surjective.mp fun s ↦ by simp [hn]
    let σ := pullback.diagonal p
    have hσ : σ ≫ pullback.snd p p = 𝟙 X := pullback.diagonal_snd p
    obtain ⟨S', X', t, a, q, h1, h2, h3, H, hq⟩ := ih ((complOpen σ).ι ≫ pullback.snd p p)
      fun x ↦ by
        have := finrank_eq_add σ (complOpen σ).ι (range_complOpen_ι σ) (pullback.snd p p) x
        rw [hσ, Scheme.Hom.finrank_eq_one_of_isIso (𝟙 X), Scheme.Hom.finrank_pullback_snd, hn,
          Pi.one_apply] at this
        omega
    have G := IsPullback.of_hasPullback (pullback.snd p p) t
    have Gσ := isPullback_section G σ hσ
    have Gj := IsPullback.of_hasPullback (complOpen σ).ι (pullback.fst (pullback.snd p p) t)
    refine ⟨S', _, t ≫ p, _, _, inferInstance, inferInstance, inferInstance,
      G.paste_horiz (IsPullback.of_hasPullback p p), ?_⟩
    have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) Gσ.flip inferInstance
    refine IsSplitOfRank.succ (G.lift (t ≫ σ) (𝟙 _) _) (G.lift_snd _ _ _)
      (pullback.snd (complOpen σ).ι _) ?_
      (hq.of_isPullback_of_isPullback H (Gj.paste_vert G))
    rw [Scheme.Pullback.range_snd, range_of_isPullback Gσ, range_complOpen_ι, Set.preimage_compl]

/- English proof (translation)
Take `⟨S', X', t, a, q, h1, h2, h3, H, hq⟩` from `exists_isPullback_isSplitOfRank n p hn`. Conclude with `⟨S', t, h1, h2, h3, hq.of_isPullback_of_isPullback H (IsPullback.of_hasPullback p t)⟩`.
-/
theorem exists_isSplitOfRank_pullback {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] [Etale p]
    {n : ℕ} (hn : ∀ s, p.finrank s = n) :
    ∃ (S' : Scheme.{u}) (t : S' ⟶ S), IsFinite t ∧ Etale t ∧ Surjective t ∧
      IsSplitOfRank (pullback.snd p t) n := by
  obtain ⟨S', X', t, a, q, h1, h2, h3, H, hq⟩ := exists_isPullback_isSplitOfRank n p hn
  exact ⟨S', t, h1, h2, h3, hq.of_isPullback_of_isPullback H (IsPullback.of_hasPullback p t)⟩

/- English proof (translation)
Use `wlog hX : ∃ A, X = Spec A generalizing X`. Establish `_ : IsAffine X` using `isAffine_of_isAffineHom p`. Establish `_ : Nonempty (Spec Γ(X, ⊤))` using `⟨X.isoSpec.hom (Classical.arbitrary X)⟩`. Take `⟨σ, hσ⟩` from `this (X.isoSpec.inv ≫ p) ⟨_, rfl⟩`. Conclude with `⟨σ ≫ X.isoSpec.inv, by simpa using hσ⟩`.

Take `⟨A, rfl⟩` from `hX`. Take `⟨φ, rfl⟩` from `Spec.map_surjective p`. Establish `h1 : φ.hom.Etale` using `HasRingHomProperty.Spec_iff (P := @Etale).mp inferInstance`. Set `: Algebra k A` to `φ.hom.toAlgebra`. Establish `: Algebra.Etale k A` using `h1`.

Set `x : PrimeSpectrum A` to `Classical.arbitrary (Spec A)`. Set `ψ` to `(Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k A).symm x`. Use `⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`.

Use extensionality with `a`. Conclude with `ψ.commutes a`.
-/
theorem exists_section_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] [Nonempty X] :
    ∃ σ : Spec (.of k) ⟶ X, σ ≫ p = 𝟙 _ := by
  wlog hX : ∃ A, X = Spec A generalizing X
  · have _ : IsAffine X := isAffine_of_isAffineHom p
    have _ : Nonempty (Spec Γ(X, ⊤)) := ⟨X.isoSpec.hom (Classical.arbitrary X)⟩
    obtain ⟨σ, hσ⟩ := this (X.isoSpec.inv ≫ p) ⟨_, rfl⟩
    exact ⟨σ ≫ X.isoSpec.inv, by simpa using hσ⟩
  obtain ⟨A, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective p
  have h1 : φ.hom.Etale := HasRingHomProperty.Spec_iff (P := @Etale).mp inferInstance
  let : Algebra k A := φ.hom.toAlgebra
  have : Algebra.Etale k A := h1
  let x : PrimeSpectrum A := Classical.arbitrary (Spec A)
  let ψ := (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum k A).symm x
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_⟩
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext a
  exact ψ.commutes a

/- English proof (translation)
Take `⟨S', X', t, a, q, h1, h2, h3, H, hq⟩` from `exists_isPullback_isSplitOfRank (p.finrank s) p fun s' ↦ by rw [Subsingleton.elim s' s]`. Establish `: Nonempty S'` using `⟨(t.surjective s).choose⟩`. Take `⟨σ, hσ⟩` from `exists_section_of_isSepClosed t`. Establish `G` using `(IsPullback.of_hasPullback q σ).paste_horiz H`. Rewrite `G` using `[hσ]`.

Conclude with `(hq.pullback_snd σ).of_isPullback_of_isPullback G IsPullback.of_id_fst`.
-/
theorem isSplitOfRank_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] (s : Spec (.of k)) :
    IsSplitOfRank p (p.finrank s) := by
  obtain ⟨S', X', t, a, q, h1, h2, h3, H, hq⟩ := exists_isPullback_isSplitOfRank (p.finrank s) p
    fun s' ↦ by rw [Subsingleton.elim s' s]
  have : Nonempty S' := ⟨(t.surjective s).choose⟩
  obtain ⟨σ, hσ⟩ := exists_section_of_isSepClosed t
  have G := (IsPullback.of_hasPullback q σ).paste_horiz H
  rw [hσ] at G
  exact (hq.pullback_snd σ).of_isPullback_of_isPullback G IsPullback.of_id_fst

/- English proof (translation)
Take `⟨s⟩ : Nonempty (Spec (.of k))` from `inferInstance`. Conclude with `⟨_, (isSplitOfRank_iff_exists_iso p _).mp (isSplitOfRank_of_isSepClosed p s)⟩`.
-/
theorem exists_iso_sigma_of_isSepClosed {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsFinite p] [Etale p] :
    ∃ (n : ℕ) (e : (∐ fun _ : Fin n ↦ Spec (.of k)) ≅ X),
      e.hom ≫ p = Sigma.desc fun _ : Fin n ↦ 𝟙 (Spec (.of k)) := by
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstance
  exact ⟨_, (isSplitOfRank_iff_exists_iso p _).mp (isSplitOfRank_of_isSepClosed p s)⟩

/- English proof (translation)
Take `⟨s, hs, ho, hx⟩` from `(isSplitOfRank_iff _ _).mp (isSplitOfRank_of_isSepClosed (pullback.snd p t) z)`. Rewrite using `[← Scheme.Hom.finrank_pullback_snd]`. Set `F : Fin ((pullback.snd p t).finrank z) → {x : Spec (.of k) ⟶ X // x ≫ p = t}` to `fun i ↦ ⟨s i ≫ pullback.fst p t, by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]⟩`. Establish `hF : Function.Bijective F`.

Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Establish `: s i = s j` using `pullback.hom_ext congr(($hij).1) (by rw [hs, hs])`. Conclude with `(hx (s i z)).unique ⟨z, rfl⟩ ⟨z, by rw [this]⟩`. Introduce and unpack `⟨x, hxp⟩`.

Set `y : Spec (.of k) ⟶ pullback p t` to `pullback.lift x (𝟙 _) (by simp [hxp])`. Take `⟨i, hi⟩` from `(hx (y z)).exists`. Establish `hr : Set.range y ⊆ Set.range (s i)`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Subsingleton.elim w z]` and apply the resulting hypothesis.

Establish `h1` using `IsOpenImmersion.lift_fac (s i) y hr`. Establish `h2 : IsOpenImmersion.lift (s i) y hr = 𝟙 _`. Use `h1 =≫ pullback.snd p t` as an intermediate fact. Rewrite `this` using `[Category.assoc, hs, Category.comp_id, pullback.lift_snd]`. Then use the resulting hypothesis. Rewrite `h1` using `[h2, Category.id_comp]`.

Use `⟨i, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[F, h1, y]`. Conclude with `⟨.of_surjective F hF.2, by rw [← Nat.card_eq_of_bijective F hF, Nat.card_fin]⟩`.
-/
theorem card_points_eq_finrank {X S : Scheme.{u}} (p : X ⟶ S) [IsFinite p] [Etale p]
    {k : Type u} [Field k] [IsSepClosed k] (t : Spec (.of k) ⟶ S) (z : Spec (.of k)) :
    Finite {x : Spec (.of k) ⟶ X // x ≫ p = t} ∧
      Nat.card {x : Spec (.of k) ⟶ X // x ≫ p = t} = p.finrank (t z) := by
  obtain ⟨s, hs, ho, hx⟩ :=
    (isSplitOfRank_iff _ _).mp (isSplitOfRank_of_isSepClosed (pullback.snd p t) z)
  rw [← Scheme.Hom.finrank_pullback_snd]
  let F : Fin ((pullback.snd p t).finrank z) → {x : Spec (.of k) ⟶ X // x ≫ p = t} :=
    fun i ↦ ⟨s i ≫ pullback.fst p t, by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i j hij
      have : s i = s j := pullback.hom_ext congr(($hij).1) (by rw [hs, hs])
      exact (hx (s i z)).unique ⟨z, rfl⟩ ⟨z, by rw [this]⟩
    · rintro ⟨x, hxp⟩
      let y : Spec (.of k) ⟶ pullback p t := pullback.lift x (𝟙 _) (by simp [hxp])
      obtain ⟨i, hi⟩ := (hx (y z)).exists
      have hr : Set.range y ⊆ Set.range (s i) := by
        rintro _ ⟨w, rfl⟩
        rwa [Subsingleton.elim w z]
      have h1 := IsOpenImmersion.lift_fac (s i) y hr
      have h2 : IsOpenImmersion.lift (s i) y hr = 𝟙 _ := by
        have := h1 =≫ pullback.snd p t
        rwa [Category.assoc, hs, Category.comp_id, pullback.lift_snd] at this
      rw [h2, Category.id_comp] at h1
      refine ⟨i, Subtype.ext ?_⟩
      simp [F, h1, y]
  exact ⟨.of_surjective F hF.2, by rw [← Nat.card_eq_of_bijective F hF, Nat.card_fin]⟩

def isoLocusOpen (f : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    S.Opens := ⟨isoLocus f, (isClopen_isoLocus f).isOpen⟩

def eqLocusOpen (f g : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    S.Opens := ⟨eqLocus f g, (isClopen_eqLocus f g).isOpen⟩

instance (f : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsClosedImmersion (isoLocusOpen f).ι := .of_isPreimmersion _ (by
  rw [Scheme.Opens.range_ι]; exact (isClopen_isoLocus f).isClosed)

instance (f g : X ⟶ Y) [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsClosedImmersion (eqLocusOpen f g).ι := .of_isPreimmersion _ (by
  rw [Scheme.Opens.range_ι]; exact (isClopen_eqLocus f g).isClosed)

/- English proof (translation)
The claim follows from `(isIso_pullback_map_iff t f).trans (range_subset_iff_factors t (isoLocusOpen f))`.
-/
theorem isIso_pullback_map_iff_factors {T : Scheme.{u}} (t : T ⟶ S) (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    IsIso ((Over.pullback t).map f) ↔ ∃ t' : T ⟶ isoLocusOpen f, t' ≫ (isoLocusOpen f).ι = t :=
  (isIso_pullback_map_iff t f).trans (range_subset_iff_factors t (isoLocusOpen f))

/- English proof (translation)
The claim follows from `(pullback_map_eq_iff t f g).trans (range_subset_iff_factors t (eqLocusOpen f g))`.
-/
theorem pullback_map_eq_iff_factors {T : Scheme.{u}} (t : T ⟶ S) (f g : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    (Over.pullback t).map f = (Over.pullback t).map g ↔
      ∃ t' : T ⟶ eqLocusOpen f g, t' ≫ (eqLocusOpen f g).ι = t :=
  (pullback_map_eq_iff t f g).trans (range_subset_iff_factors t (eqLocusOpen f g))

/- English proof (translation)
The claim follows from `(eq_iff_eqLocus_eq_univ f g).mpr ((isClopen_eqLocus f g).eq_univ ⟨s, hs⟩)`.
-/
theorem eq_of_mem_eqLocus [PreconnectedSpace S] (f g : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] {s : S} (hs : s ∈ eqLocus f g) :
    f = g :=
  (eq_iff_eqLocus_eq_univ f g).mpr ((isClopen_eqLocus f g).eq_univ ⟨s, hs⟩)

/- English proof (translation)
The claim follows from `(isIso_iff_isoLocus_eq_univ f).mpr ((isClopen_isoLocus f).eq_univ ⟨s, hs⟩)`.
-/
theorem isIso_of_mem_isoLocus [PreconnectedSpace S] (f : X ⟶ Y)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] {s : S} (hs : s ∈ isoLocus f) :
    IsIso f :=
  (isIso_iff_isoLocus_eq_univ f).mpr ((isClopen_isoLocus f).eq_univ ⟨s, hs⟩)

/- English proof (translation)
Use `⟨fun f ↦ ⟨⟨isFinite_left f, etale_left f⟩, isClopen_isoLocus f, fun t ↦ isIso_pullback_map_iff_factors t f, ?_⟩, fun f g ↦ ⟨isClopen_eqLocus f g, fun t ↦ pullback_map_eq_iff_factors t f g⟩, ?_, fun n hn ↦ exists_isSplitOfRank_pullback X.hom hn⟩` and prove the remaining obligations. Use `isFinite_left f` as an intermediate fact. Use `etale_left f` as an intermediate fact. Rewrite using `[isIso_iff_isIso_left, isIso_iff_bijective_algClosed]`. Introduce and unpack `k _ _ ⟨e⟩`.

Take `⟨s⟩ : Nonempty (Spec (.of k))` from `inferInstance`. Conclude with `⟨_, (isSplitOfRank_of_isSepClosed (X.hom ≫ e.hom) s).of_isPullback (a := 𝟙 _) (t := e.hom) (IsPullback.of_horiz_isIso ⟨by simp⟩)⟩`.
-/
theorem finiteEtale_open_closed_conditions {S : Scheme.{u}} (X Y : Over S)
    [IsFinite X.hom] [Etale X.hom] [IsFinite Y.hom] [Etale Y.hom] :
    (∀ f : X ⟶ Y, (IsFinite f.left ∧ Etale f.left) ∧ IsClopen (isoLocus f) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ S), IsIso ((Over.pullback t).map f) ↔
        ∃ t' : T ⟶ isoLocusOpen f, t' ≫ (isoLocusOpen f).ι = t) ∧
      (IsIso f ↔ ∀ (k : Type u) [Field k] [IsAlgClosed k],
        Function.Bijective fun x : Spec (.of k) ⟶ X.left ↦ x ≫ f.left)) ∧
    (∀ f g : X ⟶ Y, IsClopen (eqLocus f g) ∧
      ∀ {T : Scheme.{u}} (t : T ⟶ S), (Over.pullback t).map f = (Over.pullback t).map g ↔
        ∃ t' : T ⟶ eqLocusOpen f g, t' ≫ (eqLocusOpen f g).ι = t) ∧
    (∀ (k : Type u) [Field k] [IsSepClosed k], Nonempty (S ≅ Spec (.of k)) →
      ∃ n, IsSplitOfRank X.hom n) ∧
    (∀ n : ℕ, (∀ s, X.hom.finrank s = n) → ∃ (S' : Scheme.{u}) (t : S' ⟶ S),
      IsFinite t ∧ Etale t ∧ Surjective t ∧ IsSplitOfRank (pullback.snd X.hom t) n) := by
  refine ⟨fun f ↦ ⟨⟨isFinite_left f, etale_left f⟩, isClopen_isoLocus f,
    fun t ↦ isIso_pullback_map_iff_factors t f, ?_⟩,
    fun f g ↦ ⟨isClopen_eqLocus f g, fun t ↦ pullback_map_eq_iff_factors t f g⟩, ?_,
    fun n hn ↦ exists_isSplitOfRank_pullback X.hom hn⟩
  · have := isFinite_left f
    have := etale_left f
    rw [isIso_iff_isIso_left, isIso_iff_bijective_algClosed]
  · rintro k _ _ ⟨e⟩
    obtain ⟨s⟩ : Nonempty (Spec (.of k)) := inferInstance
    exact ⟨_, (isSplitOfRank_of_isSepClosed (X.hom ≫ e.hom) s).of_isPullback (a := 𝟙 _)
      (t := e.hom) (IsPullback.of_horiz_isIso ⟨by simp⟩)⟩

end GlobalTheory.FinEt
