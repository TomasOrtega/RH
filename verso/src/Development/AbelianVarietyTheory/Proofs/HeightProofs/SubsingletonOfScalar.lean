import Mathlib
import Formalism.SharpRestriction.AbelianModels.AbelianLocalSystemsExist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondIffHasMultiplicities
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso

noncomputable section

namespace GlobalTheory.DefiniteAbelian

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

section Scalar

variable {S S' : Scheme.{0}} {k : Type} [CommRing k]

def ActsBy (G : Over S) [GrpObj G] (φ : G ⟶ G) (t : Sp k ⟶ S) (c : k) : Prop :=
  ∀ v : Sp (DualNumber k) ⟶ G.left, v ≫ G.hom = spMap (algebraMap k (DualNumber k)) ≫ t →
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v = t ≫ η[G].left →
      v ≫ φ.left = spMap (epsScaleR c) ≫ v

/- English proof (translation)
Establish `e` using `congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))`. Establish `e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G']` using `by rw [Hom.one_def]; simp`. Rewrite `e` using `[e₁]`. Use `e.trans ?_` and prove the remaining obligations. Use `show (toUnit _ ≫ η[G]).left = _`.

Simplify using the standard rewrite rules.
-/
theorem unit_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f F) : η[G'].left ≫ F = f ≫ η[G].left :=
  by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp

/- English proof (translation)
The claim follows from `Over.w η[G]`.
-/
theorem unit_hom (G : Over S) [GrpObj G] : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `H v hv h0`. Set `v'` to `h.1.lift v (spMap (algebraMap k (DualNumber k)) ≫ t) (by rw [hv, Category.assoc])`. Establish `e₁ : v' ≫ F = v` using `h.1.lift_fst _ _ _`. Establish `e₂ : v' ≫ G'.hom = _` using `h.1.lift_snd _ _ _`.

Use `H v' e₂ (h.1.hom_ext (by rw [Category.assoc, e₁, h0, Category.assoc, Category.assoc, unit_pull h]) (by rw [Category.assoc, e₂, Category.assoc, unit_hom, reassoc_of% Diag.fstHom_base (R := k), Category.comp_id]))` as an intermediate fact. Rewrite using `[← e₁, Category.assoc, ← hφ, reassoc_of% this]`. Introduce `H v hv h0`. Use `H (v ≫ F) (by rw [Category.assoc, h.1.w, reassoc_of% hv]) (by rw [reassoc_of% h0, unit_pull h, Category.assoc])` as an intermediate fact. Use `h.1.hom_ext (by rw [Category.assoc, hφ, ← Category.assoc, this, Category.assoc]) ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, Over.w, Category.assoc, hv, ← reassoc_of% Diag.epsScaleR_base c]`.
-/
theorem actsBy_pull {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f F) {φ : G ⟶ G} {φ' : G' ⟶ G'} (hφ : φ'.left ≫ F = F ≫ φ.left)
    (t : Sp k ⟶ S') (c : k) : ActsBy G' φ' t c ↔ ActsBy G φ (t ≫ f) c := by
  constructor
  · intro H v hv h0
    let v' := h.1.lift v (spMap (algebraMap k (DualNumber k)) ≫ t) (by rw [hv, Category.assoc])
    have e₁ : v' ≫ F = v := h.1.lift_fst _ _ _
    have e₂ : v' ≫ G'.hom = _ := h.1.lift_snd _ _ _
    have := H v' e₂ (h.1.hom_ext (by rw [Category.assoc, e₁, h0, Category.assoc, Category.assoc, unit_pull h])
      (by rw [Category.assoc, e₂, Category.assoc, unit_hom, reassoc_of% Diag.fstHom_base (R := k), Category.comp_id]))
    rw [← e₁, Category.assoc, ← hφ, reassoc_of% this]
  · intro H v hv h0
    have := H (v ≫ F) (by rw [Category.assoc, h.1.w, reassoc_of% hv])
      (by rw [reassoc_of% h0, unit_pull h, Category.assoc])
    refine h.1.hom_ext (by rw [Category.assoc, hφ, ← Category.assoc, this, Category.assoc]) ?_
    rw [Category.assoc, Over.w, Category.assoc, hv, ← reassoc_of% Diag.epsScaleR_base c]

/- English proof (translation)
Set `f' : Over.mk (f ≫ s) ⟶ Over.mk s` to `Over.homMk f rfl`. Set `g' : Over.mk (f ≫ s) ⟶ Over.mk s` to `Over.homMk g hs.symm`. Establish `: IsSeparated (Over.mk s).hom` using `‹_›`. Establish `hci : IsClosedImmersion (equalizer.ι f' g').left` using `inferInstance`. Set `l : Over.mk (spMap i ≫ f ≫ s) ⟶ Over.mk (f ≫ s)` to `Over.homMk (spMap i) rfl`.

Take `⟨l', hl⟩ : ∃ l' : Sp A ⟶ (equalizer f' g').left, l' ≫ (equalizer.ι f' g').left = spMap i` from `⟨_, congrArg (·.left) (equalizer.lift_ι l (Over.OverMorphism.ext h : l ≫ f' = l ≫ g'))⟩`. Establish `hc : (equalizer.ι f' g').left ≫ f = (equalizer.ι f' g').left ≫ g` using `congrArg (·.left) (equalizer.condition f' g')`. Take `⟨I, e, he⟩` from `IsClosedImmersion.Spec_iff.mp hci`. Rewrite `hl` using `[he, ← Category.assoc, ← Spec.map_preimage (l' ≫ e.hom), ← Spec.map_comp]`. Establish `hI : I = ⊥` using `le_bot_iff.mp fun x hx => hi (by`.

Establish `h8` using `congrArg (fun φ => φ.hom x) (Spec.map_injective hl)`. Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h8`. Rewrite using `[← h8, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero])`. Substitute `hI` using the available equality. Establish `: IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (CommRingCat.of R))))`.

Rewrite using `[ConcreteCategory.isIso_iff_bijective]`. Conclude with `(RingEquiv.quotientBot R).symm.bijective`. Rewrite `hc` using `[he]`. Conclude with `(cancel_epi _).1 hc`.
-/
theorem ext_of_injective {R A : Type} [CommRing R] [CommRing A] (i : R →+* A) (hi : Function.Injective i)
    {X : Scheme.{0}} (s : X ⟶ S) [IsSeparated s] (f g : Sp R ⟶ X) (hs : f ≫ s = g ≫ s)
    (h : spMap i ≫ f = spMap i ≫ g) : f = g := by
  let f' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk f rfl
  let g' : Over.mk (f ≫ s) ⟶ Over.mk s := Over.homMk g hs.symm
  have : IsSeparated (Over.mk s).hom := ‹_›
  have hci : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  let l : Over.mk (spMap i ≫ f ≫ s) ⟶ Over.mk (f ≫ s) := Over.homMk (spMap i) rfl
  obtain ⟨l', hl⟩ : ∃ l' : Sp A ⟶ (equalizer f' g').left, l' ≫ (equalizer.ι f' g').left = spMap i :=
    ⟨_, congrArg (·.left) (equalizer.lift_ι l (Over.OverMorphism.ext h : l ≫ f' = l ≫ g'))⟩
  have hc : (equalizer.ι f' g').left ≫ f = (equalizer.ι f' g').left ≫ g :=
    congrArg (·.left) (equalizer.condition f' g')
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hci
  rw [he, ← Category.assoc, ← Spec.map_preimage (l' ≫ e.hom), ← Spec.map_comp] at hl
  have hI : I = ⊥ := le_bot_iff.mp fun x hx => hi (by
    have h8 := congrArg (fun φ => φ.hom x) (Spec.map_injective hl)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at h8
    rw [← h8, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero, map_zero])
  subst hI
  have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (⊥ : Ideal (CommRingCat.of R)))) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (RingEquiv.quotientBot R).symm.bijective
  rw [he] at hc
  exact (cancel_epi _).1 hc

variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `(Spec.map_comp _ _).symm`.
-/
theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

/- English proof (translation)
Rewrite using `[sp_comp, sp_comp]`. Use `congr 1`. Apply the tactic sequence `ext x <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dual_base (i : R →+* k) : spMap (dualMapR i) ≫ spMap (algebraMap R (DualNumber R)) =
    spMap (algebraMap k (DualNumber k)) ≫ spMap i := by
  rw [sp_comp, sp_comp]
  congr 1
  ext x <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Rewrite using `[sp_comp, sp_comp]`. Use `congr 1`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `[dualMapR]`.
-/
theorem fst_dual (i : R →+* k) : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (dualMapR i) =
    spMap i ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  rw [sp_comp, sp_comp]
  congr 1
  refine RingHom.ext fun x => ?_
  simp [dualMapR]

/- English proof (translation)
Rewrite using `[sp_comp, sp_comp]`. Use `congr 1`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [dualMapR, epsScaleR, mul_comm]`.
-/
theorem scale_dual (i : R →+* k) (c : R) : spMap (epsScaleR (i c)) ≫ spMap (dualMapR i) =
    spMap (dualMapR i) ≫ spMap (epsScaleR c) := by
  rw [sp_comp, sp_comp]
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMapR, epsScaleR, mul_comm]

/- English proof (translation)
Rewrite using `[sp_comp, sp_comp]`. Use `congr 1`. Use `RingHom.ext fun x => ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [epsScaleR, mul_left_comm]`.
-/
theorem scale_comm (a c : k) : spMap (epsScaleR a) ≫ spMap (epsScaleR c) =
    spMap (epsScaleR c) ≫ spMap (epsScaleR a) := by
  rw [sp_comp, sp_comp]
  congr 1
  refine RingHom.ext fun x => ?_
  ext <;> simp [epsScaleR, mul_left_comm]

/- English proof (translation)
Introduce `v hv h0`. Use `H (spMap (dualMapR i) ≫ v) (by rw [Category.assoc, hv, reassoc_of% dual_base i]) (by rw [reassoc_of% fst_dual i, h0, Category.assoc])` as an intermediate fact. Use `ext_of_injective (dualMapR i) (fun a b e => ?_) G.hom _ _ ?_ ?_` and prove the remaining obligations. Establish `e₁` using `congrArg TrivSqZeroExt.fst e`. Establish `e₂` using `congrArg TrivSqZeroExt.snd e`.

Simplify using `[dualMapR] at e₁ e₂`. Conclude with `TrivSqZeroExt.ext (hi e₁) (hi e₂)`. Rewrite using `[Category.assoc, Over.w, Category.assoc, hv, ← reassoc_of% Diag.epsScaleR_base c]`. Rewrite using `[← Category.assoc, this, reassoc_of% scale_dual i c]`.
-/
theorem actsBy_of_injective {G : Over S} [GrpObj G] [IsSeparated G.hom] {φ : G ⟶ G} (i : R →+* k)
    (hi : Function.Injective i) (x : Sp R ⟶ S) (c : R) (H : ActsBy G φ (spMap i ≫ x) (i c)) :
    ActsBy G φ x c := by
  intro v hv h0
  have := H (spMap (dualMapR i) ≫ v) (by rw [Category.assoc, hv, reassoc_of% dual_base i])
    (by rw [reassoc_of% fst_dual i, h0, Category.assoc])
  refine ext_of_injective (dualMapR i) (fun a b e => ?_) G.hom _ _ ?_ ?_
  · have e₁ := congrArg TrivSqZeroExt.fst e
    have e₂ := congrArg TrivSqZeroExt.snd e
    simp [dualMapR] at e₁ e₂
    exact TrivSqZeroExt.ext (hi e₁) (hi e₂)
  · rw [Category.assoc, Over.w, Category.assoc, hv, ← reassoc_of% Diag.epsScaleR_base c]
  · rw [← Category.assoc, this, reassoc_of% scale_dual i c]

/- English proof (translation)
Establish `h₁` using `isGrpPullback_pullback G x`. Use `set G₁ := (Over.pullback x).obj G`. Set `φ₁ : G₁ ⟶ G₁` to `(Over.pullback x).map φ`. Establish `e₁ : φ₁.left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ φ.left` using `pullback.lift_fst _ _ _`. Establish `h₂` using `isGrpPullback_pullback G₁ (spMap j)`.

Use `set G₂ := (Over.pullback (spMap j)).obj G₁`. Set `φ₂ : G₂ ⟶ G₂` to `(Over.pullback (spMap j)).map φ₁`. Establish `e₂ : φ₂.left ≫ pullback.fst G₁.hom (spMap j) = pullback.fst G₁.hom (spMap j) ≫ φ₁.left` using `pullback.lift_fst _ _ _`. Establish `hs : Smooth G₁.hom` using `inferInstanceAs (Smooth (pullback.snd G.hom x))`. Establish `H₁ : ActsBy G₁ φ₁ (𝟙 _) c` using `(actsBy_pull h₁ e₁ _ _).2 (by rwa [Category.id_comp])`.

Rewrite using `[← actsBy_pull h₁ e₁, ← Category.id_comp (spMap j), ← actsBy_pull h₂ e₂]`. Take `⟨d, v, hv⟩` from `ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G₁ hs`. Establish `w₁ : ∀ a, (spMap (dualMapR j) ≫ (v a).left) ≫ G₁.hom = spMap (algebraMap k (DualNumber k)) ≫ spMap j` using `fun a => by rw [Category.assoc, Over.w]; exact dual_base j`. Set `v' : Fin d → (epsR k ⟶ G₂)` to `fun a => Over.homMk (h₂.1.lift _ _ (w₁ a)) (h₂.1.lift_snd _ _ _)`. Establish `hv' : ∀ a, (v' a).left ≫ pullback.fst G₁.hom (spMap j) = spMap (dualMapR j) ≫ (v a).left` using `fun a => h₂.1.lift_fst _ _ _`.

Establish `hb` using `ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_baseChange j h₂ hv hv'`. Establish `eig : ∀ a, (v' a).left ≫ φ₂.left = spMap (epsScaleR (j c)) ≫ (v' a).left` using `fun a => by`. Use `H₁ (v a).left ((Over.w (v a)).trans (Category.comp_id _).symm) ((hv.1 a).trans (Category.id_comp _).symm)` as an intermediate fact. Use `h₂.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, e₂, reassoc_of% hv' a, this, Category.assoc, hv', reassoc_of% scale_dual j c]`.

Rewrite using `[Category.assoc, Over.w, Category.assoc, Over.w]`. Conclude with `Diag.epsScaleR_base _`. Introduce `w hw h0`. Set `w' : epsR k ⟶ G₂` to `Over.homMk w (hw.trans (Category.comp_id _))`. Take `⟨a, ⟨u, hu, e⟩, -⟩` from `hb.2 w' (h0.trans (Category.id_comp _))`.

Establish `key : w' ≫ φ₂ = GrpTangent.epsScale (j c) ≫ w'`. Establish `q₁` using `map_list_prod (IsMonHom.monoidHom φ₂ (epsR k)) (List.ofFn u)`. Establish `q₂` using `map_list_prod (preHom (G := G₂) (GrpTangent.epsScale (j c))) (List.ofFn u)`. Rewrite using `[e]`. Use `q₁.trans (Eq.trans ?_ q₂.symm)` and prove the remaining obligations.

Rewrite using `[List.map_ofFn, List.map_ofFn]`. Use `congr 2`. Use function extensionality and compare the values at `b`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(u b).left ≫ φ₂.left = spMap (epsScaleR (j c)) ≫ (u b).left`.

Rewrite using `[hu, Category.assoc, eig, reassoc_of% scale_comm]`. Conclude with `congrArg (·.left) key`.
-/
theorem actsBy_baseChange [IsLocalRing R] {G : Over S} [GrpObj G] [Smooth G.hom] {φ : G ⟶ G} [IsMonHom φ]
    (j : R →+* k) (x : Sp R ⟶ S) (c : R) (H : ActsBy G φ x c) : ActsBy G φ (spMap j ≫ x) (j c) := by
  have h₁ := isGrpPullback_pullback G x
  set G₁ := (Over.pullback x).obj G
  let φ₁ : G₁ ⟶ G₁ := (Over.pullback x).map φ
  have e₁ : φ₁.left ≫ pullback.fst G.hom x = pullback.fst G.hom x ≫ φ.left := pullback.lift_fst _ _ _
  have h₂ := isGrpPullback_pullback G₁ (spMap j)
  set G₂ := (Over.pullback (spMap j)).obj G₁
  let φ₂ : G₂ ⟶ G₂ := (Over.pullback (spMap j)).map φ₁
  have e₂ : φ₂.left ≫ pullback.fst G₁.hom (spMap j) = pullback.fst G₁.hom (spMap j) ≫ φ₁.left :=
    pullback.lift_fst _ _ _
  have hs : Smooth G₁.hom := inferInstanceAs (Smooth (pullback.snd G.hom x))
  have H₁ : ActsBy G₁ φ₁ (𝟙 _) c := (actsBy_pull h₁ e₁ _ _).2 (by rwa [Category.id_comp])
  rw [← actsBy_pull h₁ e₁, ← Category.id_comp (spMap j), ← actsBy_pull h₂ e₂]
  obtain ⟨d, v, hv⟩ := ReciprocityTheory.ChartRestriction.G.Chart.exists_isLieBasis G₁ hs
  have w₁ : ∀ a, (spMap (dualMapR j) ≫ (v a).left) ≫ G₁.hom = spMap (algebraMap k (DualNumber k)) ≫ spMap j :=
    fun a => by rw [Category.assoc, Over.w]; exact dual_base j
  let v' : Fin d → (epsR k ⟶ G₂) := fun a => Over.homMk (h₂.1.lift _ _ (w₁ a)) (h₂.1.lift_snd _ _ _)
  have hv' : ∀ a, (v' a).left ≫ pullback.fst G₁.hom (spMap j) = spMap (dualMapR j) ≫ (v a).left :=
    fun a => h₂.1.lift_fst _ _ _
  have hb := ReciprocityTheory.ChartRestriction.G.Chart.isLieBasis_baseChange j h₂ hv hv'
  have eig : ∀ a, (v' a).left ≫ φ₂.left = spMap (epsScaleR (j c)) ≫ (v' a).left := fun a => by
    have := H₁ (v a).left ((Over.w (v a)).trans (Category.comp_id _).symm)
      ((hv.1 a).trans (Category.id_comp _).symm)
    refine h₂.1.hom_ext ?_ ?_
    · rw [Category.assoc, e₂, reassoc_of% hv' a, this, Category.assoc, hv', reassoc_of% scale_dual j c]
    · rw [Category.assoc, Over.w, Category.assoc, Over.w]
      exact Diag.epsScaleR_base _
  intro w hw h0
  let w' : epsR k ⟶ G₂ := Over.homMk w (hw.trans (Category.comp_id _))
  obtain ⟨a, ⟨u, hu, e⟩, -⟩ := hb.2 w' (h0.trans (Category.id_comp _))
  have key : w' ≫ φ₂ = GrpTangent.epsScale (j c) ≫ w' := by
    have q₁ := map_list_prod (IsMonHom.monoidHom φ₂ (epsR k)) (List.ofFn u)
    have q₂ := map_list_prod (preHom (G := G₂) (GrpTangent.epsScale (j c))) (List.ofFn u)
    rw [e]
    refine q₁.trans (Eq.trans ?_ q₂.symm)
    rw [List.map_ofFn, List.map_ofFn]
    congr 2
    funext b
    refine Over.OverMorphism.ext ?_
    change (u b).left ≫ φ₂.left = spMap (epsScaleR (j c)) ≫ (u b).left
    rw [hu, Category.assoc, eig, reassoc_of% scale_comm]
  exact congrArg (·.left) key

end Scalar

section Torus

/- English proof (translation)
Assume the negation of the conclusion as `hX`. Rewrite `hX` using `[not_subsingleton_iff_nontrivial]`. Set `b` to `Module.Free.chooseBasis ℤ X`. Set `J` to `Module.Free.ChooseBasisIndex ℤ X`. Take `⟨i₀⟩ : Nonempty J` from `b.index_nonempty`.

Set `U : Matrix J J ℤ` to `LinearMap.toMatrix b b u.toIntLinearMap`. Establish `hU : U * U + (m : Matrix J J ℤ) = U`. Establish `: u.toIntLinearMap * u.toIntLinearMap + (m : Module.End ℤ X) = u.toIntLinearMap`. Use extensionality with `x`. Simplify using `using hu x`.

Establish `h2` using `congrArg (LinearMap.toMatrixAlgEquiv b) this`. Rewrite `h2` using `[map_add, map_mul, map_natCast]`. Then use the resulting hypothesis. Establish `hco : ∀ i j, ((U i j : ℤ) : k) = c * ((1 : Matrix J J ℤ) i j : ℤ)` using `fun i j => by`. Use `hc ((Int.castAddHom k).comp (b.coord i).toAddMonoidHom) (b j)` as an intermediate fact. Simplify `this` using `[U, LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]`.

Set `n : ℤ` to `U i₀ i₀`. Establish `hn : (n : k) = c` using `by simpa using hco i₀ i₀`. Set `l` to `ringChar k`. Establish `hdiv : ∀ i j, (l : ℤ) ∣ (U - (n : Matrix J J ℤ)) i j` using `fun i j => by`. Rewrite using `[← CharP.intCast_eq_zero_iff k l, Matrix.sub_apply, Int.cast_sub, hco, ← hn, Matrix.intCast_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use `choose B hB using hdiv`. Set `B' : Matrix J J ℤ` to `Matrix.of B`. Establish `hUB : U = (l : Matrix J J ℤ) * B' + (n : Matrix J J ℤ)`. Rewrite using `[← sub_eq_iff_eq_add, ← nsmul_eq_mul]`.

Use extensionality with `i j`. Rewrite using `[hB]`. Simplify using `[B']`. Set `ψ : Matrix J J ℤ →+* Module.End ℂ (J → ℂ)` to `(Matrix.toLinAlgEquiv' (R := ℂ) (n := J)).toRingEquiv.toRingHom.comp (Int.castRingHom ℂ).mapMatrix`. Establish `: Nonempty J` using `⟨i₀⟩`.

Take `⟨z, hz⟩` from `Module.End.exists_eigenvalue (ψ B')`. Take `⟨v, hv⟩` from `hz.exists_hasEigenvector`. Establish `hint : IsIntegral ℤ z`. Take `⟨p, hp, hp0⟩ : IsIntegral ℤ (ψ B')` from `(Algebra.IsIntegral.isIntegral (R := ℤ) B').map ψ.toIntAlgHom`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Establish `e` using `Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap ℤ ℂ)) hv`. Rewrite `e` using `[Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp0, Polynomial.eval_map]`. Conclude with `(smul_eq_zero.1 e.symm).resolve_right hv.2`. Establish `hUv : ψ U v = ((l : ℂ) * z + n) • v`. Rewrite using `[hUB, map_add, map_mul, map_natCast, map_intCast, LinearMap.add_apply, Module.End.mul_apply, hv.apply_eq_smul, Module.End.natCast_apply, Module.End.intCast_apply, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, Int.cast_smul_eq_zsmul]`.

Use `set y : ℂ := (l : ℂ) * z + n with hy`. Establish `hy2 : y * y + m = y`. Establish `e` using `congrArg (fun M => ψ M v) hU`. Simplify using `only [map_add, map_mul, map_natCast, LinearMap.add_apply, Module.End.mul_apply, hUv, map_smul, Module.End.natCast_apply] at e`. Rewrite `e` using `[smul_smul, ← Nat.cast_smul_eq_nsmul ℂ, ← add_smul]`.

Conclude with `smul_left_injective ℂ hv.2 e`. Establish `hm' : (4 : ℝ) * m = 1 + d` using `by exact_mod_cast hm`. Establish `hd0 : (0 : ℝ) < d` using `by exact_mod_cast hd.pos`. Establish `hre` using `congrArg Complex.re hy2`. Establish `him` using `congrArg Complex.im hy2`.

Simplify using `at hre him`. Establish `h1 : y.re = 1 / 2`. Assume the negation of the conclusion as `h`. Establish `h0 : y.im = 0`. Establish `: (2 * y.re - 1) * y.im = 0` using `by linarith`.

Conclude with `(mul_eq_zero.1 this).resolve_left fun e => h (by linarith)`. Rewrite `hre` using `[h0]`. Use polynomial arithmetic with `[sq_nonneg (2 * y.re - 1)]`. Establish `h2 : 4 * (y.im * y.im) = d` using `by rw [h1] at hre; linarith`. Establish `h3 : y.im = l * z.im` using `by simp [hy]`.

Establish `hint2 : IsIntegral ℤ ((z - starRingEnd ℂ z) ^ 2)` using `(hint.sub (hint.map (starRingEnd ℂ).toIntAlgHom)).pow 2`. Establish `hl0 : (l : ℝ) ≠ 0`. Introduce `e`. Rewrite `h2` using `[h3, e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq : (z - starRingEnd ℂ z) ^ 2 = algebraMap ℚ ℂ (-(d : ℚ) / (l : ℚ) ^ 2)`. Rewrite using `[Complex.sub_conj, mul_pow, Complex.I_sq]`. Establish `: (2 * z.im) ^ 2 = (d : ℝ) / (l : ℝ) ^ 2`. Rewrite using `[eq_div_iff (pow_ne_zero 2 hl0), ← h2, h3]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← Complex.ofReal_pow, this]`. Simplify using `[neg_div]`. Rewrite `hint2` using `[hq, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective]`. Take `⟨t, ht⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint2`. Establish `hl0' : (l : ℚ) ≠ 0` using `by exact_mod_cast hl0`.

Establish `ht' : (d : ℤ) = (l : ℤ) * l * (-t)`. Establish `: (d : ℚ) = (l : ℚ) * l * (-t)`. Rewrite `ht` using `[eq_intCast]`. Rewrite using `[ht]`. Clear the denominators using the available nonvanishing facts.

Conclude with `this` after adjusting the coercions. Establish `hdv : l * l ∣ d` using `by exact_mod_cast (Dvd.intro _ ht'.symm : (l : ℤ) * l ∣ d)`. Conclude with `CharP.ringChar_ne_one (R := k) (Nat.isUnit_iff.1 (hd.squarefree l hdv))`.
-/
theorem subsingleton_of_scalar {X k : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [Field k]
    (u : X →+ X) {m d : ℕ} (hd : d.Prime) (hm : 4 * m = 1 + d) (hu : ∀ x, u (u x) + m • x = u x) (c : k)
    (hc : ∀ (f : X →+ k) x, f (u x) = c * f x) : Subsingleton X := by
  classical
  by_contra hX
  rw [not_subsingleton_iff_nontrivial] at hX
  let b := Module.Free.chooseBasis ℤ X
  let J := Module.Free.ChooseBasisIndex ℤ X
  obtain ⟨i₀⟩ : Nonempty J := b.index_nonempty
  let U : Matrix J J ℤ := LinearMap.toMatrix b b u.toIntLinearMap
  have hU : U * U + (m : Matrix J J ℤ) = U := by
    have : u.toIntLinearMap * u.toIntLinearMap + (m : Module.End ℤ X) = u.toIntLinearMap := by
      ext x; simpa using hu x
    have h2 := congrArg (LinearMap.toMatrixAlgEquiv b) this
    rwa [map_add, map_mul, map_natCast] at h2
  have hco : ∀ i j, ((U i j : ℤ) : k) = c * ((1 : Matrix J J ℤ) i j : ℤ) := fun i j => by
    have := hc ((Int.castAddHom k).comp (b.coord i).toAddMonoidHom) (b j)
    simpa [U, LinearMap.toMatrix_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm] using this
  let n : ℤ := U i₀ i₀
  have hn : (n : k) = c := by simpa using hco i₀ i₀
  let l := ringChar k
  have hdiv : ∀ i j, (l : ℤ) ∣ (U - (n : Matrix J J ℤ)) i j := fun i j => by
    rw [← CharP.intCast_eq_zero_iff k l, Matrix.sub_apply, Int.cast_sub, hco, ← hn, Matrix.intCast_apply, Matrix.one_apply]
    split_ifs <;> simp
  choose B hB using hdiv
  let B' : Matrix J J ℤ := Matrix.of B
  have hUB : U = (l : Matrix J J ℤ) * B' + (n : Matrix J J ℤ) := by
    rw [← sub_eq_iff_eq_add, ← nsmul_eq_mul]
    ext i j
    rw [hB]; simp [B']
  let ψ : Matrix J J ℤ →+* Module.End ℂ (J → ℂ) :=
    (Matrix.toLinAlgEquiv' (R := ℂ) (n := J)).toRingEquiv.toRingHom.comp (Int.castRingHom ℂ).mapMatrix
  have : Nonempty J := ⟨i₀⟩
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue (ψ B')
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hint : IsIntegral ℤ z := by
    obtain ⟨p, hp, hp0⟩ : IsIntegral ℤ (ψ B') := (Algebra.IsIntegral.isIntegral (R := ℤ) B').map ψ.toIntAlgHom
    refine ⟨p, hp, ?_⟩
    have e := Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap ℤ ℂ)) hv
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp0, Polynomial.eval_map] at e
    exact (smul_eq_zero.1 e.symm).resolve_right hv.2
  have hUv : ψ U v = ((l : ℂ) * z + n) • v := by
    rw [hUB, map_add, map_mul, map_natCast, map_intCast, LinearMap.add_apply, Module.End.mul_apply, hv.apply_eq_smul,
      Module.End.natCast_apply, Module.End.intCast_apply, add_smul, mul_smul, Nat.cast_smul_eq_nsmul,
      Int.cast_smul_eq_zsmul]
  set y : ℂ := (l : ℂ) * z + n with hy
  have hy2 : y * y + m = y := by
    have e := congrArg (fun M => ψ M v) hU
    simp only [map_add, map_mul, map_natCast, LinearMap.add_apply, Module.End.mul_apply, hUv, map_smul,
      Module.End.natCast_apply] at e
    rw [smul_smul, ← Nat.cast_smul_eq_nsmul ℂ, ← add_smul] at e
    exact smul_left_injective ℂ hv.2 e
  have hm' : (4 : ℝ) * m = 1 + d := by exact_mod_cast hm
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.pos
  have hre := congrArg Complex.re hy2
  have him := congrArg Complex.im hy2
  simp at hre him
  have h1 : y.re = 1 / 2 := by
    by_contra h
    have h0 : y.im = 0 := by
      have : (2 * y.re - 1) * y.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left fun e => h (by linarith)
    rw [h0] at hre
    nlinarith [sq_nonneg (2 * y.re - 1)]
  have h2 : 4 * (y.im * y.im) = d := by rw [h1] at hre; linarith
  have h3 : y.im = l * z.im := by simp [hy]
  have hint2 : IsIntegral ℤ ((z - starRingEnd ℂ z) ^ 2) :=
    (hint.sub (hint.map (starRingEnd ℂ).toIntAlgHom)).pow 2
  have hl0 : (l : ℝ) ≠ 0 := by
    intro e
    rw [h3, e] at h2
    linarith
  have hq : (z - starRingEnd ℂ z) ^ 2 = algebraMap ℚ ℂ (-(d : ℚ) / (l : ℚ) ^ 2) := by
    rw [Complex.sub_conj, mul_pow, Complex.I_sq]
    have : (2 * z.im) ^ 2 = (d : ℝ) / (l : ℝ) ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hl0), ← h2, h3]; ring
    rw [← Complex.ofReal_pow, this]
    simp [neg_div]
  rw [hq, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at hint2
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint2
  have hl0' : (l : ℚ) ≠ 0 := by exact_mod_cast hl0
  have ht' : (d : ℤ) = (l : ℤ) * l * (-t) := by
    have : (d : ℚ) = (l : ℚ) * l * (-t) := by
      rw [eq_intCast] at ht
      rw [ht]; field_simp
    exact_mod_cast this
  have hdv : l * l ∣ d := by exact_mod_cast (Dvd.intro _ ht'.symm : (l : ℤ) * l ∣ d)
  exact CharP.ringChar_ne_one (R := k) (Nat.isUnit_iff.1 (hd.squarefree l hdv))

end Torus

section Fibre

variable {O : Type} [CommRing O]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Establish `h` using `a.add 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[Nat.cast_zero, pow_zero]`.

Conclude with `mul_eq_left.1 h.symm`. Consider the case `succ m ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]`.
-/
theorem act_natCast {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) (m : ℕ) :
    a.act (m : O) = 𝟙 G ^ m := by
  induction m with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact mul_eq_left.1 h.symm
  | succ m ih => rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => rw [zero_smul, Diag.diagMap_zero, pow_zero]`. Consider the case `succ m ih => rw [succ_nsmul, Diag.diagMap_add, ih, Diag.diagMap_id, pow_succ]`.
-/
theorem diagMap_nsmul (S : Scheme.{0}) (X : Type) [AddCommGroup X] (m : ℕ) :
    Diag.diagMap S (m • AddMonoidHom.id X) = 𝟙 _ ^ m := by
  induction m with
  | zero => rw [zero_smul, Diag.diagMap_zero, pow_zero]
  | succ m ih => rw [succ_nsmul, Diag.diagMap_add, ih, Diag.diagMap_id, pow_succ]

/- English proof (translation)
Use `letI := T.addCommGroup`. Use `letI := T.grpB`. Use `T.free` as an intermediate fact. Use `T.finite` as an intermediate fact. Use `T.i_hom` as an intermediate fact.

Use `T.q_hom` as an intermediate fact. Use `T.q_flat` as an intermediate fact. Use `T.q_surjective` as an intermediate fact. Use `T.q_quasiCompact` as an intermediate fact. Use `T.isAbelian.proper` as an intermediate fact.

Use `a.hom w` as an intermediate fact. Establish `: Mono T.i` using `T.isKernel.flip.mono_snd_of_mono`. Take `⟨α, ⟨_, hα⟩, -⟩` from `(SemiRigid.exists_torus_and_quotient_hom T T (a.act w)).1`. Take `⟨u, hu⟩` from `SplitTorusHom.exists_addMonoidHom α`. Take `rfl : α = Diag.diagMap _ u` from `Diag.hom_ext fun x => by`.

Establish `e` using `hu x`. Rewrite `e` using `[SplitTorus.charUnit_val, SplitTorus.charUnit_val, ← Diag.diagMap_chi]`. Rewrite using `[← Category.comp_id α, Rosenlicht.coord_comp, ← Category.comp_id (Diag.diagMap _ u), Rosenlicht.coord_comp]`. Conclude with `e`. Establish `hrel : u.comp u + m • AddMonoidHom.id T.X = u`.

Apply `Diag.diagMap_injective (Sp k)` to reduce the goal to its premises. Establish `e` using `congrArg (fun z => T.i ≫ a.act z) hw`. Simplify using `only [a.add, a.mul, act_natCast] at e`. Rewrite using `[← cancel_mono T.i, hα, ← e, Diag.diagMap_add, Diag.diagMap_comp, diagMap_nsmul, MonObj.mul_comp, MonObj.comp_mul, Category.assoc, hα, reassoc_of% hα, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]`. Establish `hs : Subsingleton T.X` using `subsingleton_of_scalar u hd hm (fun x => DFunLike.congr_fun hrel x) c fun f x => by`.

Establish `e` using `H (Diag.lieVec f ≫ T.i).left ((Over.w _).trans (Category.comp_id _).symm) (by`. Rewrite using `[Over.comp_left, reassoc_of% Diag.isTangent_lieVec f, ← Over.comp_left, IsMonHom.one_hom, Category.id_comp])`. Establish `e' : Diag.lieVec (f.comp u) = Diag.lieVec (c • f)`. Rewrite using `[← cancel_mono T.i, ← Diag.lieVec_comp_diagMap, Category.assoc, hα]`. Use `Over.OverMorphism.ext ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc, Over.comp_left, e, Over.comp_left, Over.comp_left, Diag.lieVec_smul_left, Category.assoc]`. Conclude with `DFunLike.congr_fun (Diag.lieVec_injective e') x`. Establish `hone : T.i = 1`. Establish `e : AddMonoidHom.id T.X = 0` using `Subsingleton.elim _ _`. Rewrite using `[← Category.id_comp T.i, ← Diag.diagMap_id, e, Diag.diagMap_zero, MonObj.one_comp]`.

Establish `: Mono T.q` using `⟨fun {Z} x y h => by`. Take `⟨τ, rfl⟩` from `SemiRigid.exists_eq_mul T.isKernel h`. Rewrite using `[hone, MonObj.comp_one, _root_.one_mul]⟩`. Establish `: Mono T.q.left` using `inferInstanceAs (Mono ((Over.forget _).map T.q))`. Establish `: IsIso T.q.left` using `Flat.isIso_of_surjective_of_mono _`.

Rewrite using `[← Over.w T.q]`. Use `infer_instance`.
-/
theorem isProper_of_actsBy {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] (T : TorusExtension G) (a : OAct O G)
    {w : O} {m d : ℕ} (hd : d.Prime) (hm : 4 * m = 1 + d) (hw : w * w + m = w) (c : k)
    (H : ActsBy G (a.act w) (𝟙 _) c) : IsProper G.hom := by
  letI := T.addCommGroup; letI := T.grpB
  have := T.free
  have := T.finite
  have := T.i_hom
  have := T.q_hom
  have := T.q_flat
  have := T.q_surjective
  have := T.q_quasiCompact
  have := T.isAbelian.proper
  have := a.hom w
  have : Mono T.i := T.isKernel.flip.mono_snd_of_mono
  obtain ⟨α, ⟨_, hα⟩, -⟩ := (SemiRigid.exists_torus_and_quotient_hom T T (a.act w)).1
  obtain ⟨u, hu⟩ := SplitTorusHom.exists_addMonoidHom α
  obtain rfl : α = Diag.diagMap _ u := Diag.hom_ext fun x => by
    have e := hu x
    rw [SplitTorus.charUnit_val, SplitTorus.charUnit_val, ← Diag.diagMap_chi] at e
    rw [← Category.comp_id α, Rosenlicht.coord_comp, ← Category.comp_id (Diag.diagMap _ u), Rosenlicht.coord_comp]
    exact e
  have hrel : u.comp u + m • AddMonoidHom.id T.X = u := by
    apply Diag.diagMap_injective (Sp k)
    have e := congrArg (fun z => T.i ≫ a.act z) hw
    simp only [a.add, a.mul, act_natCast] at e
    rw [← cancel_mono T.i, hα, ← e, Diag.diagMap_add, Diag.diagMap_comp, diagMap_nsmul, MonObj.mul_comp,
      MonObj.comp_mul, Category.assoc, hα, reassoc_of% hα, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
      Category.comp_id]
  have hs : Subsingleton T.X := subsingleton_of_scalar u hd hm (fun x => DFunLike.congr_fun hrel x) c fun f x => by
    have e := H (Diag.lieVec f ≫ T.i).left ((Over.w _).trans (Category.comp_id _).symm) (by
      rw [Over.comp_left, reassoc_of% Diag.isTangent_lieVec f, ← Over.comp_left, IsMonHom.one_hom, Category.id_comp])
    have e' : Diag.lieVec (f.comp u) = Diag.lieVec (c • f) := by
      rw [← cancel_mono T.i, ← Diag.lieVec_comp_diagMap, Category.assoc, hα]
      refine Over.OverMorphism.ext ?_
      rw [← Category.assoc, Over.comp_left, e, Over.comp_left, Over.comp_left, Diag.lieVec_smul_left, Category.assoc]
    exact DFunLike.congr_fun (Diag.lieVec_injective e') x
  have hone : T.i = 1 := by
    have e : AddMonoidHom.id T.X = 0 := Subsingleton.elim _ _
    rw [← Category.id_comp T.i, ← Diag.diagMap_id, e, Diag.diagMap_zero, MonObj.one_comp]
  have : Mono T.q := ⟨fun {Z} x y h => by
    obtain ⟨τ, rfl⟩ := SemiRigid.exists_eq_mul T.isKernel h
    rw [hone, MonObj.comp_one, _root_.one_mul]⟩
  have : Mono T.q.left := inferInstanceAs (Mono ((Over.forget _).map T.q))
  have : IsIso T.q.left := Flat.isIso_of_surjective_of_mono _
  rw [← Over.w T.q]
  infer_instance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨_, hs⟩` from `DetCompare.exists_splitting (E := E) (k := k)`. Establish `key : ∀ z : TanMod.TanSp t G, TanMod.TanSp.act t a H.w0 z = c • z` using `fun z => by`. Rewrite using `[← EigenSplit.sum_proj hs (TanMod.TanSp.act t a) z, map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hz` using `EigenSplit.proj_mem hs (TanMod.TanSp.act t a) τ z`.

Distinguish the cases in `hτ : τ H.rt = ρ`. Rewrite using `[EigenSplit.mem_eigenSub.1 hz]`. Use `congr 1`. Establish `e` using `congrArg τ H.two_weight_eq_one_add_root`. Rewrite `e` using `[map_mul, map_add, map_one, map_ofNat, hτ, ← hc]`.

Conclude with `mul_left_cancel₀ two_ne_zero e`. Take `⟨_, h0⟩` from `(DetCompare.hasEigenDim_iff a t τ _).1 ((DetCompare.lieMult_iff a t τ _).1 ((h τ).2 hτ))`. Rewrite `h0` using `[hq, Submodule.finrank_eq_zero]`. Rewrite `hz` using `[h0, Submodule.mem_bot]`. Rewrite using `[hz, map_zero, smul_zero]`.

Introduce `v hv h0`. Establish `h1 : (1 : Over.mk t ⟶ G).left = t ≫ η[G].left`. Rewrite using `[Hom.one_def, Over.comp_left, Over.toUnit_left]`. Both sides reduce to the same expression. Conclude with `congrArg (fun z => z.pt.left) (key (TanMod.TanSp.mk (Over.homMk v hv) (TanMod.smT_zero_of t _ (h0.trans h1.symm))))`.
-/
theorem actsBy_of_detCond {k : Type} [Field k] [CharZero k] [IsAlgClosed k] {S : Scheme.{0}} {G : Over S} [GrpObj G]
    [IsCommMonObj G] (D : Datum H) (hq : D.q = 0) (a : OAct (𝓞 E) G) (t : Sp k ⟶ S) (ρ c : k) (hc : 2 * c = 1 + ρ)
    (h : DetCond D a t ρ) : ActsBy G (a.act H.w0) t c := by
  classical
  obtain ⟨_, hs⟩ := DetCompare.exists_splitting (E := E) (k := k)
  have key : ∀ z : TanMod.TanSp t G, TanMod.TanSp.act t a H.w0 z = c • z := fun z => by
    rw [← EigenSplit.sum_proj hs (TanMod.TanSp.act t a) z, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hz := EigenSplit.proj_mem hs (TanMod.TanSp.act t a) τ z
    by_cases hτ : τ H.rt = ρ
    · rw [EigenSplit.mem_eigenSub.1 hz]
      congr 1
      have e := congrArg τ H.two_weight_eq_one_add_root
      rw [map_mul, map_add, map_one, map_ofNat, hτ, ← hc] at e
      exact mul_left_cancel₀ two_ne_zero e
    · obtain ⟨_, h0⟩ := (DetCompare.hasEigenDim_iff a t τ _).1 ((DetCompare.lieMult_iff a t τ _).1 ((h τ).2 hτ))
      rw [hq, Submodule.finrank_eq_zero] at h0
      rw [h0, Submodule.mem_bot] at hz
      rw [hz, map_zero, smul_zero]
  intro v hv h0
  have h1 : (1 : Over.mk t ⟶ G).left = t ≫ η[G].left := by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]; rfl
  exact congrArg (fun z => z.pt.left)
    (key (TanMod.TanSp.mk (Over.homMk v hv) (TanMod.smT_zero_of t _ (h0.trans h1.symm))))

/- English proof (translation)
Take `⟨m, hm⟩ : ∃ m : ℕ, 4 * m = 1 + H.d` from `⟨(1 + H.d) / 4, by have := H.d_mod; omega⟩`. Use `⟨m, hm, mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num) ?_⟩` and prove the remaining obligations. Establish `hm' : (4 : 𝓞 E) * m = 1 + H.d` using `by exact_mod_cast hm`. Take the linear combination `(2 * H.w0 + H.rt - 1) * H.two_weight_eq_one_add_root + H.rt_sq + hm'`.
-/
theorem exists_w0_relation (H : Host E) : ∃ m : ℕ, 4 * m = 1 + H.d ∧ H.w0 * H.w0 + m = H.w0 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 * m = 1 + H.d := ⟨(1 + H.d) / 4, by have := H.d_mod; omega⟩
  refine ⟨m, hm, mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num) ?_⟩
  have hm' : (4 : 𝓞 E) * m = 1 + H.d := by exact_mod_cast hm
  linear_combination (2 * H.w0 + H.rt - 1) * H.two_weight_eq_one_add_root + H.rt_sq + hm'

end Fibre

section Spread

/- English proof (translation)
Establish `hfin : (genericPoints U).Finite` using `genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`. Establish `hcl : IsClosed (⋃ u ∈ genericPoints U, closure {j u})` using `hfin.isClosed_biUnion fun _ _ => isClosed_closure`. Establish `hsub : Set.range j ⊆ ⋃ u ∈ genericPoints U, closure {j u}`. Introduce and unpack `_ ⟨y, rfl⟩`. Set `g` to `genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩`.

Establish `hg : g.1 ⤳ y` using `(genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent`. Conclude with `Set.mem_biUnion g.2 (hg.map j.continuous).mem_closure`. Establish `hx : x ∈ ⋃ u ∈ genericPoints U, closure {j u}` using `hcl.closure_subset_iff.2 hsub (j.denseRange x)`. Take `⟨u, -, hu⟩` from `Set.mem_iUnion₂.1 hx`. Conclude with `⟨u, specializes_iff_mem_closure.2 hu⟩`.
-/
theorem exists_specializes {U X : Scheme.{0}} [TopologicalSpace.NoetherianSpace U] (j : U ⟶ X) [IsDominant j] (x : X) :
    ∃ u : U, j u ⤳ x := by
  have hfin : (genericPoints U).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hcl : IsClosed (⋃ u ∈ genericPoints U, closure {j u}) := hfin.isClosed_biUnion fun _ _ => isClosed_closure
  have hsub : Set.range j ⊆ ⋃ u ∈ genericPoints U, closure {j u} := by
    rintro _ ⟨y, rfl⟩
    let g := genericPoints.ofComponent ⟨_, irreducibleComponent_mem_irreducibleComponents y⟩
    have hg : g.1 ⤳ y := (genericPoints.isGenericPoint_ofComponent _).specializes mem_irreducibleComponent
    exact Set.mem_biUnion g.2 (hg.map j.continuous).mem_closure
  have hx : x ∈ ⋃ u ∈ genericPoints U, closure {j u} :=
    hcl.closure_subset_iff.2 hsub (j.denseRange x)
  obtain ⟨u, -, hu⟩ := Set.mem_iUnion₂.1 hx
  exact ⟨u, specializes_iff_mem_closure.2 hu⟩

/- English proof (translation)
Set `A` to `X.presheaf.stalk (t (IsLocalRing.closedPoint k))`. Set `g : A ⟶ CommRingCat.of L` to `X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y`. Set `g' : A ⟶ CommRingCat.of k` to `Scheme.stalkClosedPointTo t`. Establish `hg : Spec.map g ≫ X.fromSpecStalk _ = y`. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]`.

Establish `hg' : Spec.map g' ≫ X.fromSpecStalk _ = t` using `Scheme.Spec_stalkClosedPointTo_fromSpecStalk _`. Set `P : Ideal A` to `RingHom.ker g.hom`. Establish `hP : P ≠ ⊤` using `RingHom.ker_ne_top _`. Establish `: Nontrivial (A ⧸ P)` using `Ideal.Quotient.nontrivial_iff.2 hP`. Establish `hk : ∀ a ∈ P, g'.hom a = 0` using `fun a ha => by`.

Assume the negation of the conclusion as `h0`. Conclude with `hP (Ideal.eq_top_of_isUnit_mem _ ha (IsUnit.of_map g'.hom a (IsUnit.mk0 _ h0)))`. Use `⟨A ⧸ P, inferInstance, IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective, RingHom.kerLift g.hom, Ideal.Quotient.lift P g'.hom hk, spMap (Ideal.Quotient.mk P) ≫ X.fromSpecStalk _, RingHom.kerLift_injective _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, sp_comp]`. Conclude with `hg`.

Rewrite using `[← Category.assoc, sp_comp]`. Conclude with `hg'`.
-/
theorem exists_local {X : Scheme.{0}} {L k : Type} [Field L] [Field k] (y : Sp L ⟶ X) (t : Sp k ⟶ X)
    (h : y (IsLocalRing.closedPoint L) ⤳ t (IsLocalRing.closedPoint k)) :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (i : R →+* L) (j : R →+* k) (x : Sp R ⟶ X),
      Function.Injective i ∧ spMap i ≫ x = y ∧ spMap j ≫ x = t := by
  let A := X.presheaf.stalk (t (IsLocalRing.closedPoint k))
  let g : A ⟶ CommRingCat.of L := X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y
  let g' : A ⟶ CommRingCat.of k := Scheme.stalkClosedPointTo t
  have hg : Spec.map g ≫ X.fromSpecStalk _ = y := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hg' : Spec.map g' ≫ X.fromSpecStalk _ = t := Scheme.Spec_stalkClosedPointTo_fromSpecStalk _
  let P : Ideal A := RingHom.ker g.hom
  have hP : P ≠ ⊤ := RingHom.ker_ne_top _
  have : Nontrivial (A ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP
  have hk : ∀ a ∈ P, g'.hom a = 0 := fun a ha => by
    by_contra h0
    exact hP (Ideal.eq_top_of_isUnit_mem _ ha (IsUnit.of_map g'.hom a (IsUnit.mk0 _ h0)))
  refine ⟨A ⧸ P, inferInstance, IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective,
    RingHom.kerLift g.hom, Ideal.Quotient.lift P g'.hom hk, spMap (Ideal.Quotient.mk P) ≫ X.fromSpecStalk _,
    RingHom.kerLift_injective _, ?_, ?_⟩
  · rw [← Category.assoc, sp_comp]; exact hg
  · rw [← Category.assoc, sp_comp]; exact hg'

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x`. Establish `hη : (spMap V.subtype) (IsLocalRing.closedPoint F) ⤳ s x`. Use `(PrimeSpectrum.le_iff_specializes (R := V) (PrimeSpectrum.comap V.subtype (IsLocalRing.closedPoint F)) (s x)).mp ?_` and prove the remaining obligations. Introduce `a ha`.

Establish `ha' : V.subtype a ∈ IsLocalRing.maximalIdeal F` using `ha`. Rewrite `ha'` using `[IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]`. Establish `: a = 0` using `Subtype.ext ha'`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`.

Take `⟨y, hy, hy'⟩` from `Flat.generalizingMap s hη`. Use `closure_mono (Set.singleton_subset_iff.mpr ?_) hy.mem_closure` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_fst]`. Conclude with `⟨_, hy'.symm⟩`.
-/
theorem isDominant_generic {F : Type} [Field F] (V : ValuationSubring F) {X : Scheme.{0}} (s : X ⟶ Sp V) [Flat s] :
    IsDominant (pullback.fst s (spMap V.subtype)) := by
  constructor
  intro x
  have hη : (spMap V.subtype) (IsLocalRing.closedPoint F) ⤳ s x := by
    refine (PrimeSpectrum.le_iff_specializes (R := V)
      (PrimeSpectrum.comap V.subtype (IsLocalRing.closedPoint F)) (s x)).mp ?_
    intro a ha
    have ha' : V.subtype a ∈ IsLocalRing.maximalIdeal F := ha
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at ha'
    have : a = 0 := Subtype.ext ha'
    rw [this]; exact Ideal.zero_mem _
  obtain ⟨y, hy, hy'⟩ := Flat.generalizingMap s hη
  refine closure_mono (Set.singleton_subset_iff.mpr ?_) hy.mem_closure
  rw [Scheme.Pullback.range_fst]
  exact ⟨_, hy'.symm⟩

/- English proof (translation)
Establish `hprop : IsProper Y.s`. Take `⟨N, i, hi, e⟩` from `Y.proj`. Use `isProper_str O N` as an intermediate fact. Rewrite using `[← e]`. Use `infer_instance`.

Establish `: IsLocallyNoetherian (pullback Y.s (spMap β))` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap β))`. Establish `: CompactSpace ↥(pullback Y.s (spMap β))` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap β))`. Establish `: IsNoetherian (pullback Y.s (spMap β))` using `{}`. Use `Y.jQ_open` as an intermediate fact. Conclude with `Y.jQ.isEmbedding.isInducing.noetherianSpace`.
-/
theorem noetherianSpace_open {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    TopologicalSpace.NoetherianSpace (Xo.XF c) := by
  have hprop : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str O N
    rw [← e]; infer_instance
  have : IsLocallyNoetherian (pullback Y.s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap β))
  have : CompactSpace ↥(pullback Y.s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap β))
  have : IsNoetherian (pullback Y.s (spMap β)) := {}
  have := Y.jQ_open
  exact Y.jQ.isEmbedding.isInducing.noetherianSpace

/- English proof (translation)
Take `⟨m, hm, hw⟩` from `exists_w0_relation H`. Set `inc` to `(IntermediateField.inclusion c.le).toRingHom`. Set `ρ : c.F` to `inc (baseKA l).ρ`. Establish `hρ : ρ ^ 2 = -(H.d : c.F)` using `by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]`. Establish `hm' : (4 : c.F) * m = 1 + H.d` using `by exact_mod_cast hm`.

Set `z : c.F` to `(1 + ρ) / 2`. Establish `hz2 : 2 * z = 1 + ρ` using `mul_div_cancel₀ _ two_ne_zero`. Establish `hz : z * z + m = z` using `mul_left_cancel₀ (show (4 : c.F) ≠ 0 by norm_num) (by`. Take the linear combination `(2 * z + ρ - 1) * hz2 + hρ + hm')`. Establish `hzV : z ∈ V`.

Break down `V.mem_or_inv_mem z with h | h` into its components or cases. Conclude with `h`. Distinguish the cases in `h0 : z = 0`. Rewrite using `[h0]`. Conclude with `V.zero_mem`.

Establish `: z = 1 - m * z⁻¹` using `by field_simp; linear_combination hz`. Rewrite using `[this]`. Conclude with `sub_mem (one_mem V) (mul_mem (natCast_mem V m) h)`. Use `Y.flat` as an intermediate fact. Use `isDominant_generic V Y.s` as an intermediate fact.

Establish `: IsDominant Y.jQ` using `⟨Y.jQ_dense⟩`. Establish `: IsDominant Y.j` using `inferInstanceAs (IsDominant (_ ≫ _))`. Use `noetherianSpace_open Y` as an intermediate fact. Use `Y.t.semi.smooth` as an intermediate fact. Use `Y.t.semi.separated` as an intermediate fact.

Use `Y.t.act.hom H.w0` as an intermediate fact. Use `Set.eq_univ_of_forall fun x K _ _ t ⟨pt, hpt⟩ => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `exists_specializes Y.j x`. Set `L` to `AlgebraicClosure ((Xo.XF c).residueField u)`. Set `y : Sp L ⟶ Xo.XF c` to `spMap (algebraMap ((Xo.XF c).residueField u) L) ≫ (Xo.XF c).fromSpecResidueField u`.

Establish `hy : y (IsLocalRing.closedPoint L) = u` using `Scheme.fromSpecResidueField_apply u _`. Use `clear_value y`. Take `⟨R, _, _, i, j, χ, hi, hiy, hjt⟩` from `exists_local (y ≫ Y.j) t (by`. Establish `e₁ : (y ≫ Y.j) (IsLocalRing.closedPoint L) = Y.j u` using `(Scheme.Hom.comp_apply y Y.j _).trans (congrArg Y.j hy)`. Establish `e₂ : t (IsLocalRing.closedPoint K) = x` using `(congrArg t (Subsingleton.elim (α := PrimeSpectrum K) _ pt)).trans hpt`.

Rewrite using `[e₁, e₂]`. Conclude with `hu)`. Take `⟨ga, hga⟩` from `Spec.map_surjective (y ≫ pullback.snd Xo.s (spMap inc))`. Take `⟨b, hb⟩` from `Spec.map_surjective (χ ≫ Y.s)`. Establish `hbga : i.comp b.hom = ga.hom.comp V.subtype`.

Establish `e : spMap (i.comp b.hom) = spMap (ga.hom.comp V.subtype)`. Rewrite using `[← sp_comp, ← sp_comp]`. Express the relevant statement in the definitionally equal form `spMap i ≫ Spec.map b = Spec.map ga ≫ _`. Rewrite using `[hb, hga, reassoc_of% hiy, Model.j, Category.assoc, pullback.condition, reassoc_of% Y.jQ_over, Category.assoc]`. Conclude with `congrArg (·.hom) (Spec.map_injective e)`.

Establish `: CharZero L` using `(RingHom.charZero_iff ga.hom.injective).1 (inferInstanceAs (CharZero c.F))`. Establish `hdet` using `(Y.oF.geom L y (ga.hom.comp inc) (by`. Rewrite using `[pullback.condition, ← Category.assoc, ← hga, ← sp_comp]`. Use the proof step `rfl)).1`. Establish `h₁` using `actsBy_of_detCond D hq _ y _ (ga.hom z) (by rw [← map_ofNat ga.hom 2, ← map_mul, hz2, map_add, map_one]; rfl) hdet`.

Establish `h₂ : ActsBy Y.t.G (Y.t.act.act H.w0) (spMap i ≫ χ) (i (b.hom ⟨z, hzV⟩))`. Rewrite using `[hiy, show i (b.hom ⟨z, hzV⟩) = ga.hom z from RingHom.congr_fun hbga ⟨z, hzV⟩]`. Conclude with `(actsBy_pull Y.m.cart (Y.m.act H.w0) y _).1 h₁`. Establish `h₃` using `actsBy_baseChange j χ _ (actsBy_of_injective i hi χ _ h₂)`. Rewrite `h₃` using `[hjt]`.

Take `⟨T⟩` from `Y.t.semi.fibres K t`. Conclude with `isProper_of_actsBy T (OAct.pullback t Y.t.G Y.t.act) H.d_prime hm hw _ ((actsBy_pull (isGrpPullback_pullback Y.t.G t) (pullback.lift_fst _ _ _) _ _).2 (by rwa [Category.id_comp]))`.
-/
theorem abLocus_eq_univ (hq : D.q = 0) (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) :
    abLocus Y.t.G = Set.univ := by
  obtain ⟨m, hm, hw⟩ := exists_w0_relation H
  let inc := (IntermediateField.inclusion c.le).toRingHom
  let ρ : c.F := inc (baseKA l).ρ
  have hρ : ρ ^ 2 = -(H.d : c.F) := by rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hm' : (4 : c.F) * m = 1 + H.d := by exact_mod_cast hm
  let z : c.F := (1 + ρ) / 2
  have hz2 : 2 * z = 1 + ρ := mul_div_cancel₀ _ two_ne_zero
  have hz : z * z + m = z := mul_left_cancel₀ (show (4 : c.F) ≠ 0 by norm_num) (by
    linear_combination (2 * z + ρ - 1) * hz2 + hρ + hm')
  have hzV : z ∈ V := by
    rcases V.mem_or_inv_mem z with h | h
    · exact h
    · by_cases h0 : z = 0
      · rw [h0]; exact V.zero_mem
      · have : z = 1 - m * z⁻¹ := by field_simp; linear_combination hz
        rw [this]
        exact sub_mem (one_mem V) (mul_mem (natCast_mem V m) h)
  have := Y.flat
  have := isDominant_generic V Y.s
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  have : IsDominant Y.j := inferInstanceAs (IsDominant (_ ≫ _))
  have := noetherianSpace_open Y
  have := Y.t.semi.smooth
  have := Y.t.semi.separated
  have := Y.t.act.hom H.w0
  refine Set.eq_univ_of_forall fun x K _ _ t ⟨pt, hpt⟩ => ?_
  obtain ⟨u, hu⟩ := exists_specializes Y.j x
  let L := AlgebraicClosure ((Xo.XF c).residueField u)
  let y : Sp L ⟶ Xo.XF c := spMap (algebraMap ((Xo.XF c).residueField u) L) ≫ (Xo.XF c).fromSpecResidueField u
  have hy : y (IsLocalRing.closedPoint L) = u := Scheme.fromSpecResidueField_apply u _
  clear_value y
  obtain ⟨R, _, _, i, j, χ, hi, hiy, hjt⟩ := exists_local (y ≫ Y.j) t (by
    have e₁ : (y ≫ Y.j) (IsLocalRing.closedPoint L) = Y.j u :=
      (Scheme.Hom.comp_apply y Y.j _).trans (congrArg Y.j hy)
    have e₂ : t (IsLocalRing.closedPoint K) = x :=
      (congrArg t (Subsingleton.elim (α := PrimeSpectrum K) _ pt)).trans hpt
    rw [e₁, e₂]; exact hu)
  obtain ⟨ga, hga⟩ := Spec.map_surjective (y ≫ pullback.snd Xo.s (spMap inc))
  obtain ⟨b, hb⟩ := Spec.map_surjective (χ ≫ Y.s)
  have hbga : i.comp b.hom = ga.hom.comp V.subtype := by
    have e : spMap (i.comp b.hom) = spMap (ga.hom.comp V.subtype) := by
      rw [← sp_comp, ← sp_comp]
      change spMap i ≫ Spec.map b = Spec.map ga ≫ _
      rw [hb, hga, reassoc_of% hiy, Model.j, Category.assoc, pullback.condition, reassoc_of% Y.jQ_over, Category.assoc]
    exact congrArg (·.hom) (Spec.map_injective e)
  have : CharZero L := (RingHom.charZero_iff ga.hom.injective).1 (inferInstanceAs (CharZero c.F))
  have hdet := (Y.oF.geom L y (ga.hom.comp inc) (by
    rw [pullback.condition, ← Category.assoc, ← hga, ← sp_comp]; rfl)).1
  have h₁ := actsBy_of_detCond D hq _ y _ (ga.hom z)
    (by rw [← map_ofNat ga.hom 2, ← map_mul, hz2, map_add, map_one]; rfl) hdet
  have h₂ : ActsBy Y.t.G (Y.t.act.act H.w0) (spMap i ≫ χ) (i (b.hom ⟨z, hzV⟩)) := by
    rw [hiy, show i (b.hom ⟨z, hzV⟩) = ga.hom z from RingHom.congr_fun hbga ⟨z, hzV⟩]
    exact (actsBy_pull Y.m.cart (Y.m.act H.w0) y _).1 h₁
  have h₃ := actsBy_baseChange j χ _ (actsBy_of_injective i hi χ _ h₂)
  rw [hjt] at h₃
  obtain ⟨T⟩ := Y.t.semi.fibres K t
  exact isProper_of_actsBy T (OAct.pullback t Y.t.G Y.t.act) H.d_prime hm hw _
    ((actsBy_pull (isGrpPullback_pullback Y.t.G t) (pullback.lift_fst _ _ _) _ _).2 (by rwa [Category.id_comp]))

end Spread

end GlobalTheory.DefiniteAbelian
