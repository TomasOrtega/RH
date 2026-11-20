import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescendsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsDescendToLargeSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjDescendsToLargeSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfieldStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedDataStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegDesc

/- English proof (translation)
Establish `v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom` using `Over.w _`. Establish `v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom` using `Over.w _`. Conclude with `⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ) (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`.
-/
theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

/- English proof (translation)
Establish `w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom` using `Over.w _`. Establish `v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom` using `Over.w _`. Establish `h₁` using `h.1`. Rewrite using `[← w₁, reassoc_of% h₁, w, reassoc_of% v₁]`.
-/
theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

/- English proof (translation)
Establish `a₁` using `hψ.1`. Establish `a₂` using `hψ.2`. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ ≫ (fst A A).left = _ ≫ (fst A A).left`. Rewrite using `[Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]`.

Express the relevant statement in the definitionally equal form `_ ≫ (snd A A).left = _ ≫ (snd A A).left`. Rewrite using `[Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]`.
-/
theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

/- English proof (translation)
Establish `w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom` using `Over.w _`. Establish `w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom` using `Over.w _`. Establish `v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom` using `Over.w _`. Establish `v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom` using `Over.w _`. Establish `h₁` using `h.1`.

Establish `h₂` using `h.2`. Use `⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => pullback.lift (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition])) (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition])) (by rw [IsPullback.lift_snd, IsPullback.l …` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `_ ≫ (fst A A).left = _ ≫ (fst A A).left`. Rewrite using `[Category.assoc, h₁, ← Category.assoc]`.

Conclude with `(congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)`. Express the relevant statement in the definitionally equal form `_ ≫ (snd A A).left = _ ≫ (snd A A).left`. Rewrite using `[Category.assoc, h₂, ← Category.assoc]`. Conclude with `(congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)`. Rewrite using `[← v₁, ← Category.assoc]`.

Conclude with `(congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)`. Apply `pullback.hom_ext` to reduce the goal to its premises. Use `Eq.trans ?_ (pullback.lift_fst _ _ _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ (fst A' A').left = _`. Apply `hA.hom_ext` to reduce the goal to its premises.

Rewrite using `[IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]`. Rewrite using `[IsPullback.lift_snd, ← h2, Category.assoc, v₁]`. Use `Eq.trans ?_ (pullback.lift_snd _ _ _).symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ (snd A' A').left = _`. Apply `hA.hom_ext` to reduce the goal to its premises.

Rewrite using `[IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]`. Rewrite using `[IsPullback.lift_snd, ← h2, Category.assoc, v₂]`.
-/
theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_subtype_inclusion {K : Type} [Field K] {K₀ K₁ : Subfield K} (h : K₀ ≤ K₁) :
    spMap K₁.subtype ≫ spMap (Subfield.inclusion h) = spMap K₀.subtype := by
  rw [← Spec.map_comp]
  rfl

/- English proof (translation)
Introduce `h M o _ ζ K _ K₀ s₀ s c hs hc`. Take `⟨sA, hA⟩` from `GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K K₀ c.A.left c.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple hc.1)`. Set `K' : Subfield K` to `K₀ ⊔ Subfield.closure (sA : Set K)`. Take `⟨X', p', φ', hproj, hpb⟩` from `hA K' le_sup_left (Subfield.subset_closure.trans (SetLike.coe_subset_coe.2 le_sup_right))`. Establish `: IsProper p'`.

Take `⟨N, i, _, rfl⟩` from `hproj`. Use `isProper_str K' N` as an intermediate fact. Use `infer_instance`. Establish `: LocallyOfFinitePresentation p'` using `LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance`. Set `A' : Over (Sp K')` to `Over.mk p'`.

Establish `: IsProper A'.hom` using `‹IsProper p'›`. Establish `: LocallyOfFinitePresentation A'.hom` using `‹LocallyOfFinitePresentation p'›`. Establish `hpb' : IsPullback (φ' : c.A.left ⟶ A'.left) c.A.hom A'.hom (spMap K'.subtype)` using `hpb`. Take `⟨sG, hG⟩` from `GlobalTheory.grpObj_descends_to_large_subfield K K' A' c.A φ' hpb'`. Take `⟨φ₂', hsq'⟩` from `exists_isSquare hpb'.w`.

Establish `: IsProper (A' ⊗ A').hom`. Express the relevant statement in the definitionally equal form `IsProper (pullback.fst A'.hom A'.hom ≫ A'.hom)`. Use `infer_instance`. Take `⟨sL, hL⟩` from `GlobalTheory.T.exists_lineBundle_descent_to_subfield K K' (A' ⊗ A').left (c.A ⊗ c.A).left (A' ⊗ A').hom (c.A ⊗ c.A).hom φ₂' c.P c.isLB (isPullback_of_isSquare hpb' hsq')`. Take `⟨lv, hlv⟩ : ∃ lv : Fin h ⊕ Fin h → (Sp K ⟶ c.A.left), ∀ u, lv u = (c.lev (Pi.single u 1)).left` from `⟨_, fun _ => rfl⟩`.

Establish `hlev : ∀ u, lv u ≫ c.A.hom = 𝟙 (Sp K)` using `fun u => (congrArg (· ≫ c.A.hom) (hlv u)).trans (Over.w (c.lev (Pi.single u 1)))`. Take `⟨sP, hP⟩` from `GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K' (Sp K') (Sp K) (𝟙 _) (𝟙 _) (spMap K'.subtype) X' p' (Fin h ⊕ Fin h) (fun u => lv u ≫ φ') IsPullback.of_id_snd (fun u => by`. Establish `e` using `hlev u`. Rewrite using `[Category.comp_id, Category.assoc, hpb.w, reassoc_of% e])`. Use `⟨sA ∪ sG ∪ sL ∪ sP, fun K₁ hK hF => ?_⟩` and prove the remaining obligations.

Simplify using `only [Finset.coe_union, Set.union_subset_iff] at hF`. Take `⟨⟨⟨hsA, hsG⟩, hsL⟩, hsP⟩` from `hF`. Establish `h' : K' ≤ K₁` using `sup_le hK (Subfield.closure_le.2 hsA)`. Set `j` to `spMap (Subfield.inclusion h')`. Establish `hj : spMap K₁.subtype ≫ j = spMap K'.subtype` using `spMap_subtype_inclusion h'`.

Set `A₁ : Over (Sp K₁)` to `Over.mk (pullback.snd p' j)`. Set `φ₁ : A₁.left ⟶ A'.left` to `pullback.fst p' j`. Establish `hpb₁ : IsPullback φ₁ A₁.hom A'.hom j` using `IsPullback.of_hasPullback p' j`. Set `ψ : c.A.left ⟶ A₁.left` to `hpb₁.lift φ' (c.A.hom ≫ spMap K₁.subtype) (by rw [Category.assoc, hj]; exact hpb.w)`. Establish `hψ₁ : ψ ≫ φ₁ = φ'` using `hpb₁.lift_fst _ _ _`.

Establish `hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap K₁.subtype` using `hpb₁.lift_snd _ _ _`. Take `⟨grp, hgrp⟩` from `hG K₁ h' hsG A₁ φ₁ ψ hpb₁ hψ₁ hψ₂`. Take `⟨φ₂, hsq₁⟩` from `exists_isSquare hpb₁.w`. Take `⟨ψ₂, hsqψ⟩` from `exists_isSquare hψ₂`. Take `⟨P₁, hP₁, hiso⟩` from `hL K₁ h' hsL (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂ ψ₂ (isPullback_of_isSquare hpb₁ hsq₁) (isSquare_comp hψ₁ hsqψ hsq₁ hsq') (isSquare_w hψ₂ hsqψ)`.

Take `⟨f₁, hf₁⟩` from `hP K₁ h' hsP (Sp K₁) (𝟙 _) j (spMap K₁.subtype) IsPullback.of_id_snd hj (by simp)`. Set `l : Fin h ⊕ Fin h → (Sp K₁ ⟶ A₁.left)` to `fun u => hpb₁.lift (f₁ u) (𝟙 _) (by rw [Category.id_comp]; exact (hf₁ u).2.trans (Category.comp_id _))`. Establish `hl₁ : ∀ u, l u ≫ φ₁ = f₁ u` using `fun u => hpb₁.lift_fst _ _ _`. Establish `hl₂ : ∀ u, l u ≫ A₁.hom = 𝟙 _` using `fun u => hpb₁.lift_snd _ _ _`. Set `lev₁ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₁)) ⟶ A₁)` to `fun u => Over.homMk (l u) (hl₂ u)`.

Take `⟨c₁, hc₁⟩` from `GlobalTheory.T.exists_siegelObject_of_descended_data h M o ζ K₁ K K₁.subtype (spMap (Subfield.inclusion hK) ≫ s₀) s c A₁ ψ ψ₂ P₁ lev₁ (by rw [hs, ← Category.assoc, spMap_subtype_inclusion]) hgrp hsqψ hP₁ hiso (fun u => by`. Establish `e` using `hlev u`. Establish `key : lv u ≫ ψ = spMap K₁.subtype ≫ l u`. Apply `hpb₁.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Category.assoc, hψ₁, hl₁]`.

Conclude with `(hf₁ u).1.symm`. Rewrite using `[Category.assoc, Category.assoc, hψ₂, hl₂, reassoc_of% e, Category.comp_id]`. Conclude with `(congrArg (· ≫ ψ) (hlv u)).symm.trans key)`. Conclude with `⟨c₁, GlobalTheory.SiegelDescent.principal_of_fieldExtension h M o ζ K₁ K K₁.subtype _ s c₁ c hc₁ hc, hc₁⟩`.
-/
theorem siegPre_descends : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (K : Type) [Field K] (K₀ : Subfield K) (s₀ : Sp K₀ ⟶ Sp o) (s : Sp K ⟶ Sp o) (c : SiegPre h M ζ s), s = spMap K₀.subtype ≫ s₀ → c.Principal → ∃ F : Finset K, ∀ (K₁ : Subfield K) (hK : K₀ ≤ K₁), (F : Set K) ⊆ K₁ → ∃ c₁ : SiegPre h M ζ (spMap (Subfield.inclusion hK) ≫ s₀), c₁.Principal ∧ SiegPB c c₁ (spMap K₁.subtype) := by
  intro h M o _ ζ K _ K₀ s₀ s c hs hc
  classical
  obtain ⟨sA, hA⟩ := GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield K K₀ c.A.left c.A.hom (GlobalTheory.ProjSpace.isProjOver_of_relAmple hc.1)
  let K' : Subfield K := K₀ ⊔ Subfield.closure (sA : Set K)
  obtain ⟨X', p', φ', hproj, hpb⟩ := hA K' le_sup_left
    (Subfield.subset_closure.trans (SetLike.coe_subset_coe.2 le_sup_right))
  have : IsProper p' := by
    obtain ⟨N, i, _, rfl⟩ := hproj
    have := isProper_str K' N
    infer_instance
  have : LocallyOfFinitePresentation p' :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance
  let A' : Over (Sp K') := Over.mk p'
  have : IsProper A'.hom := ‹IsProper p'›
  have : LocallyOfFinitePresentation A'.hom := ‹LocallyOfFinitePresentation p'›
  have hpb' : IsPullback (φ' : c.A.left ⟶ A'.left) c.A.hom A'.hom (spMap K'.subtype) := hpb
  obtain ⟨sG, hG⟩ := GlobalTheory.grpObj_descends_to_large_subfield K K' A' c.A φ' hpb'
  obtain ⟨φ₂', hsq'⟩ := exists_isSquare hpb'.w
  have : IsProper (A' ⊗ A').hom := by
    change IsProper (pullback.fst A'.hom A'.hom ≫ A'.hom)
    infer_instance
  obtain ⟨sL, hL⟩ := GlobalTheory.T.exists_lineBundle_descent_to_subfield K K' (A' ⊗ A').left (c.A ⊗ c.A).left (A' ⊗ A').hom (c.A ⊗ c.A).hom φ₂'
    c.P c.isLB (isPullback_of_isSquare hpb' hsq')
  obtain ⟨lv, hlv⟩ : ∃ lv : Fin h ⊕ Fin h → (Sp K ⟶ c.A.left), ∀ u, lv u = (c.lev (Pi.single u 1)).left :=
    ⟨_, fun _ => rfl⟩
  have hlev : ∀ u, lv u ≫ c.A.hom = 𝟙 (Sp K) := fun u =>
    (congrArg (· ≫ c.A.hom) (hlv u)).trans (Over.w (c.lev (Pi.single u 1)))
  obtain ⟨sP, hP⟩ := GlobalTheory.T.exists_descent_of_morphisms_to_subfield K K' (Sp K') (Sp K) (𝟙 _) (𝟙 _) (spMap K'.subtype) X' p' (Fin h ⊕ Fin h)
    (fun u => lv u ≫ φ') IsPullback.of_id_snd
    (fun u => by
      have e := hlev u
      rw [Category.comp_id, Category.assoc, hpb.w, reassoc_of% e])
  refine ⟨sA ∪ sG ∪ sL ∪ sP, fun K₁ hK hF => ?_⟩
  simp only [Finset.coe_union, Set.union_subset_iff] at hF
  obtain ⟨⟨⟨hsA, hsG⟩, hsL⟩, hsP⟩ := hF
  have h' : K' ≤ K₁ := sup_le hK (Subfield.closure_le.2 hsA)
  let j := spMap (Subfield.inclusion h')
  have hj : spMap K₁.subtype ≫ j = spMap K'.subtype := spMap_subtype_inclusion h'
  let A₁ : Over (Sp K₁) := Over.mk (pullback.snd p' j)
  let φ₁ : A₁.left ⟶ A'.left := pullback.fst p' j
  have hpb₁ : IsPullback φ₁ A₁.hom A'.hom j := IsPullback.of_hasPullback p' j
  let ψ : c.A.left ⟶ A₁.left := hpb₁.lift φ' (c.A.hom ≫ spMap K₁.subtype)
    (by rw [Category.assoc, hj]; exact hpb.w)
  have hψ₁ : ψ ≫ φ₁ = φ' := hpb₁.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap K₁.subtype := hpb₁.lift_snd _ _ _
  obtain ⟨grp, hgrp⟩ := hG K₁ h' hsG A₁ φ₁ ψ hpb₁ hψ₁ hψ₂
  obtain ⟨φ₂, hsq₁⟩ := exists_isSquare hpb₁.w
  obtain ⟨ψ₂, hsqψ⟩ := exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hL K₁ h' hsL (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom φ₂ ψ₂
    (isPullback_of_isSquare hpb₁ hsq₁) (isSquare_comp hψ₁ hsqψ hsq₁ hsq') (isSquare_w hψ₂ hsqψ)
  obtain ⟨f₁, hf₁⟩ := hP K₁ h' hsP (Sp K₁) (𝟙 _) j (spMap K₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Fin h ⊕ Fin h → (Sp K₁ ⟶ A₁.left) := fun u => hpb₁.lift (f₁ u) (𝟙 _)
    (by rw [Category.id_comp]; exact (hf₁ u).2.trans (Category.comp_id _))
  have hl₁ : ∀ u, l u ≫ φ₁ = f₁ u := fun u => hpb₁.lift_fst _ _ _
  have hl₂ : ∀ u, l u ≫ A₁.hom = 𝟙 _ := fun u => hpb₁.lift_snd _ _ _
  let lev₁ : Fin h ⊕ Fin h → (𝟙_ (Over (Sp K₁)) ⟶ A₁) := fun u => Over.homMk (l u) (hl₂ u)
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.T.exists_siegelObject_of_descended_data h M o ζ K₁ K K₁.subtype (spMap (Subfield.inclusion hK) ≫ s₀) s c A₁ ψ ψ₂ P₁
    lev₁ (by rw [hs, ← Category.assoc, spMap_subtype_inclusion]) hgrp hsqψ hP₁ hiso (fun u => by
      have e := hlev u
      have key : lv u ≫ ψ = spMap K₁.subtype ≫ l u := by
        apply hpb₁.hom_ext
        · rw [Category.assoc, Category.assoc, hψ₁, hl₁]
          exact (hf₁ u).1.symm
        · rw [Category.assoc, Category.assoc, hψ₂, hl₂, reassoc_of% e, Category.comp_id]
      exact (congrArg (· ≫ ψ) (hlv u)).symm.trans key)
  exact ⟨c₁, GlobalTheory.SiegelDescent.principal_of_fieldExtension h M o ζ K₁ K K₁.subtype _ s c₁ c hc₁ hc, hc₁⟩

end GlobalTheory.SiegDesc
