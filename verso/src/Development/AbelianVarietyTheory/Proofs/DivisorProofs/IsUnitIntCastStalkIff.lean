import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.LocSpread

set_option backward.isDefEq.respectTransparency false

section Loc

variable {R K : Type} [CommRing R] [CommRing K]

def IsStalkMap (σ : R →+* K) : Prop :=
  ∃ (x : Sp R) (e : Sp K ≅ Spec ((Sp R).presheaf.stalk x)), e.hom ≫ (Sp R).fromSpecStalk x = spMap σ ∧
    ∀ a, a ∉ x.asIdeal → IsUnit (σ a)

/- English proof (translation)
Use `letI := σ.toAlgebra`. Set `x : PrimeSpectrum R` to `⟨(maximalIdeal K).comap σ, inferInstance⟩`. Establish `hx : ∀ a, a ∉ x.asIdeal ↔ IsUnit (σ a)` using `fun a => by show ¬ σ a ∈ maximalIdeal K ↔ _`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff, not_not]`. Use `haveI : IsLocalization.AtPrime K x.asIdeal := by`.

Use `(isLocalization_iff _ _).2 ⟨fun y => (hx _).1 y.2, fun s => ?_, fun {a b} h => ⟨1, by rw [hi h]⟩⟩` and prove the remaining obligations. Take `⟨a, b, hb, e⟩` from `hs s`. Conclude with `⟨⟨a, ⟨b, (hx b).2 hb⟩⟩, e⟩`. Set `T` to `(Spec.structureSheaf R).presheaf.stalk x`. Use `haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x`.

Set `e : T ≃ₐ[R] K` to `IsLocalization.algEquiv x.asIdeal.primeCompl T K`. Use `⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha => (hx a).1 ha⟩` and prove the remaining obligations. Rewrite using `[Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`.

Conclude with `e.commutes a`.
-/
theorem isStalkMap_of [IsLocalRing K] (σ : R →+* K) (hi : Function.Injective σ)
    (hs : ∀ s : K, ∃ a b : R, IsUnit (σ b) ∧ s * σ b = σ a) : IsStalkMap σ := by
  letI := σ.toAlgebra
  let x : PrimeSpectrum R := ⟨(maximalIdeal K).comap σ, inferInstance⟩
  have hx : ∀ a, a ∉ x.asIdeal ↔ IsUnit (σ a) := fun a => by
    show ¬ σ a ∈ maximalIdeal K ↔ _
    rw [mem_maximalIdeal, mem_nonunits_iff, not_not]
  haveI : IsLocalization.AtPrime K x.asIdeal := by
    refine (isLocalization_iff _ _).2 ⟨fun y => (hx _).1 y.2, fun s => ?_, fun {a b} h => ⟨1, by rw [hi h]⟩⟩
    obtain ⟨a, b, hb, e⟩ := hs s
    exact ⟨⟨a, ⟨b, (hx b).2 hb⟩⟩, e⟩
  let T := (Spec.structureSheaf R).presheaf.stalk x
  haveI : IsLocalization x.asIdeal.primeCompl T := StructureSheaf.IsLocalization.to_stalk R x
  let e : T ≃ₐ[R] K := IsLocalization.algEquiv x.asIdeal.primeCompl T K
  refine ⟨x, asIso (Spec.map (e.toRingEquiv.toCommRingCatIso).hom), ?_, fun a ha => (hx a).1 ha⟩
  rw [Spec.fromSpecStalk_eq', asIso_hom, ← Spec.map_comp]
  congr 1
  ext a
  exact e.commutes a

/- English proof (translation)
Take `⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ha, hle⟩` from `PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen`. Conclude with `⟨a, ha, fun R' _ g hg z => hle fun h => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hg)⟩`.
-/
theorem exists_forall_mem {x : Sp R} {V : (Sp R).Opens} (hV : x ∈ V) :
    ∃ a : R, a ∉ x.asIdeal ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ z : Sp R', spMap g z ∈ V := by
  obtain ⟨_, ⟨_, ⟨a, rfl⟩, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  exact ⟨a, ha, fun R' _ g hg z => hle fun h => z.2.ne_top (Ideal.eq_top_of_isUnit_mem _ h hg)⟩

variable {σ : R →+* K}

/- English proof (translation)
Take `⟨x, e, he, hx⟩` from `hσ`. Establish `h₁ : IsPullback φ (p₀ ≫ e.hom) p ((Sp R).fromSpecStalk x)` using `h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) (by simpa using he.symm)`. Take `⟨V, hV, -, w, u, hw, hwu, hq⟩` from `StalkLimit.exists_spread h₁ q u₀ hu`. Take `⟨a, ha, H⟩` from `exists_forall_mem hV`. Use `⟨a, hx a ha, fun R' _ g hg Y' π p' e => ?_⟩` and prove the remaining obligations.

Take `⟨l, hl⟩` from `GenSpread.exists_lift_open p V e (H R' g hg)`. Use `⟨l ≫ u, by rw [Category.assoc, hq, reassoc_of% hl], fun φ' hφ' => ?_⟩` and prove the remaining obligations. Establish `: φ' ≫ l = w`. Rewrite using `[← cancel_mono (pullback.fst p V.ι), Category.assoc, hl, hφ', hw]`. Rewrite using `[reassoc_of% this, hwu]`.
-/
theorem exists_hom (hσ : IsStalkMap σ) {Y X Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p]
    (q : X ⟶ Sp R) [LocallyOfFinitePresentation q] {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K}
    (h : IsPullback φ p₀ p (spMap σ)) (u₀ : Y₀ ⟶ X) (hu : u₀ ≫ q = φ ≫ p) :
    ∃ a : R, IsUnit (σ a) ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        ∃ u : Y' ⟶ X, u ≫ q = π ≫ p ∧ ∀ φ' : Y₀ ⟶ Y', φ' ≫ π = φ → φ' ≫ u = u₀ := by
  obtain ⟨x, e, he, hx⟩ := hσ
  have h₁ : IsPullback φ (p₀ ≫ e.hom) p ((Sp R).fromSpecStalk x) :=
    h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) (by simpa using he.symm)
  obtain ⟨V, hV, -, w, u, hw, hwu, hq⟩ := StalkLimit.exists_spread h₁ q u₀ hu
  obtain ⟨a, ha, H⟩ := exists_forall_mem hV
  refine ⟨a, hx a ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := GenSpread.exists_lift_open p V e (H R' g hg)
  refine ⟨l ≫ u, by rw [Category.assoc, hq, reassoc_of% hl], fun φ' hφ' => ?_⟩
  have : φ' ≫ l = w := by
    rw [← cancel_mono (pullback.fst p V.ι), Category.assoc, hl, hφ', hw]
  rw [reassoc_of% this, hwu]

open GenSpread in

/- English proof (translation)
Take `⟨x, e, he, hx⟩` from `hσ`. Establish `h₁ : IsPullback φ (p₀ ≫ e.hom) p ((Sp R).fromSpecStalk x)` using `h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) (by simpa using he.symm)`. Take `⟨hc⟩` from `StalkLimit.nonempty_isLimit h₁`. Take `⟨V₀⟩ : Nonempty (StalkLimit.AffNhd x)` from `IsCofiltered.nonempty`. Establish `: IsAffine V₀.1.toScheme` using `V₀.2.2`.

Establish `: CompactSpace ((StalkLimit.diagram _ p).obj V₀)` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V₀.1.ι)`. Establish `: QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V₀)` using `quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V₀.1.ι)`. Set `ι₀ : (StalkLimit.diagram _ p).obj V₀ ⟶ Y` to `pullback.fst p V₀.1.ι`. Establish `e₀ : φ = (StalkLimit.cone h₁).π.app V₀ ≫ ι₀` using `(StalkLimit.cone_π_fst h₁ V₀).symm`. Take `⟨V, i, HV⟩` from `exists_lbIso_of_isLimit (StalkLimit.diagram _ p) (fun V => (StalkLimit.cone h₁).π.app V) (fun i => (StalkLimit.cone h₁).w i) hc (M.pull ι₀) (N.pull ι₀) (pull_isLB hM _) (pull_isLB hN _) (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _) (l …`.

Establish `e₁ : pullback.fst p V.1.ι = (StalkLimit.diagram _ p).map i ≫ ι₀` using `(StalkLimit.diagram_map_fst _ p i).symm`. Establish `HV' : LBIso (M.pull (pullback.fst p V.1.ι)) (N.pull (pullback.fst p V.1.ι))` using `LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (lbIso_pull_pull hM _ e₁) (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) HV (lbIso_pull_pull hN _ e₁).symm)`. Take `⟨a, ha, Ha⟩` from `exists_forall_mem V.2.1`. Use `⟨a, hx a ha, fun R' _ g hg Y' π p' e => ?_⟩` and prove the remaining obligations. Take `⟨l, hl⟩` from `exists_lift_open p V.1 e (Ha R' g hg)`.

Conclude with `lbIso_pull_comp l hl.symm hl.symm HV'`.
-/
theorem exists_lbIso (hσ : IsStalkMap σ) {Y Y₀ : Scheme.{0}} (p : Y ⟶ Sp R) [QuasiCompact p] [QuasiSeparated p]
    {φ : Y₀ ⟶ Y} {p₀ : Y₀ ⟶ Sp K} (h : IsPullback φ p₀ p (spMap σ)) {M N : LB Y}
    (hM : M.IsLB) (hN : N.IsLB) (H : LBIso (M.pull φ) (N.pull φ)) :
    ∃ a : R, IsUnit (σ a) ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (Y' : Scheme.{0}) (π : Y' ⟶ Y) (p' : Y' ⟶ Sp R'), π ≫ p = p' ≫ spMap g →
        LBIso (M.pull π) (N.pull π) := by
  obtain ⟨x, e, he, hx⟩ := hσ
  have h₁ : IsPullback φ (p₀ ≫ e.hom) p ((Sp R).fromSpecStalk x) :=
    h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) (by simpa using he.symm)
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd x) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ p).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V₀.1.ι)
  have : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V₀) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V₀.1.ι)
  let ι₀ : (StalkLimit.diagram _ p).obj V₀ ⟶ Y := pullback.fst p V₀.1.ι
  have e₀ : φ = (StalkLimit.cone h₁).π.app V₀ ≫ ι₀ := (StalkLimit.cone_π_fst h₁ V₀).symm
  obtain ⟨V, i, HV⟩ := exists_lbIso_of_isLimit (StalkLimit.diagram _ p) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (M.pull ι₀) (N.pull ι₀) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) (pull_isLB (pull_isLB hN _) _)
      (lbIso_pull_pull hM _ e₀).symm
      (LBIso.trans (pull_isLB hM _) (pull_isLB hN _) (pull_isLB (pull_isLB hN _) _) H (lbIso_pull_pull hN _ e₀)))
  have e₁ : pullback.fst p V.1.ι = (StalkLimit.diagram _ p).map i ≫ ι₀ := (StalkLimit.diagram_map_fst _ p i).symm
  have HV' : LBIso (M.pull (pullback.fst p V.1.ι)) (N.pull (pullback.fst p V.1.ι)) :=
    LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) (pull_isLB hN _) (lbIso_pull_pull hM _ e₁)
      (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB (pull_isLB hN _) _) (pull_isLB hN _) HV
        (lbIso_pull_pull hN _ e₁).symm)
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, hx a ha, fun R' _ g hg Y' π p' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open p V.1 e (Ha R' g hg)
  exact lbIso_pull_comp l hl.symm hl.symm HV'

end Loc

/- English proof (translation)
Use `a₁.proper` as an intermediate fact. Use `a₁.smooth` as an intermediate fact. Use `a₂.proper` as an intermediate fact. Use `a₂.smooth` as an intermediate fact. Take `⟨b₁, hb₁, H₁⟩` from `exists_hom hσ G₁.hom G₂.hom h₁.1 α₂ (h₂.1.w.trans h₁.1.w.symm)`.

Take `⟨b₂, hb₂, H₂⟩` from `exists_hom hσ G₂.hom G₁.hom h₂.1 α₁ (h₁.1.w.trans h₂.1.w.symm)`. Use `⟨b₁ * b₂, by rw [map_mul]; exact hb₁.mul hb₂, fun B' _ g j hu hj e => ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[map_mul, IsUnit.mul_iff]`. Establish `e' : spMap j ≫ spMap g = spMap σ` using `by rw [← Spec.map_comp, ← e]; rfl`. Use `haveI : IsSchemeTheoreticallyDominant (spMap j) := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hj`.

Take `⟨u, hu₁, hu₂⟩` from `H₁ B' g hu.1 _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition`. Take `⟨v, hv₁, hv₂⟩` from `H₂ B' g hu.2 _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition`. Establish `p₁` using `isGrpPullback_pullback G₁ (spMap g)`. Establish `p₂` using `isGrpPullback_pullback G₂ (spMap g)`. Establish `w₁ : α₁ ≫ G₁.hom = (G.hom ≫ spMap j) ≫ spMap g` using `by rw [Category.assoc, e']; exact h₁.1.w`.

Establish `w₂ : α₂ ≫ G₂.hom = (G.hom ≫ spMap j) ≫ spMap g` using `by rw [Category.assoc, e']; exact h₂.1.w`. Establish `q₁` using `p₁.cancel (h₁.congr e'.symm (pullback.lift_fst _ _ w₁).symm) (pullback.lift_snd _ _ w₁)`. Establish `q₂` using `p₂.cancel (h₂.congr e'.symm (pullback.lift_fst _ _ w₂).symm) (pullback.lift_snd _ _ w₂)`. Set `U : (Over.pullback (spMap g)).obj G₁ ⟶ (Over.pullback (spMap g)).obj G₂` to `Over.homMk (pullback.lift u (pullback.snd _ _) (hu₁.trans pullback.condition)) (pullback.lift_snd _ _ _)`. Set `V : (Over.pullback (spMap g)).obj G₂ ⟶ (Over.pullback (spMap g)).obj G₁` to `Over.homMk (pullback.lift v (pullback.snd _ _) (hv₁.trans pullback.condition)) (pullback.lift_snd _ _ _)`.

Establish `hU : U.left ≫ pullback.fst _ _ = u` using `pullback.lift_fst _ _ _`. Establish `hV : V.left ≫ pullback.fst _ _ = v` using `pullback.lift_fst _ _ _`. Establish `eU : (Iso.refl G).hom.left ≫ pullback.lift _ _ w₂ = pullback.lift _ _ w₁ ≫ U.left`. Use `(Category.id_comp _).trans (pullback.hom_ext ?_ ?_)` and prove the remaining obligations. Conclude with `(pullback.lift_fst _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ hU)).trans (hu₂ _ (pullback.lift_fst _ _ _))).symm`.

Conclude with `(pullback.lift_snd _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ (Over.w U))).trans (pullback.lift_snd _ _ _)).symm`. Establish `eV : (Iso.refl G).inv.left ≫ pullback.lift _ _ w₁ = pullback.lift _ _ w₂ ≫ V.left`. Use `(Category.id_comp _).trans (pullback.hom_ext ?_ ?_)` and prove the remaining obligations. Conclude with `(pullback.lift_fst _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ hV)).trans (hv₂ _ (pullback.lift_fst _ _ _))).symm`. Conclude with `(pullback.lift_snd _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ (Over.w V))).trans (pullback.lift_snd _ _ _)).symm`.

Use `haveI : Flat ((Over.pullback (spMap g)).obj G₁).hom := inferInstanceAs (Flat (pullback.snd _ _))`. Use `haveI : Flat ((Over.pullback (spMap g)).obj G₂).hom := inferInstanceAs (Flat (pullback.snd _ _))`. Use `haveI : IsSeparated ((Over.pullback (spMap g)).obj G₁).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))`. Use `haveI : IsSeparated ((Over.pullback (spMap g)).obj G₂).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))`. Use `haveI : IsIso U := ExtUnique.isIso_of_isPullback q₁.1 q₂.1 (Iso.refl G) U V eU eV`.

Use `haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))`. Use `haveI : IsMonHom (asIso U).hom := ExtUnique.isMonHom_of_isGrpPullback q₁ q₂ (Iso.refl G).hom U eU`. Conclude with `⟨u, _, ((isGrpPullback_of_iso (asIso U)).comp p₂).congr (Category.id_comp _) hU, q₁, pullback.lift_fst _ _ _, hu₂ _ (pullback.lift_fst _ _ _)⟩`.
-/
theorem exists_spread_grp {B Ω : Type} [CommRing B] [CommRing Ω] {σ : B →+* Ω} (hσ : IsStalkMap σ)
    {G₁ G₂ : Over (Sp B)} [GrpObj G₁] [GrpObj G₂] (a₁ : IsAbelianScheme G₁) (a₂ : IsAbelianScheme G₂) {G : Over (Sp Ω)}
    [GrpObj G] {α₁ : G.left ⟶ G₁.left} {α₂ : G.left ⟶ G₂.left} (h₁ : IsGrpPullback G G₁ (spMap σ) α₁)
    (h₂ : IsGrpPullback G G₂ (spMap σ) α₂) :
    ∃ a : B, IsUnit (σ a) ∧ ∀ (B' : Type) [CommRing B'] (g : B →+* B') (j : B' →+* Ω), IsUnit (g a) →
      Function.Injective j → j.comp g = σ →
      ∃ (β : pullback G₁.hom (spMap g) ⟶ G₂.left) (φ : G.left ⟶ pullback G₁.hom (spMap g)),
        IsGrpPullback ((Over.pullback (spMap g)).obj G₁) G₂ (spMap g) β ∧
        IsGrpPullback G ((Over.pullback (spMap g)).obj G₁) (spMap j) φ ∧ φ ≫ pullback.fst _ _ = α₁ ∧ φ ≫ β = α₂ := by
  have := a₁.proper
  have := a₁.smooth
  have := a₂.proper
  have := a₂.smooth
  obtain ⟨b₁, hb₁, H₁⟩ := exists_hom hσ G₁.hom G₂.hom h₁.1 α₂ (h₂.1.w.trans h₁.1.w.symm)
  obtain ⟨b₂, hb₂, H₂⟩ := exists_hom hσ G₂.hom G₁.hom h₂.1 α₁ (h₁.1.w.trans h₂.1.w.symm)
  refine ⟨b₁ * b₂, by rw [map_mul]; exact hb₁.mul hb₂, fun B' _ g j hu hj e => ?_⟩
  rw [map_mul, IsUnit.mul_iff] at hu
  have e' : spMap j ≫ spMap g = spMap σ := by rw [← Spec.map_comp, ← e]; rfl
  haveI : IsSchemeTheoreticallyDominant (spMap j) := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hj
  obtain ⟨u, hu₁, hu₂⟩ := H₁ B' g hu.1 _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  obtain ⟨v, hv₁, hv₂⟩ := H₂ B' g hu.2 _ (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have p₁ := isGrpPullback_pullback G₁ (spMap g)
  have p₂ := isGrpPullback_pullback G₂ (spMap g)
  have w₁ : α₁ ≫ G₁.hom = (G.hom ≫ spMap j) ≫ spMap g := by rw [Category.assoc, e']; exact h₁.1.w
  have w₂ : α₂ ≫ G₂.hom = (G.hom ≫ spMap j) ≫ spMap g := by rw [Category.assoc, e']; exact h₂.1.w
  have q₁ := p₁.cancel (h₁.congr e'.symm (pullback.lift_fst _ _ w₁).symm) (pullback.lift_snd _ _ w₁)
  have q₂ := p₂.cancel (h₂.congr e'.symm (pullback.lift_fst _ _ w₂).symm) (pullback.lift_snd _ _ w₂)
  let U : (Over.pullback (spMap g)).obj G₁ ⟶ (Over.pullback (spMap g)).obj G₂ :=
    Over.homMk (pullback.lift u (pullback.snd _ _) (hu₁.trans pullback.condition)) (pullback.lift_snd _ _ _)
  let V : (Over.pullback (spMap g)).obj G₂ ⟶ (Over.pullback (spMap g)).obj G₁ :=
    Over.homMk (pullback.lift v (pullback.snd _ _) (hv₁.trans pullback.condition)) (pullback.lift_snd _ _ _)
  have hU : U.left ≫ pullback.fst _ _ = u := pullback.lift_fst _ _ _
  have hV : V.left ≫ pullback.fst _ _ = v := pullback.lift_fst _ _ _
  have eU : (Iso.refl G).hom.left ≫ pullback.lift _ _ w₂ = pullback.lift _ _ w₁ ≫ U.left := by
    refine (Category.id_comp _).trans (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ hU)).trans
        (hu₂ _ (pullback.lift_fst _ _ _))).symm
    · exact (pullback.lift_snd _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ (Over.w U))).trans
        (pullback.lift_snd _ _ _)).symm
  have eV : (Iso.refl G).inv.left ≫ pullback.lift _ _ w₁ = pullback.lift _ _ w₂ ≫ V.left := by
    refine (Category.id_comp _).trans (pullback.hom_ext ?_ ?_)
    · exact (pullback.lift_fst _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ hV)).trans
        (hv₂ _ (pullback.lift_fst _ _ _))).symm
    · exact (pullback.lift_snd _ _ _).trans (((Category.assoc _ _ _).trans (congrArg _ (Over.w V))).trans
        (pullback.lift_snd _ _ _)).symm
  haveI : Flat ((Over.pullback (spMap g)).obj G₁).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : Flat ((Over.pullback (spMap g)).obj G₂).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : IsSeparated ((Over.pullback (spMap g)).obj G₁).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  haveI : IsSeparated ((Over.pullback (spMap g)).obj G₂).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
  haveI : IsIso U := ExtUnique.isIso_of_isPullback q₁.1 q₂.1 (Iso.refl G) U V eU eV
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  haveI : IsMonHom (asIso U).hom := ExtUnique.isMonHom_of_isGrpPullback q₁ q₂ (Iso.refl G).hom U eU
  exact ⟨u, _, ((isGrpPullback_of_iso (asIso U)).comp p₂).congr (Category.id_comp _) hU, q₁, pullback.lift_fst _ _ _,
    hu₂ _ (pullback.lift_fst _ _ _)⟩

section Model

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {w : M.Z}

/- English proof (translation)
Take `⟨U, f, hwU, rfl⟩` from `hx`. Establish `hne : (V : Set M.Z).Nonempty` using `⟨w, hwV⟩`. Take `⟨g, hgU, hwg⟩` from `hV.exists_basicOpen_le (V := U) ⟨w, hwU⟩ hwV`. Establish `hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty` using `⟨w, hwg⟩`. Use `hV.isLocalization_basicOpen g` as an intermediate fact.

Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj g (resG M.Z hgU f)`. Establish `h1` using `congrArg (M.res _ hg) ha`. Establish `h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t` using `fun t => M.res_resG (M.Z.basicOpen_le g) hg t`. Rewrite `h1` using `[map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply, RatModel.res_apply]`. Take `⟨h3, h4⟩` from `(RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hwV g).2 hwg)`.

Conclude with `⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _, pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ h3, by rw [← inv_pow]; exact pow_mem h4 n, h1⟩`.
-/
theorem exists_mul_eq_of_mem_O {V : M.Z.Opens} (hV : IsAffineOpen V) (hwV : w ∈ V) {x : Ω} (hx : x ∈ M.O w) :
    ∃ a ∈ M.ringOn V, ∃ b ∈ M.ringOn V, b ≠ 0 ∧ b⁻¹ ∈ M.O w ∧ x * b = a := by
  obtain ⟨U, f, hwU, rfl⟩ := hx
  have hne : (V : Set M.Z).Nonempty := ⟨w, hwV⟩
  obtain ⟨g, hgU, hwg⟩ := hV.exists_basicOpen_le (V := U) ⟨w, hwU⟩ hwV
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwg⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply, RatModel.res_apply] at h1
  obtain ⟨h3, h4⟩ := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hwV g).2 hwg)
  exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩, _,
    pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ h3,
    by rw [← inv_pow]; exact pow_mem h4 n, h1⟩

/- English proof (translation)
Establish `ho : IsOpen (⋂ x ∈ s, {z | x ∈ M.O z})` using `hs.isOpen_biInter fun x _ => M.isOpen_setOf_mem_O x`. Take `⟨U, hU, hw, hle⟩` from `exists_isAffineOpen_mem_and_subset (U := V ⊓ ⟨_, ho⟩) (x := w) ⟨hwV, Set.mem_iInter₂.2 fun x hx => h hx⟩`. Conclude with `⟨U, fun z hz => (hle hz).1, hU, hw, fun x hx => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 (hle hz).2 x hx⟩`.
-/
theorem exists_affine_subset {V : M.Z.Opens} (hwV : w ∈ V) {s : Set Ω} (hs : s.Finite) (h : s ⊆ M.O w) :
    ∃ U : M.Z.Opens, U ≤ V ∧ IsAffineOpen U ∧ w ∈ U ∧ s ⊆ M.ringOn U := by
  have ho : IsOpen (⋂ x ∈ s, {z | x ∈ M.O z}) := hs.isOpen_biInter fun x _ => M.isOpen_setOf_mem_O x
  obtain ⟨U, hU, hw, hle⟩ := exists_isAffineOpen_mem_and_subset (U := V ⊓ ⟨_, ho⟩) (x := w)
    ⟨hwV, Set.mem_iInter₂.2 fun x hx => h hx⟩
  exact ⟨U, fun z hz => (hle hz).1, hU, hw, fun x hx => RatModel.mem_ringOn.2 fun z hz =>
    Set.mem_iInter₂.1 (hle hz).2 x hx⟩

/- English proof (translation)
Introduce `x hx` and use `by obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx obtain ⟨h1, h2⟩ := (RatModel.isUnit_O_iff _).1 (hc n hn) have e : ((n : M.O w) : Ω) = n := by simp rw [e] at h1 h2 have := mul_mem h2 (RatModel.ringOn_le_O hwV h) rwa [inv_mul_cancel_left₀ h1] at this`.
-/
theorem ratHull_le_O (hc : ∀ n : ℤ, n ≠ 0 → IsUnit (n : M.O w)) {V : M.Z.Opens} (hwV : w ∈ V) :
    ratHull (M.ringOn V) ≤ M.O w := fun x hx => by
  obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
  obtain ⟨h1, h2⟩ := (RatModel.isUnit_O_iff _).1 (hc n hn)
  have e : ((n : M.O w) : Ω) = n := by simp
  rw [e] at h1 h2
  have := mul_mem h2 (RatModel.ringOn_le_O hwV h)
  rwa [inv_mul_cancel_left₀ h1] at this

/- English proof (translation)
Use `isStalkMap_of _ (Subalgebra.inclusion_injective h) fun s => ?_` and prove the remaining obligations. Take `⟨a, ha, b, hb, h0, h1, e⟩` from `exists_mul_eq_of_mem_O hV hwV s.2`. Conclude with `⟨⟨a, le_ratHull _ ha⟩, ⟨b, le_ratHull _ hb⟩, (RatModel.isUnit_O_iff _).2 ⟨h0, h1⟩, Subtype.ext e⟩`.
-/
theorem isStalkMap_ratHull {V : M.Z.Opens} (hV : IsAffineOpen V) (hwV : w ∈ V) (h : ratHull (M.ringOn V) ≤ M.O w) :
    IsStalkMap (Subalgebra.inclusion h).toRingHom := by
  refine isStalkMap_of _ (Subalgebra.inclusion_injective h) fun s => ?_
  obtain ⟨a, ha, b, hb, h0, h1, e⟩ := exists_mul_eq_of_mem_O hV hwV s.2
  exact ⟨⟨a, le_ratHull _ ha⟩, ⟨b, le_ratHull _ hb⟩, (RatModel.isUnit_O_iff _).2 ⟨h0, h1⟩, Subtype.ext e⟩

/- English proof (translation)
Take `⟨h0, h1⟩` from `(RatModel.isUnit_O_iff _).1 ha`. Take `⟨U, hle, hU, hw, hs⟩` from `exists_affine_subset hwV (Set.finite_singleton _) (Set.singleton_subset_iff.2 h1)`. Conclude with `⟨U, hle, hU, hw, IsUnit.of_mul_eq_one ⟨_, le_ratHull _ (hs rfl)⟩ (Subtype.ext (mul_inv_cancel₀ h0))⟩`.
-/
theorem exists_affine_isUnit {V : M.Z.Opens} (hwV : w ∈ V) (h : ratHull (M.ringOn V) ≤ M.O w) {a : ratHull (M.ringOn V)}
    (ha : IsUnit ((Subalgebra.inclusion h).toRingHom a)) :
    ∃ (U : M.Z.Opens) (hle : U ≤ V), IsAffineOpen U ∧ w ∈ U ∧
      IsUnit ((Subalgebra.inclusion (ratHull_mono (RatModel.ringOn_anti (M := M) hle))).toRingHom a) := by
  obtain ⟨h0, h1⟩ := (RatModel.isUnit_O_iff _).1 ha
  obtain ⟨U, hle, hU, hw, hs⟩ := exists_affine_subset hwV (Set.finite_singleton _) (Set.singleton_subset_iff.2 h1)
  exact ⟨U, hle, hU, hw, IsUnit.of_mul_eq_one ⟨_, le_ratHull _ (hs rfl)⟩ (Subtype.ext (mul_inv_cancel₀ h0))⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

/- English proof (translation)
Take `⟨G, _, α, β, hα, hβ, hL⟩` from `h`. Establish `e₀ : spMap (Subalgebra.inclusion (hS R hR)).toRingHom ≫ spMap (toRat R) = spMap (Subalgebra.inclusion ((le_ratHull R).trans (hS R hR))).toRingHom`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `p₁` using `isGrpPullback_pullback P.A (spMap (toRat R))`.

Establish `p₂` using `isGrpPullback_pullback Xo.univ.t.G (u ≫ pullback.fst _ _)`. Establish `w₁ : α ≫ P.A.hom = (G.hom ≫ spMap (Subalgebra.inclusion (hS R hR)).toRingHom) ≫ spMap (toRat R)`. Rewrite using `[Category.assoc, e₀]`. Conclude with `hα.1.w`. Establish `w₂ : β ≫ Xo.univ.t.G.hom = (G.hom ≫ spMap (Subalgebra.inclusion (hS R hR)).toRingHom) ≫ u ≫ pullback.fst _ _`.

Rewrite using `[hβ.1.w]`. Simplify using `only [Category.assoc]`. Establish `q₁` using `p₁.cancel (hα.congr e₀.symm (pullback.lift_fst _ _ w₁).symm) (pullback.lift_snd _ _ w₁)`. Establish `q₂` using `p₂.cancel (hβ.congr (Category.assoc _ _ _) (pullback.lift_fst _ _ w₂).symm) (pullback.lift_snd _ _ w₂)`. Establish `a₁` using `PolPull.isAbelianScheme_of_isGrpPullback P.isAb p₁`.

Take `⟨a, ha, H₁⟩` from `exists_spread_grp (hst R hR) a₁ (PolPull.isAbelianScheme_of_isGrpPullback (Obj.toPolAV Xo.univ).isAb p₂) q₁ q₂`. Take `⟨R₁, h₁, f₁, u₁⟩` from `hun R hR _ ha`. Take `⟨β₁, φ, g₂, gφ, e₁, e₂⟩` from `H₁ _ _ (Subalgebra.inclusion (hS R₁ f₁)).toRingHom u₁ (Subalgebra.inclusion_injective _) rfl`. Establish `g₁` using `isGrpPullback_pullback ((Over.pullback (spMap (toRat R))).obj P.A) (spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom)`. Use `haveI := (PolPull.isAbelianScheme_of_isGrpPullback a₁ g₁).proper`.

Establish `eα : φ ≫ pullback.fst _ _ ≫ pullback.fst P.A.hom (spMap (toRat R)) = α` using `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans (pullback.lift_fst _ _ _))`. Establish `eβ : φ ≫ β₁ ≫ pullback.fst Xo.univ.t.G.hom (u ≫ pullback.fst _ _) = β` using `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (pullback.lift_fst _ _ _))`. Establish `hP` using `P.isLB`. Establish `hU` using `Xo.univ.t.PP.isLB`. Take `⟨a', ha', H₂⟩` from `exists_lbIso (hst R₁ f₁) _ gφ.1 (pull_isLB hP _) (pull_isLB hU _) (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hU _) _) (GenSpread.lbIso_pull_pull hP φ eα.symm).symm (LBIso.trans (pull_isLB hP _) (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _ …`.

Take `⟨R₂, h₂, f₂, u₂⟩` from `hun R₁ f₁ _ ha'`. Establish `g₃` using `isGrpPullback_pullback ((Over.pullback (spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom)).obj ((Over.pullback (spMap (toRat R))).obj P.A)) (spMap (Subalgebra.inclusion (ratHull_mono h₂)).toRingHom)`. Use `⟨R₂, h₁.trans h₂, f₂, _, _, _, _, (g₃.comp (g₁.comp p₁)).congr ?_ rfl, (g₃.comp (g₂.comp p₂)).congr ?_ rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[← Category.assoc, ← Spec.map_comp, Category.assoc]`. Both sides reduce to the same expression. Conclude with `LBIso.trans (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hU _) (GenSpread.lbIso_pull_pull hP _ rfl) (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (H₂ _ _ u₂ _ _ _ g₃.1.w) (GenSpread.lbIso_pull_pull hU _ rfl).symm)`.
-/
theorem exists_spread_of_family {Xo : Moduli D l} {c : Coeff l} {S : Subalgebra o Ω} (good : Subalgebra o Ω → Prop)
    (hS : ∀ R, good R → ratHull R ≤ S) (hst : ∀ R (h : good R), IsStalkMap (Subalgebra.inclusion (hS R h)).toRingHom)
    (hun : ∀ R (h : good R) (a : ratHull R), IsUnit ((Subalgebra.inclusion (hS R h)).toRingHom a) →
      ∃ (R' : Subalgebra o Ω) (hle : R ≤ R'), good R' ∧ IsUnit ((Subalgebra.inclusion (ratHull_mono hle)).toRingHom a))
    {R : Subalgebra o Ω} (hR : good R) {P : PolAV (Sp R)} {u : Sp (ratHull R) ⟶ Xo.XF c}
    (h : UOver Xo c P (Subalgebra.inclusion ((le_ratHull R).trans (hS R hR))).toRingHom
      (spMap (Subalgebra.inclusion (hS R hR)).toRingHom ≫ u)) :
    ∃ (R' : Subalgebra o Ω) (hle : R ≤ R'), good R' ∧
      UOver Xo c P ((toRat R').comp (Subalgebra.inclusion hle).toRingHom)
      (spMap (Subalgebra.inclusion (ratHull_mono hle)).toRingHom ≫ u) := by
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have e₀ : spMap (Subalgebra.inclusion (hS R hR)).toRingHom ≫ spMap (toRat R) =
      spMap (Subalgebra.inclusion ((le_ratHull R).trans (hS R hR))).toRingHom := by
    rw [← Spec.map_comp]; rfl
  have p₁ := isGrpPullback_pullback P.A (spMap (toRat R))
  have p₂ := isGrpPullback_pullback Xo.univ.t.G (u ≫ pullback.fst _ _)
  have w₁ : α ≫ P.A.hom = (G.hom ≫ spMap (Subalgebra.inclusion (hS R hR)).toRingHom) ≫
      spMap (toRat R) := by
    rw [Category.assoc, e₀]; exact hα.1.w
  have w₂ : β ≫ Xo.univ.t.G.hom = (G.hom ≫ spMap (Subalgebra.inclusion (hS R hR)).toRingHom) ≫
      u ≫ pullback.fst _ _ := by
    rw [hβ.1.w]; simp only [Category.assoc]
  have q₁ := p₁.cancel (hα.congr e₀.symm (pullback.lift_fst _ _ w₁).symm) (pullback.lift_snd _ _ w₁)
  have q₂ := p₂.cancel (hβ.congr (Category.assoc _ _ _) (pullback.lift_fst _ _ w₂).symm) (pullback.lift_snd _ _ w₂)
  have a₁ := PolPull.isAbelianScheme_of_isGrpPullback P.isAb p₁
  obtain ⟨a, ha, H₁⟩ := exists_spread_grp (hst R hR) a₁
    (PolPull.isAbelianScheme_of_isGrpPullback (Obj.toPolAV Xo.univ).isAb p₂) q₁ q₂
  obtain ⟨R₁, h₁, f₁, u₁⟩ := hun R hR _ ha
  obtain ⟨β₁, φ, g₂, gφ, e₁, e₂⟩ := H₁ _ _ (Subalgebra.inclusion (hS R₁ f₁)).toRingHom u₁
    (Subalgebra.inclusion_injective _) rfl
  have g₁ := isGrpPullback_pullback ((Over.pullback (spMap (toRat R))).obj P.A)
    (spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom)
  haveI := (PolPull.isAbelianScheme_of_isGrpPullback a₁ g₁).proper
  have eα : φ ≫ pullback.fst _ _ ≫ pullback.fst P.A.hom (spMap (toRat R)) = α :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁).trans (pullback.lift_fst _ _ _))
  have eβ : φ ≫ β₁ ≫ pullback.fst Xo.univ.t.G.hom (u ≫ pullback.fst _ _) = β :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (pullback.lift_fst _ _ _))
  have hP := P.isLB
  have hU := Xo.univ.t.PP.isLB
  obtain ⟨a', ha', H₂⟩ := exists_lbIso (hst R₁ f₁) _ gφ.1
    (pull_isLB hP _) (pull_isLB hU _)
    (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hU _) _)
      (GenSpread.lbIso_pull_pull hP φ eα.symm).symm
      (LBIso.trans (pull_isLB hP _) (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) hL
        (GenSpread.lbIso_pull_pull hU φ eβ.symm)))
  obtain ⟨R₂, h₂, f₂, u₂⟩ := hun R₁ f₁ _ ha'
  have g₃ := isGrpPullback_pullback ((Over.pullback
    (spMap (Subalgebra.inclusion (ratHull_mono h₁)).toRingHom)).obj
    ((Over.pullback (spMap (toRat R))).obj P.A))
    (spMap (Subalgebra.inclusion (ratHull_mono h₂)).toRingHom)
  refine ⟨R₂, h₁.trans h₂, f₂, _, _, _, _, (g₃.comp (g₁.comp p₁)).congr ?_ rfl,
    (g₃.comp (g₂.comp p₂)).congr ?_ rfl, ?_⟩
  · rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  · rw [← Category.assoc, ← Spec.map_comp, Category.assoc]; rfl
  · exact LBIso.trans (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hU _)
      (GenSpread.lbIso_pull_pull hP _ rfl) (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hU _) _)
        (pull_isLB hU _) (H₂ _ _ u₂ _ _ _ g₃.1.w) (GenSpread.lbIso_pull_pull hU _ rfl).symm)

/- English proof (translation)
Take `⟨_, _, ⟨U, hle, hU, hwU, rfl⟩, H⟩` from `exists_spread_of_family (S := M.O w) (fun R => ∃ U : M.Z.Opens, U ≤ V ∧ IsAffineOpen U ∧ w ∈ U ∧ M.ringOn U = R) (by rintro _ ⟨U, -, -, hwU, rfl⟩; exact ratHull_le_O hc hwU) (by rintro _ ⟨U, h1, hU, hwU, rfl⟩; exact isStalkMap_ratHull hU hwU _) (by`. Introduce and unpack `_ ⟨U, h1, hU, hwU, rfl⟩ a ha`. Take `⟨U', h2, hU', hwU', H⟩` from `exists_affine_isUnit hwU _ ha`. Conclude with `⟨_, RatModel.ringOn_anti h2, ⟨U', h2.trans h1, hU', hwU', rfl⟩, H⟩)`. Use the proof step `⟨V, le_rfl, hV, hw, rfl⟩ h`.

Conclude with `⟨U, hle, hU, hwU, H⟩`.
-/
theorem exists_spread {Xo : Moduli D l} {c : Coeff l} (hc : ∀ n : ℤ, n ≠ 0 → IsUnit (n : M.O w)) {V : M.Z.Opens}
    (hV : IsAffineOpen V) (hw : w ∈ V) {P : PolAV (Sp (M.ringOn V))} {u : Sp (ratHull (M.ringOn V)) ⟶ Xo.XF c}
    (h : UOver Xo c P (Subalgebra.inclusion (RatModel.ringOn_le_O hw)).toRingHom
      (spMap (Subalgebra.inclusion (ratHull_le_O hc hw)).toRingHom ≫ u)) :
    ∃ (U : M.Z.Opens) (hle : U ≤ V), IsAffineOpen U ∧ w ∈ U ∧
      UOver Xo c P ((toRat (M.ringOn U)).comp (Subalgebra.inclusion (RatModel.ringOn_anti (M := M) hle)).toRingHom)
      (spMap (Subalgebra.inclusion (ratHull_mono (RatModel.ringOn_anti (M := M) hle))).toRingHom ≫ u) := by
  obtain ⟨_, _, ⟨U, hle, hU, hwU, rfl⟩, H⟩ := exists_spread_of_family (S := M.O w)
    (fun R => ∃ U : M.Z.Opens, U ≤ V ∧ IsAffineOpen U ∧ w ∈ U ∧ M.ringOn U = R)
    (by rintro _ ⟨U, -, -, hwU, rfl⟩; exact ratHull_le_O hc hwU)
    (by rintro _ ⟨U, h1, hU, hwU, rfl⟩; exact isStalkMap_ratHull hU hwU _)
    (by
      rintro _ ⟨U, h1, hU, hwU, rfl⟩ a ha
      obtain ⟨U', h2, hU', hwU', H⟩ := exists_affine_isUnit hwU _ ha
      exact ⟨_, RatModel.ringOn_anti h2, ⟨U', h2.trans h1, hU', hwU', rfl⟩, H⟩)
    ⟨V, le_rfl, hV, hw, rfl⟩ h
  exact ⟨U, hle, hU, hwU, H⟩

/- English proof (translation)
Set `ψ : R →+* Ω` to `S.val.toRingHom.comp R.subtype`. Establish `hR : ∀ a : R, ψ a ∈ R₁` using `fun a => by`. Establish `ha : a ∈ Algebra.adjoin ℤ (t : Set R)` using `ht ▸ Algebra.mem_top`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha => exact hR ⟨a, ha, rfl⟩`.

Consider the case `algebraMap n => simpa using intCast_mem R₁ n`. Consider the case `add a b _ _ ha hb => exact map_add ψ a b ▸ add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact map_mul ψ a b ▸ mul_mem ha hb`. Take `⟨P₁, φ₁, hφ₁, hL₁⟩` from `exists_pol_baseChange P (spMap (ψ.codRestrict R₁ hR))`. Conclude with `⟨P₁, (uOver_baseChange_iff hφ₁ hL₁ _).2 h⟩`.
-/
theorem exists_model_of_subring {Xo : Moduli D l} {c : Coeff l} {S R₁ : Subalgebra o Ω} (hS : R₁ ≤ S) {R : Subring S}
    {P : PolAV (Sp R)} {v : Sp S ⟶ Xo.XF c} (h : UOver Xo c P R.subtype v) {t : Finset R}
    (ht : Algebra.adjoin ℤ (t : Set R) = ⊤) (hR : (fun a : R => ((a : S) : Ω)) '' t ⊆ R₁) :
    ∃ P₁ : PolAV (Sp R₁), UOver Xo c P₁ (Subalgebra.inclusion hS).toRingHom v := by
  let ψ : R →+* Ω := S.val.toRingHom.comp R.subtype
  have hR : ∀ a : R, ψ a ∈ R₁ := fun a => by
    have ha : a ∈ Algebra.adjoin ℤ (t : Set R) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem a ha => exact hR ⟨a, ha, rfl⟩
    | algebraMap n => simpa using intCast_mem R₁ n
    | add a b _ _ ha hb => exact map_add ψ a b ▸ add_mem ha hb
    | mul a b _ _ ha hb => exact map_mul ψ a b ▸ mul_mem ha hb
  obtain ⟨P₁, φ₁, hφ₁, hL₁⟩ := exists_pol_baseChange P (spMap (ψ.codRestrict R₁ hR))
  exact ⟨P₁, (uOver_baseChange_iff hφ₁ hL₁ _).2 h⟩

/- English proof (translation)
Rewrite using `[← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_inclusion_comp {R₀ R₁ R₂ : Subalgebra o Ω} (h₁ : R₀ ≤ R₁) (h₂ : R₁ ≤ R₂) {Y : Scheme.{0}} (u : Sp R₀ ⟶ Y) :
    spMap (Subalgebra.inclusion h₂).toRingHom ≫ spMap (Subalgebra.inclusion h₁).toRingHom ≫ u =
      spMap (Subalgebra.inclusion (h₁.trans h₂)).toRingHom ≫ u := by
  rw [← Category.assoc, ← Spec.map_comp]; rfl

/- English proof (translation)
Take `⟨R, P₀, ⟨t, ht⟩, h₀⟩` from `exists_uOver_finiteType (spMap (Subalgebra.inclusion (ratHull_le_O hc hw)).toRingHom ≫ u)`. Take `⟨U₁, h₁, f₁, m₁, s₁⟩` from `exists_affine_subset hw (s := (fun a : R => ((a : M.O w) : Ω)) '' t) (t.finite_toSet.image _) (by rintro _ ⟨a, -, rfl⟩; exact (a : M.O w).2)`. Take `⟨P₁, H₁⟩` from `exists_model_of_subring (RatModel.ringOn_le_O m₁) h₀ ht s₁`. Rewrite `H₁` using `[← spMap_inclusion_comp (ratHull_mono (RatModel.ringOn_anti (M := M) h₁)) (ratHull_le_O hc m₁)]`. Take `⟨U₂, h₂, f₂, m₂, H₂⟩` from `exists_spread hc f₁ m₁ H₁`.

Rewrite `H₂` using `[spMap_inclusion_comp]`. Take `⟨P₂, φ₂, hφ₂, hL₂⟩` from `exists_pol_baseChange P₁ (spMap (Subalgebra.inclusion (RatModel.ringOn_anti (M := M) h₂)).toRingHom)`. Conclude with `⟨U₂, RatModel.ringOn_anti (h₂.trans h₁), P₂, h₂.trans h₁, f₂, m₂, (uOver_baseChange_iff hφ₂ hL₂ _).2 H₂⟩`.
-/
theorem exists_model {Xo : Moduli D l} {c : Coeff l} (hc : ∀ n : ℤ, n ≠ 0 → IsUnit (n : M.O w)) {V : M.Z.Opens}
    (hw : w ∈ V) (u : Sp (ratHull (M.ringOn V)) ⟶ Xo.XF c) :
    ∃ (U : M.Z.Opens) (h : M.ringOn V ≤ M.ringOn U) (P : PolAV (Sp (M.ringOn U))), U ≤ V ∧ IsAffineOpen U ∧ w ∈ U ∧
      UOver Xo c P (toRat (M.ringOn U)) (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u) := by
  obtain ⟨R, P₀, ⟨t, ht⟩, h₀⟩ :=
    exists_uOver_finiteType (spMap (Subalgebra.inclusion (ratHull_le_O hc hw)).toRingHom ≫ u)
  obtain ⟨U₁, h₁, f₁, m₁, s₁⟩ := exists_affine_subset hw (s := (fun a : R => ((a : M.O w) : Ω)) '' t)
    (t.finite_toSet.image _) (by rintro _ ⟨a, -, rfl⟩; exact (a : M.O w).2)
  obtain ⟨P₁, H₁⟩ := exists_model_of_subring (RatModel.ringOn_le_O m₁) h₀ ht s₁
  rw [← spMap_inclusion_comp (ratHull_mono (RatModel.ringOn_anti (M := M) h₁)) (ratHull_le_O hc m₁)] at H₁
  obtain ⟨U₂, h₂, f₂, m₂, H₂⟩ := exists_spread hc f₁ m₁ H₁
  rw [spMap_inclusion_comp] at H₂
  obtain ⟨P₂, φ₂, hφ₂, hL₂⟩ := exists_pol_baseChange P₁
    (spMap (Subalgebra.inclusion (RatModel.ringOn_anti (M := M) h₂)).toRingHom)
  exact ⟨U₂, RatModel.ringOn_anti (h₂.trans h₁), P₂, h₂.trans h₁, f₂, m₂, (uOver_baseChange_iff hφ₂ hL₂ _).2 H₂⟩

end Model

/- English proof (translation)
Rewrite using `[← map_intCast (f.stalkMap x).hom n]`. Conclude with `isUnit_map_iff _ _`.
-/
theorem isUnit_intCast_stalk_iff {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) (n : ℤ) :
    IsUnit (n : X.presheaf.stalk x) ↔ IsUnit (n : Y.presheaf.stalk (f x)) := by
  rw [← map_intCast (f.stalkMap x).hom n]
  exact isUnit_map_iff _ _

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo cf C X U₀ u₀ w _ hw ⟨x, hx⟩`. Use `exists_model (fun n hn => ?_) hw u₀` and prove the remaining obligations. Rewrite using `[← map_intCast (X.M.stalkEquiv w) n, MulEquiv.isUnit_map, isUnit_intCast_stalk_iff X.π, ← hx, ← isUnit_intCast_stalk_iff C.i, isUnit_intCast_stalk_iff (pullback.snd _ _ : Xo.XF cf ⟶ Sp cf.F)]`. Establish `h : IsUnit (n : cf.F)` using `IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)`. Establish `h'` using `(h.map (Scheme.ΓSpecIso (CommRingCat.of cf.F)).inv.hom).map ((Sp cf.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF cf ⟶ Sp cf.F) x) trivial).hom`.

Rewrite `h'` using `[map_intCast, map_intCast]`. Then use the resulting hypothesis.
-/
theorem exists_uOver_ringOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (U₀ : X.M.Z.Opens) (u₀ : Sp (ratHull (X.M.ringOn U₀)) ⟶ Xo.XF cf) (w : X.M.Z), IsAffineOpen U₀ → w ∈ U₀ → X.π w ∈ Set.range C.i → ∃ (U₁ : X.M.Z.Opens) (h : X.M.ringOn U₀ ≤ X.M.ringOn U₁) (P₁ : PolAV (Sp (X.M.ringOn U₁))), U₁ ≤ U₀ ∧ IsAffineOpen U₁ ∧ w ∈ U₁ ∧ UOver Xo cf P₁ (toRat (X.M.ringOn U₁)) (spMap (Subalgebra.inclusion (ratHull_mono h)).toRingHom ≫ u₀) := by
  intro E _ _ _ H Dw l Xo cf C X U₀ u₀ w _ hw ⟨x, hx⟩
  refine exists_model (fun n hn => ?_) hw u₀
  rw [← map_intCast (X.M.stalkEquiv w) n, MulEquiv.isUnit_map, isUnit_intCast_stalk_iff X.π, ← hx,
    ← isUnit_intCast_stalk_iff C.i, isUnit_intCast_stalk_iff (pullback.snd _ _ : Xo.XF cf ⟶ Sp cf.F)]
  have h : IsUnit (n : cf.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
  have h' := (h.map (Scheme.ΓSpecIso (CommRingCat.of cf.F)).inv.hom).map
    ((Sp cf.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF cf ⟶ Sp cf.F) x) trivial).hom
  rwa [map_intCast, map_intCast] at h'

end GlobalTheory.UPoinc.LocSpread
