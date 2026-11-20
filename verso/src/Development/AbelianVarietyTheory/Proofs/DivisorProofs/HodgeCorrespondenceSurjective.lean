import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.HodgeSubSurj

/- English proof (translation)
Establish `e` using `hV.fromSpec_preimage_self.ge`. Use `letI := QCoh.appLEAlgebra hV.fromSpec e`. Use `letI := QCoh.appLEModule hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e`. Use `haveI := QCoh.appLE_isScalarTower hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e`. Establish `H` using `QCoh.isBaseChange_pullbackSections hV.fromSpec F (isAffineOpen_top _) hV e`.

Establish `hs : Function.Surjective (hV.fromSpec.appLE V ⊤ e)`. Establish `: hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(T, V)).inv`. Rewrite using `[Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Conclude with `(congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)`. Rewrite using `[this]`.

Conclude with `(ConcreteCategory.bijective_of_isIso _).2`. Proceed by induction on `t using H.inductionOn with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul s => exact ⟨s, rfl⟩`. Consider the case `smul r t ih`.

Take `⟨s, rfl⟩` from `ih`. Take `⟨r, rfl⟩` from `hs r`. Conclude with `⟨r • s, QCoh.pullbackSections_smul _ _ _ _ _⟩`. Consider the case `add t t' ih ih'`. Take `⟨s, rfl⟩` from `ih`.

Take `⟨s', rfl⟩` from `ih'`. Conclude with `⟨s + s', map_add _ _ _⟩`.
-/
theorem pullbackSections_fromSpec_surjective {T : Scheme.{0}} (F : T.Modules) [F.IsQuasicoherent]
    {V : T.Opens} (hV : IsAffineOpen V) (t : Γ((Scheme.Modules.pullback hV.fromSpec).obj F, ⊤)) :
    ∃ s, pullbackSections hV.fromSpec F hV.fromSpec_preimage_self.ge s = t := by
  have e := hV.fromSpec_preimage_self.ge
  letI := QCoh.appLEAlgebra hV.fromSpec e
  letI := QCoh.appLEModule hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e
  haveI := QCoh.appLE_isScalarTower hV.fromSpec ((Scheme.Modules.pullback hV.fromSpec).obj F) e
  have H := QCoh.isBaseChange_pullbackSections hV.fromSpec F (isAffineOpen_top _) hV e
  have hs : Function.Surjective (hV.fromSpec.appLE V ⊤ e) := by
    have : hV.fromSpec.appLE V ⊤ e = (Scheme.ΓSpecIso Γ(T, V)).inv := by
      rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
    rw [this]
    exact (ConcreteCategory.bijective_of_isIso _).2
  induction t using H.inductionOn with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s => exact ⟨s, rfl⟩
  | smul r t ih =>
    obtain ⟨s, rfl⟩ := ih
    obtain ⟨r, rfl⟩ := hs r
    exact ⟨r • s, QCoh.pullbackSections_smul _ _ _ _ _⟩
  | add t t' ih ih' =>
    obtain ⟨s, rfl⟩ := ih
    obtain ⟨s', rfl⟩ := ih'
    exact ⟨s + s', map_add _ _ _⟩

section Affine

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

/- English proof (translation)
Use `⟨fun h => ?_, fun h => congrArg Over.Hom.left (epsZero_comp (G := G) ⟨v, h⟩)⟩` and prove the remaining obligations. Establish `h' : (toUnit (Pdiv.specO R R)).left = 𝟙 (Sp R)`. Rewrite using `[Over.toUnit_left]`. Conclude with `Spec.map_id _`. Use `ext1`.

Simplify using `only [Over.comp_left, h']`. Conclude with `h.trans (Category.id_comp _).symm`.
-/
theorem isTangent_iff_ptMap (v : epsR R ⟶ G) : IsTangent v ↔
    Pdiv.ptMap (TrivSqZeroExt.fstHom R R R) ≫ (v : Pdiv.specO R (DualNumber R) ⟶ G) =
      toUnit (Pdiv.specO R R) ≫ η[G] := by
  refine ⟨fun h => ?_, fun h => congrArg Over.Hom.left (epsZero_comp (G := G) ⟨v, h⟩)⟩
  have h' : (toUnit (Pdiv.specO R R)).left = 𝟙 (Sp R) := by
    rw [Over.toUnit_left]
    exact Spec.map_id _
  ext1
  simp only [Over.comp_left, h']
  exact h.trans (Category.id_comp _).symm

/- English proof (translation)
Take `⟨w, hw⟩` from `(OmegaGlobal.toOmega_bijective R G ⟨tangent_injective _ _, TangentSurj.tangent_surjective _ _⟩).2 ⟨fun x => tanVal (A := G) x.1 f, fun x y _ => tanVal_mul ((isTangent_iff_ptMap _).2 x.2) ((isTangent_iff_ptMap _).2 y.2) f, fun a x _ => tanVal_epsScale a x.1 f⟩`. Conclude with `⟨w, fun x => (congrArg (fun u => u.1 x) hw).symm⟩`.
-/
theorem exists_omega [QuasiSeparated G.hom] [Smooth G.hom] (f : Cris.Form (G.hom ≫ 𝟙 _)) :
    ∃ w : Γ(omega G, ⊤), ∀ x : Pdiv.LieG G, tanVal (A := G) x.1 f =
      (Scheme.ΓSpecIso (.of R)).hom (VB.dualApp (tangent x) le_top w) := by
  obtain ⟨w, hw⟩ := (OmegaGlobal.toOmega_bijective R G
    ⟨tangent_injective _ _, TangentSurj.tangent_surjective _ _⟩).2
    ⟨fun x => tanVal (A := G) x.1 f,
      fun x y _ => tanVal_mul ((isTangent_iff_ptMap _).2 x.2) ((isTangent_iff_ptMap _).2 y.2) f,
      fun a x _ => tanVal_epsScale a x.1 f⟩
  exact ⟨w, fun x => (congrArg (fun u => u.1 x) hw).symm⟩

/- English proof (translation)
Use `Eq.trans ?_ (Category.assoc _ _ _)` and prove the remaining obligations. Use `congrArg (· ≫ (epsIso R).hom) ?_` and prove the remaining obligations. Use `Conormal.pullback_hom_ext (sec_hom η[A]) fun W a => ?_` and prove the remaining obligations. Establish `k₁` using `Conormal.le_of_sq (unitSec_comp h) (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl`. Establish `k₂` using `Conormal.le_of_sq we (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl`.

Use `(Conormal.baseMap_d (sec_hom η[A]) _ w we le_rfl le_rfl k₂ le_rfl a).trans (Eq.symm ?_)` and prove the remaining obligations. Use `(congrArg ((cotMap x.1 (epsZero_comp x)).app _) (omegaBase_dUnit h le_rfl le_rfl k₁ le_rfl a)).trans ?_` and prove the remaining obligations. Use `(cotMap_d x.1 (epsZero_comp x) k₁ k₂ le_rfl _).trans ?_` and prove the remaining obligations. Conclude with `congrArg _ (Conormal.appLE_appLE rfl _ _ _ a)`.
-/
theorem form_eq {T : Scheme.{0}} {A : Over T} [GrpObj A] {b : Sp R ⟶ T} {φ : G.left ⟶ A.left}
    (h : IsGrpPullback G A b φ) (x : Pdiv.LieG G)
    (w : (x.1.left ≫ φ) ≫ A.hom = (Pdiv.specO R (DualNumber R)).hom ≫ b)
    (we : sec (epsZero R) ≫ x.1.left ≫ φ = b ≫ unitSec A) :
    TanFibre.form w we = omegaBase h ≫ cotMap x.1 (epsZero_comp x) ≫ (epsIso R).hom := by
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine congrArg (· ≫ (epsIso R).hom) ?_
  refine Conormal.pullback_hom_ext (sec_hom η[A]) fun W a => ?_
  have k₁ := Conormal.le_of_sq (unitSec_comp h) (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl
  have k₂ := Conormal.le_of_sq we (le_refl (unitSec A ⁻¹ᵁ W)) le_rfl
  refine (Conormal.baseMap_d (sec_hom η[A]) _ w we le_rfl le_rfl k₂ le_rfl a).trans (Eq.symm ?_)
  refine (congrArg ((cotMap x.1 (epsZero_comp x)).app _)
    (omegaBase_dUnit h le_rfl le_rfl k₁ le_rfl a)).trans ?_
  refine (cotMap_d x.1 (epsZero_comp x) k₁ k₂ le_rfl _).trans ?_
  exact congrArg _ (Conormal.appLE_appLE rfl _ _ _ a)

/- English proof (translation)
Establish `: QuasiSeparated G.hom` using `MorphismProperty.of_isPullback h.1 ‹_›`. Establish `: Smooth G.hom` using `MorphismProperty.of_isPullback h.1 ‹_›`. Take `⟨u, hu⟩` from `exists_omega f`. Use `isIso_omegaBase h` as an intermediate fact. Take `⟨t, rfl⟩` from `(ConcreteCategory.bijective_of_isIso ((omegaBase h).app ⊤)).2 u`.

Use `⟨t, fun v hv w we => ?_⟩` and prove the remaining obligations. Set `x : Pdiv.LieG G` to `⟨v, (isTangent_iff_ptMap v).1 hv⟩`. Establish `e` using `form_eq h x w we`. Use `(hu x).trans (congrArg (fun a : Γ(Sp R, ⊤) => (Scheme.ΓSpecIso (.of R)).hom a) ?_)` and prove the remaining obligations. Conclude with `(congr(($e).app ⊤ t)).symm`.
-/
theorem exists_pullback_omega {T : Scheme.{0}} {A : Over T} [GrpObj A] [QuasiSeparated A.hom]
    [Smooth A.hom] {b : Sp R ⟶ T} {φ : G.left ⟶ A.left} (h : IsGrpPullback G A b φ)
    (f : Cris.Form (G.hom ≫ 𝟙 _)) :
    ∃ t : Γ((Scheme.Modules.pullback b).obj (omega A), ⊤), ∀ (v : epsR R ⟶ G), IsTangent v →
      ∀ (w : (v.left ≫ φ) ≫ A.hom = (Pdiv.specO R (DualNumber R)).hom ≫ b)
        (we : sec (epsZero R) ≫ v.left ≫ φ = b ≫ unitSec A),
        tanVal v f = (Scheme.ΓSpecIso (.of R)).hom ((TanFibre.form w we).app ⊤ t) := by
  have : QuasiSeparated G.hom := MorphismProperty.of_isPullback h.1 ‹_›
  have : Smooth G.hom := MorphismProperty.of_isPullback h.1 ‹_›
  obtain ⟨u, hu⟩ := exists_omega f
  have := isIso_omegaBase h
  obtain ⟨t, rfl⟩ := (ConcreteCategory.bijective_of_isIso ((omegaBase h).app ⊤)).2 u
  refine ⟨t, fun v hv w we => ?_⟩
  let x : Pdiv.LieG G := ⟨v, (isTangent_iff_ptMap v).1 hv⟩
  have e := form_eq h x w we
  refine (hu x).trans (congrArg (fun a : Γ(Sp R, ⊤) => (Scheme.ΓSpecIso (.of R)).hom a) ?_)
  exact (congr(($e).app ⊤ t)).symm

/- English proof (translation)
Express the relevant statement in the definitionally equal form `c.1 ∈ Cris.F1 _ at hc`. Rewrite `hc` using `[Cris.hodgeFiltration_eq_range]`. Take `⟨c, hc'⟩` from `c`. Take `⟨f, rfl⟩` from `hc`. Conclude with `⟨f, fun v k hk => hk.2 f hc'⟩`.
-/
theorem exists_form {c : primDR G} (hc : c ∈ PrimitiveSubmodule G) : ∃ f : Cris.Form (G.hom ≫ 𝟙 _),
    ∀ (v : epsR R ⟶ G) (k : HdR G), IsLieImage k v → k c = tanVal v f := by
  change c.1 ∈ Cris.F1 _ at hc
  rw [Cris.hodgeFiltration_eq_range] at hc
  obtain ⟨c, hc'⟩ := c
  obtain ⟨f, rfl⟩ := hc
  exact ⟨f, fun v k hk => hk.2 f hc'⟩

end Affine

/- English proof (translation)
Establish `h : IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec)` using `isGrpPullback_pullback A hV.fromSpec`. Take `⟨f, hf⟩` from `exists_form hc`. Take `⟨t, ht⟩` from `exists_pullback_omega h f`. Take `⟨s, hs⟩` from `pullbackSections_fromSpec_surjective (omega A) hV t`. Use `⟨s, fun v k hk w we => (hf v k hk).trans ((ht v hk.1 w we).trans ?_)⟩` and prove the remaining obligations.

Rewrite using `[← hs]`. Both sides reduce to the same expression.
-/
theorem exists_corr {T : Scheme.{0}} (A : Over T) [GrpObj A] [QuasiSeparated A.hom] [Smooth A.hom]
    {V : T.Opens} (hV : IsAffineOpen V) (c : primDR (onAff A hV)) (hc : c ∈ PrimitiveSubmodule (onAff A hV)) :
    ∃ s, GlobalTheory.HodgeSub.Corr A hV s c := by
  have h : IsGrpPullback (onAff A hV) A hV.fromSpec (pullback.fst A.hom hV.fromSpec) :=
    isGrpPullback_pullback A hV.fromSpec
  obtain ⟨f, hf⟩ := exists_form hc
  obtain ⟨t, ht⟩ := exists_pullback_omega h f
  obtain ⟨s, hs⟩ := pullbackSections_fromSpec_surjective (omega A) hV t
  refine ⟨s, fun v k hk w we => (hf v k hk).trans ((ht v hk.1 w we).trans ?_)⟩
  rw [← hs]
  rfl

/- English proof (translation)
Introduce `_ T A _ g hA hg V hV c hc`. Use `hA.proper` as an intermediate fact. Establish `: Smooth A.hom` using `SmoothOfRelativeDimension.smooth g _`. Conclude with `exists_corr A hV c hc`.
-/
theorem main : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (c : primDR (onAff A hV)), c ∈ PrimitiveSubmodule (onAff A hV) →
      ∃ s, GlobalTheory.HodgeSub.Corr A hV s c := by
  intro _ T A _ g hA hg V hV c hc
  have := hA.proper
  have : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  exact exists_corr A hV c hc

end GlobalTheory.HodgeSubSurj
