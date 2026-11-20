import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CommAlgFunctorCohomologyTwoEqZeroOfIsInitial

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.CechPic

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.PoincareDeRhamDuality.Test

/- English proof (translation)
Take `⟨B', _, P', -, -, h₁, h₂⟩` from `D S A hA`. Take `⟨u, hu, -⟩` from `h.univ B' P' h₁.isLB h₁.additive`. Use `⟨h.isLB, (triv_ev_iff h.isLB _ _).2 (h.additive.evc_one h.isLB _), h.zero, fun T x hx ↦ ?_, fun _ ↦ h.eq_one⟩` and prove the remaining obligations. Use `(h₁.isPerfect h₂).ker_left T x ((triv_ev_iff h₁.isLB _ _).2 ?_)` and prove the remaining obligations. Establish `e` using `congrArg (CechPic.pull (lift (fst T B') (snd T B' ≫ u)).left) ((triv_ev_iff h.isLB _ _).1 hx)`.

Rewrite `e` using `[pull_evc, map_zero, lift_fst_assoc, lift_snd]`. Establish `k` using `(cls_eq_iff h₁.isLB (pull_isLB h.isLB _)).2 hu`. Rewrite using `[evc, k, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc, e]`.
-/
theorem isPerfect_of_isDual (D : DualAbelianScheme) {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (h : IsDual A B P) : IsPerfect A B P := by
  obtain ⟨B', _, P', -, -, h₁, h₂⟩ := D S A hA
  obtain ⟨u, hu, -⟩ := h.univ B' P' h₁.isLB h₁.additive
  refine ⟨h.isLB, (triv_ev_iff h.isLB _ _).2 (h.additive.evc_one h.isLB _), h.zero, fun T x hx ↦ ?_,
    fun _ ↦ h.eq_one⟩
  refine (h₁.isPerfect h₂).ker_left T x ((triv_ev_iff h₁.isLB _ _).2 ?_)
  have e := congrArg (CechPic.pull (lift (fst T B') (snd T B' ≫ u)).left) ((triv_ev_iff h.isLB _ _).1 hx)
  rw [pull_evc, map_zero, lift_fst_assoc, lift_snd] at e
  have k := (cls_eq_iff h₁.isLB (pull_isLB h.isLB _)).2 hu
  rw [evc, k, cls_ev h.isLB, pull_evc, lift_fst, lift_snd_assoc, e]

/- English proof (translation)
Introduce `R _ A B _ _ g hA hB hg hg' P hP φ hφ`. Take `⟨h1, h2, -⟩` from `hφ.perfect H hA hg hB hg' (isPerfect_of_isDual D hA hP)`. Conclude with `⟨h1, fun x hx ↦ (h2 x).1 hx⟩`.
-/
theorem of_abelianDeRham (D : DualAbelianScheme) (H : AbelianDeRham) : PoincareDeRhamDuality := by
  intro R _ A B _ _ g hA hB hg hg' P hP φ hφ
  obtain ⟨h1, h2, -⟩ := hφ.perfect H hA hg hB hg' (isPerfect_of_isDual D hA hP)
  exact ⟨h1, fun x hx ↦ (h2 x).1 hx⟩

variable (R : Type) [CommRing R]

/- English proof (translation)
Assemble the required witnesses or components as `⟨(AbelianDeRham.Test.unit_hyp R).1, (AbelianDeRham.Test.unit_hyp R).2, isDual_unit, 0, Fin.elim0, Fin.elim0, by simpa using isChern_zero _ _ _ fun _ _ ↦ rfl, by simp⟩`.
-/
theorem unit_hyp : IsAbelianScheme (𝟙_ (Over (Sp R))) ∧ SmoothOfRelativeDimension 0 (𝟙_ (Over (Sp R))).hom ∧
    IsDual (𝟙_ (Over (Sp R))) (𝟙_ (Over (Sp R))) (LB.triv _) ∧
    IsCorrForm (dp0 R) (𝟙 _) (𝟙_ (Over (Sp R))) (𝟙_ (Over (Sp R))) (LB.triv _) 0 :=
  ⟨(AbelianDeRham.Test.unit_hyp R).1, (AbelianDeRham.Test.unit_hyp R).2, isDual_unit,
    0, Fin.elim0, Fin.elim0, by simpa using isChern_zero _ _ _ fun _ _ ↦ rfl, by simp⟩

/- English proof (translation)
The claim follows from `((AbelianDeRham.Test.unit_hodge_duality R).2 φ).symm`.
-/
theorem unit_concl (φ : HdR (𝟙_ (Over (Sp R))) →ₗ[R] HdR (𝟙_ (Over (Sp R))) →ₗ[R] R) :
    LinearMap.IsPerfPair φ ∧ ∀ x ∈ Fil (𝟙_ (Over (Sp R))), ∀ y ∈ Fil (𝟙_ (Over (Sp R))), φ x y = 0 :=
  ((AbelianDeRham.Test.unit_hodge_duality R).2 φ).symm

/- English proof (translation)
Take `⟨B, _, P, hB, hd, h₁, h₂⟩` from `D _ A hA`. Establish `hP` using `h₁.isPerfect h₂`. Take `⟨φ, hφ⟩` from `exists_isCorrForm (cupSquare_of_free F (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg (hd g hg))) hP.isLB hP.zero_left hP.zero_right`. Conclude with `⟨B, _, P, φ, hB, hd g hg, h₁, hφ⟩`.
-/
theorem exists_hyp (D : DualAbelianScheme) (F : AbelianDeRham.Free) (A : Over (Sp R)) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (B : Over (Sp R)) (_ : GrpObj B) (P : LB (A ⊗ B).left) (φ : HdR A →ₗ[R] HdR B →ₗ[R] R),
      IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ IsDual A B P ∧ IsCorrForm (dp0 R) (𝟙 _) A B P φ := by
  obtain ⟨B, _, P, hB, hd, h₁, h₂⟩ := D _ A hA
  have hP := h₁.isPerfect h₂
  obtain ⟨φ, hφ⟩ := exists_isCorrForm
    (cupSquare_of_free F (AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB) (smooth_prod hg (hd g hg)))
    hP.isLB hP.zero_left hP.zero_right
  exact ⟨B, _, P, φ, hB, hd g hg, h₁, hφ⟩

/- English proof (translation)
Set `E` to `GlobalTheory.WeierstrassCurve.ellPolAV W`. Establish `hg : SmoothOfRelativeDimension 1 E.A.hom` using `E.smoothDim`. Take `⟨B, _, P, φ, hB, hg', hP, hφ⟩` from `exists_hyp k D F E.A 1 E.isAb hg`. Establish `hp` using `(H k E.A B 1 E.isAb hB hg hg' P hP φ hφ).1`. Use `⟨B, _, P, φ, hφ, hp, ?_⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Establish `h0 : Subsingleton (HdR E.A)` using `⟨fun a b ↦ hp.bijective_left.1 rfl⟩`. Establish `h1 : Subsingleton (primDR E.A)` using `(Module.subsingleton_dual_iff k).1 h0`. Establish `h2` using `(F.prim E.isAb hg).2.2 ⊥`. Rewrite `h2` using `[Module.rankAtStalk_eq_zero_of_subsingleton]`.

Simplify using `at h2`.
-/
theorem elliptic (H : PoincareDeRhamDuality) (D : DualAbelianScheme) (F : AbelianDeRham.Free) (k : Type) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic] :
    ∃ (B : Over (Sp k)) (_ : GrpObj B) (P : LB ((GlobalTheory.WeierstrassCurve.ellPolAV W).A ⊗ B).left)
      (φ : HdR (GlobalTheory.WeierstrassCurve.ellPolAV W).A →ₗ[k] HdR B →ₗ[k] k),
      IsCorrForm (dp0 k) (𝟙 _) _ B P φ ∧ φ.IsPerfPair ∧ φ ≠ 0 := by
  let E := GlobalTheory.WeierstrassCurve.ellPolAV W
  have hg : SmoothOfRelativeDimension 1 E.A.hom := E.smoothDim
  obtain ⟨B, _, P, φ, hB, hg', hP, hφ⟩ := exists_hyp k D F E.A 1 E.isAb hg
  have hp := (H k E.A B 1 E.isAb hB hg hg' P hP φ hφ).1
  refine ⟨B, _, P, φ, hφ, hp, ?_⟩
  rintro rfl
  have h0 : Subsingleton (HdR E.A) := ⟨fun a b ↦ hp.bijective_left.1 rfl⟩
  have h1 : Subsingleton (primDR E.A) := (Module.subsingleton_dual_iff k).1 h0
  have h2 := (F.prim E.isAb hg).2.2 ⊥
  rw [Module.rankAtStalk_eq_zero_of_subsingleton] at h2
  simp at h2

end GlobalTheory.Published.PoincareDeRhamDuality.Test
