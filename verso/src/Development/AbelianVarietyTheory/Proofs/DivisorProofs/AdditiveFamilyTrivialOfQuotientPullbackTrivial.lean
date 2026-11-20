import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeIsIsoOfMonoSameDimension
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualInjPull

/- English proof (translation)
Establish `h1 : SmoothOfRelativeDimension g (pullback.snd A.hom (𝟙 S))` using `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom (𝟙 S)) hA`. Establish `h2` using `h g S (𝟙 S) h1`. Establish `sq : IsPullback (inv (pullback.fst C.hom (𝟙 S))) C.hom (pullback.snd C.hom (𝟙 S)) (𝟙 S)` using `IsPullback.of_horiz_isIso ⟨by rw [IsIso.inv_comp_eq, Category.comp_id, pullback.condition, Category.comp_id]⟩`. Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h2`.
-/
theorem smooth_of_dimLe {S : Scheme.{0}} {A C : Over S} (h : DimLe A C) {g : ℕ}
    (hA : SmoothOfRelativeDimension g A.hom) : SmoothOfRelativeDimension g C.hom := by
  have h1 : SmoothOfRelativeDimension g (pullback.snd A.hom (𝟙 S)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback A.hom (𝟙 S)) hA
  have h2 := h g S (𝟙 S) h1
  have sq : IsPullback (inv (pullback.fst C.hom (𝟙 S))) C.hom (pullback.snd C.hom (𝟙 S)) (𝟙 S) :=
    IsPullback.of_horiz_isIso ⟨by rw [IsIso.inv_comp_eq, Category.comp_id, pullback.condition, Category.comp_id]⟩
  exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback sq h2

/- English proof (translation)
Use `hB.proper` as an intermediate fact. Use `hB'.proper` as an intermediate fact. Use `hB'.geomConnected` as an intermediate fact. Establish `: Mono x.left` using `inferInstanceAs (Mono ((Over.forget S).map x))`. Establish `: IsProper (x.left ≫ B'.hom)` using `by rw [Over.w]; infer_instance`.

Establish `: IsProper x.left` using `IsProper.of_comp x.left B'.hom`. Establish `: IsClosedImmersion x.left` using `(IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩`. Establish `hs : Surjective B.hom` using `⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by`. Rewrite using `[← Scheme.Hom.comp_apply, Over.w]`. Use the proof step `rfl⟩⟩`.

Establish `: Surjective (x.left ≫ B'.hom)` using `by rw [Over.w]; exact hs`. Establish `: IsIso x.left` using `GlobalTheory.AbMonoIsoAny.isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl`. Establish `: IsIso ((Over.forget _).map x)` using `‹_›`. Conclude with `isIso_of_reflects_iso x (Over.forget _)`.
-/
theorem isIso_of_mono' {S : Scheme.{0}} {B B' : Over S} [GrpObj B] [GrpObj B'] (hB : IsAbelianScheme B)
    (hB' : IsAbelianScheme B') {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    (hg' : SmoothOfRelativeDimension g B'.hom) (x : B ⟶ B') [Mono x] : IsIso x := by
  have := hB.proper
  have := hB'.proper
  have := hB'.geomConnected
  have : Mono x.left := inferInstanceAs (Mono ((Over.forget S).map x))
  have : IsProper (x.left ≫ B'.hom) := by rw [Over.w]; infer_instance
  have : IsProper x.left := IsProper.of_comp x.left B'.hom
  have : IsClosedImmersion x.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have hs : Surjective B.hom := ⟨fun t => ⟨(η[B] : 𝟙_ (Over S) ⟶ B).left t, by
    rw [← Scheme.Hom.comp_apply, Over.w]; rfl⟩⟩
  have : Surjective (x.left ≫ B'.hom) := by rw [Over.w]; exact hs
  have : IsIso x.left :=
    GlobalTheory.AbMonoIsoAny.isIso_of_isClosedImmersion B'.hom x.left hg' (by rw [Over.w]; exact hg) le_rfl
  have : IsIso ((Over.forget _).map x) := ‹_›
  exact isIso_of_reflects_iso x (Over.forget _)

/- English proof (translation)
Establish `c : cls M hM = cls _ (pull_isLB hN _)` using `(cls_eq_iff hM (pull_isLB hN _)).2 e`. Rewrite using `[← evc_ev hN f g (pull_isLB hN _) a t, evc, evc, c]`.
-/
theorem evc_of_iso {S : Scheme.{0}} {A T X U Y : Over S} {M : LB (A ⊗ T).left} {N : LB (X ⊗ U).left}
    (hM : M.IsLB) (hN : N.IsLB) (f : A ⊗ T ⟶ X) (g : A ⊗ T ⟶ U) (e : LBIso M (ev N f g))
    (a : Y ⟶ A) (t : Y ⟶ T) : evc hM a t = evc hN (lift a t ≫ f) (lift a t ≫ g) := by
  have c : cls M hM = cls _ (pull_isLB hN _) := (cls_eq_iff hM (pull_isLB hN _)).2 e
  rw [← evc_ev hN f g (pull_isLB hN _) a t, evc, evc, c]

/- English proof (translation)
Introduce `K _ _ A A' B _ _ _ g P P' q hA hA' hB hgA' hgB hD hq hP' haP' eP T M hM haM hT`. Take `⟨C, _, Q, hC, hdim, hQ⟩` from `GlobalTheory.T.exists_dual_abelianScheme_poincare _ A' hA'`. Establish `hgC : SmoothOfRelativeDimension g C.hom` using `smooth_of_dimLe hdim hgA'`. Establish `hP` using `hD.isLB`. Establish `hQl` using `hQ.isLB`.

Establish `hR : (ev Q (fst A C ≫ q) (snd A C)).IsLB` using `pull_isLB hQl _`. Establish `haR : IsAdditive (ev Q (fst A C ≫ q) (snd A C))`. Use `(isAdditive_iff hR).2 fun Y a a' t ↦ ?_` and prove the remaining obligations. Rewrite using `[evc_ev hQl, evc_ev hQl, evc_ev hQl]`. Simplify using `only [lift_fst_assoc, lift_snd, MonObj.mul_comp]`.

Conclude with `(isAdditive_iff hQl).1 hQ.additive Y _ _ t`. Take `⟨s, hs, -⟩` from `hQ.univ B P' hP' haP'`. Take `⟨r, hr, -⟩` from `hD.univ C _ hR haR`. Establish `hsr : s ≫ r = 𝟙 B`. Use `GlobalTheory.AbDual.IsDual.eq_of_evc hD ?_` and prove the remaining obligations.

Establish `e1` using `evc_of_iso hR hP _ _ hr (fst A B) (snd A B ≫ s)`. Establish `e1'` using `evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A B) (snd A B ≫ s)`. Establish `e2` using `evc_of_iso hP' hQl _ _ hs (fst A B ≫ q) (snd A B)`. Establish `e3 : evc hP' (fst A B ≫ q) (snd A B) = evc hP (fst A B) (snd A B)`. Rewrite using `[← cls_ev hP' _ _ (pull_isLB hP' _), (cls_eq_iff _ hP).2 eP, evc, lift_fst_snd, Over.id_left, pull_id]`.

Simplify using `only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at e1 e1' e2`. Rewrite using `[Category.comp_id, ← e3, e2, ← e1', e1]`. Take `⟨c, hc, -⟩` from `hQ.univ T M hM haM`. Establish `hcr : c ≫ r = 1` using `hD.eq_one _ ((triv_ev_iff hP _ _).2 (by`. Establish `f1` using `evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ c)`.

Establish `f1'` using `evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ c)`. Establish `f2` using `evc_of_iso hM hQl _ _ hc (fst A T ≫ q) (snd A T)`. Establish `f3` using `(triv_ev_iff hM _ _).1 hT`. Simplify using `only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1' f2`. Rewrite using `[← f1, f1', ← f2, f3]))`.

Establish `h1r : (1 : T ⟶ C) ≫ r = 1` using `hD.eq_one _ ((triv_ev_iff hP _ _).2 (by`. Establish `f1` using `evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ (1 : T ⟶ C))`. Establish `f1'` using `evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ (1 : T ⟶ C))`. Simplify using `only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1'`. Rewrite using `[← f1, f1', MonObj.comp_one, evc_one_right hQl hQ.zero]))`.

Use `haveI : IsSplitMono s := IsSplitMono.mk' ⟨r, hsr⟩`. Use `haveI : IsIso s := isIso_of_mono' hB hC hgB hgC s`. Establish `hrinv : r = inv s` using `(IsIso.inv_eq_of_hom_inv_id hsr).symm`. Use `haveI : IsIso r := by rw [hrinv]; infer_instance`. Establish `hc1 : c = 1` using `(cancel_mono r).1 (hcr.trans h1r.symm)`.

Use `(cls_eq_zero_iff hM).1 ?_` and prove the remaining obligations. Rewrite using `[(cls_eq_iff hM (pull_isLB hQl _)).2 hc, cls_ev hQl, hc1, MonObj.comp_one, evc_one_right hQl hQ.zero]`.
-/
theorem triv_of_triv_pull : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' B : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left) (P' : LB (A' ⊗ B).left) (q : A ⟶ A'), IsAbelianScheme A → IsAbelianScheme A' → IsAbelianScheme B → SmoothOfRelativeDimension g A'.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → IsMonHom q → P'.IsLB → IsAdditive P' → LBIso (ev P' (fst A B ≫ q) (snd A B)) P → ∀ (T : Over (Sp K)) (M : LB (A' ⊗ T).left), M.IsLB → IsAdditive M → Triv (ev M (fst A T ≫ q) (snd A T)) → Triv M := by
  intro K _ _ A A' B _ _ _ g P P' q hA hA' hB hgA' hgB hD hq hP' haP' eP T M hM haM hT
  obtain ⟨C, _, Q, hC, hdim, hQ⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare _ A' hA'
  have hgC : SmoothOfRelativeDimension g C.hom := smooth_of_dimLe hdim hgA'
  have hP := hD.isLB
  have hQl := hQ.isLB
  have hR : (ev Q (fst A C ≫ q) (snd A C)).IsLB := pull_isLB hQl _
  have haR : IsAdditive (ev Q (fst A C ≫ q) (snd A C)) := by
    refine (isAdditive_iff hR).2 fun Y a a' t ↦ ?_
    rw [evc_ev hQl, evc_ev hQl, evc_ev hQl]
    simp only [lift_fst_assoc, lift_snd, MonObj.mul_comp]
    exact (isAdditive_iff hQl).1 hQ.additive Y _ _ t
  obtain ⟨s, hs, -⟩ := hQ.univ B P' hP' haP'
  obtain ⟨r, hr, -⟩ := hD.univ C _ hR haR
  have hsr : s ≫ r = 𝟙 B := by
    refine GlobalTheory.AbDual.IsDual.eq_of_evc hD ?_
    have e1 := evc_of_iso hR hP _ _ hr (fst A B) (snd A B ≫ s)
    have e1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A B) (snd A B ≫ s)
    have e2 := evc_of_iso hP' hQl _ _ hs (fst A B ≫ q) (snd A B)
    have e3 : evc hP' (fst A B ≫ q) (snd A B) = evc hP (fst A B) (snd A B) := by
      rw [← cls_ev hP' _ _ (pull_isLB hP' _), (cls_eq_iff _ hP).2 eP, evc, lift_fst_snd, Over.id_left, pull_id]
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at e1 e1' e2
    rw [Category.comp_id, ← e3, e2, ← e1', e1]
  obtain ⟨c, hc, -⟩ := hQ.univ T M hM haM
  have hcr : c ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ c)
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ c)
    have f2 := evc_of_iso hM hQl _ _ hc (fst A T ≫ q) (snd A T)
    have f3 := (triv_ev_iff hM _ _).1 hT
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1' f2
    rw [← f1, f1', ← f2, f3]))
  have h1r : (1 : T ⟶ C) ≫ r = 1 := hD.eq_one _ ((triv_ev_iff hP _ _).2 (by
    have f1 := evc_of_iso hR hP _ _ hr (fst A T) (snd A T ≫ (1 : T ⟶ C))
    have f1' := evc_ev hQl (fst A C ≫ q) (snd A C) hR (fst A T) (snd A T ≫ (1 : T ⟶ C))
    simp only [lift_fst, lift_snd_assoc, lift_fst_assoc, lift_snd, Category.assoc] at f1 f1'
    rw [← f1, f1', MonObj.comp_one, evc_one_right hQl hQ.zero]))
  haveI : IsSplitMono s := IsSplitMono.mk' ⟨r, hsr⟩
  haveI : IsIso s := isIso_of_mono' hB hC hgB hgC s
  have hrinv : r = inv s := (IsIso.inv_eq_of_hom_inv_id hsr).symm
  haveI : IsIso r := by rw [hrinv]; infer_instance
  have hc1 : c = 1 := (cancel_mono r).1 (hcr.trans h1r.symm)
  refine (cls_eq_zero_iff hM).1 ?_
  rw [(cls_eq_iff hM (pull_isLB hQl _)).2 hc, cls_ev hQl, hc1, MonObj.comp_one, evc_one_right hQl hQ.zero]
end GlobalTheory.DualInjPull
