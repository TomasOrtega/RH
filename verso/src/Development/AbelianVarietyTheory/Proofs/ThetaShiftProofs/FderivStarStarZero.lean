import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding

noncomputable section

namespace GlobalTheory.ArchConj

section Diff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt.Arch GlobalTheory.IndefiniteRowSideFullHecke.L2SquaredNorms
open GlobalTheory.ArchMetricCompare

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Distinguish the cases in `hF : DifferentiableAt ℂ F 0`. Establish `d` using `hF.hasFDerivAt.star_star`. Rewrite `d` using `[star_zero]`. Rewrite using `[d.fderiv]`. Simplify using the standard rewrite rules.

Establish `hG : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0` using `fun hG => hF (by`. Use `hG.star_star` as an intermediate fact. Establish `e : star ∘ (star ∘ F ∘ star) ∘ star = F` using `funext fun z => by simp`. Rewrite using `[star_zero, e] at this)` and apply the resulting hypothesis. Rewrite using `[fderiv_zero_of_not_differentiableAt hF, fderiv_zero_of_not_differentiableAt hG]`.

Simplify using the standard rewrite rules.
-/
theorem fderiv_star_star_zero {g : ℕ} (F : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) :
    fderiv ℂ (star ∘ F ∘ star) 0 (star w) = star (fderiv ℂ F 0 w) := by
  by_cases hF : DifferentiableAt ℂ F 0
  · have d := hF.hasFDerivAt.star_star
    rw [star_zero] at d
    rw [d.fderiv]
    simp
  · have hG : ¬ DifferentiableAt ℂ (star ∘ F ∘ star) 0 := fun hG => hF (by
      have := hG.star_star
      have e : star ∘ (star ∘ F ∘ star) ∘ star = F := funext fun z => by simp
      rwa [star_zero, e] at this)
    rw [fderiv_zero_of_not_differentiableAt hF, fderiv_zero_of_not_differentiableAt hG]
    simp

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {ψ : A'.left ⟶ A.left} (h : IsGrpPullback A' A cj ψ)
variable {X : Scheme.{0}} {L : LB X} {φ : A.left ⟶ X} {g : ℕ} (u : HolUnif A (L.pull φ) g)

/- English proof (translation)
Use `haveI := isIso_of_cj h`. Introduce `U hU f`. Establish `e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ`. Rewrite using `[← Category.assoc]`. Conclude with `(IsIso.eq_comp_inv ψ).2 e`.

Establish `h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U)` using `fun q _ => by`. Use `subsingleton_dual ℂ` as an intermediate fact. Establish `hq` using `hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)`. Rewrite `hq` using `[e2]`. Rewrite using `[Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q (spMap (dualMap (starRingEnd ℂ)) q)]`.

Conclude with `hq`. Establish `e1 : (fun z => valAt' ((cjUnif h u).ex z).left U f) = star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star`. Use function extensionality and compare the values at `fun z => cj_val h _ U f`. Rewrite using `[e1, fderiv_star_star_zero]`. Establish `k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U), y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ → TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ) (TangentOrigin.evalPt (R` using `DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by`.

Introduce and unpack `_ hy rfl`. Rewrite using `[TangentOrigin.evalPt_spMap_comp _ _ U h2]`. Use `congr 1`. Use `(congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_` and prove the remaining obligations. Establish `e3` using `hd _ h2 (((inv ψ).app U).hom f)`.

Simplify using `only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]`. Conclude with `congrArg (starRingEnd ℂ) e3`.
-/
theorem cj_isDiff' {t : epsR ℂ ⟶ A} {t' : epsR ℂ ⟶ A'}
    (e : t'.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t.left) {w : Fin g → ℂ} (hd : u.IsDiff w t) :
    (cjUnif h u).IsDiff (star w) t' := by
  haveI := isIso_of_cj h
  intro U hU f
  have e2 : t'.left = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv ψ).2 e
  have h2 : ⊤ ≤ t.left ⁻¹ᵁ (inv ψ ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q (spMap (dualMap (starRingEnd ℂ)) q)]
    exact hq
  have e1 : (fun z => valAt' ((cjUnif h u).ex z).left U f) =
      star ∘ (fun z => valAt' (u.ex z).left (inv ψ ⁻¹ᵁ U) (((inv ψ).app U).hom f)) ∘ star :=
    funext fun z => cj_val h _ U f
  rw [e1, fderiv_star_star_zero]
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (dualMap (starRingEnd ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from t.left) ≫ inv ψ →
      TangentOrigin.evalPt y U hy f = dualMap (starRingEnd ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) t.left _ h2 (((inv ψ).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  refine (congrArg TrivSqZeroExt.snd (k _ hU e2)).trans ?_
  have e3 := hd _ h2 (((inv ψ).app U).hom f)
  simp only [dualMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
    TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg (starRingEnd ℂ) e3

/- English proof (translation)
Take `⟨P', φ, w, t', h, hw, e, u, Hm, χ, z, hAH, hd, rfl⟩` from `H`. Establish `hg` using `g_eq h`. Take `⟨A', _, ψ, hc⟩ : ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (ψ : A'.left ⟶ P'.A.left), IsGrpPullback A' P'.A cj ψ` from `⟨_, _, _, isGrpPullback_pullback P'.A cj⟩`. Establish `sq : (spMap (dualMap (starRingEnd ℂ)) ≫ t'.left) ≫ P'.A.hom = (epsR ℂ).hom ≫ cj`. Rewrite using `[Category.assoc, Over.w]`.

Express the relevant statement in the definitionally equal form `Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`. Set `t'' : epsR ℂ ⟶ A'` to `Over.homMk (hc.1.lift _ _ sq) (hc.1.lift_snd _ _ _)`.

Establish `e' : t''.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left` using `hc.1.lift_fst _ _ _`. Establish `h' : IsGrpPullback A' P.A (spMap (ComplexEmbedding.conjugate σ)) (ψ ≫ φ)` using `(hc.comp h).congr (spMap_conjugate σ) rfl`. Establish `e'' : t''.left ≫ ψ ≫ φ = spMap (dualMap (ComplexEmbedding.conjugate σ)) ≫ t.left`. Rewrite using `[← Category.assoc, e', Category.assoc]`. Use `(congrArg _ e).trans ?_` and prove the remaining obligations.

Rewrite using `[← Category.assoc]`. Use `congr 1`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Apply the tactic sequence `ext a <;> simp [dualMap]`.

Establish `hM` using `pull_isLB P.isLB φ`. Establish `hAH'` using `cj_isAH hc (carry u P'.isLB hM hw) (carry_isAH _ _ hw hAH)`. Establish `hd'` using `cj_isDiff' hc (carry u P'.isLB hM hw) e' (w := z) hd`. Establish `hz : (z ⬝ᵥ Hm.mulVec (star z)).re = (star z ⬝ᵥ (Hm.map star).mulVec (star (star z))).re`. Use `hermSq_star Hm (star z)` as an intermediate fact.

Rewrite `this` using `[star_star]`. Conclude with `this.symm`. Take `⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩` from `P`. Take `rfl : P'.g = g` from `hg`. Conclude with `⟨pullPol _ h', ψ ≫ φ, idIso _, t'', h', idIso_isGen (pull_isLB isLB _), e'', cjUnif hc (carry u P'.isLB hM hw), _, _, star z, hAH', hd', by rw [hz]; rfl⟩`.
-/
theorem isLieNormAt_conjugate {K : Type} [Field K] {P : Out.PolAV (Sp K)} {σ : K →+* ℂ} {t : epsR K ⟶ P.A} {v : ℝ}
    (H : IsLieNormAt P t σ v) : IsLieNormAt P t (ComplexEmbedding.conjugate σ) v := by
  obtain ⟨P', φ, w, t', h, hw, e, u, Hm, χ, z, hAH, hd, rfl⟩ := H
  have hg := g_eq h
  obtain ⟨A', _, ψ, hc⟩ : ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (ψ : A'.left ⟶ P'.A.left),
      IsGrpPullback A' P'.A cj ψ := ⟨_, _, _, isGrpPullback_pullback P'.A cj⟩
  have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ t'.left) ≫ P'.A.hom = (epsR ℂ).hom ≫ cj := by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let t'' : epsR ℂ ⟶ A' := Over.homMk (hc.1.lift _ _ sq) (hc.1.lift_snd _ _ _)
  have e' : t''.left ≫ ψ = spMap (dualMap (starRingEnd ℂ)) ≫ t'.left := hc.1.lift_fst _ _ _
  have h' : IsGrpPullback A' P.A (spMap (ComplexEmbedding.conjugate σ)) (ψ ≫ φ) :=
    (hc.comp h).congr (spMap_conjugate σ) rfl
  have e'' : t''.left ≫ ψ ≫ φ = spMap (dualMap (ComplexEmbedding.conjugate σ)) ≫ t.left := by
    rw [← Category.assoc, e', Category.assoc]
    refine (congrArg _ e).trans ?_
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [dualMap]
  have hM := pull_isLB P.isLB φ
  have hAH' := cj_isAH hc (carry u P'.isLB hM hw) (carry_isAH _ _ hw hAH)
  have hd' := cj_isDiff' hc (carry u P'.isLB hM hw) e' (w := z) hd
  have hz : (z ⬝ᵥ Hm.mulVec (star z)).re = (star z ⬝ᵥ (Hm.map star).mulVec (star (star z))).re := by
    have := hermSq_star Hm (star z)
    rw [star_star] at this
    exact this.symm
  obtain ⟨A, isAb, g, sm, L, isLB, rigid, sym, ample, ktriv⟩ := P
  obtain rfl : P'.g = g := hg
  exact ⟨pullPol _ h', ψ ≫ φ, idIso _, t'', h', idIso_isGen (pull_isLB isLB _), e'',
    cjUnif hc (carry u P'.isLB hM hw), _, _, star z, hAH', hd', by rw [hz]; rfl⟩

end Diff

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

/- English proof (translation)
Introduce `_ _ _ P σ v` and use `⟨fun rig th H => (ArchMetricCompare.isL2Sq_iff_isThNormAt P rig _ th v).1 (ArchMetricCompare.isL2Sq_conjugate_embedding ((ArchMetricCompare.isL2Sq_iff_isThNormAt P rig σ th v).2 H)), fun _ H => isLieNormAt_conjugate H⟩`.
-/
theorem norms_conj : Known → ∀ (K : Type) [Field K] (P : Out.PolAV (Sp K)) (σ : K →+* ℂ) (v : ℝ), (∀ (rig : LB.Gen (P.L.pull (eSec P.A))) (th : P.L.Sec), Arch.IsThNormAt P rig th σ v → Arch.IsThNormAt P rig th ((starRingEnd ℂ).comp σ) v) ∧ ∀ η' : epsR K ⟶ P.A, Arch.IsLieNormAt P η' σ v → Arch.IsLieNormAt P η' ((starRingEnd ℂ).comp σ) v :=
  fun _ _ _ P σ v => ⟨fun rig th H => (ArchMetricCompare.isL2Sq_iff_isThNormAt P rig _ th v).1
    (ArchMetricCompare.isL2Sq_conjugate_embedding ((ArchMetricCompare.isL2Sq_iff_isThNormAt P rig σ th v).2 H)),
    fun _ H => isLieNormAt_conjugate H⟩

end GlobalTheory.ArchConj
