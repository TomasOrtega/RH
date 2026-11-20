import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReductionClosedSubschemeIffIdealEqStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

/- English proof (translation)
Introduce `R _ I W f t ht`. Establish `hci : ∀ e, IsClosedImmersion (thick R I e)` using `fun e => IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) Ideal.Quotient.mk_surjective`. Establish `hmono : ∀ e, Mono (thick R I e)` using `fun e => by haveI := hci e; infer_instance`. Establish `hfst : ∀ e, (pullback.fst f (thick R I e)).ker = baseIdeal f (I ^ (e + 1))`. Introduce `e`.

Use `haveI := hci e`. Establish `h` using `(GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W W (pullback f (thick R I e)) f (𝟙 W) (pullback.fst f (thick R I e)) (pullback.snd f (thick R I e)) inferInstance inferInstance pullback.condition).1 ⟨pullback.fst f (thick R I e), Category.comp_id _, by`. Simplify using `using IsPullback.of_hasPullback f (thick R I e)⟩`. Simplify using `using h.symm`. Establish `hle : ∀ e, (pullback.fst f (thick R I e)).ker ≤ (t e).subschemeι.ker` using `fun e => by`.

Rewrite using `[hfst, Scheme.IdealSheafData.ker_subschemeι]`. Conclude with `ht.baseIdeal_le e`. Set `q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))` to `fun e => haveI := hci e IsClosedImmersion.lift (pullback.fst f (thick R I e)) (t e).subschemeι (hle e) ≫ pullback.snd _ _`. Establish `hq : ∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e` using `fun e => by haveI := hci e`. Simplify using `only [q, Category.assoc, ← pullback.condition]`.

Rewrite using `[← Category.assoc, IsClosedImmersion.lift_fac]`. Use `clear_value q`. Establish `hb : ∀ e, ∃ b : (t e).subscheme ⟶ (t (e + 1)).subscheme, b ≫ (t (e + 1)).subschemeι = (t e).subschemeι ∧ IsPullback b (q e) ((t (e + 1)).subschemeι ≫ f) (thick R I e)` using `fun e => (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W _ _ f (t (e + 1)).subschemeι (t e).subschemeι (q e) inferInstance inferInstance (hq e)).2 (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]; exact (ht e).symm)`. Use `choose β hβ using hb`. Use `⟨q, β, hq, fun e => (hβ e).1, fun e => ?_⟩` and prove the remaining obligations.

Establish `hbot : IsPullback (thickTrans R I e) (𝟙 _) (thick R I (e + 1)) (thick R I e)` using `by haveI := hmono (e + 1)`. Use `IsPullback.of_isLimit' ⟨by simp [thickTrans_comp]⟩ ?_` and prove the remaining obligations. Use `PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp) (fun s m _ h2 => by simpa using h2)` and prove the remaining obligations. Rewrite using `[← cancel_mono (thick R I (e + 1)), Category.assoc, thickTrans_comp]`. Conclude with `s.condition.symm`.

Establish `hcomm : β e ≫ q (e + 1) = q e ≫ thickTrans R I e` using `by haveI := hmono (e + 1)`. Rewrite using `[← cancel_mono (thick R I (e + 1))]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Category.assoc, hq]`. Use `_ = (t e).subschemeι ≫ f := by rw [← Category.assoc, (hβ e).1]`.

Use `_ = q e ≫ thick R I e := hq e`. Use `_ = (q e ≫ thickTrans R I e) ≫ thick R I (e + 1) := by rw [Category.assoc, thickTrans_comp]`. Use `IsPullback.of_bot ?_ hcomm hbot` and prove the remaining obligations. Rewrite using `[Category.comp_id, ← hq]`. Conclude with `(hβ e).2`.
-/
theorem isSystem_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R))
    (t : ℕ → W.IdealSheafData), IsSystem f I t →
    ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme),
      (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧
      (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧
      ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  intro R _ I W f t ht
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))
      Ideal.Quotient.mk_surjective
  have hmono : ∀ e, Mono (thick R I e) := fun e => by haveI := hci e; infer_instance
  have hfst : ∀ e, (pullback.fst f (thick R I e)).ker = baseIdeal f (I ^ (e + 1)) := by
    intro e
    haveI := hci e
    have h := (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W W (pullback f (thick R I e)) f (𝟙 W)
      (pullback.fst f (thick R I e)) (pullback.snd f (thick R I e)) inferInstance inferInstance
      pullback.condition).1
      ⟨pullback.fst f (thick R I e), Category.comp_id _, by
        simpa using IsPullback.of_hasPullback f (thick R I e)⟩
    simpa using h.symm
  have hle : ∀ e, (pullback.fst f (thick R I e)).ker ≤ (t e).subschemeι.ker := fun e => by
    rw [hfst, Scheme.IdealSheafData.ker_subschemeι]
    exact ht.baseIdeal_le e
  let q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) := fun e =>
    haveI := hci e
    IsClosedImmersion.lift (pullback.fst f (thick R I e)) (t e).subschemeι (hle e) ≫ pullback.snd _ _
  have hq : ∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e := fun e => by
    haveI := hci e
    simp only [q, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
  clear_value q
  have hb : ∀ e, ∃ b : (t e).subscheme ⟶ (t (e + 1)).subscheme, b ≫ (t (e + 1)).subschemeι = (t e).subschemeι ∧
      IsPullback b (q e) ((t (e + 1)).subschemeι ≫ f) (thick R I e) := fun e =>
    (GlobalTheory.T.isReduction_closedSubscheme_iff_ideal_eq R (I ^ (e + 1)) W _ _ f (t (e + 1)).subschemeι (t e).subschemeι (q e)
      inferInstance inferInstance (hq e)).2
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]; exact (ht e).symm)
  choose β hβ using hb
  refine ⟨q, β, hq, fun e => (hβ e).1, fun e => ?_⟩
  have hbot : IsPullback (thickTrans R I e) (𝟙 _) (thick R I (e + 1)) (thick R I e) := by
    haveI := hmono (e + 1)
    refine IsPullback.of_isLimit' ⟨by simp [thickTrans_comp]⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp)
      (fun s m _ h2 => by simpa using h2)
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, thickTrans_comp]
    exact s.condition.symm
  have hcomm : β e ≫ q (e + 1) = q e ≫ thickTrans R I e := by
    haveI := hmono (e + 1)
    rw [← cancel_mono (thick R I (e + 1))]
    calc (β e ≫ q (e + 1)) ≫ thick R I (e + 1) = β e ≫ (t (e + 1)).subschemeι ≫ f := by
          rw [Category.assoc, hq]
      _ = (t e).subschemeι ≫ f := by rw [← Category.assoc, (hβ e).1]
      _ = q e ≫ thick R I e := hq e
      _ = (q e ≫ thickTrans R I e) ≫ thick R I (e + 1) := by rw [Category.assoc, thickTrans_comp]
  refine IsPullback.of_bot ?_ hcomm hbot
  rw [Category.comp_id, ← hq]
  exact (hβ e).2

end GlobalTheory.FormalAlg
