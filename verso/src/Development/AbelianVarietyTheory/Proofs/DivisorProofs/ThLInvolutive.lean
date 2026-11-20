import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLevelFamilyIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.TwistInvol

/- English proof (translation)
Unfold `cj`. Use `split_ifs with h`. Take `⟨hc, he⟩` from `h.choose_spec`. Establish `hd : DenseRange (algebraMap E (w.adicCompletion E))` using `HeightOneSpectrum.denseRange_algebraMap E w`. Use `hd.induction_on (p := fun x => h.choose (h.choose x) = x) x (isClosed_eq (hc.comp hc) continuous_id) fun y => ?_` and prove the remaining obligations.

Rewrite using `[he, he, IsCMField.complexConj_apply_apply]`. Both sides reduce to the same expression.
-/
theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (x : w.adicCompletion E) :
    cj w (cj w x) = x := by
  unfold cj
  split_ifs with h
  · obtain ⟨hc, he⟩ := h.choose_spec
    have hd : DenseRange (algebraMap E (w.adicCompletion E)) := HeightOneSpectrum.denseRange_algebraMap E w
    refine hd.induction_on (p := fun x => h.choose (h.choose x) = x) x
      (isClosed_eq (hc.comp hc) continuous_id) fun y => ?_
    rw [he, he, IsCMField.complexConj_apply_apply]
  · rfl

/- English proof (translation)
Introduce `E _ _ _ n w g`. Unfold `thL`. Use `split_ifs`. Both sides reduce to the same expression. Conclude with `GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj w) g`.
-/
theorem thL_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    thL n w (thL n w g) = g := by
  intro E _ _ _ n w g
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj w) g

end GlobalTheory.BCT.TwistInvol
