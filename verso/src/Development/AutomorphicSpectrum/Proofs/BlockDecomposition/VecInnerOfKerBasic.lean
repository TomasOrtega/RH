import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.E1

/- English proof (translation)
Introduce `hK X ι _ Φ y j k u hΦ`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Rewrite using `[PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hk l] with z hz`. Rewrite using `[hz, RCLike.inner_apply, mul_comm]`. Introduce `hk`.

Rewrite using `[PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hk l] with z hz`.

Establish `h` using `(hK X (Φ j l) (hΦ j l)).2.2.2.2.1 z y`. Rewrite using `[hz, h, RCLike.inner_apply, Complex.conj_conj, mul_comm]`.
-/
theorem vecInner_of_kerBasic : KerBasic → VecInner := by
  intro hK X ι _ Φ y j k u hΦ
  constructor
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    rw [hz, RCLike.inner_apply, mul_comm]
  · intro hk
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hk l] with z hz
    have h := (hK X (Φ j l) (hΦ j l)).2.2.2.2.1 z y
    rw [hz, h, RCLike.inner_apply, Complex.conj_conj, mul_comm]

end GlobalTheory.CompanionTheory.E1

end
