import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.MollId

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.WR.D.Moll

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D

variable {n : ℕ} {X : Type} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Establish `hm : Measurable (fun p : E n × X => kr ε t (qq p.2 - p.1))` using `(continuous_kr ε t hε).measurable.comp ((hqq.comp measurable_snd).sub measurable_fst)`. Establish `hs : AEStronglyMeasurable (fun p : E n × X => Ψ p.2) ((volume : Measure (E n)).prod μ)` using `hΨ.aestronglyMeasurable.comp_snd`. Establish `hψm : AEStronglyMeasurable (fun p : E n × X => ψ p.1) ((volume : Measure (E n)).prod μ)` using `(hψc.measurable.comp measurable_fst).aestronglyMeasurable`. Establish `hint : Integrable (fun p : E n × X => ψ p.1 * (C * (Ψ p.2 * kr ε t (qq p.2 - p.1)))) ((volume : Measure (E n)).prod μ)`. Use `Integrable.mono' ((hψi.norm.mul_prod hΨ.norm).mul_const (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)) (hψm.mul (aestronglyMeasurable_const.mul (hs.mul hm.aestronglyMeasurable))) ?_` and prove the remaining obligations.

Use `Eventually.of_forall fun p => ?_` and prove the remaining obligations. Take `⟨β, x⟩` from `p`. Use `show ‖ψ β * (C * (Ψ x * kr ε t (qq x - β)))‖ ≤ ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)`. Rewrite using `[norm_mul, norm_mul, norm_mul]`. Establish `hk` using `norm_kr_le ε t hε (qq x - β)`.

Combine the equalities or inequalities in the displayed calculation. Establish `e1 : (fun β : E n => ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ))) = fun β => ∫ x, ψ β * (C * (Ψ x * kr ε t (qq x - β))) ∂μ`. Use function extensionality and compare the values at `β`. Rewrite using `[← integral_const_mul, ← integral_const_mul]`. Establish `e2 : (fun x : X => ∫ β : E n, ψ β * (C * (Ψ x * kr ε t (qq x - β)))) = fun x => Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β)))`.

Use function extensionality and compare the values at `x`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `β`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, integral_integral_swap (f := fun (β : E n) (x : X) => ψ β * (C * (Ψ x * kr ε t (qq x - β)))) hint, e2]`.
-/
theorem step_b (Ψ : X → ℂ) (qq : X → E n) (hΨ : Integrable Ψ μ) (hqq : Measurable qq) (t ε : ℝ) (hε : 0 < ε)
    (ψ : E n → ℂ) (hψc : Continuous ψ) (hψi : Integrable ψ) (C : ℂ) :
    ∫ β, ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ)) =
      ∫ x, Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) ∂μ := by
  have hm : Measurable (fun p : E n × X => kr ε t (qq p.2 - p.1)) :=
    (continuous_kr ε t hε).measurable.comp ((hqq.comp measurable_snd).sub measurable_fst)
  have hs : AEStronglyMeasurable (fun p : E n × X => Ψ p.2) ((volume : Measure (E n)).prod μ) :=
    hΨ.aestronglyMeasurable.comp_snd
  have hψm : AEStronglyMeasurable (fun p : E n × X => ψ p.1) ((volume : Measure (E n)).prod μ) :=
    (hψc.measurable.comp measurable_fst).aestronglyMeasurable
  have hint : Integrable (fun p : E n × X => ψ p.1 * (C * (Ψ p.2 * kr ε t (qq p.2 - p.1))))
      ((volume : Measure (E n)).prod μ) := by
    refine Integrable.mono' ((hψi.norm.mul_prod hΨ.norm).mul_const (‖C‖ * ∫ y, ‖gam (n := n) ε y‖))
      (hψm.mul (aestronglyMeasurable_const.mul (hs.mul hm.aestronglyMeasurable))) ?_
    refine Eventually.of_forall fun p => ?_
    obtain ⟨β, x⟩ := p
    show ‖ψ β * (C * (Ψ x * kr ε t (qq x - β)))‖ ≤ ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖)
    rw [norm_mul, norm_mul, norm_mul]
    have hk := norm_kr_le ε t hε (qq x - β)
    calc ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ‖kr ε t (qq x - β)‖)) ≤
          ‖ψ β‖ * (‖C‖ * (‖Ψ x‖ * ∫ y, ‖gam (n := n) ε y‖)) := by gcongr
      _ = ‖ψ β‖ * ‖Ψ x‖ * (‖C‖ * ∫ y, ‖gam (n := n) ε y‖) := by ring
  have e1 : (fun β : E n => ψ β * (C * (∫ x, Ψ x * kr ε t (qq x - β) ∂μ))) =
      fun β => ∫ x, ψ β * (C * (Ψ x * kr ε t (qq x - β))) ∂μ := by
    funext β
    rw [← integral_const_mul, ← integral_const_mul]
  have e2 : (fun x : X => ∫ β : E n, ψ β * (C * (Ψ x * kr ε t (qq x - β)))) =
      fun x => Ψ x * (∫ β, ψ β * (C * kr ε t (qq x - β))) := by
    funext x
    rw [← integral_const_mul]
    congr 1
    funext β
    ring
  rw [e1, integral_integral_swap (f := fun (β : E n) (x : X) => ψ β * (C * (Ψ x * kr ε t (qq x - β)))) hint, e2]

end PositivityTheory.Rg.Sw.WR.D.Moll
