import Formalism.UnipotentAdelicQuotients.StdAdditiveCharExists
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.StdCharTR

open NumberField

namespace PI.Bridge

/- English proof (translation)
Establish `h` using `stdCharTR`. Unfold `PI.StdCharTR.Target at h`. Unfold `HeckeCharacterZeroLocus.StdAdditiveCharExists`. Introduce `F _ _ hF`. Take `⟨ψ, hψ, hinf⟩` from `h F hF`.

Unfold `Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF at hψ`. Take `⟨hc, hn, hk, x₀, hx₀⟩` from `hψ`. Use `⟨ψ.compAddMonoidHom (-(AddMonoidHom.id _)), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Continuous (fun x => ψ (-x))`. Conclude with `hc.comp continuous_neg`.

Introduce `x`. Express the relevant statement in the definitionally equal form `‖ψ (-x)‖ = 1`. Conclude with `hn _`. Introduce `a`. Express the relevant statement in the definitionally equal form `ψ (-(algebraMap F _ a)) = 1`.

Rewrite using `[← map_neg]`. Conclude with `hk (-a)`. Use `⟨-x₀, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (- -x₀) ≠ 1`. Rewrite using `[neg_neg]`.

Conclude with `hx₀`. Introduce `x`. Express the relevant statement in the definitionally equal form `ψ (-_) = _`. Rewrite using `[AddChar.map_neg_eq_inv, Complex.exp_neg, ← hinf x]`. Both sides reduce to the same expression.
-/
theorem bridge_stdAddChar : HeckeCharacterZeroLocus.StdAdditiveCharExists := by
  have h := stdCharTR
  unfold PI.StdCharTR.Target at h
  unfold HeckeCharacterZeroLocus.StdAdditiveCharExists
  intro F _ _ hF
  obtain ⟨ψ, hψ, hinf⟩ := h F hF
  unfold Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF at hψ
  obtain ⟨hc, hn, hk, x₀, hx₀⟩ := hψ

  refine ⟨ψ.compAddMonoidHom (-(AddMonoidHom.id _)), ?_, ?_, ?_, ?_, ?_⟩
  · change Continuous (fun x => ψ (-x))
    exact hc.comp continuous_neg
  · intro x
    change ‖ψ (-x)‖ = 1
    exact hn _
  · intro a
    change ψ (-(algebraMap F _ a)) = 1
    rw [← map_neg]
    exact hk (-a)
  · refine ⟨-x₀, ?_⟩
    change ψ (- -x₀) ≠ 1
    rw [neg_neg]
    exact hx₀
  · intro x
    change ψ (-_) = _
    rw [AddChar.map_neg_eq_inv, Complex.exp_neg, ← hinf x]
    rfl

end PI.Bridge
