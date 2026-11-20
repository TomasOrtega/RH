import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDisc
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveRegularPoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Introduce `n J M w _ hdim hw`. Establish `hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ)`. Rewrite using `[M.ringKrullDim_eq, hdim]`. Take `⟨A, O, V, g, hO, -, hwV, hg, hAg, hZV⟩` from `hreg (Fin n ⊕ Fin M.m) M.ideal w M.isPrime M.isIntegrallyClosed hdim' hw`. Establish `hwg : w ∈ g '' O` using `hZV ▸ ⟨hw, hwV⟩`.

Take `⟨y₀, hy₀, hgy₀⟩` from `hwg`. Take `⟨r, hr, hball⟩` from `Metric.isOpen_iff.mp hO y₀ hy₀`. Establish `hmem : ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) r, y₀ + τ ∈ O` using `fun τ hτ ↦ hball (by`. Rewrite using `[Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]`. Simplify using `using hτ)`.

Use `⟨r, hr, fun τ ↦ g (y₀ + τ), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ hτ`. Conclude with `((hg _ (hmem τ hτ)).differentiableAt.comp τ (differentiableAt_const y₀ |>.add differentiableAt_id)).differentiableWithinAt`. Introduce `s hs t ht hst`. Establish `h` using `congrArg A hst`.

Simplify using `only at h`. Rewrite `h` using `[hAg _ (hmem s hs), hAg _ (hmem t ht)]`. Conclude with `add_left_cancel h`. Introduce `τ hτ`. Establish `h : g (y₀ + τ) ∈ g '' O` using `⟨_, hmem τ hτ, rfl⟩`.

Rewrite `h` using `[← hZV]`. Conclude with `h.1`. Simplify using `[hgy₀]`.
-/
theorem NormalModelDisc.proof (hreg : NormalCurveRegularPoint.Statement) : NormalModelDisc.Statement := by
  intro n J M w _ hdim hw
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  obtain ⟨A, O, V, g, hO, -, hwV, hg, hAg, hZV⟩ :=
    hreg (Fin n ⊕ Fin M.m) M.ideal w M.isPrime M.isIntegrallyClosed hdim' hw
  have hwg : w ∈ g '' O := hZV ▸ ⟨hw, hwV⟩
  obtain ⟨y₀, hy₀, hgy₀⟩ := hwg
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y₀ hy₀
  have hmem : ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) r, y₀ + τ ∈ O := fun τ hτ ↦ hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    simpa using hτ)
  refine ⟨r, hr, fun τ ↦ g (y₀ + τ), ?_, ?_, ?_, ?_⟩
  · intro τ hτ
    exact ((hg _ (hmem τ hτ)).differentiableAt.comp τ
      (differentiableAt_const y₀ |>.add differentiableAt_id)).differentiableWithinAt
  · intro s hs t ht hst
    have h := congrArg A hst
    simp only at h
    rw [hAg _ (hmem s hs), hAg _ (hmem t ht)] at h
    exact add_left_cancel h
  · intro τ hτ
    have h : g (y₀ + τ) ∈ g '' O := ⟨_, hmem τ hτ, rfl⟩
    rw [← hZV] at h
    exact h.1
  · simp [hgy₀]

end GroundTheory.Heights₂.Heights
