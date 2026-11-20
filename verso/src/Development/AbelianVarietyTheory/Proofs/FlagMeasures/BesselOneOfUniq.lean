import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsPeriodMapDet
import Formalism.PeriodIntegrals.BesselMapUniq

open GlobalTheory.Mom

namespace GlobalTheory.BesselMultOne

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA`. Rewrite using `[Finset.mul_sum]`.
-/
theorem psi_eq_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    Formalism.QuantumDeterminants.psi k r z c = PI.BesselMapUniq.psiGen k r z (fun _ => c) := by
  funext g
  unfold Formalism.QuantumDeterminants.psi Formalism.QuantumDeterminants.ell PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA
  rw [Finset.mul_sum]

/- English proof (translation)
Proceed by induction on `w generalizing v with`. Consider the case `nil => rfl`. Consider the case `cons X w ih => simp only [PI.UpqRep.dsigW, Formalism.MainNotions.S.dsigW, ih]`. Both sides reduce to the same expression.
-/
theorem dsigW_eq {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (w : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (v : H) :
    PI.UpqRep.dsigW (k := k) (r := r) σ w v = Formalism.MainNotions.S.dsigW (k := k) (r := r) σ w v := by
  induction w generalizing v with
  | nil => rfl
  | cons X w ih => simp only [PI.UpqRep.dsigW, Formalism.MainNotions.S.dsigW, ih]; rfl

/- English proof (translation)
Take `⟨h1, h2, h3, C, Ws, h4, h5⟩` from `h`. Use `⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [dsigW_eq]`. Conclude with `h5 v hv`.
-/
theorem isBesselMapSm_of {k r : ℕ} {H W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {z : Fin (2 * r + k + 1) → ℂ}
    {ψ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (W →L[ℂ] W)} {B : H → W}
    (h : Formalism.MainNotions.S.IsBesselMapSm (k := k) (r := r) z ψ σ π B) :
    PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  refine ⟨h1, h2, h3, C, Ws, h4, fun v hv => ?_⟩
  simp only [dsigW_eq]
  exact h5 v hv

end GlobalTheory.BesselMultOne
