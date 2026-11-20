import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

namespace GlobalTheory.KerT

/- English proof (translation)
Establish `hN : 0 < N` using `a.pos`. Establish `h1 : lam.w a ≤ lam.w ⟨0, hN⟩` using `lam.anti (Fin.le_def.2 (Nat.zero_le _))`. Establish `h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w b` using `lam.anti (Fin.le_def.2 (by have := b.2; simp only; omega))`. Unfold `DomWeight.spread`. Rewrite using `[dif_pos hN]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sub_add_le_spread {N : ℕ} (lam : DomWeight N) (a b : Fin N) :
    lam.w a - lam.w b + (N : ℤ) ≤ lam.spread := by
  have hN : 0 < N := a.pos
  have h1 : lam.w a ≤ lam.w ⟨0, hN⟩ := lam.anti (Fin.le_def.2 (Nat.zero_le _))
  have h2 : lam.w ⟨N - 1, by omega⟩ ≤ lam.w b := lam.anti (Fin.le_def.2 (by have := b.2; simp only; omega))
  unfold DomWeight.spread
  rw [dif_pos hN]
  linarith

/- English proof (translation)
Introduce `Z hZ u j hj τ a b`. Establish `h1` using `hZ.sizes.two_spread_lt u j hj τ`. Establish `h2` using `sub_add_le_spread (Z.W.lamTrue u j τ) a b`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem alcoveAt_of_ok : ∀ (Z : Dat), Z.Ok → ∀ (u : Z.Pr.Word) (j : ℕ), j ≤ Z.R.m → AlcoveAt Z.W u j := by
  intro Z hZ u j hj τ a b
  have h1 := hZ.sizes.two_spread_lt u j hj τ
  have h2 := sub_add_le_spread (Z.W.lamTrue u j τ) a b
  linarith

end GlobalTheory.KerT
