import Formalism.LocalToGlobal.CharacterGerms.CoeffFirstPairingLinear

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
Introduce `C _ V σ f hf μ`. Establish `hl : 0 < V.l` using `V.l_prime.pos`. Establish `h` using `PhPowP.frobPowMv f hf (V.l • μ)`. Establish `hdiv : ∀ t, V.l ∣ (V.l • μ) t` using `fun t => by simp [Finsupp.smul_apply]`. Establish `hdl : PhPowP.divL V.l (V.l • μ) = μ`.

Use extensionality with `t`. Rewrite using `[PhPowP.divL_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]`. Rewrite `h` using `[if_pos hdiv, hdl]`. Conclude with `h`.
-/
theorem frobPow_smul : ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f →
    ∀ μ : σ →₀ ℕ, V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l) := by
  intro C _ V σ f hf μ
  have hl : 0 < V.l := V.l_prime.pos
  have h := PhPowP.frobPowMv f hf (V.l • μ)
  have hdiv : ∀ t, V.l ∣ (V.l • μ) t := fun t => by simp [Finsupp.smul_apply]
  have hdl : PhPowP.divL V.l (V.l • μ) = μ := by
    ext t
    rw [PhPowP.divL_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]
  rw [if_pos hdiv, hdl] at h
  exact h

end Formalism.L2.FormalSeriesBounds
