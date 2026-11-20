import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section

namespace GlobalTheory.CobSimeqProof

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (cob)

/- English proof (translation)
Establish `h'` using `(Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.1 f g h`. Unfold `Formalism.InvariantFactorPaths.G7.Simeq at h' ⊢`. Rewrite using `[show -f - -g = g - f by ring]` and apply the resulting hypothesis.
-/
theorem simeq_neg {K ι : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {f g : MvPowerSeries ι K}
    (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : Formalism.InvariantFactorPaths.G7.Simeq (-f) (-g) := by
  have h' := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K ι).2.1 f g h
  unfold Formalism.InvariantFactorPaths.G7.Simeq at h' ⊢
  rwa [show -f - -g = g - f by ring]

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPowerSeries.coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem integral_X {K ι : Type} [NormedField K] (i : ι) : Integral (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Introduce `K _ _ _ F hF0 hFI f f' h`. Establish `R` using `Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit`. Establish `hs : ∀ (φ : Unit → MvPowerSeries (Fin 2) K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) → (∀ i, Integral (φ i)) → Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst φ (f : MvPowerSeries Unit K)) (MvPowerSeries.subst φ (f' : MvPowerSeries Unit K))` using `fun φ h0 hI => R.2.2.2.2 (Fin 2) f f' φ h0 hI h`. Establish `h1` using `hs (fun _ => F) (fun _ => hF0) (fun _ => hFI)`. Establish `h2` using `simeq_neg (hs (fun _ => MvPowerSeries.X 0) (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => integral_X _))`.

Establish `h3` using `simeq_neg (hs (fun _ => MvPowerSeries.X 1) (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => integral_X _))`. Establish `R2` using `Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)`. Establish `H` using `R2.2.2.2.1 _ _ _ _ (R2.2.2.2.1 _ _ _ _ h1 h2) h3`. Establish `e : ∀ q : PowerSeries K, cob F q = MvPowerSeries.subst (fun _ => F) (q : MvPowerSeries Unit K) + -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) + -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) …`. Introduce `q`.

Unfold `cob Formalism.InvariantFactorPaths.G7.at1 PowerSeries.subst`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e f, e f']`. Conclude with `H`.
-/
theorem cobSimeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  intro K _ _ _ F hF0 hFI f f' h
  have R := Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit
  have hs : ∀ (φ : Unit → MvPowerSeries (Fin 2) K), (∀ i, MvPowerSeries.constantCoeff (φ i) = 0) →
      (∀ i, Integral (φ i)) →
      Formalism.InvariantFactorPaths.G7.Simeq (MvPowerSeries.subst φ (f : MvPowerSeries Unit K))
        (MvPowerSeries.subst φ (f' : MvPowerSeries Unit K)) :=
    fun φ h0 hI => R.2.2.2.2 (Fin 2) f f' φ h0 hI h
  have h1 := hs (fun _ => F) (fun _ => hF0) (fun _ => hFI)
  have h2 := simeq_neg (hs (fun _ => MvPowerSeries.X 0) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have h3 := simeq_neg (hs (fun _ => MvPowerSeries.X 1) (fun _ => MvPowerSeries.constantCoeff_X _)
    (fun _ => integral_X _))
  have R2 := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)
  have H := R2.2.2.2.1 _ _ _ _ (R2.2.2.2.1 _ _ _ _ h1 h2) h3
  have e : ∀ q : PowerSeries K, cob F q = MvPowerSeries.subst (fun _ => F) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) +
      -MvPowerSeries.subst (fun _ => (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) (q : MvPowerSeries Unit K) := by
    intro q
    unfold cob Formalism.InvariantFactorPaths.G7.at1 PowerSeries.subst
    ring
  rw [e f, e f']
  exact H

end GlobalTheory.CobSimeqProof
