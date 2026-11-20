import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.SerMap

/- English proof (translation)
Set `_ : Invertible c` to `invertibleOfNonzero hc`. Proceed by induction on `n with`. Consider the case `zero`. Use extensionality with `x m`. Simplify using `[iteratedFDeriv_zero_apply]`.

Consider the case `succ n ih`. Rewrite using `[iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Rewrite using `[fderiv_const_smul_of_invertible c, map_smul]`.

Both sides reduce to the same expression.
-/
theorem iteratedFDeriv_smul_of_ne {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (c : ℂ) (hc : c ≠ 0) (f : E → F) (n : ℕ) :
    iteratedFDeriv ℂ n (fun y => c • f y) = c • iteratedFDeriv ℂ n f := by
  let _ : Invertible c := invertibleOfNonzero hc
  induction n with
  | zero =>
    ext x m
    simp [iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [iteratedFDeriv_succ_eq_comp_left, iteratedFDeriv_succ_eq_comp_left, ih]
    funext x
    simp only [Function.comp_apply]
    rw [fderiv_const_smul_of_invertible c, map_smul]
    rfl

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Substitute `hc` using the available equality. Simplify using `only [zero_mul]`. Unfold `TaylorLogMetric.taylor`. Simplify using the standard rewrite rules.

Unfold `TaylorLogMetric.taylor`. Establish `h` using `iteratedFDeriv_smul_of_ne c hc G (Multiset.card α.toMultiset)`. Simplify using `only [smul_eq_mul] at h`. Rewrite using `[h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]`.
-/
theorem taylor_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (α : TaylorLogMetric.Mono D N N') :
    TaylorLogMetric.taylor D (fun z => c * G z) α = c * TaylorLogMetric.taylor D G α := by
  by_cases hc : c = 0
  · subst hc
    simp only [zero_mul]
    unfold TaylorLogMetric.taylor
    simp
  · unfold TaylorLogMetric.taylor
    have h := iteratedFDeriv_smul_of_ne c hc G (Multiset.card α.toMultiset)
    simp only [smul_eq_mul] at h
    rw [h, Pi.smul_apply, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

/- English proof (translation)
Introduce `D p _ lam ι hι a b K G s s' hs hK hKG`. Use extensionality with `α`. Establish `hKt : TaylorLogMetric.taylor D K α = s' * TaylorLogMetric.taylor D G α`. Establish `: K = fun z => s' * G z` using `funext hKG`. Rewrite using `[this, taylor_mul]`.

Establish `hmem : s * TaylorLogMetric.taylor D K α ∈ TaylorLogMetric.Qbar` using `TaylorLogMetric.Qbar.mul_mem hs (hK α)`. Use `show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * K z) α) = _`. Rewrite using `[taylor_mul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]`. Unfold `TaylorLogMetric.lamC`. Rewrite using `[dif_pos hmem, ← hι ⟨_, hmem⟩]`.

Use `show ι (s * TaylorLogMetric.taylor D K α) = _`. Rewrite using `[hKt, ← mul_assoc, map_mul]`. Both sides reduce to the same expression.
-/
theorem padicSeries_const_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]),
    (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ {a b : ℕ} (K G : TaylorLogMetric.VC D a b → ℂ) (s s' : ℂ), s ∈ TaylorLogMetric.Qbar →
    TaylorLogMetric.CoefIn D K TaylorLogMetric.Qbar → (∀ z, K z = s' * G z) →
    serP lam (fun z => s * K z) = ι (s * s') • MvPowerSeries.map ι (tay G) := by
  intro D p _ lam ι hι a b K G s s' hs hK hKG
  ext α
  have hKt : TaylorLogMetric.taylor D K α = s' * TaylorLogMetric.taylor D G α := by
    have : K = fun z => s' * G z := funext hKG
    rw [this, taylor_mul]
  have hmem : s * TaylorLogMetric.taylor D K α ∈ TaylorLogMetric.Qbar := TaylorLogMetric.Qbar.mul_mem hs (hK α)
  show TaylorLogMetric.lamC lam (TaylorLogMetric.taylor D (fun z => s * K z) α) = _
  rw [taylor_mul, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  unfold TaylorLogMetric.lamC
  rw [dif_pos hmem, ← hι ⟨_, hmem⟩]
  show ι (s * TaylorLogMetric.taylor D K α) = _
  rw [hKt, ← mul_assoc, map_mul]
  rfl

end GlobalTheory.TwV.SerMap
