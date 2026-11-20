import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Formalism.LandauZeroFreeBounds.Statement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerronIntegralShiftPrimitiveLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteBox
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TruncatedPerronPsi
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory

namespace GlobalTheory.ExplicitFormula

/- English proof (translation)
Take `⟨C₁, hC₁, h₁⟩` from `GlobalTheory.PerronPsi.truncated_perron_psi`. Take `⟨C₂, hC₂, h₂⟩` from `GlobalTheory.T.perron_integral_shift_primitive_LFunction`. Take `⟨C₃, hC₃, h₃⟩` from `GlobalTheory.ZeroBand.zeros_band`. Use `⟨C₁ + C₂ + C₃, by positivity, fun N _ χ hχ u T hT hTu => ?_⟩` and prove the remaining obligations. Take `⟨T', hT1, hT2, hs⟩` from `h₂ N χ hχ u T hT hTu`.

Take `⟨hfin, hb⟩` from `h₃ N χ hχ u T T' hT hTu hT1 hT2`. Establish `hp` using `h₁ N χ u T' (by linarith) (by linarith) (by linarith)`. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Establish `hN : (1 : ℝ) ≤ N` using `by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)`. Establish `hiff : χ = 1 ↔ N = 1`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : χ.conductor = N` using `hχ`. Rewrite `h1` using `[h, DirichletCharacter.conductor_one]`. Conclude with `h1.symm`.

Introduce `h`. Substitute `h` using the available equality. Conclude with `DirichletCharacter.level_one χ`. Establish `hpsi : psi0 χ u = (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod N)) - (if N = 1 then (u : ℂ) else 0)`. Unfold `psi0`.

Distinguish the cases in `h : N = 1`. Rewrite using `[if_pos h, if_pos (hiff.mpr h)]`. Rewrite using `[if_neg h, if_neg (fun h' => h (hiff.mp h'))]`. Rewrite using `[hpsi]`. Establish `hZ : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖` using `finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity`.

Establish `hu : (2 : ℝ) ≤ u` using `hT.trans hTu`. Establish `hlu : 0 ≤ Real.log u` using `Real.log_nonneg (by linarith)`. Establish `hl1 : Real.log u ≤ Real.log (N * u)` using `Real.log_le_log (by linarith) (by nlinarith)`. Establish `hl2 : Real.log u ≤ Real.log (N * u * T)`. Use `Real.log_le_log (by linarith) ?_` and prove the remaining obligations.

Establish `: u ≤ N * u` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hA : u * Real.log u ^ 2 / T' ≤ u * Real.log (N * u * T) ^ 2 / T`. Establish `: Real.log u ^ 2 ≤ Real.log (N * u * T) ^ 2` using `pow_le_pow_left₀ hlu hl2 2`. Use `gcongr`.

Establish `hA0 : 0 ≤ u * Real.log (N * u * T) ^ 2 / T`. Establish `: 0 ≤ u` using `by linarith`. Establish `: 0 ≤ T` using `by linarith`. Check the signs of the components of the expression. Establish `key : ∀ S P m Z Z' : ℂ, ‖S - m + Z‖ ≤ ‖S - P‖ + ‖P - m + Z'‖ + ‖Z' - Z‖`.

Introduce `S P m Z Z'`. Establish `: S - m + Z = (S - P) + (P - m + Z') - (Z' - Z)` using `by ring`. Rewrite using `[this]`. Conclude with `(norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)`. Use `(key _ _ _ _ _).trans ((add_le_add (add_le_add hp hs) hb).trans ?_)` and prove the remaining obligations.

Generalize the expression as in `(∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢`. Generalize the expression as in `u * Real.log (N * u * T) ^ 2 / T = A at hA hA0 ⊢`. Generalize the expression as in `u * Real.log u ^ 2 / T' = A' at hA ⊢`. Generalize the expression as in `Real.log (N * u) = B at hl1 ⊢`. Generalize the expression as in `Real.log u = B' at hl1 hlu ⊢`.

Establish `e1 : C₁ * (A' + B') ≤ C₁ * (A + B + Z)` using `mul_le_mul_of_nonneg_left (by linarith) hC₁.le`. Establish `e2 : C₃ * A ≤ C₃ * (A + B + Z)` using `mul_le_mul_of_nonneg_left (by linarith) hC₃.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem truncated_explicit_formula : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}.Finite ∧ ‖psi0 χ u + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by
  obtain ⟨C₁, hC₁, h₁⟩ := GlobalTheory.PerronPsi.truncated_perron_psi
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.T.perron_integral_shift_primitive_LFunction
  obtain ⟨C₃, hC₃, h₃⟩ := GlobalTheory.ZeroBand.zeros_band
  refine ⟨C₁ + C₂ + C₃, by positivity, fun N _ χ hχ u T hT hTu => ?_⟩
  obtain ⟨T', hT1, hT2, hs⟩ := h₂ N χ hχ u T hT hTu
  obtain ⟨hfin, hb⟩ := h₃ N χ hχ u T T' hT hTu hT1 hT2
  have hp := h₁ N χ u T' (by linarith) (by linarith) (by linarith)
  refine ⟨hfin, ?_⟩
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hiff : χ = 1 ↔ N = 1 := by
    constructor
    · intro h
      have h1 : χ.conductor = N := hχ
      rw [h, DirichletCharacter.conductor_one] at h1
      exact h1.symm
    · intro h
      subst h
      exact DirichletCharacter.level_one χ
  have hpsi : psi0 χ u = (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (Λ n : ℂ) * χ (n : ZMod N)) -
      (if N = 1 then (u : ℂ) else 0) := by
    unfold psi0
    by_cases h : N = 1
    · rw [if_pos h, if_pos (hiff.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mp h'))]
  rw [hpsi]
  have hZ : 0 ≤ ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖ :=
    finsum_nonneg fun ρ => finsum_nonneg fun _ => by positivity
  have hu : (2 : ℝ) ≤ u := hT.trans hTu
  have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hl1 : Real.log u ≤ Real.log (N * u) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hl2 : Real.log u ≤ Real.log (N * u * T) := by
    refine Real.log_le_log (by linarith) ?_
    have : u ≤ N * u := by nlinarith
    nlinarith
  have hA : u * Real.log u ^ 2 / T' ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have : Real.log u ^ 2 ≤ Real.log (N * u * T) ^ 2 := pow_le_pow_left₀ hlu hl2 2
    gcongr
  have hA0 : 0 ≤ u * Real.log (N * u * T) ^ 2 / T := by
    have : 0 ≤ u := by linarith
    have : 0 ≤ T := by linarith
    positivity
  have key : ∀ S P m Z Z' : ℂ, ‖S - m + Z‖ ≤ ‖S - P‖ + ‖P - m + Z'‖ + ‖Z' - Z‖ := by
    intro S P m Z Z'
    have : S - m + Z = (S - P) + (P - m + Z') - (Z' - Z) := by ring
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  refine (key _ _ _ _ _).trans ((add_le_add (add_le_add hp hs) hb).trans ?_)
  generalize (∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0},
      ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) = Z at hZ ⊢
  generalize u * Real.log (N * u * T) ^ 2 / T = A at hA hA0 ⊢
  generalize u * Real.log u ^ 2 / T' = A' at hA ⊢
  generalize Real.log (N * u) = B at hl1 ⊢
  generalize Real.log u = B' at hl1 hlu ⊢
  have e1 : C₁ * (A' + B') ≤ C₁ * (A + B + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₁.le
  have e2 : C₃ * A ≤ C₃ * (A + B + Z) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₃.le
  nlinarith

end GlobalTheory.ExplicitFormula
