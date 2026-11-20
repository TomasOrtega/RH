import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

/- English proof (translation)
Introduce `a b n j β s y hj hcard hrho`. Establish `hsum : ∀ i, ∑ l with β l = i, stageS j β s y l = (j i : ℂ) * s i`. Introduce `i`. Establish `hj0 : (j i : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (by have := hj i; omega)`. Establish `h1 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)), stageS j β s y l = s i + Complex.I * ((y l - blockMean j β y i : ℝ) : ℂ)`.

Introduce `l hl`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hl`. Simplify using `[stageS, hl]`. Establish `h2 : ∑ l with β l = i, ((y l - blockMean j β y i : ℝ) : ℂ) = 0`. Rewrite using `[← Complex.ofReal_sum, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, blockMean]`.

Rewrite using `[mul_div_cancel₀ _ hj0, sub_self, Complex.ofReal_zero]`. Rewrite using `[Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const, hcard, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Introduce `x`.

Simplify using `only [pairing, Nat.cast_one, one_mul, Pi.add_apply, Function.comp_apply]`. Rewrite using `[← Finset.sum_fiberwise Finset.univ β]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h3 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)), (stageS j β s y l + rho n (fun _ => 1) l) * (x (β l) : ℂ) = (stageS j β s y l + rho n (fun _ => 1) l) * (x i : ℂ)`. Introduce `l hl`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hl`. Rewrite using `[hl]`. Rewrite using `[Finset.sum_congr rfl h3, ← Finset.sum_mul, Finset.sum_add_distrib, hsum, hrho]`. Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`.

Simplify using `only [pairing, Nat.cast_one, one_mul]`. Rewrite using `[← sub_eq_zero, ← Finset.sum_sub_distrib, ← Finset.sum_fiberwise Finset.univ β]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `h4 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)), stageS j β s y l * (x l : ℂ) - Complex.I * (y l : ℂ) * (x l : ℂ) = (s i - Complex.I * (blockMean j β y i : ℂ)) * (x l : ℂ)`. Introduce `l hl`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hl`. Simplify using `only [stageS, hl]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl h4, ← Finset.mul_sum, ← Complex.ofReal_sum, hx i]`.

Simplify using the standard rewrite rules.
-/
theorem stageS_pairings : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) (β : Fin b → Fin a) (s : Fin a → ℂ) (y : Fin b → ℝ), (∀ i, 1 ≤ j i) → (∀ i, #{l | β l = i} = j i) → (∀ i, ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (stageS j β s y + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) ∧ ∀ x : Fin b → ℝ, (∀ i, ∑ l with β l = i, x l = 0) → pairing (fun _ => 1) (stageS j β s y) x = pairing (fun _ => 1) (fun l => Complex.I * y l) x := by
  intro a b n j β s y hj hcard hrho
  have hsum : ∀ i, ∑ l with β l = i, stageS j β s y l = (j i : ℂ) * s i := by
    intro i
    have hj0 : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
    have h1 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        stageS j β s y l = s i + Complex.I * ((y l - blockMean j β y i : ℝ) : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp [stageS, hl]
    have h2 : ∑ l with β l = i, ((y l - blockMean j β y i : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_sum, Finset.sum_sub_distrib, Finset.sum_const, hcard, nsmul_eq_mul, blockMean]
      rw [mul_div_cancel₀ _ hj0, sub_self, Complex.ofReal_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, ← Finset.mul_sum, h2, Finset.sum_const, hcard,
      nsmul_eq_mul]
    ring
  constructor
  · intro x
    simp only [pairing, Nat.cast_one, one_mul, Pi.add_apply, Function.comp_apply]
    rw [← Finset.sum_fiberwise Finset.univ β]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        (stageS j β s y l + rho n (fun _ => 1) l) * (x (β l) : ℂ)
          = (stageS j β s y l + rho n (fun _ => 1) l) * (x i : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      rw [hl]
    rw [Finset.sum_congr rfl h3, ← Finset.sum_mul, Finset.sum_add_distrib, hsum, hrho]
    ring
  · intro x hx
    simp only [pairing, Nat.cast_one, one_mul]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← Finset.sum_fiberwise Finset.univ β]
    refine Finset.sum_eq_zero fun i _ => ?_
    have h4 : ∀ l ∈ ({l | β l = i} : Finset (Fin b)),
        stageS j β s y l * (x l : ℂ) - Complex.I * (y l : ℂ) * (x l : ℂ)
          = (s i - Complex.I * (blockMean j β y i : ℂ)) * (x l : ℂ) := by
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
      simp only [stageS, hl]
      push_cast
      ring
    rw [Finset.sum_congr rfl h4, ← Finset.mul_sum, ← Complex.ofReal_sum, hx i]
    simp

end GlobalTheory.RealInd.Stages
