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

namespace GlobalTheory.RealInd

/- English proof (translation)
Introduce `n a ε j W hW x t ht m hm`. Establish `hmi : m⁻¹ ∈ flagM ε W` using `(GlobalTheory.FlagLeviGroup.leviSub ε W).inv_mem hm`. Establish `hmul : ∀ g h : UJ ε, uMat (g * h) = uMat g * uMat h` using `fun _ _ => rfl`. Establish `hmm : uMat m * uMat m⁻¹ = 1` using `by rw [← hmul, mul_inv_cancel]; rfl`. Establish `hJ : (uMat m)ᴴ * Jm ε = Jm ε * uMat m⁻¹`.

Establish `hg : (uMat m)ᴴ * Jm ε * uMat m = Jm ε` using `m.2`. Combine the equalities or inequalities in the displayed calculation. Establish `hmy : ∀ y, uMat m *ᵥ (uMat m⁻¹ *ᵥ y) = y` using `fun y => by rw [mulVec_mulVec, hmm, one_mulVec]`. Establish `key : ∀ y, uMat (m * t * m⁻¹) *ᵥ y = uMat m *ᵥ (uMat t *ᵥ (uMat m⁻¹ *ᵥ y))` using `fun y => by`. Rewrite using `[hmul, hmul, mulVec_mulVec, mulVec_mulVec]`.

Establish `hs : IsSplit ε W x (m * t * m⁻¹)`. Use `⟨(GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem ((GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem hm ht.1) hmi, fun i y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `ht.2.1 i _ (hmi _ y hy).1`. Establish `h2` using `(hm _ _ h1).1`. Use `h2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[key, mulVec_sub, mulVec_smul, hmy]`. Establish `hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = 0` using `fun z hz => by`. Rewrite using `[mulVec_mulVec, ← hJ, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]`. Conclude with `hy _ (hm _ z hz).1`. Establish `h2` using `(hm _ _ (ht.2.2 _ hy')).1`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[key, mulVec_sub, hmy]`. Use `(existsUnique_isSplit hW x).unique hs ht` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isSplit_commute_flagM : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}, IsIsoFlag ε j W →
    ∀ {x : Fin a → ℝ} {t : UJ ε}, IsSplit ε W x t → ∀ m ∈ flagM ε W, m * t = t * m := by
  intro n a ε j W hW x t ht m hm
  have hmi : m⁻¹ ∈ flagM ε W := (GlobalTheory.FlagLeviGroup.leviSub ε W).inv_mem hm
  have hmul : ∀ g h : UJ ε, uMat (g * h) = uMat g * uMat h := fun _ _ => rfl
  have hmm : uMat m * uMat m⁻¹ = 1 := by rw [← hmul, mul_inv_cancel]; rfl
  have hJ : (uMat m)ᴴ * Jm ε = Jm ε * uMat m⁻¹ := by
    have hg : (uMat m)ᴴ * Jm ε * uMat m = Jm ε := m.2
    calc (uMat m)ᴴ * Jm ε = (uMat m)ᴴ * Jm ε * (uMat m * uMat m⁻¹) := by rw [hmm, Matrix.mul_one]
      _ = Jm ε * uMat m⁻¹ := by rw [← Matrix.mul_assoc, hg]
  have hmy : ∀ y, uMat m *ᵥ (uMat m⁻¹ *ᵥ y) = y := fun y => by rw [mulVec_mulVec, hmm, one_mulVec]
  have key : ∀ y, uMat (m * t * m⁻¹) *ᵥ y = uMat m *ᵥ (uMat t *ᵥ (uMat m⁻¹ *ᵥ y)) := fun y => by
    rw [hmul, hmul, mulVec_mulVec, mulVec_mulVec]
  have hs : IsSplit ε W x (m * t * m⁻¹) := by
    refine ⟨(GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem ((GlobalTheory.FlagLeviGroup.leviSub ε W).mul_mem hm ht.1) hmi,
      fun i y hy => ?_, fun y hy => ?_⟩
    · have h1 := ht.2.1 i _ (hmi _ y hy).1
      have h2 := (hm _ _ h1).1
      convert h2 using 1
      rw [key, mulVec_sub, mulVec_smul, hmy]
    · have hy' : ∀ z ∈ W (Fin.last a), star z ⬝ᵥ (Jm ε *ᵥ (uMat m⁻¹ *ᵥ y)) = 0 := fun z hz => by
        rw [mulVec_mulVec, ← hJ, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]
        exact hy _ (hm _ z hz).1
      have h2 := (hm _ _ (ht.2.2 _ hy')).1
      convert h2 using 1
      rw [key, mulVec_sub, hmy]
  have := (existsUnique_isSplit hW x).unique hs ht
  calc m * t = m * t * m⁻¹ * m := by group
    _ = t * m := by rw [this]

end GlobalTheory.RealInd
