import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.OrthonormalPlaceBasis
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

/- English proof (translation)
Unfold `rkR`. Rewrite using `[le_min_iff]`. Prove the components needed by the constructor for the conclusion. Use `Finset.card_pos.2 ?_` and prove the remaining obligations. Consider the cases of `ha : ε a`.

Conclude with `⟨c, by simpa [ha] using h⟩`. Conclude with `⟨a, by simp [ha]⟩`. Use `Finset.card_pos.2 ?_` and prove the remaining obligations. Consider the cases of `ha : ε a`. Conclude with `⟨a, by simp [ha]⟩`.

Conclude with `⟨c, by simpa [ha] using h⟩`.
-/
theorem one_le_rkR_of_ne {n : ℕ} (ε : Fin n → Bool) {a c : Fin n} (h : ε a ≠ ε c) : 1 ≤ rkR ε := by
  unfold rkR
  rw [le_min_iff]
  constructor
  · refine Finset.card_pos.2 ?_
    cases ha : ε a
    · exact ⟨c, by simpa [ha] using h⟩
    · exact ⟨a, by simp [ha]⟩
  · refine Finset.card_pos.2 ?_
    cases ha : ε a
    · exact ⟨a, by simp [ha]⟩
    · exact ⟨c, by simpa [ha] using h⟩

/- English proof (translation)
Introduce `B Cg n₀ d p q b hn₀ hC v`. Take `⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, h8, -, -⟩` from `countHyp_numerics B Cg n₀ d p q b hn₀ hC`. Use `GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hC.1 v).1 (hC.1 v).2.1 fun a c hac => ?_` and prove the remaining obligations. Establish `hq : (1 : ℝ) ≤ q`. Use `one_le_rkR_of_ne _ hac` as an intermediate fact.

Rewrite `this` using `[hrk v]`. Conclude with `this` after adjusting the coercions. Establish `hg : h ≤ |B.lam v a - B.lam v c|` using `hgap v a c hac`. Establish `hn : (0 : ℝ) ≤ B.I.n` using `Nat.cast_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem countHyp_isKTypeOf_lowKSub : ∀ (B : RowsAut) (Cg : ℝ) (n₀ : ℕ) (d : InfinitePlace B.I.F → ℝ) (p q : ℕ) (b : ℝ), 8 ≤ n₀ → CountHyp B Cg n₀ d p q b → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) := by
  intro B Cg n₀ d p q b hn₀ hC v
  obtain ⟨-, -, -, -, -, -, hrk, -, -, -, -, -, h, -, hgap, -, -, h8, -, -⟩ :=
    countHyp_numerics B Cg n₀ d p q b hn₀ hC
  refine GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub _ _ _ _ _ (hC.1 v).1 (hC.1 v).2.1 fun a c hac => ?_
  have hq : (1 : ℝ) ≤ q := by
    have := one_le_rkR_of_ne _ hac
    rw [hrk v] at this
    exact_mod_cast this
  have hg : h ≤ |B.lam v a - B.lam v c| := hgap v a c hac
  have hn : (0 : ℝ) ≤ B.I.n := Nat.cast_nonneg _
  nlinarith

end GlobalTheory.Dec
