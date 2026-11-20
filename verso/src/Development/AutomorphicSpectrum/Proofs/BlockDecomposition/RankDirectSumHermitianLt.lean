import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hc (Matrix.ext h)`. Establish `hsub : (Matrix.fromBlocks a 0 0 c).submatrix (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j) = Matrix.fromBlocks a 0 0 (Matrix.of fun _ _ : Unit => c i j)`.

Use extensionality with `x y`. Apply the tactic sequence `rcases x with x | x <;> rcases y with y | y <;> rfl`. Establish `hdet : (Matrix.fromBlocks a 0 0 (Matrix.of fun _ _ : Unit => c i j)).det ≠ 0`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁]`. Simplify using `using ⟨ha, hij⟩`.

Establish `hrank` using `Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))`. Establish `hle` using `Matrix.rank_submatrix_le (Matrix.fromBlocks a 0 0 c) (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j)`. Rewrite `hle` using `[hsub, hrank]`. Simplify using `using hle`.
-/
theorem rank_fromBlocks_ge {K : Type*} [Field K] {ρ p : ℕ} (a : Matrix (Fin ρ) (Fin ρ) K)
    (ha : a.det ≠ 0) (c : Matrix (Fin p) (Fin p) K) (hc : c ≠ 0) :
    ρ + 1 ≤ (Matrix.fromBlocks a 0 0 c).rank := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Matrix.ext h)
  have hsub : (Matrix.fromBlocks a 0 0 c).submatrix
      (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j) =
      Matrix.fromBlocks a 0 0 (Matrix.of fun _ _ : Unit => c i j) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> rfl
  have hdet : (Matrix.fromBlocks a 0 0
      (Matrix.of fun _ _ : Unit => c i j)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using ⟨ha, hij⟩
  have hrank := Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hle := Matrix.rank_submatrix_le (Matrix.fromBlocks a 0 0 c)
    (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j)
  rw [hsub, hrank] at hle
  simpa using hle

/- English proof (translation)
Introduce `D n ρ p hn b₀ hb β' hβ`. Establish `h` using `rank_fromBlocks_ge b₀.1 hb β'.1 hβ`. Establish `e : (dsum hn b₀ β').1.rank = (Matrix.fromBlocks b₀.1 0 0 β'.1).rank` using `Matrix.rank_submatrix _ (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem rank_dsum_ge : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  intro D n ρ p hn b₀ hb β' hβ
  have h := rank_fromBlocks_ge b₀.1 hb β'.1 hβ
  have e : (dsum hn b₀ β').1.rank = (Matrix.fromBlocks b₀.1 0 0 β'.1).rank :=
    Matrix.rank_submatrix _ (finSumFinEquiv.trans (finCongr hn)).symm
      (finSumFinEquiv.trans (finCongr hn)).symm
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.PcFc
