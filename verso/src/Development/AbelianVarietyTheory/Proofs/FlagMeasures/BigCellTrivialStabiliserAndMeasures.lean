import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPtRepTrDat
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CellDataExists
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

/- English proof (translation)
Introduce `k r L μG hk hκt hκ hc hG c μ hca hμ`. Establish `hg : bigCell k r c μ ∈ UH (Hpk k r)` using `Formalism.QuantumDeterminants.bigCellMem k r c μ hca hμ`. Establish `hinv : (bigCell k r c μ)⁻¹ * bigCell k r c μ = 1` using `Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg)`. Establish `hR` using `GlobalTheory.AmpNorm.rStab_bigCell c μ hca hg`. Use `set g := bigCell k r c μ`.

Establish `h1 : (Matrix.of fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) = 1` using `rfl`. Use `⟨hg, ?_, ⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Rewrite `ha` using `[hR, Set.mem_singleton_iff]`. Rewrite using `[ha, mul_one, hinv]`.

Unfold `psi`. Rewrite using `[Model.ell_one k r L.z L.hz.1, Model.ell_one k r L.z' L.hz'.1]`. Conclude with `IsProbabilityMeasure.ne_zero _`. Rewrite using `[Measure.dirac_apply]`. Establish `: (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) ∉ {x : Mt k r | Matrix.of x ∉ RStab k r g}`.

Introduce `h`. Apply `h` to reduce the goal to its premises. Rewrite using `[h1, hR]`. Both sides reduce to the same expression. Simplify using `[Set.indicator_of_notMem this]`.

Introduce `s hs`. Rewrite `hs` using `[hR, Set.mem_singleton_iff]`. Substitute `hs` using the available equality. Establish `: (lmulM (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Mt k r → Mt k r) = id`. Use function extensionality and compare the values at `x`.

Simplify using `[lmulM]`. Both sides reduce to the same expression. Rewrite using `[this, Measure.map_id]`. Introduce `f hf`. Establish `e : ∀ x : PairSp k r, (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂(Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j))) = f x`.

Introduce `x`. Rewrite using `[lintegral_dirac, h1]`. Establish `: stabAct g 1 x = x`. Unfold `stabAct`. Rewrite using `[mul_one, hinv]`.

Simplify using `only [one_mul]`. Both sides reduce to the same expression. Rewrite using `[this]`. Repeatedly rewrite using `[e]`. Introduce `f hf`.

Rewrite using `[Measure.map_dirac, h1, mul_one, hinv]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_dirac, h1, one_mul]`. Both sides reduce to the same expression.
-/
theorem bigCell_data : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ Formalism.MainNotions.S.IsRelStab L (Formalism.QuantumDeterminants.bigCell k r c μ) ∧ IsHaarOn (Formalism.MainNotions.S.RStab k r (Formalism.QuantumDeterminants.bigCell k r c μ)) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) ∧ Formalism.MainNotions.S.IsOrbQuot L (Formalism.QuantumDeterminants.bigCell k r c μ) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) (Formalism.MainNotions.S.pairMeas L) ∧ PI.BesselPeriodGGP.IsQuotMeas μG ((MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)).map (fun x => fun i j => ((Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ * Matrix.of x * Formalism.QuantumDeterminants.bigCell k r c μ) i j)) μG := by
  intro k r L μG hk hκt hκ hc hG c μ hca hμ
  have hg : bigCell k r c μ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.bigCellMem k r c μ hca hμ
  have hinv : (bigCell k r c μ)⁻¹ * bigCell k r c μ = 1 :=
    Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg)
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ hca hg
  set g := bigCell k r c μ
  have h1 : (Matrix.of fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) = 1 := rfl
  refine ⟨hg, ?_, ⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    rw [ha, mul_one, hinv]
    unfold psi
    rw [Model.ell_one k r L.z L.hz.1, Model.ell_one k r L.z' L.hz'.1]
  · exact IsProbabilityMeasure.ne_zero _
  · rw [Measure.dirac_apply]
    have : (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) ∉
        {x : Mt k r | Matrix.of x ∉ RStab k r g} := by
      intro h
      apply h
      rw [h1, hR]; rfl
    simp [Set.indicator_of_notMem this]
  · intro s hs
    rw [hR, Set.mem_singleton_iff] at hs
    subst hs
    have : (lmulM (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Mt k r → Mt k r) = id := by
      funext x; simp [lmulM]; rfl
    rw [this, Measure.map_id]
  · intro f hf
    have e : ∀ x : PairSp k r,
        (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂(Measure.dirac
          (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j))) = f x := by
      intro x
      rw [lintegral_dirac, h1]
      have : stabAct g 1 x = x := by
        unfold stabAct
        rw [mul_one, hinv]
        simp only [one_mul]
        rfl
      rw [this]
    simp_rw [e]
  · intro f hf
    rw [Measure.map_dirac, h1, mul_one, hinv]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, h1, one_mul]
    rfl

end GlobalTheory.AmpTK
