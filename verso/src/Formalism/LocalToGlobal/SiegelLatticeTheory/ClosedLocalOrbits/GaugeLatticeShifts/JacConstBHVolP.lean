import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHVolS
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

/- English proof (translation)
Introduce `E _ _ _ _ _ s`. Set `f` to `(stdOrthonormalBasis ℝ E).repr`. Establish `hf : MeasurePreserving f` using `f.measurePreserving`. Establish `e : f ⁻¹' Metric.ball 0 s = Metric.ball 0 s`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]`. Rewrite using `[← e, hf.measure_preimage measurableSet_ball.nullMeasurableSet]`.
-/
theorem ballDim : BallDim := by
  intro E _ _ _ _ _ s
  let f := (stdOrthonormalBasis ℝ E).repr
  have hf : MeasurePreserving f := f.measurePreserving
  have e : f ⁻¹' Metric.ball 0 s = Metric.ball 0 s := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [← e, hf.measure_preimage measurableSet_ball.nullMeasurableSet]

variable {k r : ℕ}

/- English proof (translation)
Establish `hE` using `Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S`. Establish `hU : (Set.univ : Set (Formalism.MainNotions.S.lieE S)) = ⋃ n : ℕ, Metric.closedBall 0 (n : ℝ)`. Use extensionality with `x`. Simplify using `only [Set.mem_univ, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right, true_iff]`. Take `⟨n, hn⟩` from `exists_nat_ge ‖x‖`.

Conclude with `⟨n, hn⟩`. Rewrite using `[hU, Set.image_iUnion]`. Conclude with `MeasurableSet.iUnion fun n => ((isCompact_closedBall _ _).image hE).isClosed.measurableSet`.
-/
theorem measurableSet_expImage_univ (S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    MeasurableSet ((fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) '' Set.univ) := by
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) S
  have hU : (Set.univ : Set (Formalism.MainNotions.S.lieE S)) = ⋃ n : ℕ, Metric.closedBall 0 (n : ℝ) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Metric.mem_closedBall, dist_zero_right, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact ⟨n, hn⟩
  rw [hU, Set.image_iUnion]
  exact MeasurableSet.iUnion fun n => ((isCompact_closedBall _ _).image hE).isClosed.measurableSet

/- English proof (translation)
Introduce `k r S`. Use `measurable_of_Iio fun t => ?_` and prove the remaining obligations. Establish `e : rhoS k r S ⁻¹' Set.Iio t = (fun x : Formalism.MainNotions.S.lieE S => fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) '' {Y | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + …`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_Iio, rhoS, iInf_lt_iff, Set.mem_image, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Y, hY, hlt⟩`. Conclude with `⟨Y, hlt, hY⟩`. Introduce and unpack `⟨Y, hlt, hY⟩`. Conclude with `⟨Y, hY, hlt⟩`.

Rewrite using `[e]`. Break down `eq_or_ne t ⊤ with rfl | ht` into its components or cases. Establish `: {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞) < ⊤} = Set.univ`. Use extensionality with `Y`. Simplify using the standard rewrite rules.

Rewrite using `[this]`. Conclude with `measurableSet_expImage_univ S`. Break down `eq_or_ne t 0 with rfl | ht0` into its components or cases. Establish `: {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞) < 0} = ∅` using `by ext Y; simp`. Rewrite using `[this, Set.image_empty]`.

Conclude with `MeasurableSet.empty`. Establish `hb : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞) < t} = Metric.ball 0 t.toReal`. Use extensionality with `Y`. Simplify using `only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]`. Rewrite using `[← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) ht]`.

Both sides reduce to the same expression. Establish `hpos : 0 < t.toReal` using `ENNReal.toReal_pos ht0 ht`. Rewrite using `[hb]`. Conclude with `measurableSet_expBall (k := k) (r := r) S t.toReal hpos`.
-/
theorem rhoMeas : RhoMeas := by
  intro k r S
  refine measurable_of_Iio fun t => ?_
  have e : rhoS k r S ⁻¹' Set.Iio t = (fun x : Formalism.MainNotions.S.lieE S =>
      fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j : Formalism.MainNotions.S.lieE S → Mt k r) ''
        {Y | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞) < t} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Iio, rhoS, iInf_lt_iff, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨Y, hY, hlt⟩; exact ⟨Y, hlt, hY⟩
    · rintro ⟨Y, hlt, hY⟩; exact ⟨Y, hY, hlt⟩
  rw [e]
  rcases eq_or_ne t ⊤ with rfl | ht
  · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
        < ⊤} = Set.univ := by
      ext Y; simp
    rw [this]
    exact measurableSet_expImage_univ S
  · rcases eq_or_ne t 0 with rfl | ht0
    · have : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < 0} = ∅ := by ext Y; simp
      rw [this, Set.image_empty]; exact MeasurableSet.empty
    · have hb : {Y : Formalism.MainNotions.S.lieE S | (‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖₊ : ℝ≥0∞)
          < t} = Metric.ball 0 t.toReal := by
        ext Y
        simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) ht]
        rfl
      have hpos : 0 < t.toReal := ENNReal.toReal_pos ht0 ht
      rw [hb]
      exact measurableSet_expBall (k := k) (r := r) S t.toReal hpos

/- English proof (translation)
Introduce `k r Y`. Establish `hinj : ∀ Y' : Formalism.MainNotions.S.lieE (Nset k r), expL k r (Nset k r) Y' = expL k r (Nset k r) Y → Y' = Y`. Introduce `Y' h`. Establish `hY : (Y : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL`. Rewrite using `[← Formalism.MainNotions.BridgeCSB.lieE_N]`.

Conclude with `Y.2`. Establish `hY' : (Y' : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL`. Rewrite using `[← Formalism.MainNotions.BridgeCSB.lieE_N]`. Conclude with `Y'.2`. Take `⟨X, hX, hXY⟩` from `hY`.

Take `⟨X', hX', hXY'⟩` from `hY'`. Establish `e1 : Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _) = X`. Rewrite using `[← hXY]`. Conclude with `Formalism.MainNotions.BridgeCSB.unrealify_RL X`. Establish `e2 : Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _) = X'`.

Rewrite using `[← hXY']`. Conclude with `Formalism.MainNotions.BridgeCSB.unrealify_RL X'`. Establish `hexp : NormedSpace.exp X' = NormedSpace.exp X`. Establish `h2 : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _)) i j : Mt k r) = fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j` using `h`. Rewrite `h2` using `[e1, e2]`.

Use extensionality with `i j`. Conclude with `congrFun (congrFun h2 i) j`. Establish `hXX : X' = X` using `Formalism.MainNotions.BridgeCSB.exp_injOn hX'.1 hX.1 hexp`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hXY, ← hXY', hXX]`.

Unfold `rhoS`. Use `le_antisymm (iInf_le_of_le Y (iInf_le_of_le rfl le_rfl)) (le_iInf₂ fun Y' hY' => ?_)` and prove the remaining obligations. Rewrite using `[hinj Y' hY']`. Conclude with `le_of_eq rfl`.
-/
theorem rhoN : RhoN := by
  intro k r Y
  have hinj : ∀ Y' : Formalism.MainNotions.S.lieE (Nset k r), expL k r (Nset k r) Y' = expL k r (Nset k r) Y → Y' = Y := by
    intro Y' h
    have hY : (Y : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y.2
    have hY' : (Y' : EuclideanSpace ℝ _) ∈ (Formalism.MainNotions.BridgeCSB.lieNS k r).map Formalism.MainNotions.BridgeCSB.RL := by
      rw [← Formalism.MainNotions.BridgeCSB.lieE_N]; exact Y'.2
    obtain ⟨X, hX, hXY⟩ := hY
    obtain ⟨X', hX', hXY'⟩ := hY'
    have e1 : Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _) = X := by
      rw [← hXY]; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X
    have e2 : Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _) = X' := by
      rw [← hXY']; exact Formalism.MainNotions.BridgeCSB.unrealify_RL X'
    have hexp : NormedSpace.exp X' = NormedSpace.exp X := by
      have h2 : (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y' : EuclideanSpace ℝ _)) i j : Mt k r) =
          fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _)) i j := h
      rw [e1, e2] at h2
      ext i j
      exact congrFun (congrFun h2 i) j
    have hXX : X' = X := Formalism.MainNotions.BridgeCSB.exp_injOn hX'.1 hX.1 hexp
    apply Subtype.ext
    rw [← hXY, ← hXY', hXX]
  unfold rhoS
  refine le_antisymm (iInf_le_of_le Y (iInf_le_of_le rfl le_rfl)) (le_iInf₂ fun Y' hY' => ?_)
  rw [hinj Y' hY']
  exact le_of_eq rfl

end Formalism.L2.SG.Pf.BH
