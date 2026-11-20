import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TensorSLOrbitMapProperOfIsClosed
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FTensorSLOrbitMapProperOfIsClosed.lean&line=138#L138)
-/
theorem _root_.GlobalTheory.T.tensorSLOrbit_map_proper_of_isClosed : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : TIdx ι d → ℂ), IsClosed (orb d v) → ∀ C : ℝ, ∃ C' : ℝ, ∀ y : Matrix ι ι ℂ, y.det = 1 → nsq (act d v y) ≤ C → ∃ h : Matrix ι ι ℂ, h.det = 1 ∧ act d v h = v ∧ ∀ i j, ‖(h * y) i j‖ ≤ C' := by
  first | exact @GlobalTheory.ClassFin.orbit_proper_of_isClosed | exact GlobalTheory.ClassFin.orbit_proper_of_isClosed | (intros; apply GlobalTheory.ClassFin.orbit_proper_of_isClosed <;> assumption)
