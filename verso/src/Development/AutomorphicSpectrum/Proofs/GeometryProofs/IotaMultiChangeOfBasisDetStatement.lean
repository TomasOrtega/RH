import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDet
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIotaMultiChangeOfBasisDet.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.iota_multi_change_of_basis_det : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V) (P : Matrix (Fin n) (Fin n) Ω), exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family | (intros; apply GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family <;> assumption)
