import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDieudonneColengthEqLogDegree.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.dieudonneColength_eq_log_degree : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e → Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  first | exact @GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | exact GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg | (intros; apply GlobalTheory.Dieu.length_quot_range_map_eq_of_hasLogDeg <;> assumption)
