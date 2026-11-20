import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicIntCharpolyCommuteFrobeniusSemilinear
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPadicIntCharpolyCommuteFrobeniusSemilinear.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N), Function.Injective F → (∀ x, u (F x) = F (u x)) → ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  first | exact @GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | exact GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | (intros; apply GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly; all_goals assumption)
