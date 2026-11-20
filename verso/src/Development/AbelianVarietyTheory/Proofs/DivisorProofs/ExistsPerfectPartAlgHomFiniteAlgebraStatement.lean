import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectPartAlgHomFiniteAlgebra
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_perfectPart_algHom` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPerfectPartAlgHomFiniteAlgebra.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_perfectPart_algHom_finiteAlgebra : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], ∃ π : A →ₐ[k] A, ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) := by
  first | exact @GlobalTheory.exists_perfectPart_algHom | exact GlobalTheory.exists_perfectPart_algHom | (intros; apply GlobalTheory.exists_perfectPart_algHom <;> assumption)
