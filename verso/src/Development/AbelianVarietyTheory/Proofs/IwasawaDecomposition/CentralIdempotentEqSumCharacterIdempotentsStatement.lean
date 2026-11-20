import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralIdempotentEqSumCharacterIdempotents
import Mathlib
import Formalism.LocalToGlobal.Columns.GoodXgFin
open Formalism.L2.DIV
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCentralIdempotentEqSumCharacterIdempotents.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.centralIdempotent_eq_sum_character_idempotents : ∀ {G : Type} [inst : Group G] [inst_1 : Fintype G] [inst_2 : DecidableEq G] (A : Finset (G → ℂ)) (e : MonoidAlgebra ℂ G), (∀ ψ ∈ A, ψ 1 ≠ 0) → (∀ g : G, ∑ ψ ∈ A, ψ 1 * ψ g = if g = 1 then (Fintype.card G : ℂ) else 0) → (∀ ψ ∈ A, ∀ x : G, ψ 1 * ∑ g, e.coeff g * ψ (g * x) = (∑ g, e.coeff g * ψ g) * ψ x) → e * e = e → e = idemOf (A.filter fun ψ => ∑ g, e.coeff g * ψ g = ψ 1) := by
  first | exact @GlobalTheory.IdemExpand.eq_idemOf_filter | exact GlobalTheory.IdemExpand.eq_idemOf_filter | (intros; apply GlobalTheory.IdemExpand.eq_idemOf_filter <;> assumption)
