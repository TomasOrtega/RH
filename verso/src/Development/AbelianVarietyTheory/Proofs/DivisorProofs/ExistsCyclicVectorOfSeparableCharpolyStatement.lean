import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpoly
import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCyclicVectorOfSeparableCharpoly.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_cyclicVector_of_separable_charpoly' : ∀ {K : Type} [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable →
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  first | exact @GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly | exact GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly | (intros; apply GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly <;> assumption)
