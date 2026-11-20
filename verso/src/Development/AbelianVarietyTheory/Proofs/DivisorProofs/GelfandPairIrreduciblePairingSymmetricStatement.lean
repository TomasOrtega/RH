import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandPairIrreduciblePairingSymmetric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DixmierCommutantScalar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGelfandPairIrreduciblePairingSymmetric.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.gelfand_pair_irreducible_pairing_symmetric : ∀ (G : Type) [Group G] (K : Subgroup G), (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) →
    ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), Module.rank ℂ V ≤ Cardinal.aleph0 →
    (∀ N : Submodule ℂ V, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤) →
    ∀ x y : V, (∀ k ∈ K, ρ k x = x) → (∀ k ∈ K, ρ k y = y) → x ≠ 0 → ∃ c : ℂ, y = c • x := by
  first | exact @GlobalTheory.fixed_line_of_gelfand_countable | exact GlobalTheory.fixed_line_of_gelfand_countable | (intros; apply GlobalTheory.fixed_line_of_gelfand_countable <;> assumption)
