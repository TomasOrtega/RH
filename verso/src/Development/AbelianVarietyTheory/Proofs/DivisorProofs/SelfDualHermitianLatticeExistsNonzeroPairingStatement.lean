import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualHermitianLatticeExistsNonzeroPairing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSelfDualHermitianLatticeExistsNonzeroPairing.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.selfDual_hermitianLattice_exists_nonzero_pairing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ x : Fin n → E, x ≠ 0 → ∃ z ∈ L, form σ J z x ≠ 0 := by
  first | exact @GlobalTheory.selfDual_pair_nondeg | exact GlobalTheory.selfDual_pair_nondeg | (intros; apply GlobalTheory.selfDual_pair_nondeg <;> assumption)
