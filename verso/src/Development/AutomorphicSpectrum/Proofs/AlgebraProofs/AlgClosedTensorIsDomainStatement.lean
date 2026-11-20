import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgClosedTensorIsDomain
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FAlgClosedTensorIsDomain.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.alg_closed_tensor_isDomain : ∀ (K Ω C : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Field C] [Algebra K C], (∀ a : Ω, IsAlgebraic K a → a ∈ (algebraMap K Ω).range) → IsDomain (Ω ⊗[K] C) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants | exact GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isDomain_tensor_of_algebraically_closed_constants <;> assumption)
