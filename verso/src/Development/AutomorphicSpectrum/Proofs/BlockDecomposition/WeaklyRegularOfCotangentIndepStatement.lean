import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeaklyRegularOfCotangentIndep
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeaklyRegularOfCotangentIndep.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.weakly_regular_of_cotangent_indep : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ) (a : Fin d → R), ringKrullDim R ≤ d → LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} => ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) → RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧ Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | exact GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one | (intros; apply GlobalTheory.CompanionTheory.RegSeq.isWeaklyRegular_and_length_quotient_le_one <;> assumption)
