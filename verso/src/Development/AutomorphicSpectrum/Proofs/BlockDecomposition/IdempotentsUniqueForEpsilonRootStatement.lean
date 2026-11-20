import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsUniqueForEpsilonRoot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EpsilonCyclotomicElementPropertiesStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ContUniv.idem_unique` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIdempotentsUniqueForEpsilonRoot.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.idempotents_unique_for_epsilon_root : ∀ {l : ℕ} [Fact l.Prime] (ε : Eps l) (t : PAlg l) (m : ℕ) (x : t.U) (e e' : ZMod (l ^ m) → t.A),
  CompleteOrthogonalIdempotents e → CompleteOrthogonalIdempotents e' →
  (∀ c, t.sharp (e c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) →
  (∀ c, t.sharp (e' c) * (x - t.sharp (t.s (ε.e m)) ^ c.val) = 0) → e = e' := by
  first | exact @GlobalTheory.CompanionTheory.ContUniv.idem_unique | exact GlobalTheory.CompanionTheory.ContUniv.idem_unique | (intros; apply GlobalTheory.CompanionTheory.ContUniv.idem_unique <;> assumption)
