import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCharacterPairingHarishChandraCuspidalMackey.lean&line=259#L259)
-/
theorem _root_.GlobalTheory.T.characterPairing_harishChandra_cuspidal_mackey : ∀ (g : ℕ) [Fact g.Prime] (L L' : List (Pc g)) (n : ℕ), degL L = n → degL L' = n → (∀ p ∈ L, IsCusp p.2) → (∀ p ∈ L', IsCusp p.2) → (¬ L.Perm L' → ip (hcL L n) (hcL L' n) = 0) ∧ (L.Nodup → ip (hcL L n) (hcL L n) = 1) := by
  first | exact @GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp | exact GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp | (intros; apply GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp <;> assumption)
