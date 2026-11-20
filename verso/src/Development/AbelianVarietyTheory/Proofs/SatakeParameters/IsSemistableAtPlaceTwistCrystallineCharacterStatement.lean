import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemistableAtPlaceTwistCrystallineCharacter
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.GalOfCusp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SstTwist.isSstAt_twist` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIsSemistableAtPlaceTwistCrystallineCharacter.lean&line=97#L97)
-/
theorem _root_.GlobalTheory.T.isSemistableAtPlace_twist_crystallineCharacter : GlobalTheory.Published.DeRhamPotSemistable → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (Gw : Subgroup (Ω ≃ₐ[E] Ω)) (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (a : ℕ) (r : ↥Gw →* GL (Fin a) (Om l)) (c : ↥Gw →* GL (Fin 1) (Om l)), (Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → (Continuous fun g => ((c g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) → IsSstAt P Bw r → IsCrysAt P Bw c → IsSstAt P Bw (Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp c)) := by
  first | exact @GlobalTheory.SstTwist.isSstAt_twist | exact GlobalTheory.SstTwist.isSstAt_twist | (intros; apply GlobalTheory.SstTwist.isSstAt_twist <;> assumption)
