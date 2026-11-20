import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FIsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat.lean&line=81#L81)
-/
theorem _root_.GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1), IsMatRep T M → (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧ ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  first | exact @GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | exact GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | (intros; apply GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep <;> assumption)
