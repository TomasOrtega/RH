import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisLogTeichmullerRatioEqAddKummer
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LMulBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FGaloisLogTeichmullerRatioEqAddKummer.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.galois_logTeichmullerRatio_eq_add_kummer : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (Co : Core l), Co.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
  (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ϖ.untilt = ((l : ℕ) : Per.OC l) →
  ∀ u : Per.BdRp l, IsLogP (beta ϖ) u → ∀ g : GQ l,
    Per.σDp g u = u + Co.j (algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (kummer P g)) * Co.t) := by
  first | exact @GlobalTheory.Pst.StLat.gal_log | exact GlobalTheory.Pst.StLat.gal_log | (intros; apply GlobalTheory.Pst.StLat.gal_log <;> assumption)
