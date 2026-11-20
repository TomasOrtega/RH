import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOfUnityPrimeToTeichmullerLift
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRootOfUnityPrimeToTeichmullerLift.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.rootOfUnity_prime_to_teichmuller_lift : ∀ (l : ℕ) [Fact l.Prime], ∀ o : Om l →+* Per.BdRp l, IsSec o → ∀ (c : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → c ^ m = 1 → (∃ xb : Per.Fl l, IsTiltOf c m xb) ∧ ∀ xb : Per.Fl l, IsTiltOf c m xb → xb ^ m = 1 ∧ ((xb.untilt : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) ∧ aDp l (Per.tm xb) = o c := by
  first | exact @GlobalTheory.MemLoc.rootOfUnity_teichmuller | exact GlobalTheory.MemLoc.rootOfUnity_teichmuller | (intros; apply GlobalTheory.MemLoc.rootOfUnity_teichmuller <;> assumption)
