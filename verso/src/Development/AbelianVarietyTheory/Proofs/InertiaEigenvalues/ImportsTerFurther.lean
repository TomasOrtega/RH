import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

/- English proof (translation)
Unfold `φc tc`. Rewrite using `[(GlobalTheory.CrisMaps.phiA_extends l).alg]`. Use `congr 1`. Rewrite using `[GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]`.
-/
theorem φc_tc (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l) : φc l (tc l y) = tc l (y ^ l) := by
  unfold φc tc
  rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
  congr 1
  rw [GlobalTheory.RingBasics.φA_apply, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

/- English proof (translation)
Introduce `l _ y` and use `φc_tc l y`.
-/
theorem frob_teich : ∀ (l : ℕ) [Fact l.Prime] (y : Formalism.Per.Fl l), φc l (tc l y) = tc l (y ^ l) :=
  fun l _ y => φc_tc l y

end GlobalTheory.PMon.Gauss
