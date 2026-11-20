import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP

noncomputable section
namespace GlobalTheory.CrisMaps
open Formalism GlobalTheory.MemLoc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phiA_eq (l : ℕ) [Fact l.Prime] : phiA l = frob l := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sigA_eq (g : Per.Gq l) : sigA g = gal g := rfl

/- English proof (translation)
Rewrite using `[phiA_eq]`. Conclude with `frob_extends l`.
-/
theorem phiA_extends (l : ℕ) [Fact l.Prime] : Extends (Per.φA l) (phiA l) := by
  rw [phiA_eq]; exact frob_extends l

/- English proof (translation)
Rewrite using `[sigA_eq]`. Conclude with `gal_extends g`.
-/
theorem sigA_extends (g : Per.Gq l) : Extends (Per.σA g) (sigA g) := by
  rw [sigA_eq]; exact gal_extends g

/- English proof (translation)
Rewrite using `[phiA_eq, sigA_eq]`. Conclude with `frob_gal g x`.
-/
theorem phiA_sigA (g : Per.Gq l) (x : Per.Acris l) : phiA l (sigA g x) = sigA g (phiA l x) := by
  rw [phiA_eq, sigA_eq]; exact frob_gal g x

/- English proof (translation)
Rewrite using `[phiA_eq]`. Conclude with `φB_algebraMap l x`.
-/
theorem φB_phiA (l : ℕ) [Fact l.Prime] (x : Per.Acris l) :
    Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) := by
  rw [phiA_eq]; exact φB_algebraMap l x

/- English proof (translation)
Rewrite using `[sigA_eq]`. Conclude with `σB_algebraMap g x`.
-/
theorem σB_sigA (g : Per.Gq l) (x : Per.Acris l) :
    Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x) := by
  rw [sigA_eq]; exact σB_algebraMap g x

end GlobalTheory.CrisMaps
end
