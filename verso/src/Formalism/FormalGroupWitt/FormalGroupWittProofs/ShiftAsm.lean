import Formalism.FormalGroupWitt.FormalGroupWittProofs.ShiftFE
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FrobSqV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.WittTeichmullerRoot
import Formalism.FormalGroupWitt.FormalGroupWittProofs.GroupV

noncomputable section

namespace Formalism.FG.FormalGroupLawMap

open MvPowerSeries

variable {R S : Type*} [CommRing R] [CommRing S]

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem map_inj {σ : Type*} (h : R →+* S) (hh : Function.Injective h) {f g : MvPowerSeries σ R}
    (e : map h f = map h g) : f = g := by
  ext n
  have := congrArg (coeff n) e
  simp only [coeff_map] at this
  exact hh this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem map_subst' {σ τ : Type*} [Finite σ] (h : R →+* S) {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ R) :
    map h (subst a f) = subst (fun s => map h (a s)) (map h f) :=
  map_subst (hasSubst_of_constantCoeff_zero ha) f

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem coe_injective (l : ℕ) [Fact l.Prime] : Function.Injective (PadicInt.Coe.ringHom (p := l)) :=
  fun _ _ e => Subtype.ext e

end Formalism.FG.FormalGroupLawMap

namespace Formalism.FG

open Formalism.G Formalism.FG.FormalGroupLawMap

end Formalism.FG
