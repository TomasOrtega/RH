import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LeadingMinorIntegrality
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ReImESymmAdd

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

local notation "FIE" => FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ddS_ne' : ddS D ≠ 0 := Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_ne

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the hypotheses and the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem star_mem_zpow (m : ℤ) {x : D.host.E} (hx : x ∈ ddS D ^ m) : star x ∈ ddS D ^ m := by
  rcases Int.eq_nat_or_neg m with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
    obtain ⟨y', hy', e⟩ := Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_pow n y hy
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨y', hy', e⟩
  · rw [_root_.zpow_neg, zpow_natCast, Formalism.L2.SG.Pf.NcReal.JX.CovB.ddS_eq, ← FractionalIdeal.coeIdeal_pow] at hx ⊢
    exact Formalism.L2.SG.NGCut.LeadingMinorIntegrality.star_mem_inv n hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mul_mem_zpow {m n : ℤ} {x y : D.host.E} (hx : x ∈ ddS D ^ m) (hy : y ∈ ddS D ^ n) :
    x * y ∈ ddS D ^ (m + n) := by
  rw [zpow_add₀ ddS_ne']
  exact FractionalIdeal.mul_mem_mul hx hy

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem one_mem_zpow_zero : (1 : D.host.E) ∈ ddS D ^ (0 : ℤ) := by
  rw [zpow_zero]; exact FractionalIdeal.one_mem_one _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iQ_eq (b a : Fin D.R.rS) : iQ D b a = ((ddS D ^ ((b : ℤ) - a) : FIE) : Set D.host.E) := by
  unfold iQ aaD
  congr 1
  rw [← _root_.zpow_neg, ← zpow_add₀ ddS_ne']
  congr 1
  push_cast; ring

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem iP_eq (b a : Fin D.R.rS) :
    iP D b a = ((ddS D ^ (-((D.R.rS : ℤ) - b) - ((D.R.rS : ℤ) - a)) : FIE) : Set D.host.E) := by
  unfold iP aaD
  congr 1
  rw [← zpow_add₀ ddS_ne']
  congr 1

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem star_mem_iQ {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iQ D b a) : star x ∈ iQ D b a := by
  rw [iQ_eq] at hx ⊢; exact star_mem_zpow _ hx

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem star_mem_iP {b a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ iP D b a) : star x ∈ iP D b a := by
  rw [iP_eq] at hx ⊢; exact star_mem_zpow _ hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iP_comm (b a : Fin D.R.rS) : iP D b a = iP D a b := by
  rw [iP_eq, iP_eq]; congr 2; ring

end Formalism.L2.SG.Pf.NcReal.JX.NOf
