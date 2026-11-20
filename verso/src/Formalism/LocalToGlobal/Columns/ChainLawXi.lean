import Formalism.LocalToGlobal.Columns.ChainLawLev
import Formalism.LocalToGlobal.Columns.ChainLawXiStmt
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivStmt
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.Columns.RecLevelSym
import Formalism.LocalToGlobal.Columns.ChainOne

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Units

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

/- English proof (translation)
Unfold `LocE.unitV`. Rewrite using `[dif_pos hU]`. Conclude with `Units.ne_zero _`.
-/
theorem clX_unitV_ne (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hU : IsUnit (redP P a)) : LocE.unitV χ a ≠ 0 := by
  unfold LocE.unitV
  rw [dif_pos hU]
  exact Units.ne_zero _

/- English proof (translation)
Establish `h1 : redP P (1 : E) = 1`. Use `reduction_coe P (1 : 𝓞 E)` as an intermediate fact. Simplify using `using this`. Establish `hU : IsUnit (redP P (1 : E))` using `by rw [h1]; exact isUnit_one`. Unfold `LocE.unitV`.

Rewrite using `[dif_pos hU]`. Establish `: hU.unit = 1` using `Units.ext (by simpa using h1)`. Rewrite using `[this, map_one, Units.val_one]`.
-/
theorem clX_unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h1 : redP P (1 : E) = 1 := by
    have := reduction_coe P (1 : 𝓞 E)
    simpa using this
  have hU : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.unitV
  rw [dif_pos hU]
  have : hU.unit = 1 := Units.ext (by simpa using h1)
  rw [this, map_one, Units.val_one]

/- English proof (translation)
Establish `hne` using `clX_unitV_ne χ (isUnit_reduction_of_integralAt_inv hu hu' h0)`. Establish `hm` using `unitV_mul_unit χ hu hu' h0 a⁻¹`. Rewrite `hm` using `[inv_mul_cancel₀ h0, clX_unitV_one]`. Conclude with `eq_inv_of_mul_eq_one_left hm.symm`.
-/
theorem clX_unitV_inv (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hu : IntAt P a) (hu' : IntAt P a⁻¹) (h0 : a ≠ 0) :
    LocE.unitV χ a⁻¹ = (LocE.unitV χ a)⁻¹ := by
  have hne := clX_unitV_ne χ (isUnit_reduction_of_integralAt_inv hu hu' h0)
  have hm := unitV_mul_unit χ hu hu' h0 a⁻¹
  rw [inv_mul_cancel₀ h0, clX_unitV_one] at hm
  exact eq_inv_of_mul_eq_one_left hm.symm

end Units

section Assembly

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Assembly

end Formalism.L2.Col
