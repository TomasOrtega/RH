import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftQMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocChiEpsU

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module Classical

noncomputable section
namespace GlobalTheory.UseLoc

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

/- English proof (translation)
Use `show D.nd.chi i c * (D.nd.chi i 1)⁻¹ = _`. Rewrite using `[D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]`. Both sides reduce to the same expression.
-/
theorem chiRat_eq_epsU_zpow (c : ℕ) (h1 : 1 ≤ c) (h2 : c ≤ D.R.t) : chiU D.nd i c * (chiU D.nd i 1)⁻¹ = epsU D.nd i ^ (-((c : ℤ) - 1)) := by
    show D.nd.chi i c * (D.nd.chi i 1)⁻¹ = _
    rw [D.nd.chi_def i c h1 h2, mul_inv_cancel_comm]
    rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression.
-/
theorem charL_chiOC_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (χ : GE D.nd →* (D.nd.O i)ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C χ) g =
      Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw χ g) := by
    apply Units.ext
    rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Conclude with `(IntermediateField.inclusion C.le).commutes _`.
-/
theorem inc_cycLL_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g) : Units.map C.inc.toMonoidHom (cycLL (Br.PD D.loc D.nbr i w hw) (Br.LL D.nbr i w hw) g) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g := by
    apply Units.ext
    exact (IntermediateField.inclusion C.le).commutes _

/- English proof (translation)
Use `show Units.map _ ((χ ^ k) _) = (Units.map _ (χ _)) ^ k`. Rewrite using `[MonoidHom.zpow_apply, map_zpow]`.
-/
theorem locChi_zpow_apply (χ : GE D.nd →* (D.nd.O i)ˣ) (k : ℤ) (g) : Br.locChi D.nbr i w hw (χ ^ k) g = Br.locChi D.nbr i w hw χ g ^ k := by
    show Units.map _ ((χ ^ k) _) = (Units.map _ (χ _)) ^ k
    rw [MonoidHom.zpow_apply, map_zpow]

/- English proof (translation)
Use `show Units.map _ ((a * b) g) = _`. Rewrite using `[MonoidHom.mul_apply, map_mul]`. Both sides reduce to the same expression.
-/
theorem charL_mul_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (a b : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g) : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (a * b) g =
      tableLineDegreeTwo.charL (LL := ↥C.LL.1) a g * tableLineDegreeTwo.charL (LL := ↥C.LL.1) b g := by
    show Units.map _ ((a * b) g) = _
    rw [MonoidHom.mul_apply, map_mul]
    rfl

/- English proof (translation)
Simplify using `[Br.locChi, Br.chiG]`.
-/
theorem locChi_one_apply (g : Br.G D.nbr i w hw) : Br.locChi D.nbr i w hw (1 : GE D.nd →* (D.nd.O i)ˣ) g = 1 := by
    simp [Br.locChi, Br.chiG]

/- English proof (translation)
Rewrite using `[map_zpow, ← inc_cycLL_apply C g, GlobalTheory.CycBridge.locChi_epsU D i w hw g]`.
-/
theorem inc_locChi_epsU_zpow (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) (k : ℤ) :
    Units.map C.inc.toMonoidHom (Br.locChi D.nbr i w hw (epsU D.nd i) g ^ k) =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ k := by
  rw [map_zpow, ← inc_cycLL_apply C g, GlobalTheory.CycBridge.locChi_epsU D i w hw g]

/- English proof (translation)
Introduce `D i w hw C θ c h1 h2 g`. Establish `e1 : tableLineDegreeTwo.charL (LL` using `↥C.LL.1) (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) g = cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by`. Rewrite using `[charL_chiOC_apply, chiRat_eq_epsU_zpow c h1 h2, locChi_zpow_apply, inc_locChi_epsU_zpow]`. Establish `e0 : tableLineDegreeTwo.charL (LL` using `↥C.LL.1) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) g = 1 := by`. Rewrite using `[charL_chiOC_apply, mul_inv_cancel, locChi_one_apply]`.

Conclude with `map_one _`. Unfold `chiT`. Rewrite using `[charL_mul_apply, charL_mul_apply, e1, e0, one_mul]`. Conclude with `mul_comm _ _`.
-/
theorem chiT_cyc : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ), 1 ≤ c → c ≤ D.R.t → ∀ g, tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ c) g = tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g * cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
  intro D i w hw C θ c h1 h2 g
  have e1 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹)) g =
      cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g ^ (-((c : ℤ) - 1)) := by
    rw [charL_chiOC_apply, chiRat_eq_epsU_zpow c h1 h2, locChi_zpow_apply, inc_locChi_epsU_zpow]
  have e0 : tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiOC C (chiU D.nd i 1 * (chiU D.nd i 1)⁻¹)) g = 1 := by
    rw [charL_chiOC_apply, mul_inv_cancel, locChi_one_apply]
    exact map_one _
  unfold chiT
  rw [charL_mul_apply, charL_mul_apply, e1, e0, one_mul]
  exact mul_comm _ _

end GlobalTheory.UseLoc
