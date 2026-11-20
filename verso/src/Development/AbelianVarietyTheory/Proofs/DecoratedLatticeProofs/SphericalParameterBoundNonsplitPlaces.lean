import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InvariantSphericalCoefficientEqZeroOrZonalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeTrivialBoundOfBoundedZonalSphericalUnitaryStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.ParamInert

open Formalism.UG (IsUnramInv GU KU qV IsInertAt)

/- English proof (translation)
Introduce `D A L hL v hv par c hc hc1 w hw`. Take `⟨⟨C, hC⟩, V, iV, iM, ρ, x, ℓ, hpar, hℓ, hcv⟩` from `hc`. Establish `hp` using `hpar w hw`. Use `⟨hp.card, ?_⟩` and prove the remaining obligations. Break down `hp with ⟨hs, -⟩ | ⟨hin, τ, ϖ, e, α, hU, he, hsat, hB⟩` into its components or cases.

Conclude with `absurd hs hv`. Establish `hϖ0 : ϖ ≠ 0`. Introduce `h0`. Establish `h4` using `hU.2.2.2.1`. Rewrite `h4` using `[h0, map_zero]`.

Conclude with `WithZero.zero_ne_coe h4`. Use `set ϖu : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hϖu`. Establish `hU' : IsUnramInv ((ϖu : w.adicCompletion D.host.E)) τ (qV D.host.F v)` using `hU`. Use `set ρ' : Representation ℂ (GU τ A.rank) V := ρ.comp e.symm.toMonoidHom with hρ'`. Establish `hKinv : ∀ k ∈ KU τ A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x)`.

Introduce `k hk g`. Establish `hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v`. Rewrite using `[he.2.2, MulEquiv.apply_symm_apply]`. Conclude with `hk`. Simplify using `only [hρ', MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul]`.

Rewrite using `[← map_mul]`. Conclude with `hℓ _ hk' _`. Establish `h1 : ℓ x ≠ 0`. Introduce `h0`. Apply `hc1` to reduce the goal to its premises.

Rewrite using `[hcv, map_one]`. Conclude with `h0`. Establish `hz` using `(GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal _ ϖu τ (qV D.host.F v) A.rank hU' V ρ' x α hsat ℓ hKinv).2 h1`. Establish `hbd : ∃ C' : ℝ, ∀ g, ‖ℓ (ρ' g x) / ℓ x‖ ≤ C'`. Use `⟨C / ‖ℓ x‖, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[norm_div]`. Establish `: ‖ℓ (ρ' g x)‖ ≤ C`. Use `hC (e.symm g)` as an intermediate fact. Rewrite `this` using `[hcv]`. Conclude with `this`.

Conclude with `div_le_div_of_nonneg_right this (norm_nonneg _)`. Establish `htb` using `GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary hUDI _ ϖu τ (qV D.host.F v) A.rank hU' α _ hz hbd`. Introduce `β hβ`. Rewrite `hβ` using `[hB]`. Establish `hq2 : 2 ≤ qV D.host.F v` using `hU.2.2.2.2.2.1`.

Establish `hle` using `GlobalTheory.FinZeta.ParamBound.norm_le_of_mem_bcParam hq2 htb β hβ`. Establish `hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2` using `((GlobalTheory.LFun.exists_isInertChart _ (isCMExt_host D) v).2 w hw hin).2.2.2.1`. Establish `hqv : (qV D.host.F v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ)` using `rfl`. Rewrite using `[hnorm, Nat.cast_pow, ← hqv]`. Use `hle.trans (Real.rpow_le_rpow_of_exponent_le ?_ ?_)` and prove the remaining obligations.

Establish `: (1 : ℝ) ≤ qV D.host.F v` using `by exact_mod_cast (by omega : 1 ≤ qV D.host.F v)`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem paramBoundOn_nonsplit (hUDI : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert) :
    ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro D A L hL v hv par c hc hc1 w hw
  obtain ⟨⟨C, hC⟩, V, iV, iM, ρ, x, ℓ, hpar, hℓ, hcv⟩ := hc
  have hp := hpar w hw
  refine ⟨hp.card, ?_⟩
  rcases hp with ⟨hs, -⟩ | ⟨hin, τ, ϖ, e, α, hU, he, hsat, hB⟩
  · exact absurd hs hv
  have hϖ0 : ϖ ≠ 0 := by
    intro h0
    have h4 := hU.2.2.2.1
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  set ϖu : (w.adicCompletion D.host.E)ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have hU' : IsUnramInv ((ϖu : w.adicCompletion D.host.E)) τ (qV D.host.F v) := hU
  set ρ' : Representation ℂ (GU τ A.rank) V := ρ.comp e.symm.toMonoidHom with hρ'
  have hKinv : ∀ k ∈ KU τ A.rank, ∀ g, ℓ (ρ' (k * g) x) = ℓ (ρ' g x) := by
    intro k hk g
    have hk' : e.symm k ∈ stabLoc D.sp.cm.sig A.gram L v := by
      rw [he.2.2, MulEquiv.apply_symm_apply]; exact hk
    simp only [hρ', MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, map_mul]
    rw [← map_mul]
    exact hℓ _ hk' _
  have h1 : ℓ x ≠ 0 := by
    intro h0; apply hc1; rw [hcv, map_one]; exact h0
  have hz := (GlobalTheory.T.invariant_sphericalCoefficient_eq_zero_or_zonal _ ϖu τ (qV D.host.F v) A.rank hU' V ρ' x α hsat ℓ hKinv).2 h1
  have hbd : ∃ C' : ℝ, ∀ g, ‖ℓ (ρ' g x) / ℓ x‖ ≤ C' := by
    refine ⟨C / ‖ℓ x‖, fun g => ?_⟩
    rw [norm_div]
    have : ‖ℓ (ρ' g x)‖ ≤ C := by
      have := hC (e.symm g); rw [hcv] at this; exact this
    exact div_le_div_of_nonneg_right this (norm_nonneg _)
  have htb := GlobalTheory.T.satakeTrivialBound_of_bounded_zonal_spherical_unitary hUDI _ ϖu τ (qV D.host.F v) A.rank hU' α _ hz hbd
  intro β hβ
  rw [hB] at hβ
  have hq2 : 2 ≤ qV D.host.F v := hU.2.2.2.2.2.1
  have hle := GlobalTheory.FinZeta.ParamBound.norm_le_of_mem_bcParam hq2 htb β hβ
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 :=
    ((GlobalTheory.LFun.exists_isInertChart _ (isCMExt_host D) v).2 w hw hin).2.2.2.1
  have hqv : (qV D.host.F v : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) := rfl
  rw [hnorm, Nat.cast_pow, ← hqv]
  refine hle.trans (Real.rpow_le_rpow_of_exponent_le ?_ ?_)
  · have : (1 : ℝ) ≤ qV D.host.F v := by exact_mod_cast (by omega : 1 ≤ qV D.host.F v)
    nlinarith
  · linarith

end GlobalTheory.Core.Rk.ParamInert
