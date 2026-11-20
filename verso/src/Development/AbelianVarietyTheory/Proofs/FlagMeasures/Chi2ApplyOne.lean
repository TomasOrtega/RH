import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.LocalRingCardinality.DataTies
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DEqFinrankHHX
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FEqAndRdEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeRatioEqSignatureIndex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolFormalDegreeEq

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.BundleTie

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Take `⟨h1, -, -, hmul, hnorm⟩` from `Formalism.L2.SG.Pf.level_subgroup_character_unitary X`. Establish `hsq` using `hmul 1 h1 1 h1`. Rewrite `hsq` using `[mul_one (1 : X.B.I.Gf)]`. Establish `hne : X.chi2 1 ≠ 0`. Introduce `h0`.

Establish `hn` using `hnorm 1 h1`. Rewrite `hn` using `[h0, norm_zero]`. Conclude with `zero_ne_one hn`. Conclude with `mul_left_cancel₀ hne (by rw [mul_one]; exact hsq.symm)`.
-/
theorem chi2_apply_one : X.chi2 1 = 1 := by

  obtain ⟨h1, -, -, hmul, hnorm⟩ := Formalism.L2.SG.Pf.level_subgroup_character_unitary X
  have hsq := hmul 1 h1 1 h1
  rw [mul_one (1 : X.B.I.Gf)] at hsq
  have hne : X.chi2 1 ≠ 0 := by
    intro h0
    have hn := hnorm 1 h1
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  exact mul_left_cancel₀ hne (by rw [mul_one]; exact hsq.symm)

/- English proof (translation)
Establish `h1 : (1 : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw` using `(Formalism.L2.SG.Pf.level_subgroup_character_unitary X).1`. Rewrite using `[X.e_eq 1, if_pos h1]`. Establish `hc : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd 1 = 1` using `chi2_apply_one X`. Rewrite using `[hc, star_one]`. Both sides reduce to the same expression.
-/
theorem e_one : X.B.e 1 = 1 / (X.volK2 : ℂ) := by
  have h1 : (1 : X.B.I.Gf) ∈ K2set X.B.I X.B.g X.e0 X.z0 X.bw := (Formalism.L2.SG.Pf.level_subgroup_character_unitary X).1
  rw [X.e_eq 1, if_pos h1]
  have hc : chi2f X.B.I X.psiEf X.B.g X.e0 X.f0 X.z0 X.bw X.bwd 1 = 1 := chi2_apply_one X
  rw [hc, star_one]
  rfl

open Formalism Formalism.L2 Formalism.L2.SG in

/- English proof (translation)
Establish `hre : (X.B.e 1).re = 1 / X.volK2`. Rewrite using `[e_one X, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]`. Establish `hd : (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) = ∏ v, X.dv v` using `rfl`. Establish `hsub : X.K2 ⊆ X.B.I.Kset` using `fun x hx => hx.1`. Establish `hv2 : X.volK2 = (X.B.μf X.K2).toReal` using `rfl`.

Use `show Formalism.MainNotions.StandardLattice.volY0 D * Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ ρ, D.dsig ρ = (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) * X.B.I.vol X.B.μf X.B.fund * (X.B.e 1).re`. Rewrite using `[hre, hd, ← hI]`. Distinguish the cases in `hv : X.volK2 = 0`. Rewrite using `[hv]`. Simplify using the standard rewrite rules.

Establish `hK2 : X.B.μf X.K2 ≠ 0`. Introduce `h`. Apply `hv` to reduce the goal to its premises. Simplify using `[hv2, h]`. Establish `hμ : (X.B.μf X.B.I.Kset).toReal ≠ 0`.

Rewrite using `[Ne, ENNReal.toReal_eq_zero_iff, not_or]`. Conclude with `⟨fun h => hK2 (measure_mono_null hsub h), (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top.ne⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_mul_cancel₀ _ hμ, mul_one_div]`.
-/
theorem dstarD_eq
    (hI : (X.B.μf X.B.I.Kset).toReal / X.volK2 = Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1))
    (hV : (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal =
      Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) :
    Formalism.MainNotions.StandardLattice.DstarD D =
      X.B.I.Dstar (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) X.B.μf X.B.fund X.B.e := by
  have hre : (X.B.e 1).re = 1 / X.volK2 := by
    rw [e_one X, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  have hd : (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) = ∏ v, X.dv v := rfl
  have hsub : X.K2 ⊆ X.B.I.Kset := fun x hx => hx.1
  have hv2 : X.volK2 = (X.B.μf X.K2).toReal := rfl
  show Formalism.MainNotions.StandardLattice.volY0 D * Formalism.MainNotions.StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) * ∏ ρ, D.dsig ρ =
    (∏ v, fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) * X.B.I.vol X.B.μf X.B.fund * (X.B.e 1).re
  rw [hre, hd, ← hI]
  by_cases hv : X.volK2 = 0
  · rw [hv]
    simp
  ·
    have hK2 : X.B.μf X.K2 ≠ 0 := by
      intro h
      apply hv
      simp [hv2, h]
    have hμ : (X.B.μf X.B.I.Kset).toReal ≠ 0 := by
      rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨fun h => hK2 (measure_mono_null hsub h),
        (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top.ne⟩
    calc Formalism.MainNotions.StandardLattice.volY0 D * ((X.B.μf X.B.I.Kset).toReal / X.volK2) * ∏ ρ, D.dsig ρ
        = (Formalism.MainNotions.StandardLattice.volY0 D * ∏ ρ, D.dsig ρ) * (X.B.μf X.B.I.Kset).toReal / X.volK2 := by ring
      _ = ((∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund / (X.B.μf X.B.I.Kset).toReal) *
            (X.B.μf X.B.I.Kset).toReal / X.volK2 := by rw [hV]
      _ = (∏ v, X.dv v) * X.B.I.vol X.B.μf X.B.fund * (1 / X.volK2) := by
        rw [div_mul_cancel₀ _ hμ, mul_one_div]

/- English proof (translation)
Introduce `D X hHH hint hD hinst hVol hcd hds`. Take `⟨ι⟩` from `hHH`. Establish `hV` using `GlobalTheory.covol_formalDegree_eq D X hinst hVol hcd hds`. Establish `hI` using `Formalism.L2.SG.Pf.DstarIdxPf.dstarIdx_holds X`. Conclude with `{ n_eq := X.n_eq f_eq := GlobalTheory.DegreeRankEquations.f_eq D X rd_eq := GlobalTheory.DegreeRankEquations.rd_eq D X eps_eq := X.eps_eq lam_eq := X.lam_eq ds := X.ds low := X.low g_eq := X.g_eq g0_eq := X.g0_eq D_eq := by`.

Rewrite using `[GlobalTheory.RowsCount.D_eq_finrank_HHX D X hint, ← ι.toLinearEquiv.finrank_eq, D.s_HH]`. Use `Dstar_eq := hD.trans (dstarD_eq X hI hV) }`.
-/
theorem autTie : ∀ (D : D7) (X : HidaSetting D), Nonempty (D.s.HH ≃ₗᵢ[ℂ] HHX X) →
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) → D.what₂.Dstar = Formalism.MainNotions.StandardLattice.DstarD D →
    X.B.I = Formalism.L2.SG.InstExistsPf.instOf D → Formalism.MainNotions.StandardLattice.VolTie D → cdScaleTie D → dsigTie D →
    AutTie D X.B X.pl := by
  intro D X hHH hint hD hinst hVol hcd hds
  obtain ⟨ι⟩ := hHH
  have hV := GlobalTheory.covol_formalDegree_eq D X hinst hVol hcd hds
  have hI := Formalism.L2.SG.Pf.DstarIdxPf.dstarIdx_holds X
  exact
    { n_eq := X.n_eq
      f_eq := GlobalTheory.DegreeRankEquations.f_eq D X
      rd_eq := GlobalTheory.DegreeRankEquations.rd_eq D X
      eps_eq := X.eps_eq
      lam_eq := X.lam_eq
      ds := X.ds
      low := X.low
      g_eq := X.g_eq
      g0_eq := X.g0_eq
      D_eq := by
        rw [GlobalTheory.RowsCount.D_eq_finrank_HHX D X hint, ← ι.toLinearEquiv.finrank_eq, D.s_HH]
      Dstar_eq := hD.trans (dstarD_eq X hI hV) }

end GlobalTheory.BundleTie
