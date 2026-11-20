import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGapsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightRegularRepUnitaryStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralInvOfSupport
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowLev

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

/- English proof (translation)
Take `⟨-, hKm, hKi, hχm, hχn⟩` from `Formalism.L2.SG.Closed.level_subgroup_is_group X`. Establish `hK : ∀ z, z ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw ↔ z ∈ X.K2` using `fun z => Iff.rfl`. Rewrite using `[X.e_eq y, X.e_eq (k * y)]`. Distinguish the cases in `hy : y ∈ X.K2`. Establish `hky : k * y ∈ X.K2` using `hKm k hk y hy`.

Rewrite using `[if_pos ((hK y).2 hy), if_pos ((hK _).2 hky)]`. Express the relevant statement in the definitionally equal form `star (X.chi2 y) / _ = X.chi2 k * (star (X.chi2 (k * y)) / _)`. Rewrite using `[hχm k hk y hy, star_mul', ← mul_div_assoc, ← mul_assoc]`. Establish `h1 : X.chi2 k * star (X.chi2 k) = 1`. Rewrite using `[← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχn k hk]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, one_mul]`. Establish `hky : k * y ∉ X.K2` using `fun h' => hy (by simpa using hKm _ (hKi k hk) _ h')`. Rewrite using `[if_neg (fun h' => hy ((hK y).1 h')), if_neg (fun h' => hky ((hK _).1 h')), mul_zero]`.
-/
theorem e_left (k : X.B.I.Gf) (hk : k ∈ X.K2) (y : X.B.I.Gf) : X.B.e y = X.chi2 k * X.B.e (k * y) := by
  obtain ⟨-, hKm, hKi, hχm, hχn⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hK : ∀ z, z ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw ↔ z ∈ X.K2 := fun z => Iff.rfl
  rw [X.e_eq y, X.e_eq (k * y)]
  by_cases hy : y ∈ X.K2
  · have hky : k * y ∈ X.K2 := hKm k hk y hy
    rw [if_pos ((hK y).2 hy), if_pos ((hK _).2 hky)]
    change star (X.chi2 y) / _ = X.chi2 k * (star (X.chi2 (k * y)) / _)
    rw [hχm k hk y hy, star_mul', ← mul_div_assoc, ← mul_assoc]
    have h1 : X.chi2 k * star (X.chi2 k) = 1 := by
      rw [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχn k hk]; simp
    rw [h1, one_mul]
  · have hky : k * y ∉ X.K2 := fun h' => hy (by simpa using hKm _ (hKi k hk) _ h')
    rw [if_neg (fun h' => hy ((hK y).1 h')), if_neg (fun h' => hky ((hK _).1 h')), mul_zero]

/- English proof (translation)
Take `⟨R1, Rm, Rn, -⟩` from `GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B`. Take `⟨-, hT⟩` from `X.B.Re_spec`. Establish `p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1` using `R1`. Establish `pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b)`. Introduce `a b`.

Rewrite using `[← Rm]`. Simplify using the standard rewrite rules. Establish `pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖` using `fun g v => Rn _ v`. Use `ContinuousLinearMap.ext fun y => ?_` and prove the remaining obligations. Apply `ext_inner_left ℂ` to reduce the goal to its premises.

Introduce `x`. Rewrite using `[ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right, GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, hT, hT, ← integral_const_mul, ← integral_mul_left_eq_self (fun h => X.chi2 k * (X.B.e h * ⟪x, X.B.R (1, h) y⟫_ℂ)) k]`. Use `congr 1`. Use function extensionality and compare the values at `h`. Establish `e1 : ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = ⟪x, X.B.R (1, k * h) y⟫_ℂ`.

Rewrite using `[← GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, pm]`. Both sides reduce to the same expression. Use `show X.B.e h * ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = X.chi2 k * (X.B.e (k * h) * ⟪x, X.B.R (1, k * h) y⟫_ℂ)`. Rewrite using `[e1, e_left X k hk h, mul_assoc]`.
-/
theorem R_comp_Re (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨R1, Rm, Rn, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous X.B
  obtain ⟨-, hT⟩ := X.B.Re_spec
  have p1 : (fun g : X.B.I.Gf => X.B.R (1, g)) 1 = 1 := R1
  have pm : ∀ a b : X.B.I.Gf, X.B.R (1, a * b) = X.B.R (1, a) * X.B.R (1, b) := by
    intro a b; rw [← Rm]; simp
  have pn : ∀ (g : X.B.I.Gf) v, ‖X.B.R (1, g) v‖ = ‖v‖ := fun g v => Rn _ v
  refine ContinuousLinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, hT, hT, ← integral_const_mul,
    ← integral_mul_left_eq_self (fun h => X.chi2 k * (X.B.e h * ⟪x, X.B.R (1, h) y⟫_ℂ)) k]
  congr 1
  funext h
  have e1 : ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = ⟪x, X.B.R (1, k * h) y⟫_ℂ := by
    rw [← GlobalTheory.IdemProj.inner_rep (fun g : X.B.I.Gf => X.B.R (1, g)) p1 pm pn, pm]
    rfl
  show X.B.e h * ⟪X.B.R (1, k⁻¹) x, X.B.R (1, h) y⟫_ℂ = X.chi2 k * (X.B.e (k * h) * ⟪x, X.B.R (1, k * h) y⟫_ℂ)
  rw [e1, e_left X k hk h, mul_assoc]

end GlobalTheory.ConjRowLev

namespace GlobalTheory.ConjRowMult

open GlobalTheory.ConjRowLev in

/- English proof (translation)
Introduce `_ D X h θ S M J χ t c _ _ _ _ hM _ Φ hΦ hrep u k hk g`. Take `⟨-, hCL⟩` from `hM`. Take `⟨hJ, hχ⟩` from `hCL k`. Establish `hk0` using `hJ.1 hk`. Take `⟨h1, h2⟩ : (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧ (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2` from `hk0`.

Use `set k' := (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 with hk'`. Establish `hsplit : g * k * t⁻¹ = (g * t⁻¹) * (t⁻¹⁻¹ * k * t⁻¹)` using `by group`. Establish `hι : iotaX X h (g * k * t⁻¹) = iotaX X h (g * t⁻¹) * ((1, k') : X.B.I.GA)`. Rewrite using `[hsplit, map_mul]`. Use `congr 1`.

Conclude with `Prod.ext h1 rfl`. Take `⟨ψ, hψ⟩` from `hrep u`. Establish `hR : X.B.R (1, k') (Φ (X.B.tens (vecC X M c u))) = X.chi2 k' • Φ (X.B.tens (vecC X M c u))`. Take `⟨T0, -, rfl⟩` from `hΦ`. Use `congrArg (fun L => L (T0 (X.B.tens (vecC X M c u)))) (R_comp_Re X k' h2)` as an intermediate fact.

Simplify using `using this`. Establish `a` using `Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1, k') : X.B.I.GA)`. Rewrite `a` using `[hR]`. Establish `key` using `congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X a (Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 k') hψ))`. Rewrite using `[conjMap_apply, conjMap_apply, contRepL_spec X hψ, hι, key, Pi.smul_apply, smul_eq_mul, star_mul', ← hχ hk]`.

Both sides reduce to the same expression.
-/
theorem conjMap_lev : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, ∀ k ∈ J, ∀ g : GA D (D.sp.Y 0), GlobalTheory.ConjRowMult.conjMap X M c Φ h t u (g * k) = χ k * GlobalTheory.ConjRowMult.conjMap X M c Φ h t u g := by
  intro _ D X h θ S M J χ t c _ _ _ _ hM _ Φ hΦ hrep u k hk g
  obtain ⟨-, hCL⟩ := hM
  obtain ⟨hJ, hχ⟩ := hCL k
  have hk0 := hJ.1 hk
  obtain ⟨h1, h2⟩ : (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧ (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hk0
  set k' := (iotaX X h (t⁻¹⁻¹ * k * t⁻¹)).2 with hk'
  have hsplit : g * k * t⁻¹ = (g * t⁻¹) * (t⁻¹⁻¹ * k * t⁻¹) := by group
  have hι : iotaX X h (g * k * t⁻¹) = iotaX X h (g * t⁻¹) * ((1, k') : X.B.I.GA) := by
    rw [hsplit, map_mul]
    congr 1
    exact Prod.ext h1 rfl
  obtain ⟨ψ, hψ⟩ := hrep u
  have hR : X.B.R (1, k') (Φ (X.B.tens (vecC X M c u))) = X.chi2 k' • Φ (X.B.tens (vecC X M c u)) := by
    obtain ⟨T0, -, rfl⟩ := hΦ
    have := congrArg (fun L => L (T0 (X.B.tens (vecC X M c u)))) (R_comp_Re X k' h2)
    simpa using this
  have a := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1, k') : X.B.I.GA)
  rw [hR] at a
  have key := congrFun (Formalism.L2.SG.EvalTOntoRep.contRep_unique X a (Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 k') hψ))
  rw [conjMap_apply, conjMap_apply, contRepL_spec X hψ, hι, key, Pi.smul_apply, smul_eq_mul, star_mul', ← hχ hk]
  rfl

end GlobalTheory.ConjRowMult

end
