import Mathlib
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSq
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe

noncomputable section

namespace GlobalTheory.CobExactProof

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso beLT epOf BeRat)
open Formalism.InvariantFactorPaths.G7 (cob lgF IsLawOfLog at1)
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.KerInert.BeCob (eLT vLT psiLT)
open GlobalTheory.CurveDictionary (map_cob lgF_eq_logF cc_lgF')

/- English proof (translation)
Introduce `l _ g hLT hOk hb F hF`. Establish `hex` using `hOk.2.2.1`. Establish `hinv` using `hOk.2.2.2`. Use `set e := eLT hLT with he`. Use `set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc`.

Establish `hL0 : PowerSeries.constantCoeff Lc = 0` using `cc_lgF' ℂ_[l] l`. Establish `hlog0 : PowerSeries.constantCoeff (Formalism.MainNotions.FormalGroupSystem.logF l) = 0`. Establish `h1 : k0ToC l (PowerSeries.coeff 0 (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0`. Rewrite using `[← PowerSeries.coeff_map, lgF_eq_logF, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `cc_lgF' ℂ_[l] l`.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(map_eq_zero_iff _ (k0ToC l).injective).1 h1`. Establish `hcK : ∀ i : Fin 2, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0` using `fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hlog0`. Establish `hsK : MvPowerSeries.HasSubst (fun i : Fin 2 => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hcK`. Use `set c : Fin 2 → MvPowerSeries (Fin 2) ℂ_[l] := fun i => PowerSeries.subst (MvPowerSeries.X i) Lc with hcdef`.

Establish `hcC : ∀ i, MvPowerSeries.constantCoeff (c i) = 0` using `fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hL0`. Establish `hsC : MvPowerSeries.HasSubst c` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hcC`. Establish `hB : MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)) = MvPowerSeries.subst c (Formalism.L2.G.Pend.beC g e)`. Unfold `inParam`. Rewrite using `[MvPowerSeries.map_subst hsK]`.

Establish `hc' : (fun i : Fin 2 => MvPowerSeries.map (k0ToC l) (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l))) = c`. Use function extensionality and compare the values at `i`. Rewrite using `[PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)), MvPowerSeries.map_X, lgF_eq_logF]`. Rewrite using `[hc']`. Use `congr 1`.

Conclude with `Formalism.L2.G.Pend.map_beOf hb`. Establish `h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.C e⁻¹ * MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) = 0`. Introduce `i`. Rewrite using `[map_mul, MvPowerSeries.constantCoeff_X, mul_zero]`. Unfold `Formalism.L2.G.Pend.beC at hB`.

Rewrite `hB` using `[Formalism.MainNotions.J.be_subst g hex hsC (Formalism.MainNotions.J.cc_pt g hex (h0 0)) (Formalism.MainNotions.J.cc_pt g hex (h0 1)), Formalism.MainNotions.J.pt_subst g hsC (h0 0), Formalism.MainNotions.J.pt_subst g hsC (h0 1), MvPowerSeries.subst_mul hsC, MvPowerSeries.subst_mu …`. Rewrite using `[hB]`. Establish `hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0`. Rewrite using `[map_mul, hL0, mul_zero]`. Establish `hvS : PowerSeries.HasSubst (PowerSeries.C e⁻¹ * Lc)` using `PowerSeries.HasSubst.of_constantCoeff_zero' hv0`.

Establish `hvcc : PowerSeries.constantCoeff (vLT hLT) = 0` using `PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex`. Establish `hcA : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.C e⁻¹ * c i) = 0`. Introduce `i`. Rewrite using `[map_mul, hcC i, mul_zero]`. Establish `hat : ∀ i : Fin 2, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) (vLT hLT) = g.pt (MvPowerSeries.C e⁻¹ * c i)`.

Introduce `i`. Unfold `vLT`. Rewrite using `[PowerSeries.subst_comp_subst_apply hvS (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]`. Unfold `G1.pt`. Use `congr 1`.

Rewrite using `[PowerSeries.subst_mul (PowerSeries.HasSubst.X i), PowerSeries.subst_C]`. Establish `hpsi : ∀ i : Fin 2, at1 i (psiLT hLT) = g.phAt (g.pt (MvPowerSeries.C e⁻¹ * c i))`. Introduce `i`. Unfold `at1 psiLT`. Rewrite using `[PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc) (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)), hat i]`.

Both sides reduce to the same expression. Establish `hlgA : ∀ i, g.lg (g.pt (MvPowerSeries.C e⁻¹ * c i)) = MvPowerSeries.C e⁻¹ * c i`. Introduce `i`. Unfold `G1.lg G1.pt`. Rewrite using `[← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex) (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i)), hinv, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i))]`.

Use `set Fc := MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F with hFc`. Establish `hFc0 : MvPowerSeries.constantCoeff Fc = 0`. Rewrite using `[hFc, MvPowerSeries.constantCoeff_map, hF.1, map_zero]`. Establish `hLaw : PowerSeries.subst Fc Lc = c 0 + c 1`. Establish `h` using `congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) hF.2.2`.

Rewrite `h` using `[map_cob _ F hF.1, map_zero, Formalism.L2.Th1.E.Joints.map_lgF']`. Unfold `cob at1 at h`. Rewrite `h` using `[← hFc]`. Use `show _ = PowerSeries.subst (MvPowerSeries.X 0) Lc + PowerSeries.subst (MvPowerSeries.X 1) Lc`. Take the linear combination `h`.

Establish `hadd : g.add (g.pt (MvPowerSeries.C e⁻¹ * c 0)) (g.pt (MvPowerSeries.C e⁻¹ * c 1)) = PowerSeries.subst Fc (vLT hLT)`. Unfold `G1.add`. Rewrite using `[hlgA 0, hlgA 1, ← mul_add, ← hLaw]`. Unfold `vLT G1.pt`. Rewrite using `[PowerSeries.subst_comp_subst_apply hvS (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]`.

Use `congr 1`. Rewrite using `[PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hFc0), PowerSeries.subst_C]`. Unfold `G1.be cob`. Rewrite using `[hadd, ← hpsi 0, ← hpsi 1]`. Unfold `G1.phAt psiLT`.

Rewrite using `[PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc) (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]`.
-/
theorem cobExact : Formalism.L2.KerInert.BeCob.CobExact := by
  intro l _ g hLT hOk hb F hF
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' ℂ_[l] l
  have hlog0 : PowerSeries.constantCoeff (Formalism.MainNotions.FormalGroupSystem.logF l) = 0 := by
    have h1 : k0ToC l (PowerSeries.coeff 0 (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 := by
      rw [← PowerSeries.coeff_map, lgF_eq_logF, PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact cc_lgF' ℂ_[l] l
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (map_eq_zero_iff _ (k0ToC l).injective).1 h1
  have hcK : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hlog0
  have hsK : MvPowerSeries.HasSubst (fun i : Fin 2 =>
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hcK
  set c : Fin 2 → MvPowerSeries (Fin 2) ℂ_[l] := fun i => PowerSeries.subst (MvPowerSeries.X i) Lc with hcdef
  have hcC : ∀ i, MvPowerSeries.constantCoeff (c i) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hL0
  have hsC : MvPowerSeries.HasSubst c := MvPowerSeries.hasSubst_of_constantCoeff_zero hcC
  have hB : MvPowerSeries.map (k0ToC l) (inParam l (beLT hLT)) =
      MvPowerSeries.subst c (Formalism.L2.G.Pend.beC g e) := by
    unfold inParam
    rw [MvPowerSeries.map_subst hsK]
    have hc' : (fun i : Fin 2 => MvPowerSeries.map (k0ToC l)
        (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) (K0 l)) (Formalism.MainNotions.FormalGroupSystem.logF l))) = c := by
      funext i
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
        MvPowerSeries.map_X, lgF_eq_logF]
    rw [hc']
    congr 1
    exact Formalism.L2.G.Pend.map_beOf hb
  have h0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (MvPowerSeries.C e⁻¹ * MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) = 0 := by
    intro i
    rw [map_mul, MvPowerSeries.constantCoeff_X, mul_zero]
  unfold Formalism.L2.G.Pend.beC at hB
  rw [Formalism.MainNotions.J.be_subst g hex hsC (Formalism.MainNotions.J.cc_pt g hex (h0 0)) (Formalism.MainNotions.J.cc_pt g hex (h0 1)),
    Formalism.MainNotions.J.pt_subst g hsC (h0 0), Formalism.MainNotions.J.pt_subst g hsC (h0 1), MvPowerSeries.subst_mul hsC,
    MvPowerSeries.subst_mul hsC, MvPowerSeries.subst_C, MvPowerSeries.subst_X hsC, MvPowerSeries.subst_X hsC] at hB
  rw [hB]

  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hvS : PowerSeries.HasSubst (PowerSeries.C e⁻¹ * Lc) := PowerSeries.HasSubst.of_constantCoeff_zero' hv0
  have hvcc : PowerSeries.constantCoeff (vLT hLT) = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hcA : ∀ i, MvPowerSeries.constantCoeff (MvPowerSeries.C e⁻¹ * c i) = 0 := by
    intro i; rw [map_mul, hcC i, mul_zero]
  have hat : ∀ i : Fin 2, PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) ℂ_[l]) (vLT hLT) =
      g.pt (MvPowerSeries.C e⁻¹ * c i) := by
    intro i
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply hvS
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]
    unfold G1.pt
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X i), PowerSeries.subst_C]
  have hpsi : ∀ i : Fin 2, at1 i (psiLT hLT) = g.phAt (g.pt (MvPowerSeries.C e⁻¹ * c i)) := by
    intro i
    unfold at1 psiLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)), hat i]
    rfl
  have hlgA : ∀ i, g.lg (g.pt (MvPowerSeries.C e⁻¹ * c i)) = MvPowerSeries.C e⁻¹ * c i := by
    intro i
    unfold G1.lg G1.pt
    rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
      (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i)), hinv,
      PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero (hcA i))]
  set Fc := MvPowerSeries.map (MaximalUnramifiedExtension l).subtype F with hFc
  have hFc0 : MvPowerSeries.constantCoeff Fc = 0 := by
    rw [hFc, MvPowerSeries.constantCoeff_map, hF.1, map_zero]
  have hLaw : PowerSeries.subst Fc Lc = c 0 + c 1 := by
    have h := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) hF.2.2
    rw [map_cob _ F hF.1, map_zero, Formalism.L2.Th1.E.Joints.map_lgF'] at h
    unfold cob at1 at h
    rw [← hFc] at h
    show _ = PowerSeries.subst (MvPowerSeries.X 0) Lc + PowerSeries.subst (MvPowerSeries.X 1) Lc
    linear_combination h
  have hadd : g.add (g.pt (MvPowerSeries.C e⁻¹ * c 0)) (g.pt (MvPowerSeries.C e⁻¹ * c 1)) =
      PowerSeries.subst Fc (vLT hLT) := by
    unfold G1.add
    rw [hlgA 0, hlgA 1, ← mul_add, ← hLaw]
    unfold vLT G1.pt
    rw [PowerSeries.subst_comp_subst_apply hvS (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]
    congr 1
    rw [PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hFc0), PowerSeries.subst_C]
  unfold G1.be cob
  rw [hadd, ← hpsi 0, ← hpsi 1]
  unfold G1.phAt psiLT
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hvcc)
    (PowerSeries.HasSubst.of_constantCoeff_zero hFc0)]

end GlobalTheory.CobExactProof
