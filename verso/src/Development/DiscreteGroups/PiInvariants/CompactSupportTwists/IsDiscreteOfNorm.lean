import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.DescentOfLocalGlobalInputs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapPFinThetaGL
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ExistsHasInfCharGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.ContinuousAT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsConjSelfDualOfInvTransposeIsoCmConj

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace DiscreteGroups.T1.G

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `e : GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g) * (PhiU n (Ad E))⁻¹` using `rfl`. Rewrite using `[e]`. Use `congr 2`.
-/
theorem thetaA_eq (g : GA E n) :
    GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * PositivityTheory.Rg.BcB.thetaA E n g * (PhiU n (Ad E))⁻¹ := by
  have e : GlobalTheory.ThetaPull.thetaA E n g = PhiU n (Ad E) * invT n (Ad E) (GeneralLinearGroup.map (conjAd E) g) *
      (PhiU n (Ad E))⁻¹ := rfl
  rw [e]
  congr 2

omit [IsCMField E] in

/- English proof (translation)
The claim follows from `(GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU (algebraMap E (Ad E)) n).symm`.
-/
theorem phiU_ad : PhiU n (Ad E) = ratGL E n (PhiU n E) :=
  (GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU (algebraMap E (Ad E)) n).symm

/- English proof (translation)
Use `ga_ext ?_ ?_` and prove the remaining obligations. Simplify using `[GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CsdFromConj.toUnits_PhiK, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]`. Simplify using `[GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]`.
-/
theorem phiU_eq_phiG : PhiU n (Ad E) = GlobalTheory.CsdFromConj.phiG E n := by
  refine ga_ext ?_ ?_
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CsdFromConj.toUnits_PhiK, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]
  · simp [GlobalTheory.CsdFromConj.phiG, map_mul, GlobalTheory.CompanionTheory.AdelEqProof.map_PhiU]

/- English proof (translation)
Establish `h` using `((GlobalTheory.CsdFromConj.phiEquiv π).symm ⟨φ, hφ⟩).2`. Use `h using 1` and compare the differences between its conclusion and the goal. Use `Subtype.ext (funext fun x => ?_)` and prove the remaining obligations. Rewrite using `[phiU_eq_phiG]`. Simplify using `[GlobalTheory.CsdFromConj.phiEquiv, GlobalTheory.CsdFromConj.phiG, CuspSub.op, mul_assoc]`.

Use `show φ.1 _ = φ.1 (x * infGL E n (Unitary.toUnits (PhiK E n)⁻¹) * finGL E n (PhiU n (Af E))⁻¹)`. Simplify using `only [map_inv, mul_assoc]`.
-/
theorem rt_phiU_inv_mem (π : CuspSub E n) {φ : Sm E n} (hφ : φ ∈ π.V) : rt E n (PhiU n (Ad E))⁻¹ φ ∈ π.V := by
  have h := ((GlobalTheory.CsdFromConj.phiEquiv π).symm ⟨φ, hφ⟩).2
  convert h using 1
  refine Subtype.ext (funext fun x => ?_)
  rw [phiU_eq_phiG]
  simp [GlobalTheory.CsdFromConj.phiEquiv, GlobalTheory.CsdFromConj.phiG, CuspSub.op, mul_assoc]
  show φ.1 _ = φ.1 (x * infGL E n (Unitary.toUnits (PhiK E n)⁻¹) * finGL E n (PhiU n (Af E))⁻¹)
  simp only [map_inv, mul_assoc]

/- English proof (translation)
Establish `hp : ∀ φ ∈ π.V, GlobalTheory.ThetaPull.pull E n φ ∈ π.V`. Introduce `φ hφ`. Take `⟨ψ', hψ', e⟩` from `h.2 _ (rt_phiU_inv_mem π hφ)`. Use `hψ' using 1` and compare the differences between its conclusion and the goal. Use `Subtype.ext (funext fun g => ?_)` and prove the remaining obligations.

Rewrite using `[GlobalTheory.ThetaPull.pull_apply, e, rt_apply, thetaA_eq, phiU_ad, mul_assoc, (π.cusp φ hφ).1.left]`. Use `⟨LinearEquiv.ofInvolutive ((GlobalTheory.ThetaPull.pull E n).toLinearMap.restrict hp) (fun φ => Subtype.ext (GlobalTheory.ThetaPull.pull_pull φ.1)), fun o φ => Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.ThetaPull.pull E n (act (thetaOp o) φ.1) = act o (GlobalTheory.ThetaPull.pull E n φ.1)`. Conclude with `(GlobalTheory.ThetaPull.act_pull o φ.1).symm`.
-/
theorem isCsd_of_thetaFix {π : CuspSub E n} (h : ThetaFix π) : π.IsCsd := by
  have hp : ∀ φ ∈ π.V, GlobalTheory.ThetaPull.pull E n φ ∈ π.V := by
    intro φ hφ
    obtain ⟨ψ', hψ', e⟩ := h.2 _ (rt_phiU_inv_mem π hφ)
    convert hψ' using 1
    refine Subtype.ext (funext fun g => ?_)
    rw [GlobalTheory.ThetaPull.pull_apply, e, rt_apply, thetaA_eq, phiU_ad, mul_assoc, (π.cusp φ hφ).1.left]
  refine ⟨LinearEquiv.ofInvolutive ((GlobalTheory.ThetaPull.pull E n).toLinearMap.restrict hp)
    (fun φ => Subtype.ext (GlobalTheory.ThetaPull.pull_pull φ.1)), fun o φ => Subtype.ext ?_⟩
  change GlobalTheory.ThetaPull.pull E n (act (thetaOp o) φ.1) = act o (GlobalTheory.ThetaPull.pull E n φ.1)
  exact (GlobalTheory.ThetaPull.act_pull o φ.1).symm

/- English proof (translation)
The claim follows from `isDiscrete_of_cuspSub π fun φ hφ => by obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ exact GlobalTheory.DiscChar.isSqInt_of_bounded (hN φ hφ) (C := C) fun g => by simpa using hC g`.
-/
theorem isDiscrete_of_norm {π : CuspSub E n} (hu : π.IsUnitary)
    (hN : ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) : IsDiscrete π.V :=
  isDiscrete_of_cuspSub π fun φ hφ => by
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL.of_isUnitary hu hφ
    exact GlobalTheory.DiscChar.isSqInt_of_bounded (hN φ hφ) (C := C) fun g => by simpa using hC g

/- English proof (translation)
Establish `h1 : (CG.mk π).HasInfChar τ m` using `hm`. Take `⟨hnd, hz⟩` from `hreg τ`. Rewrite `hnd`, `hz` using `[h1.infChar_eq]`. Take `⟨lam, hl⟩` from `GlobalTheory.WtComb.exists_domWeight_infOf n m hm.1 hnd hz`. Conclude with `⟨lam, hl.symm.trans (GlobalTheory.UnitaryReadTrue.infOf_eq_infOfWeight lam)⟩`.
-/
theorem reg_of {π : CuspSub E n} (hreg : (CG.mk π).IsRegAlg) {τ : E →+* ℂ} {m : Multiset ℂ}
    (hm : HasInfCharGL π.V τ m) : ∃ lam : DomWeight n, m = infOfWeight lam := by
  have h1 : (CG.mk π).HasInfChar τ m := hm
  obtain ⟨hnd, hz⟩ := hreg τ
  rw [h1.infChar_eq] at hnd hz
  obtain ⟨lam, hl⟩ := GlobalTheory.WtComb.exists_domWeight_infOf n m hm.1 hnd hz
  exact ⟨lam, hl.symm.trans (GlobalTheory.UnitaryReadTrue.infOf_eq_infOfWeight lam)⟩

/- English proof (translation)
Introduce `E _ _ _ n hn π hreg hd`. Establish `hT` using `hF E n hn π hd`. Establish `hu : π.IsUnitary` using `(CG.isUnitary_mk π).1 (hU E n hn π hd)`. Establish `hD : IsDiscrete π.V` using `isDiscrete_of_norm hu hT.1`. Use `choose σ hσ using fun w => GlobalTheory.DiscLocEx.exists_isLocCompGL PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n π.V hD w`.

Use `choose m hm using fun τ => PositivityTheory.Rg.Rs.PInfInd2A.exists_hasInfCharGL hD τ`. Set `D : Pre E n` to `⟨1, fun _ => n, by simp, fun _ => π.V, fun _ w => σ w, fun _ τ => m τ, fun _ => hn, fun _ => hD, fun _ w => hσ w, fun _ τ => hm τ⟩`. Establish `hcsd : PositivityTheory.Rg.BcN.CsdAsc π.V` using `⟨n, 1, π, hu, GlobalTheory.DiscSpec.isNormalised_of_isDiscrete hD, isCsd_of_thetaFix hT, PositivityTheory.Rg.Rs.PDich.ascEmb_one ⟨LinearEquiv.refl ℂ π.V, fun _ _ => rfl⟩⟩`. Use `⟨D, ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, fun τ => ?_, hA E n D fun _ => hcsd⟩` and prove the remaining obligations. Take `⟨lam, hl⟩` from `reg_of hreg (hm τ)`.

Conclude with `⟨lam, by simpa [D] using hl⟩`.
-/
theorem oneEx_of (hF : ThetaFixOf) (hU : UnitOf) (hA : Rig.ThetaOfAsc) : OneEx := by
  intro E _ _ _ n hn π hreg hd
  have hT := hF E n hn π hd
  have hu : π.IsUnitary := (CG.isUnitary_mk π).1 (hU E n hn π hd)
  have hD : IsDiscrete π.V := isDiscrete_of_norm hu hT.1
  choose σ hσ using fun w => GlobalTheory.DiscLocEx.exists_isLocCompGL PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E n π.V hD w
  choose m hm using fun τ => PositivityTheory.Rg.Rs.PInfInd2A.exists_hasInfCharGL hD τ
  let D : Pre E n := ⟨1, fun _ => n, by simp, fun _ => π.V, fun _ w => σ w, fun _ τ => m τ, fun _ => hn,
    fun _ => hD, fun _ w => hσ w, fun _ τ => hm τ⟩
  have hcsd : PositivityTheory.Rg.BcN.CsdAsc π.V :=
    ⟨n, 1, π, hu, GlobalTheory.DiscSpec.isNormalised_of_isDiscrete hD, isCsd_of_thetaFix hT,
      PositivityTheory.Rg.Rs.PDich.ascEmb_one ⟨LinearEquiv.refl ℂ π.V, fun _ _ => rfl⟩⟩
  refine ⟨D, ⟨rfl, fun _ => ⟨rfl, rfl⟩⟩, fun τ => ?_, hA E n D fun _ => hcsd⟩
  obtain ⟨lam, hl⟩ := reg_of hreg (hm τ)
  exact ⟨lam, by simpa [D] using hl⟩

end DiscreteGroups.T1.G

end
