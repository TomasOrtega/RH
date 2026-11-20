import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ExSummand
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLetterCentralExponentProperties

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

/- English proof (translation)
Introduce `E _ _ _ n μ _ π hn`. Set `x : GlobalTheory.ResW.Letter E` to `⟨n, π⟩`. Establish `hd : ((n : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')`. Set `z : ℂ` to `-GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ E : ℂ))`. Set `χ : Formalism.L2.Host.HChar E` to `GlobalTheory.CuspRep.Model.absC E z`.

Establish `hspec` using `(GlobalTheory.ResW.letter_centralExponent E x).1`. Establish `htr : (Matrix.of (GlobalTheory.CuspRep.oneL E n)).trace = (n : ℝ) • (1 : GlobalTheory.CuspRep.Cinf E)`. Express the relevant statement in the definitionally equal form `(Matrix.of (fun i j : Fin n => if i = j then (1 : GlobalTheory.CuspRep.Cinf E) else 0)).trace = _`. Simplify using `[Matrix.trace, Nat.cast_smul_eq_nsmul]`. Establish `hz : ∀ φ ∈ (π.twist χ).V, GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) φ = 0`.

Introduce and unpack `_ ⟨ψ, hψ, rfl⟩`. Establish `e0 : GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) ψ = GlobalTheory.ResW.cex x • ψ` using `hspec ψ hψ`. Establish `e1 : GlobalTheory.CuspRep.dchi χ (Matrix.of (GlobalTheory.CuspRep.oneL E n)).trace = -GlobalTheory.ResW.cex x`. Rewrite using `[htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]`. Establish `hzd : z * ((n : ℂ) * (Module.finrank ℚ E : ℂ)) = -GlobalTheory.ResW.cex x` using `div_mul_cancel₀ _ hd`.

Simplify using `only [Complex.real_smul, Complex.ofReal_natCast]`. Take the linear combination `hzd`. Express the relevant statement in the definitionally equal form `GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) (GlobalTheory.CuspRep.mulChi n χ ψ) = 0`. Rewrite using `[GlobalTheory.CuspRep.lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]`. Take `⟨b, hb⟩` from `GlobalTheory.AbsTwist.exists_eq_mul_log_module (F := E) (GlobalTheory.Mem.Chr.CharModel.logNorm E) (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E) (GlobalTheory.Mem.Chr.CharModel.logNorm_mul E) (GlobalTheory.Mem.Chr.CharModel.logNorm_principal E)`.

Use `⟨χ, ⟨z * b, fun y => ?_⟩, _, (UpperTheory.ConvolutionTheory.Dp.exSummand E n μ (π.twist χ) _).2 ⟨Cm.carrier_le_central _ hz, rfl⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E y) = _`. Establish `hpos` using `(GroundTheory.Global.IdeleGroup.ideleModule E y).2`. Rewrite using `[hb y, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.Dp.exTwist :
    UpperTheory.ConvolutionTheory.Dp.ExTwist := by
  intro E _ _ _ n μ _ π hn
  let x : GlobalTheory.ResW.Letter E := ⟨n, π⟩
  have hd : ((n : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 (by omega)) (Nat.cast_ne_zero.2 Module.finrank_pos.ne')
  let z : ℂ := -GlobalTheory.ResW.cex x / ((n : ℂ) * (Module.finrank ℚ E : ℂ))
  let χ : Formalism.L2.Host.HChar E := GlobalTheory.CuspRep.Model.absC E z
  have hspec := (GlobalTheory.ResW.letter_centralExponent E x).1
  have htr : (Matrix.of (GlobalTheory.CuspRep.oneL E n)).trace = (n : ℝ) • (1 : GlobalTheory.CuspRep.Cinf E) := by
    change (Matrix.of (fun i j : Fin n => if i = j then (1 : GlobalTheory.CuspRep.Cinf E) else 0)).trace = _
    simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
  have hz : ∀ φ ∈ (π.twist χ).V, GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) φ = 0 := by
    rintro _ ⟨ψ, hψ, rfl⟩
    have e0 : GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) ψ = GlobalTheory.ResW.cex x • ψ := hspec ψ hψ
    have e1 : GlobalTheory.CuspRep.dchi χ (Matrix.of (GlobalTheory.CuspRep.oneL E n)).trace = -GlobalTheory.ResW.cex x := by
      rw [htr, map_smul, GlobalTheory.ResW.dchi_absC_one_finrank]
      have hzd : z * ((n : ℂ) * (Module.finrank ℚ E : ℂ)) = -GlobalTheory.ResW.cex x := div_mul_cancel₀ _ hd
      simp only [Complex.real_smul, Complex.ofReal_natCast]
      linear_combination hzd
    change GlobalTheory.CuspRep.lie E n (GlobalTheory.CuspRep.oneL E n) (GlobalTheory.CuspRep.mulChi n χ ψ) = 0
    rw [GlobalTheory.CuspRep.lie_mulChi, e0, e1, ← add_smul, add_neg_cancel, zero_smul, map_zero]
  obtain ⟨b, hb⟩ := GlobalTheory.AbsTwist.exists_eq_mul_log_module (F := E) (GlobalTheory.Mem.Chr.CharModel.logNorm E)
    (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E) (GlobalTheory.Mem.Chr.CharModel.logNorm_mul E)
    (GlobalTheory.Mem.Chr.CharModel.logNorm_principal E)
  refine ⟨χ, ⟨z * b, fun y => ?_⟩, _,
    (UpperTheory.ConvolutionTheory.Dp.exSummand E n μ (π.twist χ) _).2 ⟨Cm.carrier_le_central _ hz, rfl⟩⟩
  change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E y) = _
  have hpos := (GroundTheory.Global.IdeleGroup.ideleModule E y).2
  rw [hb y, Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'), ← Complex.ofReal_log hpos.le]
  congr 1
  push_cast
  ring
