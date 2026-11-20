import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBCovN
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFundDomainVolumeClassicalStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovNFormulaPf

/- English proof (translation)
Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.coe_nnreal_smul_apply, Measure.pi_pi]`. Simplify using `only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]`.
-/
theorem pi_const_smul' {ι : Type} [Fintype ι] {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (c : NNReal) :
    Measure.pi (fun _ : ι => c • μ) = (c ^ Fintype.card ι) • Measure.pi (fun _ : ι => μ) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.pi_pi]
  simp only [Measure.coe_nnreal_smul_apply, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ENNReal.coe_pow]

/- English proof (translation)
Introduce `D X Y θ C u hθ`. Use `haveI : SigmaFinite (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := (GlobalTheory.haarLie_isHaarOn_Nset D.R.k D.R.rS 1 one_pos ENNReal.one_lt_top).1`. Establish `hI` using `GlobalTheory.T.transportedFundDomain_volume_classical D X Y θ C u`. Use `set v2 : ℝ := 2 * D.host.v with hv2`. Establish `hv : 0 < v2` using `lt_of_lt_of_le one_pos (Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D)`.

Use `set t : ℝ := v2 ^ (-((D.R.rS : ℝ) * D.R.k)) * θ with ht`. Establish `ht0 : 0 ≤ t` using `by positivity`. Establish `hk : kapN D θ = ((Real.toNNReal t : NNReal) : ℝ≥0∞)` using `rfl`. Establish `hmu : muNB D θ = (Real.toNNReal t) • haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1`. Establish `e : ∀ κ : ℝ≥0∞, haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) κ = κ • haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1`.

Introduce `κ`. Simplify using `[haarLie]`. Unfold `muNB`. Rewrite using `[hk, e]`. Use extensionality with `s _`.

Rewrite using `[Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul]`. Unfold `Formalism.L2.SG.LoopTerm.covN Formalism.L2.SG.LoopTerm.dnB`. Rewrite using `[hmu, pi_const_smul', Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_pow, Real.coe_toNNReal _ ht0]`. Unfold `Formalism.L2.SG.LoopTerm.trInf`. Rewrite using `[hI, Real.rpow_mul_natCast hv.le, ← mul_pow, ht]`.

Use `congr 1`. Unfold `Formalism.L2.SG.Pf.LoopBCovN.eN`. Rewrite using `[mul_comm _ θ, mul_assoc, ← Real.rpow_add hv]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : Formalism.L2.SG.Pf.LoopBCovN.CovNFormula := by
  intro D X Y θ C u hθ
  haveI : SigmaFinite (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) :=
    (GlobalTheory.haarLie_isHaarOn_Nset D.R.k D.R.rS 1 one_pos ENNReal.one_lt_top).1
  have hI := GlobalTheory.T.transportedFundDomain_volume_classical D X Y θ C u
  set v2 : ℝ := 2 * D.host.v with hv2
  have hv : 0 < v2 := lt_of_lt_of_le one_pos (Formalism.L2.SG.Pf.LoopBCovN.rdE_ge_one D)
  set t : ℝ := v2 ^ (-((D.R.rS : ℝ) * D.R.k)) * θ with ht
  have ht0 : 0 ≤ t := by positivity
  have hk : kapN D θ = ((Real.toNNReal t : NNReal) : ℝ≥0∞) := rfl
  have hmu : muNB D θ = (Real.toNNReal t) • haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1 := by
    have e : ∀ κ : ℝ≥0∞, haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) κ = κ • haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1 := by
      intro κ; simp [haarLie]
    unfold muNB
    rw [hk, e]
    ext s _
    rw [Measure.coe_nnreal_smul_apply, Measure.smul_apply, smul_eq_mul]
  unfold Formalism.L2.SG.LoopTerm.covN Formalism.L2.SG.LoopTerm.dnB
  rw [hmu, pi_const_smul', Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul, ENNReal.coe_toReal,
    NNReal.coe_pow, Real.coe_toNNReal _ ht0]
  unfold Formalism.L2.SG.LoopTerm.trInf
  rw [hI, Real.rpow_mul_natCast hv.le, ← mul_pow, ht]
  congr 1
  unfold Formalism.L2.SG.Pf.LoopBCovN.eN
  rw [mul_comm _ θ, mul_assoc, ← Real.rpow_add hv]
  congr 2
  ring

end GlobalTheory.CovNFormulaPf
