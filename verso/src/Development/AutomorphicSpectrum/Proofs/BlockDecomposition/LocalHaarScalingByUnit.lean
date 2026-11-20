import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical
open scoped Pointwise

noncomputable section
namespace GlobalTheory.CompanionTheory.Haar

/- English proof (translation)
Establish `hn : (n : Fv F v) ≠ 0` using `n.ne_zero`. Establish `hva : Valued.v (n : Fv F v) ≠ 0` using `(Valuation.ne_zero_iff _).2 hn`. Establish `h` using `PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v (n : Fv F v) hn`. Rewrite `h` using `[PI.NglqJacSplitW.modF, dif_neg hn]`. Establish `hu : Units.mk0 (n : Fv F v) hn = n` using `by ext; rfl`.

Rewrite `h` using `[hu]`. Establish `habs : PI.LocJacTyp.absV v (n : Fv F v) = ‖(n : Fv F v)‖`. Unfold `PI.LocJacTyp.absV`. Rewrite using `[dif_neg hva, NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hva]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite `h` using `[habs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]`. Conclude with `(ENNReal.coe_injective h).symm`.
-/
theorem nnnorm_eq_distribHaarChar (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : (Fv F v)ˣ) :
    ‖(n : Fv F v)‖₊ = distribHaarChar (Fv F v) n := by
  have hn : (n : Fv F v) ≠ 0 := n.ne_zero
  have hva : Valued.v (n : Fv F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hn
  have h := PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v (n : Fv F v) hn
  rw [PI.NglqJacSplitW.modF, dif_neg hn] at h
  have hu : Units.mk0 (n : Fv F v) hn = n := by ext; rfl
  rw [hu] at h
  have habs : PI.LocJacTyp.absV v (n : Fv F v) = ‖(n : Fv F v)‖ := by
    unfold PI.LocJacTyp.absV
    rw [dif_neg hva, NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hva]
    push_cast
    rfl
  rw [habs, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal] at h
  exact (ENNReal.coe_injective h).symm

/- English proof (translation)
Establish `: SecondCountableTopology (Fv F v)` using `PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v`. Establish `: lam.Regular` using `inferInstance`. Establish `hc : Continuous fun t : Fv F v => (n : Fv F v) * t` using `continuous_const.mul continuous_id`. Use extensionality with `S hS`. Rewrite using `[Measure.map_apply hc.measurable hS, nnnorm_eq_distribHaarChar, ← map_inv]`.

Establish `hset : (fun t : Fv F v => (n : Fv F v) * t) ⁻¹' S = n⁻¹ • S`. Use extensionality with `y`. Rewrite using `[Set.mem_inv_smul_set_iff]`. Both sides reduce to the same expression. Rewrite using `[hset, ← distribHaarChar_mul lam n⁻¹ S]`.

Both sides reduce to the same expression.
-/
theorem map_mul_left (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (lam : Measure (Fv F v)) (hl : lam.IsAddHaarMeasure) (n : (Fv F v)ˣ) :
    lam.map (fun t => (n : Fv F v) * t) = (‖(n : Fv F v)‖₊)⁻¹ • lam := by
  have : SecondCountableTopology (Fv F v) := PI.UnitaryGroupMassFormula.LocJacTyp.BM.secondCountable_Fv v
  have : lam.Regular := inferInstance
  have hc : Continuous fun t : Fv F v => (n : Fv F v) * t := continuous_const.mul continuous_id
  ext S hS
  rw [Measure.map_apply hc.measurable hS, nnnorm_eq_distribHaarChar, ← map_inv]
  have hset : (fun t : Fv F v => (n : Fv F v) * t) ⁻¹' S = n⁻¹ • S := by
    ext y
    rw [Set.mem_inv_smul_set_iff]
    rfl
  rw [hset, ← distribHaarChar_mul lam n⁻¹ S]
  rfl

end GlobalTheory.CompanionTheory.Haar
