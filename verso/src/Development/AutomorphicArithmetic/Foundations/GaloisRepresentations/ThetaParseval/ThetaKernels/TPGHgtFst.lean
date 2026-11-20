import Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEDetUnitary
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtInt

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl
namespace UpperTheory.TP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}
/- English proof (translation)
Establish `hp : IsPar (e (g, g)) (g : GL (Fin n) (AE F E))`. Express the relevant statement in the definitionally equal form `mat2 (e (g, g)) * diagCols (E := AE F E) (Fin n) = diagCols (E := AE F E) (Fin n) * mat g`. Rewrite using `[he, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]`. Simplify using the standard rewrite rules. Establish `e1 : e (g, 1) = e (g, g) * e (1, g⁻¹)`.

Rewrite using `[← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel]`. Rewrite using `[e1, ha.mul hp, GlobalTheory.WeilEx.Jac.absE_det_unitary hJ g]`. Simplify using the standard rewrite rules.
-/
private theorem hgt_swap_pk (hJ : X.J.det ≠ 0) {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a)
    {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) (g : UA σ X.J) :
    a (e (g, 1)) = a (e (1, g⁻¹)) := by
  have hp : IsPar (e (g, g)) (g : GL (Fin n) (AE F E)) := by
    change mat2 (e (g, g)) * diagCols (E := AE F E) (Fin n) = diagCols (E := AE F E) (Fin n) * mat g
    rw [he, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp
  have e1 : e (g, 1) = e (g, g) * e (1, g⁻¹) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel]
  rw [e1, ha.mul hp, GlobalTheory.WeilEx.Jac.absE_det_unitary hJ g]
  simp
end UpperTheory.TP
/- English proof (translation)
Introduce `T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he`. Establish `cX` using `T.cpt F E σ B n X n 0 hB (.inl hX) (by simp)`. Use `haveI := cX.lc`. Use `haveI := cX.sc`. Take `⟨μ₀, D, hμ₀, -⟩` from `cX.ex`.

Take `⟨t₀, ht₀⟩` from `_root_.GlobalTheory.ThK.Dbl.hgtInt_of_k T.stab2 F E σ B n X n 0 hB (.inl hX) K a e hK ha he μ₀ hμ₀`. Use `⟨t₀, fun μ hμ t ht => ?_⟩` and prove the remaining obligations. Use `haveI := hμ`. Use `haveI := hμ₀`. Use `haveI := cX.right μ hμ`.

Establish `hJ : X.J.det ≠ 0` using `GlobalTheory.ThK.Dbl.Hgt.det_ne (.inl hX)`. Establish `h1 : Integrable (fun g => a (e (1, g)) ^ t) μ`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul μ μ₀]`. Conclude with `(ht₀ t ht).smul_measure ENNReal.coe_ne_top`. Take `⟨c, -, hc⟩` from `inv_scale μ`.

Establish `h2 : Integrable (fun g => ((a (e (g, 1)) ^ t : ℝ) : ℂ)) μ` using `(hc _).1 (by`. Simplify using `only [UpperTheory.TP.hgt_swap_pk hJ ha he, inv_inv]`. Conclude with `h1.ofReal)`. Simplify using `using h2.re`.
-/
theorem UpperTheory.TP.hgtFst_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.HgtFst_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he
  have cX := T.cpt F E σ B n X n 0 hB (.inl hX) (by simp)
  haveI := cX.lc
  haveI := cX.sc
  obtain ⟨μ₀, D, hμ₀, -⟩ := cX.ex
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.ThK.Dbl.hgtInt_of_k T.stab2 F E σ B n X n 0 hB (.inl hX) K a e hK ha he μ₀ hμ₀
  refine ⟨t₀, fun μ hμ t ht => ?_⟩
  haveI := hμ
  haveI := hμ₀
  haveI := cX.right μ hμ
  have hJ : X.J.det ≠ 0 := GlobalTheory.ThK.Dbl.Hgt.det_ne (.inl hX)
  have h1 : Integrable (fun g => a (e (1, g)) ^ t) μ := by
    rw [Measure.isMulLeftInvariant_eq_smul μ μ₀]
    exact (ht₀ t ht).smul_measure ENNReal.coe_ne_top
  obtain ⟨c, -, hc⟩ := inv_scale μ
  have h2 : Integrable (fun g => ((a (e (g, 1)) ^ t : ℝ) : ℂ)) μ := (hc _).1 (by
    simp only [UpperTheory.TP.hgt_swap_pk hJ ha he, inv_inv]
    exact h1.ofReal)
  simpa using h2.re
end
end
