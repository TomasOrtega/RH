import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.MemSEOfFin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertKStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnitEqMulConjK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.InertCompletionIsField

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF Formalism.IndefR.LiftF
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeExtend GlobalTheory.HeckeExtend.AtInf GlobalTheory.SplitDetCharF
namespace PositivityTheory.ThKW.Eta
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
/- English proof (translation)
Take `⟨δ, b, hδ, hb0, hb1, hbb⟩` from `GlobalTheory.QuadNormBase.exists_basis F E σ hB.cm.2.2.1 (sig_invol hB.cm) (sig_ne hB.cm)`. Establish `hbb' : b 1 * b 1 = algebraMap F E δ` using `hbb`. Use `(GlobalTheory.QuadSymbol.mem_normGroup_iff_form b hb0 hbb').2 ?_` and prove the remaining obligations. Break down `_root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩` into its components or cases. Establish `hs : τ (b 1) * τ (b 1) = algebraMap F (Fv F v) δ` using `by rw [← map_mul, hbb', AlgHom.commutes]`.

Establish `hs0 : τ (b 1) ≠ 0` using `(map_ne_zero τ).2 (b.ne_zero 1)`. Establish `h20 : (2 : Fv F v) ≠ 0`. Rewrite using `[← map_ofNat (algebraMap F (Fv F v)) 2]`. Conclude with `(map_ne_zero _).2 two_ne_zero`. Use `⟨((u : Fv F v) + 1) / 2, ((u : Fv F v) - 1) / (2 * τ (b 1)), ?_⟩` and prove the remaining obligations.

Rewrite using `[← hs]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hv2 : Valued.v (2 : Fv F v) = 1`. Establish `e : (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2)` using `by rw [map_ofNat, map_ofNat]`.

Rewrite using `[e]`. Use `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_` and prove the remaining obligations. Use `le_antisymm (v.valuation_le_one 2) (not_lt.1 fun h => (hB.inert v w hw).1 ?_)` and prove the remaining obligations. Conclude with `(v.valuation_lt_one_iff_mem 2).1 h`. Establish `a1 : Valued.v (2 * (u : Fv F v)) ≤ 1` using `h1`.

Establish `a2 : Valued.v (2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v)) ≤ 1` using `h2`. Rewrite `a1`, `a2` using `[map_mul, hv2, one_mul]`. Establish `hu : Valued.v (u : Fv F v) = 1`. Use `le_antisymm a1 ?_` and prove the remaining obligations. Establish `hm` using `congrArg Valued.v u.mul_inv`.

Rewrite `hm` using `[map_mul, map_one]`. Rewrite using `[← hm]`. Conclude with `mul_le_of_le_one_right' a2`. Take `⟨z, hz⟩` from `_root_.GlobalTheory.InertUnitNorm.unit_eq_mul_conj_k F E σ B hB v w hw (_root_.GlobalTheory.T.inert_completion_isField F E σ B hB v w hw) u hu`. Take `⟨x, y, rfl⟩` from `tensor_decomp (A := Fv F v) (b 1) (fun x => ⟨b.repr x 0, b.repr x 1, by`.

Establish `hx` using `b.sum_repr x`. Rewrite `hx` using `[Fin.sum_univ_two, hb0]`. Conclude with `hx.symm⟩) z`. Use `⟨x, y, tensor_inj (F := F) (E := E) ?_⟩` and prove the remaining obligations. Establish `e1 : ((1 : Fv F v) ⊗ₜ[F] b 1) * ((1 : Fv F v) ⊗ₜ[F] b 1) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) δ)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb', ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']`. Rewrite using `[hz, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hb1, TensorProduct.tmul_neg, map_sub, map_mul, map_pow, map_pow, ← e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem local_norm_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) (v : HeightOneSpectrum (𝓞 F)) (u : (Fv F v)ˣ)
    (h1 : 2 * (u : Fv F v) ∈ v.adicCompletionIntegers F)
    (h2 : 2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F) :
    u ∈ GlobalTheory.QuadSymbol.normGroup F E (Fv F v) := by
  obtain ⟨δ, b, hδ, hb0, hb1, hbb⟩ :=
    GlobalTheory.QuadNormBase.exists_basis F E σ hB.cm.2.2.1 (sig_invol hB.cm) (sig_ne hB.cm)
  have hbb' : b 1 * b 1 = algebraMap F E δ := hbb
  refine (GlobalTheory.QuadSymbol.mem_normGroup_iff_form b hb0 hbb').2 ?_
  rcases _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK F E σ B hB v with ⟨⟨τ⟩⟩ | ⟨w, hw⟩
  · have hs : τ (b 1) * τ (b 1) = algebraMap F (Fv F v) δ := by rw [← map_mul, hbb', AlgHom.commutes]
    have hs0 : τ (b 1) ≠ 0 := (map_ne_zero τ).2 (b.ne_zero 1)
    have h20 : (2 : Fv F v) ≠ 0 := by
      rw [← map_ofNat (algebraMap F (Fv F v)) 2]
      exact (map_ne_zero _).2 two_ne_zero
    refine ⟨((u : Fv F v) + 1) / 2, ((u : Fv F v) - 1) / (2 * τ (b 1)), ?_⟩
    rw [← hs]
    field_simp
    ring
  · have hv2 : Valued.v (2 : Fv F v) = 1 := by
      have e : (2 : Fv F v) = algebraMap F (Fv F v) (algebraMap (𝓞 F) F 2) := by rw [map_ofNat, map_ofNat]
      rw [e]
      refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans ?_
      refine le_antisymm (v.valuation_le_one 2) (not_lt.1 fun h => (hB.inert v w hw).1 ?_)
      exact (v.valuation_lt_one_iff_mem 2).1 h
    have a1 : Valued.v (2 * (u : Fv F v)) ≤ 1 := h1
    have a2 : Valued.v (2 * ((u⁻¹ : (Fv F v)ˣ) : Fv F v)) ≤ 1 := h2
    rw [map_mul, hv2, one_mul] at a1 a2
    have hu : Valued.v (u : Fv F v) = 1 := by
      refine le_antisymm a1 ?_
      have hm := congrArg Valued.v u.mul_inv
      rw [map_mul, map_one] at hm
      rw [← hm]
      exact mul_le_of_le_one_right' a2
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.InertUnitNorm.unit_eq_mul_conj_k F E σ B hB v w hw (_root_.GlobalTheory.T.inert_completion_isField F E σ B hB v w hw) u hu
    obtain ⟨x, y, rfl⟩ := tensor_decomp (A := Fv F v) (b 1) (fun x => ⟨b.repr x 0, b.repr x 1, by
      have hx := b.sum_repr x
      rw [Fin.sum_univ_two, hb0] at hx
      exact hx.symm⟩) z
    refine ⟨x, y, tensor_inj (F := F) (E := E) ?_⟩
    have e1 : ((1 : Fv F v) ⊗ₜ[F] b 1) * ((1 : Fv F v) ⊗ₜ[F] b 1) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) δ) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hbb', ← IsScalarTower.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply']
    rw [hz, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hb1,
      TensorProduct.tmul_neg, map_sub, map_mul, map_pow, map_pow, ← e1]
    ring
end PositivityTheory.ThKW.Eta
end
end
