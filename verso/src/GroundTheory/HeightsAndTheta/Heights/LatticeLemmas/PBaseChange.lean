import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.BaseChangeIndex
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField TensorProduct ComplexAt GroundTheory.Heights₂.Heights

noncomputable section

section GramDet

variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L] [Algebra K L]
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

omit [NumberField K] [NumberField L] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in

/- English proof (translation)
Rewrite using `[baseChangeCoord_tmul]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem baseChangeCoord_one_tmul (τ : L →+* ℂ) (e : E) :
    baseChangeCoord τ ((1 : ComplexAt τ) ⊗ₜ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] e)) =
      (1 : ComplexAt (τ.comp (algebraMap K L))) ⊗ₜ e := by
  rw [baseChangeCoord_tmul]
  congr 1
  simp

/- English proof (translation)
Establish `hv : ∀ i j, inner ℂ (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)) (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s j)) = inner ℂ (fibreVec h (τ.comp (algebraMap K L)) (s i)) (fibreVec h (τ.comp (algebraMap K L)) (s j))`. Introduce `i j`. Rewrite using `[fibreVec, fibreVec, FibreSpace.inner_equiv]`. Express the relevant statement in the definitionally equal form `inner ℂ (FibreSpace.equiv h _ (baseChangeCoord τ _)) (FibreSpace.equiv h _ (baseChangeCoord τ _)) = _`. Rewrite using `[baseChangeCoord_one_tmul, baseChangeCoord_one_tmul]`.

Both sides reduce to the same expression. Simplify using `only [gramDet]`. Use `congr 2`. Use extensionality with `i j`. Simplify using `only [Matrix.gram_apply, hv]`.
-/
theorem gramDet_baseChange (h : HermitianMetric K E) (τ : L →+* ℂ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (s : ι → E) :
    gramDet (h.baseChange L) τ (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      gramDet h (τ.comp (algebraMap K L)) s := by
  have hv : ∀ i j, inner ℂ (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s i))
      (fibreVec (h.baseChange L) τ ((1 : 𝓞 L) ⊗ₜ[𝓞 K] s j)) =
      inner ℂ (fibreVec h (τ.comp (algebraMap K L)) (s i))
        (fibreVec h (τ.comp (algebraMap K L)) (s j)) := by
    intro i j
    rw [fibreVec, fibreVec, FibreSpace.inner_equiv]
    change inner ℂ (FibreSpace.equiv h _ (baseChangeCoord τ _))
      (FibreSpace.equiv h _ (baseChangeCoord τ _)) = _
    rw [baseChangeCoord_one_tmul, baseChangeCoord_one_tmul]
    rfl
  simp only [gramDet]
  congr 2
  ext i j
  simp only [Matrix.gram_apply, hv]

end GramDet

/- English proof (translation)
Introduce `K _ _ L _ _ _ M`. Take `⟨s, hs⟩` from `exists_linearIndependent_fin (K := K) (E := M.carrier)`. Use `set N := Submodule.span (𝓞 K) (Set.range s)`. Establish `hrank : Module.finrank (𝓞 L) (𝓞 L ⊗[𝓞 K] M.carrier) = Module.finrank (𝓞 K) M.carrier` using `(TensorProduct.isBaseChange (𝓞 K) M.carrier (𝓞 L)).finrank_eq`. Set `b : Module.Basis (Fin (Module.finrank (𝓞 K) M.carrier)) (𝓞 K) N` to `Module.Basis.span hs`.

Set `bL` to `Algebra.TensorProduct.basis (𝓞 L) b`. Set `f : 𝓞 L ⊗[𝓞 K] N →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] M.carrier` to `AlgebraTensorModule.lTensor (𝓞 L) (𝓞 L) N.subtype`. Establish `hf : Function.Injective f` using `Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype`. Establish `hfb : (f ∘ bL) = fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i`. Use function extensionality and compare the values at `i`.

Simplify using `only [Function.comp_apply, bL, f, b, Algebra.TensorProduct.basis_apply, AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply]`. Rewrite using `[Module.Basis.span_apply]`. Establish `ht : LinearIndependent (𝓞 L) (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)`. Rewrite using `[← hfb]`. Conclude with `bL.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)`.

Establish `hspan : Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) = LinearMap.range f`. Rewrite using `[LinearMap.range_eq_map, ← bL.span_eq, Submodule.map_span, ← Set.range_comp, hfb]`. Establish `hfin : Finite (M.carrier ⧸ N)` using `finite_quotient_span hs (Fintype.card_fin _)`. Establish `hidx : Nat.card ((𝓞 L ⊗[𝓞 K] M.carrier) ⧸ Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)) = Nat.card (M.carrier ⧸ N) ^ Module.finrank K L`. Rewrite using `[hspan, ← card_tensor_integers L]`.

Conclude with `Nat.card_congr (AlgebraTensorModule.tensorQuotientEquiv (𝓞 L) (𝓞 K) (𝓞 L) N).toEquiv.symm`. Establish `hn : (0 : ℝ) < Module.finrank K L` using `by exact_mod_cast Module.finrank_pos`. Establish `hd : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`. Use `show arithDegree (M.metric.baseChange L) / Module.finrank ℚ L = arithDegree M.metric / Module.finrank ℚ K`. Rewrite using `[arithDegree_eq (M.metric.baseChange L) ht (by rw [Fintype.card_fin]; exact hrank.symm), arithDegree_eq M.metric hs (Fintype.card_fin _), ← Module.finrank_mul_finrank ℚ K L]`.

Simplify using `only [degreeWith, gramDet_baseChange]`. Rewrite using `[hidx, sum_comp_algebraMap L (fun σ ↦ Real.log (gramDet M.metric σ s)), Nat.cast_pow, Real.log_pow, Nat.cast_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem BaseChange.proof : BaseChange.Statement := by
  intro K _ _ L _ _ _ M
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  set N := Submodule.span (𝓞 K) (Set.range s)
  have hrank : Module.finrank (𝓞 L) (𝓞 L ⊗[𝓞 K] M.carrier) = Module.finrank (𝓞 K) M.carrier :=
    (TensorProduct.isBaseChange (𝓞 K) M.carrier (𝓞 L)).finrank_eq

  let b : Module.Basis (Fin (Module.finrank (𝓞 K) M.carrier)) (𝓞 K) N := Module.Basis.span hs
  let bL := Algebra.TensorProduct.basis (𝓞 L) b
  let f : 𝓞 L ⊗[𝓞 K] N →ₗ[𝓞 L] 𝓞 L ⊗[𝓞 K] M.carrier :=
    AlgebraTensorModule.lTensor (𝓞 L) (𝓞 L) N.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
  have hfb : (f ∘ bL) = fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i := by
    funext i
    simp only [Function.comp_apply, bL, f, b, Algebra.TensorProduct.basis_apply,
      AlgebraTensorModule.lTensor_tmul, Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  have ht : LinearIndependent (𝓞 L) (fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) := by
    rw [← hfb]
    exact bL.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have hspan : Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i) =
      LinearMap.range f := by
    rw [LinearMap.range_eq_map, ← bL.span_eq, Submodule.map_span, ← Set.range_comp, hfb]

  have hfin : Finite (M.carrier ⧸ N) := finite_quotient_span hs (Fintype.card_fin _)
  have hidx : Nat.card ((𝓞 L ⊗[𝓞 K] M.carrier) ⧸
      Submodule.span (𝓞 L) (Set.range fun i ↦ (1 : 𝓞 L) ⊗ₜ[𝓞 K] s i)) =
      Nat.card (M.carrier ⧸ N) ^ Module.finrank K L := by
    rw [hspan, ← card_tensor_integers L]
    exact Nat.card_congr (AlgebraTensorModule.tensorQuotientEquiv (𝓞 L) (𝓞 K) (𝓞 L) N).toEquiv.symm

  have hn : (0 : ℝ) < Module.finrank K L := by exact_mod_cast Module.finrank_pos
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  show arithDegree (M.metric.baseChange L) / Module.finrank ℚ L =
    arithDegree M.metric / Module.finrank ℚ K
  rw [arithDegree_eq (M.metric.baseChange L) ht (by rw [Fintype.card_fin]; exact hrank.symm),
    arithDegree_eq M.metric hs (Fintype.card_fin _), ← Module.finrank_mul_finrank ℚ K L]
  simp only [degreeWith, gramDet_baseChange]
  rw [hidx, sum_comp_algebraMap L (fun σ ↦ Real.log (gramDet M.metric σ s)), Nat.cast_pow,
    Real.log_pow, Nat.cast_mul]
  field_simp
  ring

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
