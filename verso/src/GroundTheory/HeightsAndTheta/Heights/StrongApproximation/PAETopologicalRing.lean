import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StrongApproximation.Statements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace StrongApprox

open Matrix NumberField IsDedekindDomain TensorProduct Topology ReciprocityTheory.ChartRestriction.G.SA

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ h2`. Assume the negation of the conclusion as `h`. Establish `hc2 : c * c ≠ c` using `fun h' => hc (by simpa using congrArg (c⁻¹ * ·) h')`. Establish `hcard : ({1, c, c * c} : Finset (E ≃ₐ[F] E)).card = 3`. Rewrite using `[Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc2)]`.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or]`. Conclude with `⟨Ne.symm hc, Ne.symm h⟩`. Establish `hle` using `Finset.card_le_univ ({1, c, c * c} : Finset (E ≃ₐ[F] E))`. Use `AlgEquiv.card_le (F := F) (K := E)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem AETopologicalRing.aut_mul_self (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    c * c = 1 := by
  classical
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  by_contra h
  have hc2 : c * c ≠ c := fun h' => hc (by simpa using congrArg (c⁻¹ * ·) h')
  have hcard : ({1, c, c * c} : Finset (E ≃ₐ[F] E)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hc2)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hc, Ne.symm h⟩
  have hle := Finset.card_le_univ ({1, c, c * c} : Finset (E ≃ₐ[F] E))
  have := AlgEquiv.card_le (F := F) (K := E)
  omega

/- English proof (translation)
Establish `hcc` using `AETopologicalRing.aut_mul_self c h2 hc`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, c x ≠ x := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hc (AlgEquiv.ext h)`.

Use `⟨x - c x, ?_, sub_ne_zero.2 (Ne.symm hx)⟩` and prove the remaining obligations. Establish `hx2 : c (c x) = x` using `by rw [← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]`. Rewrite using `[map_sub, hx2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem AETopologicalRing.exists_anti (c : E ≃ₐ[F] E) (h2 : Module.finrank F E = 2) (hc : c ≠ 1) :
    ∃ δ : E, c δ = -δ ∧ δ ≠ 0 := by
  have hcc := AETopologicalRing.aut_mul_self c h2 hc
  obtain ⟨x, hx⟩ : ∃ x, c x ≠ x := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  refine ⟨x - c x, ?_, sub_ne_zero.2 (Ne.symm hx)⟩
  have hx2 : c (c x) = x := by rw [← AlgEquiv.mul_apply, hcc, AlgEquiv.one_apply]
  rw [map_sub, hx2]
  ring

omit [NumberField F] in

/- English proof (translation)
Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`. Rewrite `hst` using `[Algebra.smul_def, Algebra.smul_def, mul_one]`. Establish `h'` using `congrArg c hst`. Simplify using `only [map_add, map_mul, AlgEquiv.commutes, hδ, map_zero] at h'`.

Establish `ht : algebraMap F E t = 0`. Establish `: (2 * δ) * algebraMap F E t = 0` using `by linear_combination hst - h'`. Conclude with `(mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0)`. Establish `ht' : t = 0` using `(map_eq_zero_iff _ (algebraMap F E).injective).1 ht`. Substitute `ht'` using the available equality.

Simplify using `only [map_zero, zero_mul, add_zero] at hst`. Conclude with `⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩`.
-/
theorem AETopologicalRing.linearIndependent_one_anti (c : E ≃ₐ[F] E) {δ : E} (hδ : c δ = -δ)
    (h0 : δ ≠ 0) : LinearIndependent F ![(1 : E), δ] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
  have h' := congrArg c hst
  simp only [map_add, map_mul, AlgEquiv.commutes, hδ, map_zero] at h'
  have ht : algebraMap F E t = 0 := by
    have : (2 * δ) * algebraMap F E t = 0 := by linear_combination hst - h'
    exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0)
  have ht' : t = 0 := (map_eq_zero_iff _ (algebraMap F E).injective).1 ht
  subst ht'
  simp only [map_zero, zero_mul, add_zero] at hst
  exact ⟨(map_eq_zero_iff _ (algebraMap F E).injective).1 hst, rfl⟩

def AETopologicalRing.sigALinear (c : E ≃ₐ[F] E) :
    AE F E →ₗ[FiniteAdeleRing (𝓞 F) F] AE F E :=
  LinearMap.baseChange (FiniteAdeleRing (𝓞 F) F) c.toLinearMap

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => rfl`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem AETopologicalRing.sigALinear_apply (c : E ≃ₐ[F] E) (a : AE F E) :
    AETopologicalRing.sigALinear c a = sigA c a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end

open scoped RestrictedProduct in

/- English proof (translation)
The claim follows from `inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]))`.
-/
theorem AETopologicalRing.t2Space_finiteAdeleRing (F : Type) [Field F] [NumberField F] :
    T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

/- English proof (translation)
Introduce `F E _ _ _ _ _ c h2 hc _ _`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ h2`. Establish `: IsTopologicalRing (AE F E)` using `IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)`. Establish `hσ : Continuous (sigA c)`. Use `IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F) (AETopologicalRing.sigALinear c)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Conclude with `(AETopologicalRing.sigALinear_apply c a).symm`. Take `⟨δ, hδ, h0⟩` from `AETopologicalRing.exists_anti c h2 hc`. Set `b : Module.Basis (Fin 2) F E` to `basisOfLinearIndependentOfCardEqFinrank (AETopologicalRing.linearIndependent_one_anti c hδ h0) (by simp [h2])`.

Set `B` to `Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b`. Establish `hB0 : B 0 = (1 : AE F E)`. Simplify using `[B, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]`. Establish `hB1 : B 1 = inclA F E δ`. Simplify using `[B, b, Algebra.TensorProduct.basis_apply]`.

Both sides reduce to the same expression. Use `AETopologicalRing.t2Space_finiteAdeleRing F` as an intermediate fact. Establish `: T2Space (AE F E)` using `T2Space.of_injective_continuous B.equivFun.injective (IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F) B.equivFun.toLinearMap)`. Use `⟨inferInstance, hσ, ⟨δ, hδ, fun a => ⟨(B.repr a 0, B.repr a 1), ?_, ?_⟩⟩, fun N J => ?_⟩` and prove the remaining obligations. Use `B.sum_repr a` as an intermediate fact.

Rewrite `this` using `[Fin.sum_univ_two, hB0, hB1]`. Conclude with `this.symm`. Introduce and unpack `⟨p₁, p₂⟩ hp`. Rewrite using `[hp, ← hB0, ← hB1]`. Simplify using the standard rewrite rules.

Establish `hmul : Continuous (fun p : Matrix (Fin N) (Fin N) (AE F E) × Matrix (Fin N) (Fin N) (AE F E) => p.1 * p.2)` using `continuous_fst.matrix_mul continuous_snd`. Establish `hform : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => gᵀ * J * g.map (sigA c))` using `(continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul (continuous_id.matrix_map hσ)`. Establish `hdet : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => g.det)` using `continuous_id.matrix_det`. Conclude with `⟨hmul, hform, hdet, (isClosed_eq hdet continuous_const).inter (isClosed_eq hform continuous_const)⟩`.
-/
theorem AETopologicalRing.proof : AETopologicalRing.Statement := by
  intro F E _ _ _ _ _ c h2 hc _ _
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  have : IsTopologicalRing (AE F E) :=
    IsModuleTopology.isTopologicalRing (FiniteAdeleRing (𝓞 F) F) (AE F E)
  have hσ : Continuous (sigA c) := by
    have := IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F)
      (AETopologicalRing.sigALinear c)
    convert this using 1
    funext a
    exact (AETopologicalRing.sigALinear_apply c a).symm
  obtain ⟨δ, hδ, h0⟩ := AETopologicalRing.exists_anti c h2 hc
  let b : Module.Basis (Fin 2) F E :=
    basisOfLinearIndependentOfCardEqFinrank (AETopologicalRing.linearIndependent_one_anti c hδ h0)
      (by simp [h2])
  let B := Algebra.TensorProduct.basis (FiniteAdeleRing (𝓞 F) F) b
  have hB0 : B 0 = (1 : AE F E) := by
    simp [B, b, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.one_def]
  have hB1 : B 1 = inclA F E δ := by
    simp [B, b, Algebra.TensorProduct.basis_apply]
    rfl
  have := AETopologicalRing.t2Space_finiteAdeleRing F
  have : T2Space (AE F E) := T2Space.of_injective_continuous B.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap (R := FiniteAdeleRing (𝓞 F) F) B.equivFun.toLinearMap)
  refine ⟨inferInstance, hσ, ⟨δ, hδ, fun a => ⟨(B.repr a 0, B.repr a 1), ?_, ?_⟩⟩, fun N J => ?_⟩
  · have := B.sum_repr a
    rw [Fin.sum_univ_two, hB0, hB1] at this
    exact this.symm
  · rintro ⟨p₁, p₂⟩ hp
    rw [hp, ← hB0, ← hB1]
    simp
  · have hmul : Continuous (fun p : Matrix (Fin N) (Fin N) (AE F E) × Matrix (Fin N) (Fin N) (AE F E) =>
        p.1 * p.2) := continuous_fst.matrix_mul continuous_snd
    have hform : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => gᵀ * J * g.map (sigA c)) :=
      (continuous_id.matrix_transpose.matrix_mul continuous_const).matrix_mul (continuous_id.matrix_map hσ)
    have hdet : Continuous (fun g : Matrix (Fin N) (Fin N) (AE F E) => g.det) := continuous_id.matrix_det
    exact ⟨hmul, hform, hdet, (isClosed_eq hdet continuous_const).inter (isClosed_eq hform continuous_const)⟩

end StrongApprox

end GroundTheory.Heights₂.Heights
