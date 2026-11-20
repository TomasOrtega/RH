import Mathlib

namespace GroundTheory.Automorphic

open Module

variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]

noncomputable def conjLinear : E →ₗ[F] E :=
  (Algebra.linearMap F E).comp (Algebra.trace F E) - LinearMap.id

variable {F E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjLinear_apply (x : E) :
    conjLinear F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

variable [Algebra.IsQuadraticExtension F E]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem trace_algebraMap_quadratic (c : F) : Algebra.trace F E (algebraMap F E c) = 2 * c := by
  rw [Algebra.trace_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two, nsmul_eq_mul]
  norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conjLinear_algebraMap (c : F) : conjLinear F E (algebraMap F E c) = algebraMap F E c := by
  rw [conjLinear_apply, trace_algebraMap_quadratic, map_mul, map_ofNat]
  ring

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem conjLinear_one : conjLinear F E 1 = 1 := by
  simpa using conjLinear_algebraMap (F := F) (E := E) 1

omit [Algebra.IsQuadraticExtension F E] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. It suffices to derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem linearIndependent_one_of_not_mem [Nontrivial E] {x : E}
    (hx : x ∉ Set.range (algebraMap F E)) : LinearIndependent F ![1, x] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    refine ⟨?_, rfl⟩
    by_contra hs
    exact one_ne_zero ((smul_eq_zero.mp hst).resolve_left hs)
  · exfalso
    apply hx
    refine ⟨-(s / t), ?_⟩
    have : t • x = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
    rw [Algebra.algebraMap_eq_smul_one]
    have h2 : x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [h2, this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nontrivial_quadratic (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [Algebra.IsQuadraticExtension K A] : Nontrivial A :=
  Module.nontrivial_of_finrank_pos (R := K) (by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two]; norm_num)

noncomputable def basisOneOf {x : E} (hx : x ∉ Set.range (algebraMap F E)) : Basis (Fin 2) F E :=
  haveI := nontrivial_quadratic F E
  basisOfLinearIndependentOfCardEqFinrank (linearIndependent_one_of_not_mem hx)
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two, Fintype.card_fin])

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem basisOneOf_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 0 = 1 := by
  simp [basisOneOf]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem basisOneOf_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) : basisOneOf hx 1 = x := by
  simp [basisOneOf]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sq_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    x * x = algebraMap F E ((basisOneOf hx).repr (x * x) 0) +
      algebraMap F E ((basisOneOf hx).repr (x * x) 1) * x := by
  conv_lhs => rw [← (basisOneOf hx).sum_repr (x * x)]
  rw [Fin.sum_univ_two, basisOneOf_zero, basisOneOf_one, Algebra.smul_def, Algebra.smul_def,
    mul_one]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem repr_self_zero {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 0 = 0 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem repr_self_one {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 1 = 1 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem trace_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := by
  rw [Algebra.trace_eq_matrix_trace (basisOneOf hx), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, zero_add]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_eq_of_not_mem {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    Algebra.norm F x = -(basisOneOf hx).repr (x * x) 0 := by
  rw [Algebra.norm_eq_matrix_det (basisOneOf hx), Matrix.det_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, basisOneOf_zero,
    basisOneOf_one, mul_one, repr_self_zero, repr_self_one]
  ring

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.
-/
theorem conjLinear_mul_self (x : E) :
    conjLinear F E (x * x) = conjLinear F E x * conjLinear F E x := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [← map_mul, conjLinear_algebraMap, conjLinear_algebraMap, map_mul]
  · have hsq := sq_eq_of_not_mem hx
    have htr : Algebra.trace F E x = (basisOneOf hx).repr (x * x) 1 := trace_eq_of_not_mem hx
    have htr2 : Algebra.trace F E (x * x) = 2 * (basisOneOf hx).repr (x * x) 0 +
        (basisOneOf hx).repr (x * x) 1 * (basisOneOf hx).repr (x * x) 1 := by
      conv_lhs => rw [hsq]
      rw [map_add, trace_algebraMap_quadratic, ← Algebra.smul_def, map_smul, htr, smul_eq_mul]
    rw [conjLinear_apply, conjLinear_apply, htr2, htr]
    simp only [map_add, map_mul, map_ofNat]
    linear_combination (-2 : E) * hsq

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem conjLinear_mul (x y : E) :
    conjLinear F E (x * y) = conjLinear F E x * conjLinear F E y := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conjLinear_algebraMap, ← Algebra.smul_def, ← Algebra.smul_def, map_smul]
  · have key : (conjLinear F E).comp (LinearMap.mulLeft F x) =
        (LinearMap.mulLeft F (conjLinear F E x)).comp (conjLinear F E) := by
      refine (basisOneOf hx).ext fun i => ?_
      fin_cases i
      · simp [basisOneOf_zero, conjLinear_one]
      · simp only [Fin.mk_one, basisOneOf_one, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.mulLeft_apply]
        exact conjLinear_mul_self x
    exact LinearMap.congr_fun key y

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conjLinear_conjLinear (x : E) : conjLinear F E (conjLinear F E x) = x := by
  rw [conjLinear_apply, conjLinear_apply x, map_sub, trace_algebraMap_quadratic, map_sub,
    map_mul, map_ofNat]
  ring

variable (F E) in

noncomputable def conj : E ≃ₐ[F] E :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofInvolutive (conjLinear F E) (fun x => conjLinear_conjLinear x))
    conjLinear_one conjLinear_mul

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj_apply (x : E) : conj F E x = algebraMap F E (Algebra.trace F E x) - x := rfl

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj_conj (x : E) : conj F E (conj F E x) = x := conjLinear_conjLinear x

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conj_algebraMap (c : F) : conj F E (algebraMap F E c) = algebraMap F E c :=
  conjLinear_algebraMap c

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem add_conj (x : E) : x + conj F E x = algebraMap F E (Algebra.trace F E x) := by
  rw [conj_apply]; ring

/- English proof (translation)
Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem mul_conj (x : E) : x * conj F E x = algebraMap F E (Algebra.norm F x) := by
  by_cases hx : x ∈ Set.range (algebraMap F E)
  · obtain ⟨c, rfl⟩ := hx
    rw [conj_algebraMap, Algebra.norm_algebraMap, Algebra.IsQuadraticExtension.finrank_eq_two,
      map_pow, sq]
  · have hsq := sq_eq_of_not_mem hx
    rw [conj_apply, trace_eq_of_not_mem hx, norm_eq_of_not_mem hx, map_neg]
    linear_combination (-1 : E) * hsq

end GroundTheory.Automorphic
