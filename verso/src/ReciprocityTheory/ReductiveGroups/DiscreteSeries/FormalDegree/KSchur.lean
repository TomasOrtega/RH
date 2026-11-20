import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PmatIsHermitian
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KinstSecondCountable

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

namespace CompactHaarProbability

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

/- English proof (translation)
The claim follows from `((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1).ne'`.
-/
lemma muK_univ_ne_zero (ε : Fin n → Bool) : muK ε Set.univ ≠ 0 := ((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1).ne'

/- English proof (translation)
The claim follows from `((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2).ne`.
-/
lemma muK_univ_ne_top (ε : Fin n → Bool) : muK ε Set.univ ≠ ⊤ := ((ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2).ne

instance dk_isProb (ε : Fin n → Bool) : IsProbabilityMeasure (dk ε) :=
  ⟨by simp [dk]⟩

instance dk_left (ε : Fin n → Bool) : (dk ε).IsMulLeftInvariant := by
  unfold dk; infer_instance

instance dk_right (ε : Fin n → Bool) : (dk ε).IsMulRightInvariant := by
  have := muK_rightInvariant ε
  unfold dk; infer_instance

/- English proof (translation)
Use `haveI := muK_rightInvariant ε`. Use `set ν := Measure.map (fun x : KG ε => x⁻¹) (muK ε) with hν`. Use `haveI : ν.IsMulLeftInvariant := by`. Express the relevant statement in the definitionally equal form `(muK ε).inv.IsMulLeftInvariant`. Use `infer_instance`.

Use `haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance`. Establish `e` using `Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)`. Establish `huniv : ν Set.univ = muK ε Set.univ`. Rewrite using `[hν, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ]`. Rewrite `huniv` using `[e]`.

Rewrite `huniv` using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `hc : (ν.haarScalarFactor (muK ε) : ℝ≥0∞) = 1`. Establish `h2` using `congrArg (· / muK ε Set.univ) huniv`. Rewrite `h2` using `[ENNReal.mul_div_cancel_right (muK_univ_ne_zero ε) (muK_univ_ne_top ε), ENNReal.div_self (muK_univ_ne_zero ε) (muK_univ_ne_top ε)]`. Then use the resulting hypothesis. Establish `hc' : ν.haarScalarFactor (muK ε) = 1` using `by exact_mod_cast hc`.

Rewrite using `[e, hc', one_smul]`.
-/
lemma muK_inv (ε : Fin n → Bool) : Measure.map (fun x : KG ε => x⁻¹) (muK ε) = muK ε := by
  haveI := muK_rightInvariant ε
  set ν := Measure.map (fun x : KG ε => x⁻¹) (muK ε) with hν
  haveI : ν.IsMulLeftInvariant := by
    change (muK ε).inv.IsMulLeftInvariant
    infer_instance
  haveI : IsFiniteMeasure ν := by rw [hν]; infer_instance
  have e := Measure.isMulInvariant_eq_smul_of_compactSpace ν (muK ε)
  have huniv : ν Set.univ = muK ε Set.univ := by
    rw [hν, Measure.map_apply measurable_inv MeasurableSet.univ, Set.preimage_univ]
  rw [e] at huniv
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at huniv
  have hc : (ν.haarScalarFactor (muK ε) : ℝ≥0∞) = 1 := by
    have h2 := congrArg (· / muK ε Set.univ) huniv
    rwa [ENNReal.mul_div_cancel_right (muK_univ_ne_zero ε) (muK_univ_ne_top ε),
      ENNReal.div_self (muK_univ_ne_zero ε) (muK_univ_ne_top ε)] at h2
  have hc' : ν.haarScalarFactor (muK ε) = 1 := by exact_mod_cast hc
  rw [e, hc', one_smul]

/- English proof (translation)
Unfold `dk`. Rewrite using `[Measure.map_smul, muK_inv]`.
-/
lemma dk_inv (ε : Fin n → Bool) : Measure.map (fun x : KG ε => x⁻¹) (dk ε) = dk ε := by
  unfold dk
  rw [Measure.map_smul, muK_inv]

end CompactHaarProbability

open CompactHaarProbability in

/- English proof (translation)
Use `⟨inferInstance, fun k => map_mul_left_eq_self (dk ε) k, fun k => map_mul_right_eq_self (dk ε) k, dk_inv ε⟩` and prove the remaining obligations.
-/
theorem dk_props (ε : Fin n → Bool) :
    IsProbabilityMeasure (dk ε) ∧ (∀ k : KG ε, Measure.map (fun x => k * x) (dk ε) = dk ε) ∧
      (∀ k : KG ε, Measure.map (fun x => x * k) (dk ε) = dk ε) ∧
      Measure.map (fun x : KG ε => x⁻¹) (dk ε) = dk ε := by
  refine ⟨inferInstance, fun k => map_mul_left_eq_self (dk ε) k, fun k => map_mul_right_eq_self (dk ε) k,
    dk_inv ε⟩

namespace CompactHaarProbability

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

/- English proof (translation)
Use `show ((T.τ (a * b) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _`. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
lemma op_mul (T : KType ε Λ) (a b : KG ε) : T.op (a * b) = T.op a * T.op b := by
  show ((T.τ (a * b) : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
  rw [map_mul]
  rfl

/- English proof (translation)
Use `show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
lemma op_one (T : KType ε Λ) : T.op 1 = 1 := by
  show ((T.τ 1 : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = 1
  rw [map_one]
  rfl

/- English proof (translation)
Rewrite using `[← op_mul, mul_inv_cancel, op_one]`.
-/
lemma op_mul_inv (T : KType ε Λ) (a : KG ε) : T.op a * T.op a⁻¹ = 1 := by
  rw [← op_mul, mul_inv_cancel, op_one]

/- English proof (translation)
Rewrite using `[← op_mul, inv_mul_cancel, op_one]`.
-/
lemma op_inv_mul (T : KType ε Λ) (a : KG ε) : T.op a⁻¹ * T.op a = 1 := by
  rw [← op_mul, inv_mul_cancel, op_one]

def opE (T : KType ε Λ) (k : KG ε) : T.V ≃L[ℂ] T.V :=
  ContinuousLinearEquiv.equivOfInverse (T.op k) (T.op k⁻¹)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (op_inv_mul T k)
      simpa using this)
    (fun v => by
      have := congrArg (fun A : T.V →L[ℂ] T.V => A v) (op_mul_inv T k)
      simpa using this)

def conjE (T : KType ε Λ) (k : KG ε) : (T.V →L[ℂ] T.V) ≃L[ℂ] (T.V →L[ℂ] T.V) :=
  (opE T k).arrowCongr (opE T k)

/- English proof (translation)
Conclude with `ContinuousLinearMap.ext fun v => rfl`.
-/
lemma conjE_apply (T : KType ε Λ) (k : KG ε) (A : T.V →L[ℂ] T.V) :
    conjE T k A = T.op k * A * T.op k⁻¹ := by
  exact ContinuousLinearMap.ext fun v => rfl

/- English proof (translation)
Distinguish the cases in `hV : Nontrivial T.V`. Take `⟨c, hc⟩` from `Module.End.exists_eigenvalue (A : T.V →ₗ[ℂ] T.V)`. Establish `hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c, ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c`. Introduce `k v hv`. Rewrite `hv`, the goal using `[Module.End.mem_eigenspace_iff]`.

Establish `e` using `congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)`. Simplify using `only [ContinuousLinearMap.mul_apply] at e`. Express the relevant statement in the definitionally equal form `A (T.op k v) = c • T.op k v`. Rewrite using `[← e]`. Express the relevant statement in the definitionally equal form `T.op k ((A : T.V →ₗ[ℂ] T.V) v) = _`.

Rewrite using `[hv, map_smul]`. Break down `T.irred _ hinv with h | h` into its components or cases. Take `⟨v, hv⟩` from `hc.exists_hasEigenvector`. Conclude with `absurd ((Submodule.mem_bot ℂ).mp (h ▸ hv.1)) hv.2`. Use `⟨c, ContinuousLinearMap.ext fun v => ?_⟩` and prove the remaining obligations.

Establish `hv : v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c` using `h ▸ Submodule.mem_top`. Rewrite `hv` using `[Module.End.mem_eigenspace_iff]`. Simplify using `using hv`. Use `haveI : Subsingleton T.V := not_nontrivial_iff_subsingleton.mp hV`. Conclude with `⟨0, ContinuousLinearMap.ext fun v => Subsingleton.elim _ _⟩`.
-/
lemma schur (T : KType ε Λ) (A : T.V →L[ℂ] T.V) (hA : ∀ k, T.op k * A = A * T.op k) :
    ∃ c : ℂ, A = c • (1 : T.V →L[ℂ] T.V) := by
  by_cases hV : Nontrivial T.V
  · obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A : T.V →ₗ[ℂ] T.V)
    have hinv : ∀ k : KG ε, ∀ v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c,
        ((T.τ k : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) v ∈
          Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c := by
      intro k v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      have e := congrArg (fun B : T.V →L[ℂ] T.V => B v) (hA k)
      simp only [ContinuousLinearMap.mul_apply] at e
      change A (T.op k v) = c • T.op k v
      rw [← e]
      change T.op k ((A : T.V →ₗ[ℂ] T.V) v) = _
      rw [hv, map_smul]
    rcases T.irred _ hinv with h | h
    · obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      exact absurd ((Submodule.mem_bot ℂ).mp (h ▸ hv.1)) hv.2
    · refine ⟨c, ContinuousLinearMap.ext fun v => ?_⟩
      have hv : v ∈ Module.End.eigenspace (A : T.V →ₗ[ℂ] T.V) c := h ▸ Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff] at hv
      simpa using hv
  · haveI : Subsingleton T.V := not_nontrivial_iff_subsingleton.mp hV
    exact ⟨0, ContinuousLinearMap.ext fun v => Subsingleton.elim _ _⟩

/- English proof (translation)
The claim follows from `continuous_subtype_val.comp T.cont`.
-/
lemma cont_op (T : KType ε Λ) : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont

/- English proof (translation)
The claim follows from `((cont_op T).mul continuous_const).mul ((cont_op T).comp continuous_inv)`.
-/
lemma cont_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) :
    Continuous fun k : KG ε => T.op k * P * T.op k⁻¹ := ((cont_op T).mul continuous_const).mul ((cont_op T).comp continuous_inv)

/- English proof (translation)
Establish `h` using `(cont_conj T P).continuousOn.integrableOn_compact (μ := dk ε) isCompact_univ`. Rewrite `h` using `[integrableOn_univ]`. Then use the resulting hypothesis.
-/
lemma integrable_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) :
    Integrable (fun k : KG ε => T.op k * P * T.op k⁻¹) (dk ε) := by
  have h := (cont_conj T P).continuousOn.integrableOn_compact (μ := dk ε) isCompact_univ
  rwa [integrableOn_univ] at h

/- English proof (translation)
Rewrite using `[← conjE_apply, ← ContinuousLinearEquiv.integral_comp_comm]`. Repeatedly rewrite using `[conjE_apply]`. Establish `e : ∀ k' : KG ε, T.op k * (T.op k' * P * T.op k'⁻¹) * T.op k⁻¹ = T.op (k * k') * P * T.op (k * k')⁻¹`. Introduce `k'`. Rewrite using `[op_mul, _root_.mul_inv_rev, op_mul]`.

Simplify using `only [mul_assoc]`. Repeatedly rewrite using `[e]`. Conclude with `integral_mul_left_eq_self (fun k' => T.op k' * P * T.op k'⁻¹) k`.
-/
lemma int_conj (T : KType ε Λ) (P : T.V →L[ℂ] T.V) (k : KG ε) :
    T.op k * (∫ k', T.op k' * P * T.op k'⁻¹ ∂(dk ε)) * T.op k⁻¹ =
      ∫ k', T.op k' * P * T.op k'⁻¹ ∂(dk ε) := by
  rw [← conjE_apply, ← ContinuousLinearEquiv.integral_comp_comm]
  simp_rw [conjE_apply]
  have e : ∀ k' : KG ε, T.op k * (T.op k' * P * T.op k'⁻¹) * T.op k⁻¹ =
      T.op (k * k') * P * T.op (k * k')⁻¹ := by
    intro k'
    rw [op_mul, _root_.mul_inv_rev, op_mul]
    simp only [mul_assoc]
  simp_rw [e]
  exact integral_mul_left_eq_self (fun k' => T.op k' * P * T.op k'⁻¹) k

end CompactHaarProbability

open CompactHaarProbability in

/- English proof (translation)
Use `set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP`. Use `set I := ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε) with hI`. Establish `hcomm : ∀ k, T.op k * I = I * T.op k`. Introduce `k`. Establish `h` using `int_conj T P k`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨c, hc⟩` from `schur T I hcomm`. Set `tr : (T.V →L[ℂ] T.V) →ₗ[ℂ] ℂ` to `(LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)`. Set `trL : (T.V →L[ℂ] T.V) →L[ℂ] ℂ` to `LinearMap.toContinuousLinearMap tr`. Establish `htr : ∀ A : T.V →L[ℂ] T.V, trL A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V)` using `fun A => rfl`.

Establish `hconj : ∀ k : KG ε, trL (T.op k * P * T.op k⁻¹) = trL P`. Introduce `k`. Rewrite using `[htr, htr, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_mul, mul_assoc, LinearMap.trace_mul_comm, mul_assoc, ← ContinuousLinearMap.coe_mul, op_inv_mul]`. Simplify using the standard rewrite rules. Establish `htrP : trL P = ((‖v‖ ^ 2 : ℝ) : ℂ)`.

Rewrite using `[htr, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ T.V)]`. Simplify using `only [ContinuousLinearMap.coe_coe, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]`. Rewrite using `[OrthonormalBasis.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hItr : trL I = trL P`. Rewrite using `[hI, ← ContinuousLinearMap.integral_comp_comm trL (integrable_conj T P)]`. Repeatedly rewrite using `[hconj]`. Rewrite using `[integral_const]`. Simplify using the standard rewrite rules.

Establish `htr1 : trL (c • (1 : T.V →L[ℂ] T.V)) = c * (Module.finrank ℂ T.V : ℂ)`. Rewrite using `[map_smul, htr]`. Simplify using `[LinearMap.trace_one]`. Rewrite `hItr` using `[hc, htr1, htrP]`. Establish `key : ((Module.finrank ℂ T.V : ℝ) : ℂ) * c = ((‖v‖ ^ 2 : ℝ) : ℂ)`.

Rewrite using `[← hItr]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, smul_smul, key]`.
-/
theorem kschur_op {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (v : T.V) :
    ((Module.finrank ℂ T.V : ℝ) : ℂ) •
        ∫ k, T.op k * (innerSL ℂ v).smulRight v * T.op k⁻¹ ∂(dk ε) =
      ((‖v‖ ^ 2 : ℝ) : ℂ) • (1 : T.V →L[ℂ] T.V) := by
  set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP
  set I := ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε) with hI
  have hcomm : ∀ k, T.op k * I = I * T.op k := by
    intro k
    have h := int_conj T P k
    calc T.op k * I = T.op k * I * (T.op k⁻¹ * T.op k) := by rw [op_inv_mul, mul_one]
      _ = (T.op k * I * T.op k⁻¹) * T.op k := by simp only [mul_assoc]
      _ = I * T.op k := by rw [h]
  obtain ⟨c, hc⟩ := schur T I hcomm
  let tr : (T.V →L[ℂ] T.V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ T.V).comp (ContinuousLinearMap.coeLM ℂ)
  let trL : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := LinearMap.toContinuousLinearMap tr
  have htr : ∀ A : T.V →L[ℂ] T.V, trL A = LinearMap.trace ℂ T.V (A : T.V →ₗ[ℂ] T.V) := fun A => rfl
  have hconj : ∀ k : KG ε, trL (T.op k * P * T.op k⁻¹) = trL P := by
    intro k
    rw [htr, htr, ContinuousLinearMap.coe_mul, ContinuousLinearMap.coe_mul, mul_assoc,
      LinearMap.trace_mul_comm, mul_assoc, ← ContinuousLinearMap.coe_mul, op_inv_mul]
    simp
  have htrP : trL P = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [htr, LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ T.V)]
    simp only [ContinuousLinearMap.coe_coe, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      inner_smul_right]
    rw [OrthonormalBasis.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hItr : trL I = trL P := by
    rw [hI, ← ContinuousLinearMap.integral_comp_comm trL (integrable_conj T P)]
    simp_rw [hconj]
    rw [integral_const]
    simp
  have htr1 : trL (c • (1 : T.V →L[ℂ] T.V)) = c * (Module.finrank ℂ T.V : ℂ) := by
    rw [map_smul, htr]
    simp [LinearMap.trace_one]
  rw [hc, htr1, htrP] at hItr
  have key : ((Module.finrank ℂ T.V : ℝ) : ℂ) * c = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hItr]
    push_cast
    ring
  rw [hc, smul_smul, key]

open CompactHaarProbability in

/- English proof (translation)
Use `set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP`. Establish `hop` using `kschur_op T v`. Rewrite `hop` using `[← hP]`. Establish `hadj : ∀ k : KG ε, T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k)`. Introduce `k`.

Use `show ((T.τ k⁻¹ : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _`. Rewrite using `[map_inv, ← ContinuousLinearMap.star_eq_adjoint]`. Both sides reduce to the same expression. Establish `hpt : ∀ k : KG ε, ⟪u, (T.op k * P * T.op k⁻¹) u⟫_ℂ = ((‖⟪u, T.op k v⟫_ℂ‖ ^ 2 : ℝ) : ℂ)`. Introduce `k`.

Simplify using `only [ContinuousLinearMap.mul_apply, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]`. Rewrite using `[hadj, ContinuousLinearMap.adjoint_inner_right, map_smul, inner_smul_right, ← inner_conj_symm, RCLike.conj_mul]`. Use `push_cast`. Both sides reduce to the same expression. Set `E : (T.V →L[ℂ] T.V) →L[ℂ] ℂ` to `(innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ T.V u)`.

Establish `hE : ∀ A : T.V →L[ℂ] T.V, E A = ⟪u, A u⟫_ℂ` using `fun A => rfl`. Establish `hint : ((∫ k, ‖⟪u, T.op k v⟫_ℂ‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) = ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ`. Rewrite using `[← integral_complex_ofReal, ← hE, ← ContinuousLinearMap.integral_comp_comm E (integrable_conj T P)]`. Repeatedly rewrite using `[hE, hpt]`. Establish `hfin : ((Module.finrank ℂ T.V : ℝ) : ℂ) * ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ = ((‖v‖ ^ 2 * ‖u‖ ^ 2 : ℝ) : ℂ)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ContinuousLinearMap.smul_apply, inner_smul_right]`. Use `_ = ⟪u, (((‖v‖ ^ 2 : ℝ) : ℂ) • (1 : T.V →L[ℂ] T.V)) u⟫_ℂ := by rw [hop]`. Use `_ = ((‖v‖ ^ 2 : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by`. Rewrite using `[ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]`.

Use `_ = _ := by`. Establish `h : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ)`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using inner_self_eq_norm_sq (𝕜 := ℂ) u`. Simplify using `using inner_self_im (𝕜 := ℂ) u`.

Rewrite using `[h, ← Complex.ofReal_mul]`. Rewrite `hfin` using `[← hint]`. Conclude with `hfin` after adjusting the coercions.
-/
theorem kschur_coef {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (u v : T.V) :
    (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪u, T.op k v⟫_ℂ‖ ^ 2 ∂(dk ε) = ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  set P : T.V →L[ℂ] T.V := (innerSL ℂ v).smulRight v with hP
  have hop := kschur_op T v
  rw [← hP] at hop
  have hadj : ∀ k : KG ε, T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
    intro k
    show ((T.τ k⁻¹ : unitary (T.V →L[ℂ] T.V)) : T.V →L[ℂ] T.V) = _
    rw [map_inv, ← ContinuousLinearMap.star_eq_adjoint]
    rfl
  have hpt : ∀ k : KG ε, ⟪u, (T.op k * P * T.op k⁻¹) u⟫_ℂ = ((‖⟪u, T.op k v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro k
    simp only [ContinuousLinearMap.mul_apply, hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [hadj, ContinuousLinearMap.adjoint_inner_right, map_smul, inner_smul_right, ← inner_conj_symm,
      RCLike.conj_mul]
    push_cast
    rfl
  let E : (T.V →L[ℂ] T.V) →L[ℂ] ℂ := (innerSL ℂ u).comp (ContinuousLinearMap.apply ℂ T.V u)
  have hE : ∀ A : T.V →L[ℂ] T.V, E A = ⟪u, A u⟫_ℂ := fun A => rfl
  have hint : ((∫ k, ‖⟪u, T.op k v⟫_ℂ‖ ^ 2 ∂(dk ε) : ℝ) : ℂ) =
      ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ := by
    rw [← integral_complex_ofReal, ← hE, ← ContinuousLinearMap.integral_comp_comm E (integrable_conj T P)]
    simp_rw [hE, hpt]
  have hfin : ((Module.finrank ℂ T.V : ℝ) : ℂ) * ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ =
      ((‖v‖ ^ 2 * ‖u‖ ^ 2 : ℝ) : ℂ) := by
    calc ((Module.finrank ℂ T.V : ℝ) : ℂ) * ⟪u, (∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ
        = ⟪u, (((Module.finrank ℂ T.V : ℝ) : ℂ) • ∫ k, T.op k * P * T.op k⁻¹ ∂(dk ε)) u⟫_ℂ := by
          rw [ContinuousLinearMap.smul_apply, inner_smul_right]
      _ = ⟪u, (((‖v‖ ^ 2 : ℝ) : ℂ) • (1 : T.V →L[ℂ] T.V)) u⟫_ℂ := by rw [hop]
      _ = ((‖v‖ ^ 2 : ℝ) : ℂ) * ⟪u, u⟫_ℂ := by
          rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_smul_right]
      _ = _ := by
          have h : ⟪u, u⟫_ℂ = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
            apply Complex.ext
            · simpa using inner_self_eq_norm_sq (𝕜 := ℂ) u
            · simpa using inner_self_im (𝕜 := ℂ) u
          rw [h, ← Complex.ofReal_mul]
  rw [← hint] at hfin
  exact_mod_cast hfin

end ReciprocityTheory.ChartRestriction.DS
