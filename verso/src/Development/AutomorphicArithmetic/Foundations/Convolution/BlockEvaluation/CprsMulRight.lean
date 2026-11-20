import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.
-/
private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold prj
  congr 1

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
private theorem prj_mem_iff {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (v : H) : prj V v = v ↔ v ∈ V := by
  unfold prj
  rw [Submodule.starProjection_eq_self_iff, hV.submodule_topologicalClosure_eq]

private noncomputable def cprs (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) : Module.End ℂ E :=
  (E.orthogonalProjection : H →ₗ[ℂ] E) ∘ₗ (T : H →ₗ[ℂ] H) ∘ₗ E.subtype

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cprs_coe (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) (v : E) :
    (cprs E T v : H) = E.starProjection (T v) := rfl

/- English proof (translation)
Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem trOn_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T : H →L[ℂ] H) :
    trOn E T = LinearMap.trace ℂ E (cprs E T) := by
  let b := stdOrthonormalBasis ℂ E
  rw [LinearMap.trace_eq_sum_inner _ b, trOn, prj_eq, GroundTheory.Automorphic.trace]
  set S : H →L[ℂ] H := T ∘L E.starProjection with hS
  refine HasSum.tsum_eq ?_
  have h := hasSum_sum (s := Finset.univ) fun k _ =>
    (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)
  convert h using 1
  · rfl
  · funext i
    rw [ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]
    simp only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right,
      ContinuousLinearMap.adjoint_inner_left]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply,
      Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.2 (b k).2]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem comm_proj (E : Submodule ℂ H) [FiniteDimensional ℂ E] (U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E)
    (h' : ∀ v ∈ E, ContinuousLinearMap.adjoint U v ∈ E) (v : H) :
    E.starProjection (U v) = U (E.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (E.starProjection_apply_mem v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact E.starProjection_inner_eq_zero v _ (h' w hw)

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
private theorem cprs_mul_right (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E) :
    cprs E T * cprs E U = cprs E (T * U) := by
  ext v
  rw [Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, Submodule.starProjection_eq_self_iff.2 (h _ v.2)]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
private theorem cprs_mul_left (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H)
    (h : ∀ v, E.starProjection (U v) = U (E.starProjection v)) :
    cprs E U * cprs E T = cprs E (U * T) := by
  ext v
  rw [Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, ContinuousLinearMap.mul_apply, h, h,
    Submodule.starProjection_eq_self_iff.2 (E.starProjection_apply_mem _)]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem mem_eig {V : Submodule ℂ H} (hV : IsClosed (V : Set H)) (A U : H →L[ℂ] H) (x : ℝ)
    (h1 : Commute U (prj V)) (h2 : Commute U A) : ∀ v ∈ eigIn V A x, U v ∈ eigIn V A x := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.1 hv
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [← prj_mem_iff hV] at hv1 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h1.eq
    simp only [ContinuousLinearMap.mul_apply, hv1] at this
    exact this.symm
  · rw [Module.End.mem_eigenspace_iff] at hv2 ⊢
    have := congrArg (fun L : H →L[ℂ] H => L v) h2.eq
    simp only [ContinuousLinearMap.mul_apply] at this
    simp only [ContinuousLinearMap.coe_coe] at hv2 ⊢
    rw [← this, hv2, map_smul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Proceed by induction. Treat this case separately. Both sides reduce to the same expression. Treat this case separately. Both sides reduce to the same expression.

A detailed English derivation is pending.
-/
private theorem abs_form (hE : ExpForm) (l : ℕ) (hl : 0 < l) (V : Submodule ℂ H) (hV : IsClosed (V : Set H))
    (A T : H →L[ℂ] H) (hA : 0 ≤ A) (x : ℝ) [FiniteDimensional ℂ (eigIn V A x)] (U : ZMod l → H →L[ℂ] H)
    (h1 : ∀ i, Commute (U i) (prj V)) (h2 : ∀ i, Commute (U i) A) (h3 : ∀ i k, Commute (U i) (U k))
    (h4 : ∀ i, T * U i = U (i + 1) * T) :
    ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop,
      trOn (eigIn V A x) ((U 0 ^ j) ∘L T) = ∑ ζ ∈ s, c ζ * ζ ^ j := by
  have hAs : IsSelfAdjoint A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA
  have hPs : IsSelfAdjoint (prj V) := isSelfAdjoint_starProjection _
  have hm : ∀ i, ∀ v ∈ eigIn V A x, U i v ∈ eigIn V A x := fun i => mem_eig hV A _ x (h1 i) (h2 i)
  have hm' : ∀ i, ∀ v ∈ eigIn V A x, ContinuousLinearMap.adjoint (U i) v ∈ eigIn V A x := fun i => by
    refine mem_eig hV A _ x ?_ ?_
    · have := (h1 i).star_star
      rwa [hPs.star_eq] at this
    · have := (h2 i).star_star
      rwa [hAs.star_eq] at this
  have hc := fun i => comm_proj _ (U i) (hm i) (hm' i)
  obtain ⟨s, c, hs, h⟩ := hE (eigIn V A x) l hl (fun i => cprs _ (U i)) (cprs _ T)
    (fun i k => by
      show _ * _ = _ * _
      rw [cprs_mul_right _ _ _ (hm k), cprs_mul_right _ _ _ (hm i), (h3 i k).eq])
    (fun i => by rw [cprs_mul_right _ _ _ (hm i), cprs_mul_left _ _ _ (hc (i + 1)), h4])
  refine ⟨s, c, hs, (eventually_ge_atTop (Module.finrank ℂ (eigIn V A x))).mono fun j hj => ?_⟩
  rw [← h j hj, trOn_eq]
  congr 1
  clear hj
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul]; rfl
  | succ j ih => rw [pow_succ', pow_succ', mul_assoc, ← ih, cprs_mul_left _ _ _ (hc 0)]; rfl

end SlopeTestRemainingChoices

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.Ci.trExp :
    ExpForm → TrExp := by
  intro hE K _ _ n l hl μ _ θ 𝔰 V x hA hV hfin
  exact abs_form hE l hl V hV.closed _ _ hA x 𝔰.Uq (fun i => 𝔰.Uq_inner i V hV.closed hV.inv) 𝔰.Uq_amp 𝔰.Uq_comm
    𝔰.Uq_perm
