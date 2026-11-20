import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

section SlopeTestRemainingChoices

open scoped InnerProductSpace

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `h : E.topologicalClosure = E` using `E.closed_of_finiteDimensional.submodule_topologicalClosure_eq`. Unfold `prj`. Use `congr 1`.
-/
private theorem prj_eq (E : Submodule ℂ H) [FiniteDimensional ℂ E] : prj E = E.starProjection := by
  have h : E.topologicalClosure = E := E.closed_of_finiteDimensional.submodule_topologicalClosure_eq
  unfold prj
  congr 1

/- English proof (translation)
Unfold `prj`. Rewrite using `[Submodule.starProjection_eq_self_iff, hV.submodule_topologicalClosure_eq]`.
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
Set `b` to `stdOrthonormalBasis ℂ E`. Rewrite using `[LinearMap.trace_eq_sum_inner _ b, trOn, prj_eq, GroundTheory.Automorphic.trace]`. Use `set S : H →L[ℂ] H := T ∘L E.starProjection with hS`. Use `HasSum.tsum_eq ?_` and prove the remaining obligations. Establish `h` using `hasSum_sum (s := Finset.univ) fun k _ => (GroundTheory.Automorphic.stdHilbertBasis ℂ H).hasSum_inner_mul_inner (ContinuousLinearMap.adjoint S (b k : H)) (b k : H)`.

Use `h using 1` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Rewrite using `[ContinuousLinearMap.comp_apply, b.starProjection_eq_sum_rankOne]`. Simplify using `only [ContinuousLinearMap.sum_apply, inner_sum, InnerProductSpace.rankOne_apply, inner_smul_right, ContinuousLinearMap.adjoint_inner_left]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.adjoint_inner_left, Submodule.coe_inner, cprs_coe, hS, ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.2 (b k).2, ← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (b k).2]`.
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
Use `Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (E.starProjection_apply_mem v)) fun w hw => ?_` and prove the remaining obligations. Rewrite using `[← map_sub, ← ContinuousLinearMap.adjoint_inner_right]`. Conclude with `E.starProjection_inner_eq_zero v _ (h' w hw)`.
-/
private theorem comm_proj (E : Submodule ℂ H) [FiniteDimensional ℂ E] (U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E)
    (h' : ∀ v ∈ E, ContinuousLinearMap.adjoint U v ∈ E) (v : H) :
    E.starProjection (U v) = U (E.starProjection v) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h _ (E.starProjection_apply_mem v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact E.starProjection_inner_eq_zero v _ (h' w hw)

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, Submodule.starProjection_eq_self_iff.2 (h _ v.2)]`. Both sides reduce to the same expression.
-/
private theorem cprs_mul_right (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H) (h : ∀ v ∈ E, U v ∈ E) :
    cprs E T * cprs E U = cprs E (T * U) := by
  ext v
  rw [Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, Submodule.starProjection_eq_self_iff.2 (h _ v.2)]
  rfl

/- English proof (translation)
Use extensionality with `v`. Rewrite using `[Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, ContinuousLinearMap.mul_apply, h, h, Submodule.starProjection_eq_self_iff.2 (E.starProjection_apply_mem _)]`.
-/
private theorem cprs_mul_left (E : Submodule ℂ H) [FiniteDimensional ℂ E] (T U : H →L[ℂ] H)
    (h : ∀ v, E.starProjection (U v) = U (E.starProjection v)) :
    cprs E U * cprs E T = cprs E (U * T) := by
  ext v
  rw [Module.End.mul_apply, cprs_coe, cprs_coe, cprs_coe, ContinuousLinearMap.mul_apply, h, h,
    Submodule.starProjection_eq_self_iff.2 (E.starProjection_apply_mem _)]

/- English proof (translation)
Introduce `v hv`. Take `⟨hv1, hv2⟩` from `Submodule.mem_inf.1 hv`. Use `Submodule.mem_inf.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hv1`, the goal using `[← prj_mem_iff hV]`. Use `congrArg (fun L : H →L[ℂ] H => L v) h1.eq` as an intermediate fact.

Simplify using `only [ContinuousLinearMap.mul_apply, hv1] at this`. Conclude with `this.symm`. Rewrite `hv2`, the goal using `[Module.End.mem_eigenspace_iff]`. Use `congrArg (fun L : H →L[ℂ] H => L v) h2.eq` as an intermediate fact. Simplify using `only [ContinuousLinearMap.mul_apply] at this`.

Simplify using `only [ContinuousLinearMap.coe_coe] at hv2 ⊢`. Rewrite using `[← this, hv2, map_smul]`.
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
Establish `hAs : IsSelfAdjoint A` using `GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA`. Establish `hPs : IsSelfAdjoint (prj V)` using `isSelfAdjoint_starProjection _`. Establish `hm : ∀ i, ∀ v ∈ eigIn V A x, U i v ∈ eigIn V A x` using `fun i => mem_eig hV A _ x (h1 i) (h2 i)`. Establish `hm' : ∀ i, ∀ v ∈ eigIn V A x, ContinuousLinearMap.adjoint (U i) v ∈ eigIn V A x` using `fun i => by`. Use `mem_eig hV A _ x ?_ ?_` and prove the remaining obligations.

Use `(h1 i).star_star` as an intermediate fact. Rewrite `this` using `[hPs.star_eq]`. Then use the resulting hypothesis. Use `(h2 i).star_star` as an intermediate fact. Rewrite `this` using `[hAs.star_eq]`. Then use the resulting hypothesis. Establish `hc` using `fun i => comm_proj _ (U i) (hm i) (hm' i)`.

Take `⟨s, c, hs, h⟩` from `hE (eigIn V A x) l hl (fun i => cprs _ (U i)) (cprs _ T) (fun i k => by show _ * _ = _ * _`. Rewrite using `[cprs_mul_right _ _ _ (hm k), cprs_mul_right _ _ _ (hm i), (h3 i k).eq])`. Use the proof step `(fun i => by rw [cprs_mul_right _ _ _ (hm i), cprs_mul_left _ _ _ (hc (i + 1)), h4])`. Use `⟨s, c, hs, (eventually_ge_atTop (Module.finrank ℂ (eigIn V A x))).mono fun j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[← h j hj, trOn_eq]`.

Use `congr 1`. Use `clear hj`. Proceed by induction on `j with`. Consider the case `zero => rw [pow_zero, pow_zero, one_mul]`. Both sides reduce to the same expression.

Consider the case `succ j ih => rw [pow_succ', pow_succ', mul_assoc, ← ih, cprs_mul_left _ _ _ (hc 0)]`. Both sides reduce to the same expression.
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
Introduce `hE K _ _ n l hl μ _ θ 𝔰 V x hA hV hfin`. Conclude with `abs_form hE l hl V hV.closed _ _ hA x 𝔰.Uq (fun i => 𝔰.Uq_inner i V hV.closed hV.inv) 𝔰.Uq_amp 𝔰.Uq_comm 𝔰.Uq_perm`.
-/
theorem UpperTheory.ConvolutionTheory.Ci.trExp :
    ExpForm → TrExp := by
  intro hE K _ _ n l hl μ _ θ 𝔰 V x hA hV hfin
  exact abs_form hE l hl V hV.closed _ _ hA x 𝔰.Uq (fun i => 𝔰.Uq_inner i V hV.closed hV.inv) 𝔰.Uq_amp 𝔰.Uq_comm
    𝔰.Uq_perm
