import Mathlib

open MeasureTheory InnerProductSpace
open scoped InnerProductSpace

namespace GlobalTheory.CompactRep

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Establish `h : (fun w : H => rankOne ℂ w w) = fun w => ContinuousLinearMap.smulRightL ℂ H H (innerSL ℂ w) w`. Use function extensionality and compare the values at `w`. Use extensionality with `z`. Simplify using `[rankOne_apply]`. Rewrite using `[h]`.

Conclude with `(ContinuousLinearMap.smulRightL ℂ H H).continuous₂.comp ((innerSL ℂ).continuous.prodMk continuous_id)`.
-/
theorem continuous_rankOne_self : Continuous fun w : H => rankOne ℂ w w := by
  have h : (fun w : H => rankOne ℂ w w) =
      fun w => ContinuousLinearMap.smulRightL ℂ H H (innerSL ℂ w) w := by
    funext w
    ext z
    simp [rankOne_apply]
  rw [h]
  exact (ContinuousLinearMap.smulRightL ℂ H H).continuous₂.comp
    ((innerSL ℂ).continuous.prodMk continuous_id)

/- English proof (translation)
Rewrite using `[rankOne_def']`. Conclude with `(isCompactOperator_of_locallyCompactSpace_rng (ContinuousLinearMap.toSpanSingleton ℂ w)).comp_clm (innerSL ℂ w)`.
-/
theorem isCompactOperator_rankOne_self (w : H) : IsCompactOperator (rankOne ℂ w w) := by
  rw [rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ w)).comp_clm (innerSL ℂ w)

/- English proof (translation)
Conclude with `((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex`.
-/
theorem convex_compactOperators : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := by
  exact ((compactOperator (RingHom.id ℂ) H H).restrictScalars ℝ).convex

variable [CompleteSpace H] {X : Type} [MeasurableSpace X] {μ : Measure X}

/- English proof (translation)
Establish `hs : IsClosed {f : H →L[ℂ] H | IsCompactOperator f}` using `isClosed_setOfPred_isCompactOperator`. Establish `hc : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f}` using `convex_compactOperators`. Establish `hae : ∀ᵐ k ∂μ, F k ∈ {f : H →L[ℂ] H | IsCompactOperator f}` using `Filter.Eventually.of_forall hF`. Establish `hm` using `hc.integral_mem hs hae hFi`. Conclude with `hm`.
-/
theorem isCompactOperator_integral [IsProbabilityMeasure μ] {F : X → H →L[ℂ] H}
    (hFi : Integrable F μ) (hF : ∀ k, IsCompactOperator (F k)) :
    IsCompactOperator (∫ k, F k ∂μ : H →L[ℂ] H) := by
  have hs : IsClosed {f : H →L[ℂ] H | IsCompactOperator f} := isClosed_setOfPred_isCompactOperator
  have hc : Convex ℝ {f : H →L[ℂ] H | IsCompactOperator f} := convex_compactOperators
  have hae : ∀ᵐ k ∂μ, F k ∈ {f : H →L[ℂ] H | IsCompactOperator f} := Filter.Eventually.of_forall hF
  have hm := hc.integral_mem hs hae hFi
  exact hm

/- English proof (translation)
Establish `hix : Integrable (fun k => rankOne ℂ (w k) (w k) x) μ` using `(ContinuousLinearMap.apply ℂ H x).integrable_comp hFi`. Rewrite using `[ContinuousLinearMap.integral_apply hFi x, ← integral_inner hix y]`. Simplify using `only [rankOne_apply, inner_smul_right]`.
-/
theorem inner_integral_rankOne {w : X → H} (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ)
    (x y : H) : ⟪y, (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) x⟫_ℂ =
      ∫ k, ⟪w k, x⟫_ℂ * ⟪y, w k⟫_ℂ ∂μ := by
  have hix : Integrable (fun k => rankOne ℂ (w k) (w k) x) μ :=
    (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
  rw [ContinuousLinearMap.integral_apply hFi x, ← integral_inner hix y]
  simp only [rankOne_apply, inner_smul_right]

/- English proof (translation)
Introduce `x y`. Simplify using `only [ContinuousLinearMap.coe_coe]`. Rewrite using `[← inner_conj_symm, inner_integral_rankOne hFi x y, inner_integral_rankOne hFi y x, ← integral_conj]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[map_mul, inner_conj_symm, inner_conj_symm, mul_comm]`.
-/
theorem isSymmetric_integral_rankOne {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [← inner_conj_symm, inner_integral_rankOne hFi x y, inner_integral_rankOne hFi y x,
    ← integral_conj]
  congr 1
  funext k
  rw [map_mul, inner_conj_symm, inner_conj_symm, mul_comm]

/- English proof (translation)
Introduce `h0`. Establish `h` using `inner_integral_rankOne hFi v v`. Rewrite `h` using `[h0, zero_apply, inner_zero_right]`. Establish `h3 : ∫ k, ⟪w k, v⟫_ℂ * ⟪v, w k⟫_ℂ ∂μ = ((∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ)`. Rewrite using `[← integral_complex_ofReal]`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[← inner_conj_symm (w k) v, Complex.conj_mul']`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite `h` using `[h3]`. Conclude with `hpos.ne' (by exact_mod_cast h.symm)`.
-/
theorem integral_rankOne_ne_zero {w : X → H}
    (hFi : Integrable (fun k => rankOne ℂ (w k) (w k)) μ) (v : H)
    (hpos : 0 < ∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ) :
    (∫ k, rankOne ℂ (w k) (w k) ∂μ : H →L[ℂ] H) ≠ 0 := by
  intro h0
  have h := inner_integral_rankOne hFi v v
  rw [h0, zero_apply, inner_zero_right] at h
  have h3 : ∫ k, ⟪w k, v⟫_ℂ * ⟪v, w k⟫_ℂ ∂μ = ((∫ k, ‖⟪v, w k⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext k
    rw [← inner_conj_symm (w k) v, Complex.conj_mul']
    push_cast
    rfl
  rw [h3] at h
  exact hpos.ne' (by exact_mod_cast h.symm)

end

/- English proof (translation)
Introduce `K _ _ _ _ _ _ H _ _ _ _ π hnorm hcont`. Set `: MeasurableSpace K` to `borel K`. Establish `: BorelSpace K` using `⟨rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨μ, hμ1, hμ2, hμ3⟩ : ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant ∧ μ.IsOpenPosMeasure := by`. Use `⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance, inferInstance⟩` and prove the remaining obligations.

Simplify using `using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))`. Take `⟨v, hv⟩` from `exists_ne (0 : H)`. Establish `hw : Continuous fun k => π k v` using `hcont v`. Establish `hFc : Continuous fun k => rankOne ℂ (π k v) (π k v)` using `continuous_rankOne_self.comp hw`. Establish `hFi : Integrable (fun k => rankOne ℂ (π k v) (π k v)) μ` using `hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.

Establish `hTc : IsCompactOperator (∫ k, rankOne ℂ (π k v) (π k v) ∂μ : H →L[ℂ] H)` using `isCompactOperator_integral hFi (fun k => isCompactOperator_rankOne_self _)`. Establish `hTs` using `isSymmetric_integral_rankOne hFi`. Establish `hpos : 0 < ∫ k, ‖⟪v, π k v⟫_ℂ‖ ^ 2 ∂μ`. Establish `hc : Continuous fun k => ‖⟪v, π k v⟫_ℂ‖ ^ 2` using `((continuous_const.inner hw).norm).pow 2`. Use `hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (x := 1) ?_` and prove the remaining obligations.

Simplify using `[hv]`. Establish `hT0` using `integral_rankOne_ne_zero hFi v hpos`. Use `set T : H →L[ℂ] H := ∫ k, rankOne ℂ (π k v) (π k v) ∂μ with hT`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hc0⟩ : ∃ c, Module.End.HasEigenvalue (T : Module.End ℂ H) c ∧ c ≠ 0 := by`. Assume the negation of the conclusion as `hno`.

Use `push Not at hno`. Conclude with `hT0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp hno)`. Establish `hinner : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ` using `fun g x y => LinearIsometry.inner_map_map ⟨(π g).toLinearMap, hnorm g⟩ x y`. Establish `hcomm : ∀ g x, T (π g x) = π g (T x)`. Introduce `g x`.

Establish `hix : Integrable (fun k => rankOne ℂ (π k v) (π k v) x) μ` using `(ContinuousLinearMap.apply ℂ H x).integrable_comp hFi`. Establish `hsh` using `integral_mul_left_eq_self (μ := μ) (fun k => rankOne ℂ (π k v) (π k v) (π g x)) g`. Rewrite using `[hT, ContinuousLinearMap.integral_apply hFi, ContinuousLinearMap.integral_apply hFi, ← ContinuousLinearMap.integral_comp_comm (π g) hix, ← hsh]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Establish `hm : ∀ a b : K, ∀ y, π (a * b) y = π a (π b y)` using `fun a b y => by rw [map_mul]; rfl`. Simplify using `only [rankOne_apply, hm, hinner, map_smul]`. Use `⟨Module.End.eigenspace (T : Module.End ℂ H) c, Module.End.hasEigenvalue_iff.mp hc, ContinuousLinearMap.finite_dimensional_eigenspace hTc c hc0, ?_⟩` and prove the remaining obligations. Introduce `k x hx`. Rewrite `hx`, the goal using `[Module.End.mem_eigenspace_iff]`.

Express the relevant statement in the definitionally equal form `T (π k x) = c • π k x`. Express the relevant statement in the definitionally equal form `T x = c • x at hx`. Rewrite using `[hcomm, hx, map_smul]`.
-/
theorem exists_finiteDimensional_invariant :
    ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
      [SecondCountableTopology K] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] (π : K →* (H →L[ℂ] H)), (∀ k x, ‖π k x‖ = ‖x‖) →
      (∀ x, Continuous fun k => π k x) →
      ∃ S : Submodule ℂ H, S ≠ ⊥ ∧ FiniteDimensional ℂ S ∧ ∀ k, ∀ x ∈ S, π k x ∈ S := by
  intro K _ _ _ _ _ _ H _ _ _ _ π hnorm hcont
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ : ∃ μ : Measure K, IsProbabilityMeasure μ ∧ μ.IsMulLeftInvariant ∧
      μ.IsOpenPosMeasure := by
    refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance, inferInstance⟩
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts K))
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  have hw : Continuous fun k => π k v := hcont v
  have hFc : Continuous fun k => rankOne ℂ (π k v) (π k v) := continuous_rankOne_self.comp hw
  have hFi : Integrable (fun k => rankOne ℂ (π k v) (π k v)) μ :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hTc : IsCompactOperator (∫ k, rankOne ℂ (π k v) (π k v) ∂μ : H →L[ℂ] H) :=
    isCompactOperator_integral hFi (fun k => isCompactOperator_rankOne_self _)
  have hTs := isSymmetric_integral_rankOne hFi
  have hpos : 0 < ∫ k, ‖⟪v, π k v⟫_ℂ‖ ^ 2 ∂μ := by
    have hc : Continuous fun k => ‖⟪v, π k v⟫_ℂ‖ ^ 2 :=
      ((continuous_const.inner hw).norm).pow 2
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) (fun k => by positivity) (x := 1) ?_
    simp [hv]
  have hT0 := integral_rankOne_ne_zero hFi v hpos
  set T : H →L[ℂ] H := ∫ k, rankOne ℂ (π k v) (π k v) ∂μ with hT
  obtain ⟨c, hc, hc0⟩ : ∃ c, Module.End.HasEigenvalue (T : Module.End ℂ H) c ∧ c ≠ 0 := by
    by_contra hno
    push Not at hno
    exact hT0 ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hTc hTs).mp hno)
  have hinner : ∀ g x y, ⟪π g x, π g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    LinearIsometry.inner_map_map ⟨(π g).toLinearMap, hnorm g⟩ x y
  have hcomm : ∀ g x, T (π g x) = π g (T x) := by
    intro g x
    have hix : Integrable (fun k => rankOne ℂ (π k v) (π k v) x) μ :=
      (ContinuousLinearMap.apply ℂ H x).integrable_comp hFi
    have hsh := integral_mul_left_eq_self (μ := μ)
      (fun k => rankOne ℂ (π k v) (π k v) (π g x)) g
    rw [hT, ContinuousLinearMap.integral_apply hFi, ContinuousLinearMap.integral_apply hFi,
      ← ContinuousLinearMap.integral_comp_comm (π g) hix, ← hsh]
    congr 1
    funext k
    have hm : ∀ a b : K, ∀ y, π (a * b) y = π a (π b y) := fun a b y => by rw [map_mul]; rfl
    simp only [rankOne_apply, hm, hinner, map_smul]
  refine ⟨Module.End.eigenspace (T : Module.End ℂ H) c, Module.End.hasEigenvalue_iff.mp hc,
    ContinuousLinearMap.finite_dimensional_eigenspace hTc c hc0, ?_⟩
  intro k x hx
  rw [Module.End.mem_eigenspace_iff] at hx ⊢
  change T (π k x) = c • π k x
  change T x = c • x at hx
  rw [hcomm, hx, map_smul]

end GlobalTheory.CompactRep
