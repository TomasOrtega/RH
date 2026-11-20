import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

namespace InverseCommuting

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/- English proof (translation)
Establish `hPmem : ∀ v : H, K.starProjection v ∈ K`. Introduce `v`. Rewrite using `[Submodule.starProjection_apply]`. Conclude with `Submodule.coe_mem _`. Establish `hzero : ∀ v ∈ Kᗮ, K.starProjection v = 0`.

Introduce `v hv`. Rewrite using `[Submodule.starProjection_apply, Submodule.coe_eq_zero]`. Conclude with `Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv`. Use `show K.starProjection * A = A * K.starProjection`. Use extensionality with `x`.

Simplify using `only [ContinuousLinearMap.mul_apply]`. Establish `hw : x - K.starProjection x ∈ Kᗮ` using `K.sub_starProjection_mem_orthogonal x`. Establish `hAw : A (x - K.starProjection x) ∈ Kᗮ`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `k hk`.

Rewrite using `[← ContinuousLinearMap.adjoint_inner_left]`. Conclude with `(Submodule.mem_orthogonal _ _).1 hw _ (hA' k hk)`. Establish `e1 : K.starProjection (A (K.starProjection x)) = A (K.starProjection x)` using `Submodule.starProjection_eq_self_iff.2 (hA _ (hPmem x))`. Establish `e2` using `hzero _ hAw`. Establish `hx : x = K.starProjection x + (x - K.starProjection x)` using `by abel`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_add, map_add]`. Use `_ = A (K.starProjection x) := by rw [e1, e2, add_zero]`.
-/
theorem commute_proj (K : Submodule ℂ H) [K.HasOrthogonalProjection] (A : H →L[ℂ] H)
    (hA : ∀ x ∈ K, A x ∈ K) (hA' : ∀ x ∈ K, ContinuousLinearMap.adjoint A x ∈ K) :
    Commute K.starProjection A := by
  have hPmem : ∀ v : H, K.starProjection v ∈ K := by
    intro v
    rw [Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  have hzero : ∀ v ∈ Kᗮ, K.starProjection v = 0 := by
    intro v hv
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
    exact Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hv
  show K.starProjection * A = A * K.starProjection
  ext x
  simp only [ContinuousLinearMap.mul_apply]
  have hw : x - K.starProjection x ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
  have hAw : A (x - K.starProjection x) ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro k hk
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (Submodule.mem_orthogonal _ _).1 hw _ (hA' k hk)
  have e1 : K.starProjection (A (K.starProjection x)) = A (K.starProjection x) :=
    Submodule.starProjection_eq_self_iff.2 (hA _ (hPmem x))
  have e2 := hzero _ hAw
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  calc K.starProjection (A x)
      = K.starProjection (A (K.starProjection x)) + K.starProjection (A (x - K.starProjection x)) := by
        conv_lhs => rw [hx]
        rw [map_add, map_add]
    _ = A (K.starProjection x) := by rw [e1, e2, add_zero]

end InverseCommuting

open InverseCommuting

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `H _ _ _ D B ι U hD hB hnorm hadj hU hcomm`. Set `f : ↥D →ₗ[ℂ] H` to `D.subtype ∘ₗ B`. Establish `hf_inj : Function.Injective f`. Introduce `x y hxy`. Establish `h1 : ‖x - y‖ ≤ ‖B (x - y)‖` using `hnorm _`.

Establish `h0 : B (x - y) = 0`. Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.2 (Subtype.ext hxy)`. Rewrite `h1` using `[h0, norm_zero]`. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 h1)`.

Set `R : Submodule ℂ H` to `LinearMap.range f`. Set `eqv : ↥D ≃ₗ[ℂ] ↥R` to `LinearEquiv.ofInjective f hf_inj`. Establish `heqv : ∀ z : ↥D, ((eqv z : ↥R) : H) = ((B z : ↥D) : H)` using `fun z => LinearEquiv.ofInjective_apply f z`. Set `g₀ : ↥R →ₗ[ℂ] H` to `D.subtype ∘ₗ eqv.symm.toLinearMap`. Establish `hg₀ : ∀ r : ↥R, ‖g₀ r‖ ≤ 1 * ‖r‖`.

Introduce `r`. Establish `h2` using `heqv (eqv.symm r)`. Rewrite `h2` using `[eqv.apply_symm_apply]`. Rewrite using `[one_mul]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[h2]`. Use `_ = ‖r‖ := rfl`. Set `g : ↥R →L[ℂ] H` to `g₀.mkContinuous 1 hg₀`. Establish `hgB : ∀ x : ↥D, g ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ = x`. Introduce `x`.

Use `show ((eqv.symm ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ : ↥D) : H) = x`. Use `congr 1`. Apply `eqv.injective` to reduce the goal to its premises. Rewrite using `[eqv.apply_symm_apply]`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `(heqv x).symm`. Establish `hUR : ∀ i, ∀ v ∈ R, U i v ∈ R`. Introduce and unpack `i v ⟨x, rfl⟩`. Take `⟨y, -, hy2⟩` from `hU i x`. Conclude with `⟨y, hy2⟩`.

Set `K : Submodule ℂ H` to `R.topologicalClosure`. Establish `hKcl : IsClosed (K : Set H)` using `R.isClosed_topologicalClosure`. Establish `hUK : ∀ i, ∀ v ∈ K, U i v ∈ K`. Introduce `i`. Establish `hle : R ≤ K.comap (U i : H →ₗ[ℂ] H)` using `fun v hv => R.le_topologicalClosure (hUR i v hv)`.

Establish `hcl : IsClosed ((K.comap (U i : H →ₗ[ℂ] H) : Set H))` using `hKcl.preimage (U i).continuous`. Introduce `v hv`. Conclude with `Submodule.topologicalClosure_minimal R hle hcl hv`. Use `haveI : IsClosed (K : Set H) := hKcl`. Use `haveI : CompleteSpace K := IsClosed.completeSpace_coe`.

Establish `hPcomm : ∀ i, Commute K.starProjection (U i)`. Introduce `i`. Use `commute_proj K (U i) (hUK i) ?_` and prove the remaining obligations. Introduce `v hv`. Take `⟨j, hj⟩` from `hadj i`.

Rewrite using `[hj]`. Conclude with `hUK j v hv`. Establish `hDK : ∀ x : ↥D, (x : H) ∈ K`. Introduce `x`. Take `⟨y, hy1, hy2⟩` from `hcomm K.starProjection hPcomm x`.

Establish `hBx : K.starProjection ((B x : ↥D) : H) = ((B x : ↥D) : H)` using `Submodule.starProjection_eq_self_iff.2 (R.le_topologicalClosure ⟨x, rfl⟩)`. Establish `hByx : B y = B x` using `Subtype.ext (hy2.trans hBx)`. Establish `hyx : y = x` using `hf_inj (by show ((B y : ↥D) : H) = ((B x : ↥D) : H)`. Rewrite using `[hByx])`. Apply `Submodule.starProjection_eq_self_iff.1` to reduce the goal to its premises.

Rewrite using `[← hy1, hyx]`. Establish `hKtop : K = ⊤`. Rewrite using `[eq_top_iff]`. Establish `hsub : (D : Set H) ⊆ K` using `fun v hv => hDK ⟨v, hv⟩`. Introduce `v _`.

Establish `hv : v ∈ closure (D : Set H)`. Rewrite using `[hD.closure_eq]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `(closure_minimal hsub hKcl) hv`. Establish `hRd : Dense (R : Set H)`.

Rewrite using `[dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]`. Use `show ((K : Set H)) = Set.univ`. Rewrite using `[hKtop]`. Both sides reduce to the same expression. Establish `hRdense : DenseRange R.subtypeL` using `hRd.denseRange_val`.

Establish `hRui : IsUniformInducing R.subtypeL` using `isUniformEmbedding_subtype_val.isUniformInducing`. Set `T : H →L[ℂ] H` to `g.extend R.subtypeL`. Establish `hT : ∀ r : ↥R, T r = g r` using `fun r => ContinuousLinearMap.extend_eq g hRdense hRui r`. Establish `hTB : ∀ x : ↥D, T ((B x : ↥D) : H) = x`. Introduce `x`.

Establish `h3` using `hT ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩`. Rewrite `h3` using `[hgB]`. Conclude with `h3`. Establish `base : ∀ x y : ↥D, ⟪T ((B x : ↥D) : H), ((B y : ↥D) : H)⟫_ℂ = ⟪((B x : ↥D) : H), T ((B y : ↥D) : H)⟫_ℂ`. Introduce `x y`.

Rewrite using `[hTB, hTB]`. Conclude with `(hB x y).symm`. Establish `step1 : ∀ (u : H) (y : ↥D), ⟪T u, ((B y : ↥D) : H)⟫_ℂ = ⟪u, T ((B y : ↥D) : H)⟫_ℂ`. Introduce `u y`. Establish `hfun` using `Continuous.ext_on hRd (T.continuous.inner continuous_const) (continuous_id.inner continuous_const) (f := fun u => ⟪T u, ((B y : ↥D) : H)⟫_ℂ) (g := fun u => ⟪u, T ((B y : ↥D) : H)⟫_ℂ) (by`.

Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `base x y)`. Conclude with `congrFun hfun u`. Establish `hsym : ∀ u v : H, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ`. Introduce `u v`.

Establish `hfun` using `Continuous.ext_on hRd (continuous_const.inner continuous_id) (continuous_const.inner T.continuous) (f := fun v => ⟪T u, v⟫_ℂ) (g := fun v => ⟪u, T v⟫_ℂ) (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `step1 u y)`. Conclude with `congrFun hfun v`. Use `⟨T, ?_, ?_, hTB⟩` and prove the remaining obligations.

Use `show star T = T`. Rewrite using `[ContinuousLinearMap.star_eq_adjoint]`. Conclude with `((ContinuousLinearMap.eq_adjoint_iff T T).2 hsym).symm`. Introduce `i show T * U i = U i * T`. Apply `ContinuousLinearMap.coeFn_injective` to reduce the goal to its premises.

Use `Continuous.ext_on hRd (T * U i).continuous (U i * T).continuous ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, hy1, hy2⟩` from `hU i x`. Use `show T (U i ((B x : ↥D) : H)) = U i (T ((B x : ↥D) : H))`. Rewrite using `[← hy2, hTB, hTB, hy1]`.
-/
theorem inverse_holds : Inv := by
  intro H _ _ _ D B ι U hD hB hnorm hadj hU hcomm
  let f : ↥D →ₗ[ℂ] H := D.subtype ∘ₗ B
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have h1 : ‖x - y‖ ≤ ‖B (x - y)‖ := hnorm _
    have h0 : B (x - y) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (Subtype.ext hxy)
    rw [h0, norm_zero] at h1
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h1)
  let R : Submodule ℂ H := LinearMap.range f
  let eqv : ↥D ≃ₗ[ℂ] ↥R := LinearEquiv.ofInjective f hf_inj
  have heqv : ∀ z : ↥D, ((eqv z : ↥R) : H) = ((B z : ↥D) : H) := fun z => LinearEquiv.ofInjective_apply f z
  let g₀ : ↥R →ₗ[ℂ] H := D.subtype ∘ₗ eqv.symm.toLinearMap
  have hg₀ : ∀ r : ↥R, ‖g₀ r‖ ≤ 1 * ‖r‖ := by
    intro r
    have h2 := heqv (eqv.symm r)
    rw [eqv.apply_symm_apply] at h2
    rw [one_mul]
    calc ‖g₀ r‖ = ‖eqv.symm r‖ := rfl
      _ ≤ ‖B (eqv.symm r)‖ := hnorm _
      _ = ‖(r : H)‖ := by
        show ‖((B (eqv.symm r) : ↥D) : H)‖ = ‖(r : H)‖
        rw [h2]
      _ = ‖r‖ := rfl
  let g : ↥R →L[ℂ] H := g₀.mkContinuous 1 hg₀
  have hgB : ∀ x : ↥D, g ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ = x := by
    intro x
    show ((eqv.symm ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩ : ↥D) : H) = x
    congr 1
    apply eqv.injective
    rw [eqv.apply_symm_apply]
    apply Subtype.ext
    exact (heqv x).symm
  have hUR : ∀ i, ∀ v ∈ R, U i v ∈ R := by
    rintro i v ⟨x, rfl⟩
    obtain ⟨y, -, hy2⟩ := hU i x
    exact ⟨y, hy2⟩
  let K : Submodule ℂ H := R.topologicalClosure
  have hKcl : IsClosed (K : Set H) := R.isClosed_topologicalClosure
  have hUK : ∀ i, ∀ v ∈ K, U i v ∈ K := by
    intro i
    have hle : R ≤ K.comap (U i : H →ₗ[ℂ] H) := fun v hv => R.le_topologicalClosure (hUR i v hv)
    have hcl : IsClosed ((K.comap (U i : H →ₗ[ℂ] H) : Set H)) := hKcl.preimage (U i).continuous
    intro v hv
    exact Submodule.topologicalClosure_minimal R hle hcl hv
  haveI : IsClosed (K : Set H) := hKcl
  haveI : CompleteSpace K := IsClosed.completeSpace_coe
  have hPcomm : ∀ i, Commute K.starProjection (U i) := by
    intro i
    refine commute_proj K (U i) (hUK i) ?_
    intro v hv
    obtain ⟨j, hj⟩ := hadj i
    rw [hj]
    exact hUK j v hv
  have hDK : ∀ x : ↥D, (x : H) ∈ K := by
    intro x
    obtain ⟨y, hy1, hy2⟩ := hcomm K.starProjection hPcomm x
    have hBx : K.starProjection ((B x : ↥D) : H) = ((B x : ↥D) : H) :=
      Submodule.starProjection_eq_self_iff.2 (R.le_topologicalClosure ⟨x, rfl⟩)
    have hByx : B y = B x := Subtype.ext (hy2.trans hBx)
    have hyx : y = x := hf_inj (by
      show ((B y : ↥D) : H) = ((B x : ↥D) : H)
      rw [hByx])
    apply Submodule.starProjection_eq_self_iff.1
    rw [← hy1, hyx]
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    have hsub : (D : Set H) ⊆ K := fun v hv => hDK ⟨v, hv⟩
    intro v _
    have hv : v ∈ closure (D : Set H) := by
      rw [hD.closure_eq]
      trivial
    exact (closure_minimal hsub hKcl) hv
  have hRd : Dense (R : Set H) := by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe]
    show ((K : Set H)) = Set.univ
    rw [hKtop]
    rfl
  have hRdense : DenseRange R.subtypeL := hRd.denseRange_val
  have hRui : IsUniformInducing R.subtypeL := isUniformEmbedding_subtype_val.isUniformInducing
  let T : H →L[ℂ] H := g.extend R.subtypeL
  have hT : ∀ r : ↥R, T r = g r := fun r => ContinuousLinearMap.extend_eq g hRdense hRui r
  have hTB : ∀ x : ↥D, T ((B x : ↥D) : H) = x := by
    intro x
    have h3 := hT ⟨((B x : ↥D) : H), LinearMap.mem_range_self f x⟩
    rw [hgB] at h3
    exact h3
  have base : ∀ x y : ↥D, ⟪T ((B x : ↥D) : H), ((B y : ↥D) : H)⟫_ℂ = ⟪((B x : ↥D) : H), T ((B y : ↥D) : H)⟫_ℂ := by
    intro x y
    rw [hTB, hTB]
    exact (hB x y).symm
  have step1 : ∀ (u : H) (y : ↥D), ⟪T u, ((B y : ↥D) : H)⟫_ℂ = ⟪u, T ((B y : ↥D) : H)⟫_ℂ := by
    intro u y
    have hfun := Continuous.ext_on hRd (T.continuous.inner continuous_const)
      (continuous_id.inner continuous_const)
      (f := fun u => ⟪T u, ((B y : ↥D) : H)⟫_ℂ) (g := fun u => ⟪u, T ((B y : ↥D) : H)⟫_ℂ)
      (by
        rintro _ ⟨x, rfl⟩
        exact base x y)
    exact congrFun hfun u
  have hsym : ∀ u v : H, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ := by
    intro u v
    have hfun := Continuous.ext_on hRd (continuous_const.inner continuous_id)
      (continuous_const.inner T.continuous)
      (f := fun v => ⟪T u, v⟫_ℂ) (g := fun v => ⟪u, T v⟫_ℂ)
      (by
        rintro _ ⟨y, rfl⟩
        exact step1 u y)
    exact congrFun hfun v
  refine ⟨T, ?_, ?_, hTB⟩
  · show star T = T
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact ((ContinuousLinearMap.eq_adjoint_iff T T).2 hsym).symm
  · intro i
    show T * U i = U i * T
    apply ContinuousLinearMap.coeFn_injective
    refine Continuous.ext_on hRd (T * U i).continuous (U i * T).continuous ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy1, hy2⟩ := hU i x
    show T (U i ((B x : ↥D) : H)) = U i (T ((B x : ↥D) : H))
    rw [← hy2, hTB, hTB, hy1]

end PositivityTheory.RgHe3
