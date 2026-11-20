import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

/- English proof (translation)
Apply `Submodule.eq_starProjection_of_mem_orthogonal' (z := B (x - Y.starProjection x)) (hB _ (Y.starProjection_apply_mem x))` to reduce the goal to its premises. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `y hy`. Rewrite using `[← ContinuousLinearMap.adjoint_inner_left, hBC]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (hC y hy) (Submodule.sub_starProjection_mem_orthogonal (K := Y) x)`.

Rewrite using `[← map_add, add_sub_cancel]`.
-/
private theorem starProjection_apply_comm_of_invariant_adjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (Y : Submodule ℂ H) [Y.HasOrthogonalProjection] (B C : H →L[ℂ] H)
    (hB : ∀ y ∈ Y, B y ∈ Y) (hC : ∀ y ∈ Y, C y ∈ Y)
    (hBC : ContinuousLinearMap.adjoint B = C) (x : H) :
    Y.starProjection (B x) = B (Y.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal' (z := B (x - Y.starProjection x))
    (hB _ (Y.starProjection_apply_mem x))
  · rw [Submodule.mem_orthogonal]
    intro y hy
    rw [← ContinuousLinearMap.adjoint_inner_left, hBC]
    exact Submodule.inner_right_of_mem_orthogonal (hC y hy)
      (Submodule.sub_starProjection_mem_orthogonal (K := Y) x)
  · rw [← map_add, add_sub_cancel]

/- English proof (translation)
Take `⟨s, rfl⟩` from `hM`. Establish `key : ∀ t : Finset H, (↑t : Set H) ⊆ W → ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ (↑t : Set H) ⊆ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`.

Introduce `_`. Use `⟨⊥, bot_le, inferInstance, by simp, fun i y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[(Submodule.mem_bot ℂ).1 hy, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `insert a t ha ih`.

Introduce `hsub`. Rewrite `hsub` using `[Finset.coe_insert, Set.insert_subset_iff]`. Take `⟨Y1, h1W, h1f, h1t, h1A⟩` from `ih hsub.2`. Take `⟨Y2, h2W, h2f, h2a, h2A⟩` from `hW a hsub.1`. Use `haveI := h1f`.

Use `haveI := h2f`. Use `⟨Y1 ⊔ Y2, sup_le h1W h2W, inferInstance, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.coe_insert, Set.insert_subset_iff]`. Conclude with `⟨Submodule.mem_sup_right h2a, h1t.trans (SetLike.coe_subset_coe.2 le_sup_left)⟩`. Introduce `i y hy`.

Take `⟨y1, hy1, y2, hy2, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (h1A i y1 hy1) (h2A i y2 hy2)`. Take `⟨Y, hYW, hYf, hsY, hYA⟩` from `key s (Submodule.span_le.1 hMW)`. Conclude with `⟨Y, hYW, hYf, Submodule.span_le.2 hsY, hYA⟩`.
-/
private theorem exists_finiteDimensional_invariant_le_of_fg {ι H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : ι → H →L[ℂ] H) (W M : Submodule ℂ H) (hM : M.FG) (hMW : M ≤ W)
    (hW : ∀ w ∈ W, ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ w ∈ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y) :
    ∃ Y ≤ W, FiniteDimensional ℂ Y ∧ M ≤ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have key : ∀ t : Finset H, (↑t : Set H) ⊆ W → ∃ Y ≤ W, FiniteDimensional ℂ Y ∧
      (↑t : Set H) ⊆ Y ∧ ∀ i, ∀ y ∈ Y, A i y ∈ Y := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨⊥, bot_le, inferInstance, by simp, fun i y hy => ?_⟩
      rw [(Submodule.mem_bot ℂ).1 hy, map_zero]
      exact Submodule.zero_mem _
    | insert a t ha ih =>
      intro hsub
      rw [Finset.coe_insert, Set.insert_subset_iff] at hsub
      obtain ⟨Y1, h1W, h1f, h1t, h1A⟩ := ih hsub.2
      obtain ⟨Y2, h2W, h2f, h2a, h2A⟩ := hW a hsub.1
      haveI := h1f
      haveI := h2f
      refine ⟨Y1 ⊔ Y2, sup_le h1W h2W, inferInstance, ?_, ?_⟩
      · rw [Finset.coe_insert, Set.insert_subset_iff]
        exact ⟨Submodule.mem_sup_right h2a, h1t.trans (SetLike.coe_subset_coe.2 le_sup_left)⟩
      · intro i y hy
        obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
        rw [map_add]
        exact Submodule.add_mem_sup (h1A i y1 hy1) (h2A i y2 hy2)
  obtain ⟨Y, hYW, hYf, hsY, hYA⟩ := key s (Submodule.span_le.1 hMW)
  exact ⟨Y, hYW, hYf, Submodule.span_le.2 hsY, hYA⟩

/- English proof (translation)
Introduce `ι H _ _ _ A hA W N hN hW v hv hP`. Use `haveI := hN`. Establish `hfg : (N ⊓ W).FG` using `by haveI : FiniteDimensional ℂ ↥(N ⊓ W) := Submodule.finiteDimensional_of_le inf_le_left`. Conclude with `(Submodule.fg_iff_finiteDimensional _).2 inferInstance`. Take `⟨Y0, hY0W, hY0f, hNY0, hY0A⟩` from `exists_finiteDimensional_invariant_le_of_fg A W (N ⊓ W) hfg inf_le_right hW`.

Use `haveI := hY0f`. Establish `hproj : ∀ (Y : Submodule ℂ H) [FiniteDimensional ℂ Y], Y ≤ W → (∀ i, ∀ y ∈ Y, A i y ∈ Y) → Y0 ≤ Y → Y0.starProjection v = Y.starProjection v`. Introduce `Y _ hYW hYA hY0Y`. Establish `h1 : Y.starProjection v ∈ N`. Apply `hP` to reduce the goal to its premises.

Introduce `i x`. Take `⟨j, hj⟩` from `hA i`. Conclude with `starProjection_apply_comm_of_invariant_adjoint Y (A i) (A j) (hYA i) (hYA j) hj x`. Introduce `x`. Conclude with `hYW (Y.starProjection_apply_mem x)`.

Establish `h2 : Y.starProjection v ∈ Y0` using `hNY0 ⟨h1, hYW (Y.starProjection_apply_mem v)⟩`. Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero h2` to reduce the goal to its premises. Introduce `w hw`. Conclude with `Submodule.starProjection_inner_eq_zero v w (hY0Y hw)`. Establish `horth : ∀ w ∈ W, inner ℂ w (v - Y0.starProjection v) = 0`.

Introduce `w hw`. Take `⟨Y1, h1W, h1f, hw1, h1A⟩` from `hW w hw`. Use `haveI := h1f`. Establish `hY` using `hproj (Y0 ⊔ Y1) (sup_le hY0W h1W) (fun i y hy => by`. Take `⟨y1, hy1, y2, hy2, rfl⟩` from `Submodule.mem_sup.1 hy`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hY0A i y1 hy1) (h1A i y2 hy2)) le_sup_left`. Rewrite using `[hY, inner_eq_zero_symm]`. Conclude with `Submodule.starProjection_inner_eq_zero v w (Submodule.mem_sup_right hw1)`. Establish `hcl : v - Y0.starProjection v ∈ W.topologicalClosure` using `W.topologicalClosure.sub_mem hv (W.le_topologicalClosure (hY0W (Y0.starProjection_apply_mem v)))`.

Establish `hsub : closure (W : Set H) ⊆ {x | inner ℂ x (v - Y0.starProjection v) = 0}` using `closure_minimal horth (isClosed_eq (continuous_id.inner continuous_const) continuous_const)`. Establish `hzero : inner ℂ (v - Y0.starProjection v) (v - Y0.starProjection v) = 0`. Apply `hsub` to reduce the goal to its premises. Rewrite using `[← Submodule.topologicalClosure_coe]`. Conclude with `hcl`.

Rewrite `hzero` using `[inner_self_eq_zero, sub_eq_zero]`. Rewrite using `[hzero]`. Conclude with `hY0W (Y0.starProjection_apply_mem v)`.
-/
theorem UpperTheory.V.KernelIndexFullLattice.absApprox_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsApprox := by
  intro ι H _ _ _ A hA W N hN hW v hv hP
  classical
  haveI := hN
  have hfg : (N ⊓ W).FG := by
    haveI : FiniteDimensional ℂ ↥(N ⊓ W) := Submodule.finiteDimensional_of_le inf_le_left
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  obtain ⟨Y0, hY0W, hY0f, hNY0, hY0A⟩ := exists_finiteDimensional_invariant_le_of_fg A W (N ⊓ W) hfg inf_le_right hW
  haveI := hY0f
  have hproj : ∀ (Y : Submodule ℂ H) [FiniteDimensional ℂ Y], Y ≤ W →
      (∀ i, ∀ y ∈ Y, A i y ∈ Y) → Y0 ≤ Y → Y0.starProjection v = Y.starProjection v := by
    intro Y _ hYW hYA hY0Y
    have h1 : Y.starProjection v ∈ N := by
      apply hP
      · intro i x
        obtain ⟨j, hj⟩ := hA i
        exact starProjection_apply_comm_of_invariant_adjoint Y (A i) (A j) (hYA i) (hYA j) hj x
      · intro x
        exact hYW (Y.starProjection_apply_mem x)
    have h2 : Y.starProjection v ∈ Y0 := hNY0 ⟨h1, hYW (Y.starProjection_apply_mem v)⟩
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero h2
    intro w hw
    exact Submodule.starProjection_inner_eq_zero v w (hY0Y hw)
  have horth : ∀ w ∈ W, inner ℂ w (v - Y0.starProjection v) = 0 := by
    intro w hw
    obtain ⟨Y1, h1W, h1f, hw1, h1A⟩ := hW w hw
    haveI := h1f
    have hY := hproj (Y0 ⊔ Y1) (sup_le hY0W h1W) (fun i y hy => by
      obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add]
      exact Submodule.add_mem_sup (hY0A i y1 hy1) (h1A i y2 hy2)) le_sup_left
    rw [hY, inner_eq_zero_symm]
    exact Submodule.starProjection_inner_eq_zero v w (Submodule.mem_sup_right hw1)
  have hcl : v - Y0.starProjection v ∈ W.topologicalClosure :=
    W.topologicalClosure.sub_mem hv
      (W.le_topologicalClosure (hY0W (Y0.starProjection_apply_mem v)))
  have hsub : closure (W : Set H) ⊆ {x | inner ℂ x (v - Y0.starProjection v) = 0} :=
    closure_minimal horth (isClosed_eq (continuous_id.inner continuous_const) continuous_const)
  have hzero : inner ℂ (v - Y0.starProjection v) (v - Y0.starProjection v) = 0 := by
    apply hsub
    rw [← Submodule.topologicalClosure_coe]
    exact hcl
  rw [inner_self_eq_zero, sub_eq_zero] at hzero
  rw [hzero]
  exact hY0W (Y0.starProjection_apply_mem v)
