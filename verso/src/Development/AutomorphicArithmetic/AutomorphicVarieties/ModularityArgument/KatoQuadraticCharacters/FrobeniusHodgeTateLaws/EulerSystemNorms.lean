import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob

open UpperTheory.V.Z.Kato.Joint Topology Filter

/- English proof (translation)
Establish `h1 : (Subalgebra.toSubmodule E.toSubalgebra).FG` using `Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite K E))`. Take `⟨t, ht⟩` from `h1`. Use `⟨t, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`.

Establish `hle : Algebra.adjoin K (t : Set Ω) ≤ AlgHom.equalizer (g : Ω →ₐ[K] Ω) (AlgHom.id K Ω)` using `Algebra.adjoin_le (fun y hy => by`. Rewrite using `[SetLike.mem_coe, AlgHom.mem_equalizer]`. Simplify using `using hg y hy)`. Establish `hx1 : x ∈ Submodule.span K (t : Set Ω)`. Rewrite using `[ht]`.

Conclude with `hx`. Establish `hx2 : x ∈ Algebra.adjoin K (t : Set Ω)` using `Algebra.span_le_adjoin K _ hx1`. Establish `hx3` using `hle hx2`. Rewrite `hx3` using `[AlgHom.mem_equalizer]`. Simplify using `using hx3`.
-/
private theorem mem_fixingSubgroup_of_fixes_finite_set (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] :
    ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ E.fixingSubgroup := by
  have h1 : (Subalgebra.toSubmodule E.toSubalgebra).FG :=
    Module.Finite.iff_fg.1 (inferInstanceAs (Module.Finite K E))
  obtain ⟨t, ht⟩ := h1
  refine ⟨t, fun g hg => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hle : Algebra.adjoin K (t : Set Ω) ≤ AlgHom.equalizer (g : Ω →ₐ[K] Ω) (AlgHom.id K Ω) :=
    Algebra.adjoin_le (fun y hy => by
      rw [SetLike.mem_coe, AlgHom.mem_equalizer]
      simpa using hg y hy)
  have hx1 : x ∈ Submodule.span K (t : Set Ω) := by
    rw [ht]
    exact hx
  have hx2 : x ∈ Algebra.adjoin K (t : Set Ω) := Algebra.span_le_adjoin K _ hx1
  have hx3 := hle hx2
  rw [AlgHom.mem_equalizer] at hx3
  simpa using hx3

/- English proof (translation)
Establish `hδ2 : 0 < δ / 2` using `half_pos hδ`. Establish `key : ∀ s : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ ∀ g ∈ E.fixingSubgroup, ‖f (s * g) - f s‖ < δ / 2`. Introduce `s`. Establish `hc : Continuous fun g : Ω ≃ₐ[K] Ω => ‖f (s * g) - f s‖` using `((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).norm`. Establish `hA : {g : Ω ≃ₐ[K] Ω | ‖f (s * g) - f s‖ < δ / 2} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω)` using `IsOpen.mem_nhds (isOpen_lt hc continuous_const) (by simp [hδ2])`.

Take `⟨E, hE, hsub⟩` from `(krullTopology_mem_nhds_one_iff K Ω _).1 hA`. Conclude with `⟨E, hE, fun g hg => hsub hg⟩`. Use `choose E hEf hE using key`. Set `U : (Ω ≃ₐ[K] Ω) → Set (Ω ≃ₐ[K] Ω)` to `fun i => {h | i⁻¹ * h ∈ (E i).fixingSubgroup}`. Establish `hUo : ∀ i, IsOpen (U i)`.

Introduce `i`. Use `haveI := hEf i`. Conclude with `(IntermediateField.fixingSubgroup_isOpen (E i)).preimage (continuous_const.mul continuous_id)`. Establish `hUc : Set.univ ⊆ ⋃ i, U i`. Introduce `h _`.

Use `Set.mem_iUnion.2 ⟨h, ?_⟩` and prove the remaining obligations. Use `show h⁻¹ * h ∈ (E h).fixingSubgroup`. Rewrite using `[inv_mul_cancel]`. Conclude with `one_mem _`. Take `⟨S, hS⟩` from `isCompact_univ.elim_finite_subcover U hUo hUc`.

Establish `hT : ∀ i, ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ (E i).fixingSubgroup`. Introduce `i`. Use `haveI := hEf i`. Conclude with `mem_fixingSubgroup_of_fixes_finite_set K Ω (E i)`. Use `choose T hT using hT`.

Use `⟨S.biUnion T, fun s s' hs' => ?_⟩` and prove the remaining obligations. Take `⟨i, hiS, hi⟩` from `Set.mem_iUnion₂.1 (hS (Set.mem_univ s))`. Establish `hi' : i⁻¹ * s ∈ (E i).fixingSubgroup` using `hi`. Establish `hs'i : s' ∈ (E i).fixingSubgroup` using `hT i s' (fun x hx => hs' x (Finset.mem_biUnion.2 ⟨i, hiS, hx⟩))`. Establish `h1` using `hE i _ (mul_mem hi' hs'i)`.

Establish `h2` using `hE i _ hi'`. Rewrite `h1` using `[← mul_assoc, mul_inv_cancel_left]`. Rewrite `h2` using `[mul_inv_cancel_left]`. Establish `h3 : f (s * s') - f s = (f (s * s') - f i) - (f s - f i)` using `by abel`. Rewrite using `[h3]`.

Use `norm_sub_le (f (s * s') - f i) (f s - f i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem uniform_continuity_galois_group (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] {X : Type} [NormedAddCommGroup X]
    (f : (Ω ≃ₐ[K] Ω) → X) (hf : Continuous f) (δ : ℝ) (hδ : 0 < δ) :
    ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[K] Ω, (∀ x ∈ E0, s' x = x) → ‖f (s * s') - f s‖ < δ := by
  classical
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have key : ∀ s : Ω ≃ₐ[K] Ω, ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∀ g ∈ E.fixingSubgroup, ‖f (s * g) - f s‖ < δ / 2 := by
    intro s
    have hc : Continuous fun g : Ω ≃ₐ[K] Ω => ‖f (s * g) - f s‖ :=
      ((hf.comp (continuous_const.mul continuous_id)).sub continuous_const).norm
    have hA : {g : Ω ≃ₐ[K] Ω | ‖f (s * g) - f s‖ < δ / 2} ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) :=
      IsOpen.mem_nhds (isOpen_lt hc continuous_const) (by simp [hδ2])
    obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff K Ω _).1 hA
    exact ⟨E, hE, fun g hg => hsub hg⟩
  choose E hEf hE using key
  let U : (Ω ≃ₐ[K] Ω) → Set (Ω ≃ₐ[K] Ω) := fun i => {h | i⁻¹ * h ∈ (E i).fixingSubgroup}
  have hUo : ∀ i, IsOpen (U i) := by
    intro i
    haveI := hEf i
    exact (IntermediateField.fixingSubgroup_isOpen (E i)).preimage (continuous_const.mul continuous_id)
  have hUc : Set.univ ⊆ ⋃ i, U i := by
    intro h _
    refine Set.mem_iUnion.2 ⟨h, ?_⟩
    show h⁻¹ * h ∈ (E h).fixingSubgroup
    rw [inv_mul_cancel]
    exact one_mem _
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hUo hUc
  have hT : ∀ i, ∃ T : Finset Ω, ∀ g : Ω ≃ₐ[K] Ω, (∀ x ∈ T, g x = x) → g ∈ (E i).fixingSubgroup := by
    intro i
    haveI := hEf i
    exact mem_fixingSubgroup_of_fixes_finite_set K Ω (E i)
  choose T hT using hT
  refine ⟨S.biUnion T, fun s s' hs' => ?_⟩
  obtain ⟨i, hiS, hi⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ s))
  have hi' : i⁻¹ * s ∈ (E i).fixingSubgroup := hi
  have hs'i : s' ∈ (E i).fixingSubgroup :=
    hT i s' (fun x hx => hs' x (Finset.mem_biUnion.2 ⟨i, hiS, hx⟩))
  have h1 := hE i _ (mul_mem hi' hs'i)
  have h2 := hE i _ hi'
  rw [← mul_assoc, mul_inv_cancel_left] at h1
  rw [mul_inv_cancel_left] at h2
  have h3 : f (s * s') - f s = (f (s * s') - f i) - (f s - f i) := by abel
  rw [h3]
  have := norm_sub_le (f (s * s') - f i) (f s - f i)
  linarith

/- English proof (translation)
Introduce `l _ Ω _ _ _ f hf δ hδ`. Use `haveI : IsGalois ℚ Ω := inferInstance`. Conclude with `uniform_continuity_galois_group ℚ Ω f hf δ hδ`.
-/
theorem UpperTheory.V.Z.Kato.Joint.unif :
    UpperTheory.V.Z.Kato.Joint.Unif := by
  intro l _ Ω _ _ _ f hf δ hδ
  haveI : IsGalois ℚ Ω := inferInstance
  exact uniform_continuity_galois_group ℚ Ω f hf δ hδ
