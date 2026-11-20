import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CocycleZeroMemInvariants
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.LengthExact

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Introduce `R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h _ γ hγ hcl`. Establish `memU : ∀ (V : Subgroup G) (m : M), m ∈ H0U ρ V ↔ ∀ g ∈ V, ρ g m = m`. Introduce `V m`. Simplify using `[H0U, H0, Representation.mem_invariants]`. Establish `hinv : ∀ m ∈ H0U ρ U', ρ γ m ∈ H0U ρ U'`.

Introduce `m hm`. Rewrite `hm`, the goal using `[memU]`. Introduce `u hu`. Establish `hc` using `Subgroup.Normal.conj_mem ‹(U'.subgroupOf U).Normal› ⟨u, h hu⟩ (by simpa [Subgroup.mem_subgroupOf] using hu) (⟨γ, hγ⟩⁻¹)`. Rewrite `hc` using `[Subgroup.mem_subgroupOf]`.

Simplify using `only [inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv] at hc`. Establish `e : ρ u (ρ γ m) = ρ γ (ρ (γ⁻¹ * u * γ) m)`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]`. Use `congr 2`. Use `group`.

Rewrite using `[e, hm _ hc]`. Set `T : H0U ρ U' →ₗ[R] H0U ρ U'` to `LinearMap.codRestrict (H0U ρ U') ((ρ γ - LinearMap.id) ∘ₗ (H0U ρ U').subtype) (fun m => Submodule.sub_mem _ (hinv m m.2) m.2)`. Establish `hT : ∀ m : H0U ρ U', ((T m : H0U ρ U') : M) = ρ γ m - m` using `fun m => rfl`. Take `⟨φ, hφ⟩` from `kerResGen1 R G M ρ hρ U' U h γ hγ hcl T hT`. Use `⟨fun hfin => ?_, fun hsurj => ?_⟩` and prove the remaining obligations.

Establish `hfix : ∀ m : H0U ρ U', T m = 0 → (m : M) ∈ H0U ρ U`. Introduce `m hm0`. Establish `hγm : ρ γ m = m`. Use `congrArg Subtype.val hm0` as an intermediate fact. Rewrite `this` using `[hT]`.

Conclude with `sub_eq_zero.mp this`. Set `S : Subgroup G` to `{ carrier := {g | ρ g m = m} mul_mem' := by`. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *`. Rewrite using `[hb, ha]`.

Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := by`. Introduce `a ha`. Simplify using `only [Set.mem_setOf_eq] at *`. Combine the equalities or inequalities in the displayed calculation.

Establish `hScl : IsClosed (S : Set G)` using `IsClosed.preimage (hρ.comp (Continuous.prodMk continuous_id continuous_const)) (isClosed_singleton (x := (m : M)))`. Establish `hle : Subgroup.zpowers γ ⊔ U' ≤ S` using `sup_le (Subgroup.zpowers_le.mpr hγm) (fun u hu => (memU U' m).mp m.2 u hu)`. Establish `hUS` using `hcl.trans (Subgroup.topologicalClosure_minimal _ hle hScl)`. Conclude with `(memU U m).mpr fun g hg => hUS hg`. Set `ι : LinearMap.ker T →ₗ[R] H0U ρ U` to `LinearMap.codRestrict (H0U ρ U) ((H0U ρ U').subtype ∘ₗ (LinearMap.ker T).subtype) (fun m => hfix m m.2)`.

Establish `hι : Function.Injective ι`. Introduce `a b hab`. Establish `e : ((ι a : H0U ρ U) : M) = ((ι b : H0U ρ U) : M)` using `congrArg Subtype.val hab`. Conclude with `Subtype.ext (Subtype.ext e)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hq : ∀ x : H0U ρ U' ⧸ LinearMap.range T, x = 0`. Introduce `x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨m', hm', he⟩` from `hsurj y y.2`.

Conclude with `⟨⟨m', hm'⟩, Subtype.ext (by rw [hT]; exact he)⟩`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`. Use `@hφ ⟨x, hx⟩ 0 (by rw [hq (φ _), hq (φ 0)])` as an intermediate fact. Rewrite using `[Submodule.mem_bot]`.

Conclude with `congrArg Subtype.val this`.
-/
theorem UpperTheory.V.Base.kerResCyc :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G), γ ∈ U →
      U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure →
      (Module.length R (H0U ρ U') ≠ ⊤ → Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (H0U ρ U)) ∧
      ((∀ m ∈ H0U ρ U', ∃ m' ∈ H0U ρ U', ρ γ m' - m' = m) → Function.Injective (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h _ γ hγ hcl
  have memU : ∀ (V : Subgroup G) (m : M), m ∈ H0U ρ V ↔ ∀ g ∈ V, ρ g m = m := by
    intro V m
    simp [H0U, H0, Representation.mem_invariants]
  have hinv : ∀ m ∈ H0U ρ U', ρ γ m ∈ H0U ρ U' := by
    intro m hm
    rw [memU] at hm ⊢
    intro u hu
    have hc := Subgroup.Normal.conj_mem ‹(U'.subgroupOf U).Normal› ⟨u, h hu⟩
      (by simpa [Subgroup.mem_subgroupOf] using hu) (⟨γ, hγ⟩⁻¹)
    rw [Subgroup.mem_subgroupOf] at hc
    simp only [inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv] at hc
    have e : ρ u (ρ γ m) = ρ γ (ρ (γ⁻¹ * u * γ) m) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hm _ hc]
  let T : H0U ρ U' →ₗ[R] H0U ρ U' := LinearMap.codRestrict (H0U ρ U')
    ((ρ γ - LinearMap.id) ∘ₗ (H0U ρ U').subtype)
    (fun m => Submodule.sub_mem _ (hinv m m.2) m.2)
  have hT : ∀ m : H0U ρ U', ((T m : H0U ρ U') : M) = ρ γ m - m := fun m => rfl
  obtain ⟨φ, hφ⟩ := kerResGen1 R G M ρ hρ U' U h γ hγ hcl T hT
  refine ⟨fun hfin => ?_, fun hsurj => ?_⟩
  · have hfix : ∀ m : H0U ρ U', T m = 0 → (m : M) ∈ H0U ρ U := by
      intro m hm0
      have hγm : ρ γ m = m := by
        have := congrArg Subtype.val hm0
        rw [hT] at this
        exact sub_eq_zero.mp this
      let S : Subgroup G :=
        { carrier := {g | ρ g m = m}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at *
            calc ρ a⁻¹ m = ρ a⁻¹ (ρ a m) := by rw [ha]
              _ = m := by rw [← Module.End.mul_apply, ← map_mul]; simp }
      have hScl : IsClosed (S : Set G) :=
        IsClosed.preimage (hρ.comp (Continuous.prodMk continuous_id continuous_const))
          (isClosed_singleton (x := (m : M)))
      have hle : Subgroup.zpowers γ ⊔ U' ≤ S :=
        sup_le (Subgroup.zpowers_le.mpr hγm) (fun u hu => (memU U' m).mp m.2 u hu)
      have hUS := hcl.trans (Subgroup.topologicalClosure_minimal _ hle hScl)
      exact (memU U m).mpr fun g hg => hUS hg
    let ι : LinearMap.ker T →ₗ[R] H0U ρ U := LinearMap.codRestrict (H0U ρ U)
      ((H0U ρ U').subtype ∘ₗ (LinearMap.ker T).subtype) (fun m => hfix m m.2)
    have hι : Function.Injective ι := by
      intro a b hab
      have e : ((ι a : H0U ρ U) : M) = ((ι b : H0U ρ U) : M) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext e)
    calc Module.length R (LinearMap.ker (resU ρ h))
        ≤ Module.length R (H0U ρ U' ⧸ LinearMap.range T) := Module.length_le_of_injective φ hφ
      _ = Module.length R (LinearMap.ker T) :=
        (KStar.Selmer.length_ker_eq_length_coker T hfin).symm
      _ ≤ Module.length R (H0U ρ U) := Module.length_le_of_injective ι hι
  · have hq : ∀ x : H0U ρ U' ⧸ LinearMap.range T, x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨m', hm', he⟩ := hsurj y y.2
      exact ⟨⟨m', hm'⟩, Subtype.ext (by rw [hT]; exact he)⟩
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have := @hφ ⟨x, hx⟩ 0 (by rw [hq (φ _), hq (φ 0)])
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val this
