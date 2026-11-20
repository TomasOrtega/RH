import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.PrincZl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Introduce `k Ω _ _ _ _ _ l _ U hUc hUg hUk`. Establish `hχc : Continuous (cycZ k Ω l)` using `continuous_cycZ k Ω l`. Establish `hHc : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ)`. Rewrite using `[Subgroup.coe_map]`. Conclude with `(hUc.isCompact.image hχc).isClosed`.

Establish `hHp : U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l (qExp l)`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Establish `h` using `hUg hu`. Simplify using `only [gamU, levU, Subgroup.mem_inf, Subgroup.mem_comap] at h`. Conclude with `h.2`.

Establish `hHb : U.map (cycZ k Ω l) ≠ ⊥`. Introduce `h`. Apply `hUk` to reduce the goal to its premises. Introduce `u hu`. Establish `hm : cycZ k Ω l u ∈ U.map (cycZ k Ω l)` using `⟨u, hu, rfl⟩`.

Rewrite `hm` using `[h]`. Conclude with `MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hm)`. Take `⟨⟨e⟩, htor⟩` from `princZl l _ hHc hHp hHb`. Set `ψ : U →* U.map (cycZ k Ω l)` to `(cycZ k Ω l).subgroupMap U`. Establish `hψc : Continuous ψ`.

Apply `Continuous.subtype_mk` to reduce the goal to its premises. Conclude with `hχc.comp continuous_subtype_val`. Set `κ : U →* Multiplicative ℤ_[l]` to `e.toMulEquiv.toMonoidHom.comp ψ`. Establish `hκc : Continuous κ` using `e.continuous.comp hψc`. Establish `hκs : Function.Surjective κ` using `e.surjective.comp (MonoidHom.subgroupMap_surjective _ U)`.

Establish `hkκ : ∀ x : U, κ x = 1 ↔ cycZ k Ω l x = 1`. Introduce `x`. Establish `h1 : κ x = e (ψ x)` using `rfl`. Rewrite using `[h1, map_eq_one_iff e e.injective, Subtype.ext_iff]`. Conclude with `Iff.rfl`.

Take `⟨γ, hγ⟩` from `hκs (Multiplicative.ofAdd 1)`. Use `⟨κ, γ, hκc, hκs, ?_, hγ, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Rewrite using `[MonoidHom.mem_ker, hkκ, Subgroup.mem_subgroupOf]`. Simplify using `only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]`.

Conclude with `⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩`. Use `set V := (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure with hV`. Establish `hVc : IsClosed (V : Set (G k Ω))` using `Subgroup.isClosed_topologicalClosure _`. Establish `hsub : Subgroup.zpowers γ.1 ⊔ cycU l U ≤ V` using `Subgroup.le_topologicalClosure _`. Establish `hcU : CompactSpace U` using `isCompact_iff_compactSpace.mp hUc.isCompact`.

Set `S : Set U` to `Subtype.val ⁻¹' (V : Set (G k Ω))`. Establish `hSc : IsClosed S` using `hVc.preimage continuous_subtype_val`. Establish `hIc : IsClosed (κ '' S)` using `(hSc.isCompact.image hκc).isClosed`. Set `T : Set ℤ_[l]` to `fun a => Multiplicative.ofAdd a ∈ κ '' S`. Establish `hTc : IsClosed T` using `hIc.preimage continuous_ofAdd`.

Establish `hTz : Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ T`. Introduce and unpack `_ ⟨n, rfl⟩`. Use `⟨γ ^ n, ?_, ?_⟩` and prove the remaining obligations. Use `show ((γ ^ n : U) : G k Ω) ∈ V`. Rewrite using `[Subgroup.coe_zpow]`.

Conclude with `hsub (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ n))`. Rewrite using `[map_zpow, hγ, ← ofAdd_zsmul, zsmul_one]`. Establish `hT : T = Set.univ`. Apply `Set.eq_univ_of_univ_subset` to reduce the goal to its premises. Rewrite using `[← PadicInt.denseRange_intCast.closure_range]`.

Conclude with `closure_minimal hTz hTc`. Introduce `u hu`. Establish `ha : Multiplicative.toAdd (κ ⟨u, hu⟩) ∈ T` using `by rw [hT]; trivial`. Take `⟨s, hs, hks⟩` from `ha`. Establish `hks' : κ s = κ ⟨u, hu⟩` using `hks`.

Establish `hq : κ (⟨u, hu⟩ * s⁻¹) = 1` using `by rw [map_mul, map_inv, ← hks', mul_inv_cancel]`. Establish `hq'` using `(hkκ _).mp hq`. Establish `hmem : ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) ∈ V`. Apply `hsub` to reduce the goal to its premises. Apply `Subgroup.mem_sup_right` to reduce the goal to its premises.

Simplify using `only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]`. Conclude with `⟨(⟨u, hu⟩ * s⁻¹ : U).2, hq'⟩`. Establish `hu' : u = ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) * (s : G k Ω)`. Simplify using the standard rewrite rules. Rewrite using `[hu']`.

Conclude with `V.mul_mem hmem hs`. Introduce `hfin`. Establish `hm : cycZ k Ω l γ.1 ∈ U.map (cycZ k Ω l)` using `⟨γ.1, γ.2, rfl⟩`. Establish `h1` using `(hkκ γ).mpr (htor _ hm hfin)`. Rewrite `h1` using `[hγ]`.

Conclude with `one_ne_zero (ofAdd_eq_one.mp h1)`.
-/
theorem UpperTheory.V.Base.gammaGen :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsClosed (U : Set (G k Ω)) → U ≤ gamU l ⊤ → ¬ U ≤ (cycZ k Ω l).ker →
      ∃ (κ : U →* Multiplicative ℤ_[l]) (γ : U), Continuous κ ∧ Function.Surjective κ ∧ κ.ker = (cycU l U).subgroupOf U ∧
        κ γ = Multiplicative.ofAdd 1 ∧ U ≤ (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure ∧ ¬ IsOfFinOrder (cycZ k Ω l γ.1) := by
  intro k Ω _ _ _ _ _ l _ U hUc hUg hUk
  have hχc : Continuous (cycZ k Ω l) := continuous_cycZ k Ω l
  have hHc : IsClosed ((U.map (cycZ k Ω l) : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hUc.isCompact.image hχc).isClosed
  have hHp : U.map (cycZ k Ω l) ≤ KStar.TotallyRealRoots.princ l (qExp l) := by
    rintro _ ⟨u, hu, rfl⟩
    have h := hUg hu
    simp only [gamU, levU, Subgroup.mem_inf, Subgroup.mem_comap] at h
    exact h.2
  have hHb : U.map (cycZ k Ω l) ≠ ⊥ := by
    intro h
    apply hUk
    intro u hu
    have hm : cycZ k Ω l u ∈ U.map (cycZ k Ω l) := ⟨u, hu, rfl⟩
    rw [h] at hm
    exact MonoidHom.mem_ker.mpr (Subgroup.mem_bot.mp hm)
  obtain ⟨⟨e⟩, htor⟩ := princZl l _ hHc hHp hHb
  let ψ : U →* U.map (cycZ k Ω l) := (cycZ k Ω l).subgroupMap U
  have hψc : Continuous ψ := by
    apply Continuous.subtype_mk
    exact hχc.comp continuous_subtype_val
  let κ : U →* Multiplicative ℤ_[l] := e.toMulEquiv.toMonoidHom.comp ψ
  have hκc : Continuous κ := e.continuous.comp hψc
  have hκs : Function.Surjective κ := e.surjective.comp (MonoidHom.subgroupMap_surjective _ U)
  have hkκ : ∀ x : U, κ x = 1 ↔ cycZ k Ω l x = 1 := by
    intro x
    have h1 : κ x = e (ψ x) := rfl
    rw [h1, map_eq_one_iff e e.injective, Subtype.ext_iff]
    exact Iff.rfl
  obtain ⟨γ, hγ⟩ := hκs (Multiplicative.ofAdd 1)
  refine ⟨κ, γ, hκc, hκs, ?_, hγ, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, hkκ, Subgroup.mem_subgroupOf]
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  · set V := (Subgroup.zpowers γ.1 ⊔ cycU l U).topologicalClosure with hV
    have hVc : IsClosed (V : Set (G k Ω)) := Subgroup.isClosed_topologicalClosure _
    have hsub : Subgroup.zpowers γ.1 ⊔ cycU l U ≤ V := Subgroup.le_topologicalClosure _
    have hcU : CompactSpace U := isCompact_iff_compactSpace.mp hUc.isCompact
    let S : Set U := Subtype.val ⁻¹' (V : Set (G k Ω))
    have hSc : IsClosed S := hVc.preimage continuous_subtype_val
    have hIc : IsClosed (κ '' S) := (hSc.isCompact.image hκc).isClosed
    let T : Set ℤ_[l] := fun a => Multiplicative.ofAdd a ∈ κ '' S
    have hTc : IsClosed T := hIc.preimage continuous_ofAdd
    have hTz : Set.range (Int.cast : ℤ → ℤ_[l]) ⊆ T := by
      rintro _ ⟨n, rfl⟩
      refine ⟨γ ^ n, ?_, ?_⟩
      · show ((γ ^ n : U) : G k Ω) ∈ V
        rw [Subgroup.coe_zpow]
        exact hsub (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ n))
      · rw [map_zpow, hγ, ← ofAdd_zsmul, zsmul_one]
    have hT : T = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← PadicInt.denseRange_intCast.closure_range]
      exact closure_minimal hTz hTc
    intro u hu
    have ha : Multiplicative.toAdd (κ ⟨u, hu⟩) ∈ T := by rw [hT]; trivial
    obtain ⟨s, hs, hks⟩ := ha
    have hks' : κ s = κ ⟨u, hu⟩ := hks
    have hq : κ (⟨u, hu⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hks', mul_inv_cancel]
    have hq' := (hkκ _).mp hq
    have hmem : ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) ∈ V := by
      apply hsub
      apply Subgroup.mem_sup_right
      simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
      exact ⟨(⟨u, hu⟩ * s⁻¹ : U).2, hq'⟩
    have hu' : u = ((⟨u, hu⟩ * s⁻¹ : U) : G k Ω) * (s : G k Ω) := by
      simp
    rw [hu']
    exact V.mul_mem hmem hs
  · intro hfin
    have hm : cycZ k Ω l γ.1 ∈ U.map (cycZ k Ω l) := ⟨γ.1, γ.2, rfl⟩
    have h1 := (hkκ γ).mpr (htor _ hm hfin)
    rw [hγ] at h1
    exact one_ne_zero (ofAdd_eq_one.mp h1)
