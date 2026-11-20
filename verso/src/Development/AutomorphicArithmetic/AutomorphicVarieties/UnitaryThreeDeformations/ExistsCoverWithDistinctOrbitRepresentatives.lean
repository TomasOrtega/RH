import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal

open UpperTheory.V.Alg

/- English proof (translation)
Take `⟨t, rfl⟩` from `h`. Take `⟨s, rfl⟩` from `h'`. Use `⟨s * t, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Proceed by induction on `a using DirectSum.Decomposition.inductionOn 𝒜 with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `homogeneous a`. Rewrite using `[act_of_mem 𝒜 _ _ a.2, act_of_mem 𝒜 _ _ a.2, act_of_mem 𝒜 _ _ a.2]`. Simplify using `only [zpowersHom_apply, toAdd_ofAdd, mul_zpow, Units.val_mul, mul_assoc]`.
-/
private theorem sameOrbit_trans {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A)
    [GradedAlgebra 𝒜] [Field K] [Algebra O K] {ξ ξ' ξ'' : A →ₐ[O] K}
    (h : SameOrbit 𝒜 ξ ξ') (h' : SameOrbit 𝒜 ξ' ξ'') : SameOrbit 𝒜 ξ ξ'' := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨s, rfl⟩ := h'
  refine ⟨s * t, ?_⟩
  ext a
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous a =>
    rw [act_of_mem 𝒜 _ _ a.2, act_of_mem 𝒜 _ _ a.2, act_of_mem 𝒜 _ _ a.2]
    simp only [zpowersHom_apply, toAdd_ofAdd, mul_zpow, Units.val_mul, mul_assoc]

/- English proof (translation)
Introduce `O A K _ _ _ 𝒜 _ _ _ I T hT`. Proceed by induction on `T using Finset.strongInduction with`. Consider the case `H T ih`. Distinguish the cases in `hx : ∃ ξ ∈ T, ∃ ξ' ∈ T, SameOrbit 𝒜 ξ ξ' ∧ ξ ≠ ξ'`. Take `⟨ξ, hξ, ξ', hξ', hs, hne⟩` from `hx`.

Apply `ih (T.erase ξ') (Finset.erase_ssubset hξ')` to reduce the goal to its premises. Use `⟨fun η hη => hT.1 η (Finset.mem_of_mem_erase hη), fun η h1 h2 => ?_⟩` and prove the remaining obligations. Take `⟨ζ, hζ, hζs⟩` from `hT.2 η h1 h2`. Distinguish the cases in `hz : ζ = ξ'`. Rewrite `hζs` using `[hz]`.

Conclude with `⟨ξ, Finset.mem_erase.2 ⟨hne, hξ⟩, sameOrbit_trans 𝒜 hs hζs⟩`. Conclude with `⟨ζ, Finset.mem_erase.2 ⟨hz, hζ⟩, hζs⟩`. Use `push_neg at hx`. Conclude with `⟨T, hT, fun ξ h ξ' h' hs => hx ξ h ξ' h' hs⟩`.
-/
theorem UpperTheory.exists_cover_with_distinct_orbit_representatives :
    ∀ (O A K : Type) [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [Field K] [Algebra O K] (I : Ideal A) (T : Finset (A →ₐ[O] K)),
        Covers 𝒜 I T → ∃ T' : Finset (A →ₐ[O] K), Covers 𝒜 I T' ∧ ∀ ξ ∈ T', ∀ ξ' ∈ T', SameOrbit 𝒜 ξ ξ' → ξ = ξ' := by
  intro O A K _ _ _ 𝒜 _ _ _ I T hT
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
    by_cases hx : ∃ ξ ∈ T, ∃ ξ' ∈ T, SameOrbit 𝒜 ξ ξ' ∧ ξ ≠ ξ'
    · obtain ⟨ξ, hξ, ξ', hξ', hs, hne⟩ := hx
      apply ih (T.erase ξ') (Finset.erase_ssubset hξ')
      refine ⟨fun η hη => hT.1 η (Finset.mem_of_mem_erase hη), fun η h1 h2 => ?_⟩
      obtain ⟨ζ, hζ, hζs⟩ := hT.2 η h1 h2
      by_cases hz : ζ = ξ'
      · rw [hz] at hζs
        exact ⟨ξ, Finset.mem_erase.2 ⟨hne, hξ⟩, sameOrbit_trans 𝒜 hs hζs⟩
      · exact ⟨ζ, Finset.mem_erase.2 ⟨hz, hζ⟩, hζs⟩
    · push_neg at hx
      exact ⟨T, hT, fun ξ h ξ' h' hs => hx ξ h ξ' h' hs⟩
