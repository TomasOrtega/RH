import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

/- English proof (translation)
Introduce `l _ D D' _ _ _ _ e ε d h k hk N _ _ ρ hN hker`. Set `ρ' : Representation ℤ D' N` to `ρ.comp (e.symm : D' →* D)`. Establish `hρ' : ∀ s : D', ρ' s = ρ (e.symm s)` using `fun s => rfl`. Establish `hker' : IsOpen (↑(MonoidHom.ker ρ') : Set D')`. Establish `hset : (↑(MonoidHom.ker ρ') : Set D') = e.symm ⁻¹' (↑(MonoidHom.ker ρ) : Set D)`.

Use extensionality with `s`. Simplify using `[hρ']`. Rewrite using `[hset]`. Conclude with `hker.preimage (map_continuous e.symm)`. Take `⟨hfin, hcard⟩` from `h k hk N ρ' hN hker'`.

Establish `himg : Zc ρ = (fun z : D' → N => z ∘ e) '' Zc ρ'`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz1, hz2⟩`. Use `⟨z ∘ e.symm, ⟨hz1.comp_continuous (map_continuous e.symm), ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `s t`. Simplify using `only [Function.comp_apply, map_mul, hρ']`. Conclude with `hz2 _ _`. Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules.

Introduce and unpack `⟨w, ⟨hw1, hw2⟩, rfl⟩`. Use `⟨hw1.comp_continuous (map_continuous e), ?_⟩` and prove the remaining obligations. Introduce `s t`. Simplify using `only [Function.comp_apply, map_mul]`. Rewrite using `[hw2, hρ']`.

Simplify using the standard rewrite rules. Establish `hinj : Function.Injective (fun z : D' → N => z ∘ e)`. Introduce `z₁ z₂ hz`. Use function extensionality and compare the values at `s`. Use `congrFun hz (e.symm s)` as an intermediate fact.

Simplify using `using this`. Establish `hmu : HomMu l k (ε.comp (e : D →* D')) ρ = HomMu l k ε ρ'`. Use extensionality with `f`. Simplify using `only [HomMu, Set.mem_setOf_eq, MonoidHom.coe_comp, Function.comp_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hf s x`. Rewrite using `[hρ']`. Use `hf (e.symm s) x` as an intermediate fact. Simplify using `using this`. Introduce `hf s x`.

Use `hf (e s) x` as an intermediate fact. Rewrite `this` using `[hρ']`. Simplify using `using this`. Rewrite using `[himg, hmu]`. Conclude with `⟨hfin.image _, by rw [Set.ncard_image_of_injective _ hinj]; exact hcard⟩`.
-/
theorem UpperTheory.V.Z.J.leTrans :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (e : D ≃ₜ* D') (ε : D' →* ℤ_[l]ˣ) (d : ℕ), LE l D' ε d → LE l D (ε.comp (e : D →* D')) d := by
  intro l _ D D' _ _ _ _ e ε d h k hk N _ _ ρ hN hker
  let ρ' : Representation ℤ D' N := ρ.comp (e.symm : D' →* D)
  have hρ' : ∀ s : D', ρ' s = ρ (e.symm s) := fun s => rfl
  have hker' : IsOpen (↑(MonoidHom.ker ρ') : Set D') := by
    have hset : (↑(MonoidHom.ker ρ') : Set D') = e.symm ⁻¹' (↑(MonoidHom.ker ρ) : Set D) := by
      ext s
      simp [hρ']
    rw [hset]
    exact hker.preimage (map_continuous e.symm)
  obtain ⟨hfin, hcard⟩ := h k hk N ρ' hN hker'
  have himg : Zc ρ = (fun z : D' → N => z ∘ e) '' Zc ρ' := by
    ext z
    constructor
    · rintro ⟨hz1, hz2⟩
      refine ⟨z ∘ e.symm, ⟨hz1.comp_continuous (map_continuous e.symm), ?_⟩, ?_⟩
      · intro s t
        simp only [Function.comp_apply, map_mul, hρ']
        exact hz2 _ _
      · funext s
        simp
    · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
      refine ⟨hw1.comp_continuous (map_continuous e), ?_⟩
      intro s t
      simp only [Function.comp_apply, map_mul]
      rw [hw2, hρ']
      simp
  have hinj : Function.Injective (fun z : D' → N => z ∘ e) := by
    intro z₁ z₂ hz
    funext s
    have := congrFun hz (e.symm s)
    simpa using this
  have hmu : HomMu l k (ε.comp (e : D →* D')) ρ = HomMu l k ε ρ' := by
    ext f
    simp only [HomMu, Set.mem_setOf_eq, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · intro hf s x
      rw [hρ']
      have := hf (e.symm s) x
      simpa using this
    · intro hf s x
      have := hf (e s) x
      rw [hρ'] at this
      simpa using this
  rw [himg, hmu]
  exact ⟨hfin.image _, by rw [Set.ncard_image_of_injective _ hinj]; exact hcard⟩
