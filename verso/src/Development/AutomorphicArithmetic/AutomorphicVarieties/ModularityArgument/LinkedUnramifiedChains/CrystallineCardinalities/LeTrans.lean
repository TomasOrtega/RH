import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
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
