import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DualPair

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

/- English proof (translation)
Introduce `l _ D D' _ _ _ _ α ε ε' d hε H k hk R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hb`. Set `β : D' →* D` to `α.symm.toMulEquiv.toMonoidHom`. Set `σ : Representation R D' M` to `ρ.comp β`. Set `σ' : Representation R D' M'` to `ρ'.comp β`. Establish `hσ : ∀ g, σ g = ρ (α.symm g)` using `fun _ => rfl`.

Establish `hσ' : ∀ g, σ' g = ρ' (α.symm g)` using `fun _ => rfl`. Establish `h1 : LC σ` using `fun m => (hLC m).comp_continuous α.symm.continuous`. Establish `h2 : DualPair k ε' σ σ' b`. Use `⟨hb.left, hb.right, fun g x y => ?_⟩` and prove the remaining obligations. Rewrite using `[hσ, hσ', hb.equiv]`.

Simplify using `only [hε, ContinuousMulEquiv.apply_symm_apply]`. Take `⟨hf, hc⟩` from `H k hk R M M' σ σ' b h1 h2`. Set `e : Zl ρ ≃ Zl σ` to `{ toFun := fun z => ⟨fun g => z.1 (α.symm g), z.2.1.comp_continuous α.symm.continuous, fun g h => by beta_reduce`. Rewrite using `[map_mul, z.2.2, hσ]⟩`. Use `invFun := fun z => ⟨fun g => z.1 (α g), z.2.1.comp_continuous α.continuous, fun g h => by beta_reduce`.

Rewrite using `[map_mul, z.2.2, hσ, ContinuousMulEquiv.symm_apply_apply]⟩`. Use `left_inv := fun z => Subtype.ext (funext fun g => by simp)`. Use `right_inv := fun z => Subtype.ext (funext fun g => by simp) }`. Establish `hi : ρ'.invariants = σ'.invariants`. Use extensionality with `m`.

Simplify using `only [Representation.mem_invariants, hσ']`. Conclude with `⟨fun h g => h _, fun h g => by simpa using h (α g)⟩`. Conclude with `⟨Finite.of_equiv _ e.symm, by rw [Nat.card_congr e, hc, hi]⟩`.
-/
theorem UpperTheory.V.Th.locCntCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCnt D' ε' d → LocCnt D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε H k hk R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hb
  let β : D' →* D := α.symm.toMulEquiv.toMonoidHom
  let σ : Representation R D' M := ρ.comp β
  let σ' : Representation R D' M' := ρ'.comp β
  have hσ : ∀ g, σ g = ρ (α.symm g) := fun _ => rfl
  have hσ' : ∀ g, σ' g = ρ' (α.symm g) := fun _ => rfl
  have h1 : LC σ := fun m => (hLC m).comp_continuous α.symm.continuous
  have h2 : DualPair k ε' σ σ' b := by
    refine ⟨hb.left, hb.right, fun g x y => ?_⟩
    rw [hσ, hσ', hb.equiv]
    simp only [hε, ContinuousMulEquiv.apply_symm_apply]
  obtain ⟨hf, hc⟩ := H k hk R M M' σ σ' b h1 h2
  let e : Zl ρ ≃ Zl σ :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), z.2.1.comp_continuous α.symm.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ]⟩
      invFun := fun z => ⟨fun g => z.1 (α g), z.2.1.comp_continuous α.continuous, fun g h => by
        beta_reduce
        rw [map_mul, z.2.2, hσ, ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => Subtype.ext (funext fun g => by simp)
      right_inv := fun z => Subtype.ext (funext fun g => by simp) }
  have hi : ρ'.invariants = σ'.invariants := by
    ext m
    simp only [Representation.mem_invariants, hσ']
    exact ⟨fun h g => h _, fun h g => by simpa using h (α g)⟩
  exact ⟨Finite.of_equiv _ e.symm, by rw [Nat.card_congr e, hc, hi]⟩
