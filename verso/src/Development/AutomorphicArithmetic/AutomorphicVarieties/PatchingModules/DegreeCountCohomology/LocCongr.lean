import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual

open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ D D' _ _ _ _ α ε ε' d hε h R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hdual`. Set `σ : D' →* D` to `α.symm.toMulEquiv.toMonoidHom`. Establish `hσ : ∀ g, σ g = α.symm g` using `fun g => rfl`. Set `ρ2 : Representation R D' M` to `ρ.comp σ`. Set `ρ2' : Representation R D' M'` to `ρ'.comp σ`.

Establish `heps : ∀ g : D', epsBar ε (α.symm g) = epsBar ε' g`. Introduce `g`. Simplify using `only [epsBar, hε, ContinuousMulEquiv.apply_symm_apply]`. Establish `hLC2 : LC ρ2` using `fun m => (hLC m).comp_continuous α.symm.continuous`. Establish `hdual2 : IsDualPair ε' ρ2 ρ2' b`.

Use `⟨hdual.left, hdual.right, fun g x y => ?_⟩` and prove the remaining obligations. Use `hdual.equiv (α.symm g) x y` as an intermediate fact. Rewrite using `[← heps g, ← this]`. Both sides reduce to the same expression. Take `⟨hfin, hcard⟩` from `h R M M' ρ2 ρ2' b hLC2 hdual2`.

Set `e : Zl ρ ≃ Zl ρ2` to `{ toFun := fun z => ⟨fun g => z.1 (α.symm g), by`. Take `⟨hz1, hz2⟩` from `z.2`. Use `⟨hz1.comp_continuous α.symm.continuous, fun g k => ?_⟩` and prove the remaining obligations. Use `show z.1 (α.symm (g * k)) = z.1 (α.symm g) + ρ (α.symm g) (z.1 (α.symm k))`. Rewrite using `[map_mul]`.

Conclude with `hz2 _ _⟩`. Use `invFun := fun z => ⟨fun g => z.1 (α g), by`. Take `⟨hz1, hz2⟩` from `z.2`. Use `⟨hz1.comp_continuous α.continuous, fun g k => ?_⟩` and prove the remaining obligations. Use `hz2 (α g) (α k)` as an intermediate fact.

Rewrite `this` using `[← map_mul]`. Use `show z.1 (α (g * k)) = z.1 (α g) + ρ g (z.1 (α k))`. Rewrite using `[this]`. Use `show z.1 (α g) + ρ (α.symm (α g)) (z.1 (α k)) = _`. Rewrite using `[ContinuousMulEquiv.symm_apply_apply]⟩`.

Use `left_inv := fun z => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show z.1 (α.symm (α g)) = z.1 g`. Rewrite using `[ContinuousMulEquiv.symm_apply_apply]`.

Use `right_inv := fun z => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show z.1 (α (α.symm g)) = z.1 g`. Rewrite using `[ContinuousMulEquiv.apply_symm_apply] }`.

Establish `hinv : Nat.card ρ2'.invariants = Nat.card ρ'.invariants`. Apply `Nat.card_congr` to reduce the goal to its premises. Use `Equiv.subtypeEquivRight (fun v => ?_)` and prove the remaining obligations. Simplify using `only [Representation.mem_invariants]`. Prove the components needed by the constructor for the conclusion.

Introduce `hv g`. Use `hv (α g)` as an intermediate fact. Simplify `this` using `[ρ2', hσ]`. Introduce `hv g`. Conclude with `hv (α.symm g)`.

Use `⟨Finite.of_equiv _ e.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr e, hcard, hinv]`.
-/
theorem UpperTheory.V.Pa.locCongr :
    ∀ (l : ℕ) [Fact l.Prime] (D D' : Type) [Group D] [TopologicalSpace D] [Group D'] [TopologicalSpace D'] (α : D ≃ₜ* D') (ε : D →* ℤ_[l]ˣ) (ε' : D' →* ℤ_[l]ˣ) (d : ℕ), (∀ g, ε g = ε' (α g)) → LocCount D' ε' d → LocCount D ε d := by
  intro l _ D D' _ _ _ _ α ε ε' d hε h R M M' _ _ _ _ _ _ _ ρ ρ' b hLC hdual
  let σ : D' →* D := α.symm.toMulEquiv.toMonoidHom
  have hσ : ∀ g, σ g = α.symm g := fun g => rfl
  let ρ2 : Representation R D' M := ρ.comp σ
  let ρ2' : Representation R D' M' := ρ'.comp σ
  have heps : ∀ g : D', epsBar ε (α.symm g) = epsBar ε' g := by
    intro g
    simp only [epsBar, hε, ContinuousMulEquiv.apply_symm_apply]
  have hLC2 : LC ρ2 := fun m => (hLC m).comp_continuous α.symm.continuous
  have hdual2 : IsDualPair ε' ρ2 ρ2' b := by
    refine ⟨hdual.left, hdual.right, fun g x y => ?_⟩
    have := hdual.equiv (α.symm g) x y
    rw [← heps g, ← this]
    rfl
  obtain ⟨hfin, hcard⟩ := h R M M' ρ2 ρ2' b hLC2 hdual2
  let e : Zl ρ ≃ Zl ρ2 :=
    { toFun := fun z => ⟨fun g => z.1 (α.symm g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.symm.continuous, fun g k => ?_⟩
        show z.1 (α.symm (g * k)) = z.1 (α.symm g) + ρ (α.symm g) (z.1 (α.symm k))
        rw [map_mul]
        exact hz2 _ _⟩
      invFun := fun z => ⟨fun g => z.1 (α g), by
        obtain ⟨hz1, hz2⟩ := z.2
        refine ⟨hz1.comp_continuous α.continuous, fun g k => ?_⟩
        have := hz2 (α g) (α k)
        rw [← map_mul] at this
        show z.1 (α (g * k)) = z.1 (α g) + ρ g (z.1 (α k))
        rw [this]
        show z.1 (α g) + ρ (α.symm (α g)) (z.1 (α k)) = _
        rw [ContinuousMulEquiv.symm_apply_apply]⟩
      left_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α.symm (α g)) = z.1 g
        rw [ContinuousMulEquiv.symm_apply_apply]
      right_inv := fun z => by
        apply Subtype.ext
        funext g
        show z.1 (α (α.symm g)) = z.1 g
        rw [ContinuousMulEquiv.apply_symm_apply] }
  have hinv : Nat.card ρ2'.invariants = Nat.card ρ'.invariants := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight (fun v => ?_)
    simp only [Representation.mem_invariants]
    constructor
    · intro hv g
      have := hv (α g)
      simpa [ρ2', hσ] using this
    · intro hv g
      exact hv (α.symm g)
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, hcard, hinv]
