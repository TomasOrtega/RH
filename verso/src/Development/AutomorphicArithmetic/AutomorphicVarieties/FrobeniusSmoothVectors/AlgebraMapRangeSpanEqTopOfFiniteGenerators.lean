import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.StrYMap

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

/- English proof (translation)
Introduce `k G M _ _ _ Y C a hY ha`. Take `⟨b, hbs, hspan, hli⟩` from `exists_linearIndependent k (Set.range a)`. Establish `hli' : LinearIndepOn k id b` using `hli`. Set `B` to `Module.Basis.extend hli'`. Establish `hmem : ∀ x : b, (x : M) ∈ hli'.extend (Set.subset_univ b)` using `fun x => hli'.subset_extend (Set.subset_univ b) x.2`.

Establish `hB : ∀ x : b, B ⟨x, hmem x⟩ = x` using `fun x => by`. Simplify using `only [B, Module.Basis.coe_extend]`. Establish `hco : ∀ x y : b, B.coord ⟨x, hmem x⟩ (y : M) = if y = x then 1 else 0`. Introduce `x y`. Rewrite using `[← hB y, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]`.

Distinguish the cases in `h : y = x`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h' : (⟨(y : M), hmem y⟩ : hli'.extend (Set.subset_univ b)) ≠ ⟨x, hmem x⟩`. Introduce `e`.

Apply `h` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Subtype.mk.inj e`. Simplify using `[h, h']`. Use `choose gx hgx using fun x : b => hbs x.2`.

Set `φ : b → Y` to `fun x => ⟨fun g => B.coord ⟨x, hmem x⟩ (a g), ha (B.coord ⟨x, hmem x⟩)⟩`. Establish `hφ : LinearIndependent k φ`. Rewrite using `[linearIndependent_iff']`. Introduce `s c hsum i hi`. Establish `h1` using `congrArg (fun y : Y => (y : G → k) (gx i)) hsum`.

Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply, φ, hgx] at h1`. Simplify `h1` using `[hco, hi]`. Establish `hcard : Cardinal.mk b ≤ C` using `hφ.cardinal_le_rank.trans hY`. Establish `hfin : b.Finite` using `Cardinal.lt_aleph0_iff_set_finite.mp (hcard.trans_lt (Cardinal.nat_lt_aleph0 C))`. Use `haveI := hfin.fintype`.

Use `⟨hfin.toFinset, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.card_toFinset]`. Rewrite `hcard` using `[Cardinal.mk_fintype]`. Conclude with `hcard` after adjusting the coercions. Introduce `g`.

Rewrite using `[Set.Finite.coe_toFinset, hspan]`. Conclude with `Submodule.subset_span ⟨g, rfl⟩`.
-/
theorem UpperTheory.V.Fr.algebraMap_range_span_eq_top_of_finite_generators :
    ∀ {k G M : Type} [Field k] [AddCommGroup M] [Module k M] (Y : Submodule k (G → k)) (C : ℕ) (a : G → M), Module.rank k Y ≤ C → (∀ f : M →ₗ[k] k, (fun g => f (a g)) ∈ Y) → ∃ T : Finset M, T.card ≤ C ∧ ∀ g, a g ∈ Submodule.span k (T : Set M) := by
  intro k G M _ _ _ Y C a hY ha
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent k (Set.range a)
  have hli' : LinearIndepOn k id b := hli
  let B := Module.Basis.extend hli'
  have hmem : ∀ x : b, (x : M) ∈ hli'.extend (Set.subset_univ b) :=
    fun x => hli'.subset_extend (Set.subset_univ b) x.2
  have hB : ∀ x : b, B ⟨x, hmem x⟩ = x := fun x => by
    simp only [B, Module.Basis.coe_extend]
  have hco : ∀ x y : b, B.coord ⟨x, hmem x⟩ (y : M) = if y = x then 1 else 0 := by
    intro x y
    rw [← hB y, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : y = x
    · subst h
      simp
    · have h' : (⟨(y : M), hmem y⟩ : hli'.extend (Set.subset_univ b)) ≠ ⟨x, hmem x⟩ := by
        intro e
        apply h
        apply Subtype.ext
        exact Subtype.mk.inj e
      simp [h, h']
  choose gx hgx using fun x : b => hbs x.2
  let φ : b → Y := fun x => ⟨fun g => B.coord ⟨x, hmem x⟩ (a g), ha (B.coord ⟨x, hmem x⟩)⟩
  have hφ : LinearIndependent k φ := by
    rw [linearIndependent_iff']
    intro s c hsum i hi
    have h1 := congrArg (fun y : Y => (y : G → k) (gx i)) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      ZeroMemClass.coe_zero, Pi.zero_apply, φ, hgx] at h1
    simpa [hco, hi] using h1
  have hcard : Cardinal.mk b ≤ C := hφ.cardinal_le_rank.trans hY
  have hfin : b.Finite := Cardinal.lt_aleph0_iff_set_finite.mp (hcard.trans_lt (Cardinal.nat_lt_aleph0 C))
  haveI := hfin.fintype
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · rw [Set.Finite.card_toFinset]
    rw [Cardinal.mk_fintype] at hcard
    exact_mod_cast hcard
  · intro g
    rw [Set.Finite.coe_toFinset, hspan]
    exact Submodule.subset_span ⟨g, rfl⟩
