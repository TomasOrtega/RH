import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `ι _ b hb hn`. Establish `hli : LinearIndependent ℤ (fun x : b => (x : ι →₀ ℤ))` using `hb`. Use `haveI : Finite b := hli.finite`. Use `letI := Fintype.ofFinite ι`. Use `letI := Fintype.ofFinite b`.

Establish `h1 : Fintype.card b ≤ Fintype.card ι`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[Module.finrank_finsupp_self]`. Then use the resulting hypothesis. Use `choose n hn0 hmem using hn`. Establish `hind : LinearIndependent ℤ (fun k : ι => n k • Finsupp.single k (1 : ℤ))`.

Rewrite using `[linearIndependent_iff']`. Introduce `s c hs i hi`. Use `congrArg (fun f : ι →₀ ℤ => f i) hs` as an intermediate fact. Simplify using `only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at this`. Rewrite `this` using `[Finset.sum_eq_single i]`.

Simplify using `only [if_true, mul_one] at this`. Break down `mul_eq_zero.1 this with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h (hn0 i)`. Introduce `j _ hj`.

Simplify using `[hj]`. Introduce `h`. Conclude with `absurd hi h`. Set `w : ι → Submodule.span ℤ b` to `fun k => ⟨n k • Finsupp.single k (1 : ℤ), hmem k⟩`. Establish `hw : LinearIndependent ℤ w` using `LinearIndependent.of_comp (Submodule.span ℤ b).subtype hind`.

Establish `h2 : Fintype.card ι ≤ Fintype.card b`. Use `hw.fintype_card_le_finrank` as an intermediate fact. Rewrite `this` using `[finrank_span_set_eq_card hb, Set.toFinset_card]`. Use `this` and compare the differences between its conclusion and the goal. Set `e : ι ≃ b` to `Fintype.equivOfCardEq (le_antisymm h2 h1)`.

Use `⟨fun k => (e k : ι →₀ ℤ), hli.comp e e.injective, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Conclude with `(e k).2`.

Introduce `hy`. Conclude with `⟨e.symm ⟨y, hy⟩, by simp⟩`.
-/
theorem UpperTheory.V.KH.fullEnum :
    ∀ (ι : Type) [Finite ι] (b : Set (ι →₀ ℤ)), LinearIndepOn ℤ id b →
      (∀ k : ι, ∃ n : ℤ, n ≠ 0 ∧ n • Finsupp.single k (1 : ℤ) ∈ Submodule.span ℤ b) →
      ∃ v : ι → (ι →₀ ℤ), LinearIndependent ℤ v ∧ Set.range v = b := by
  intro ι _ b hb hn
  have hli : LinearIndependent ℤ (fun x : b => (x : ι →₀ ℤ)) := hb
  haveI : Finite b := hli.finite
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite b
  have h1 : Fintype.card b ≤ Fintype.card ι := by
    have := hli.fintype_card_le_finrank
    rwa [Module.finrank_finsupp_self] at this
  choose n hn0 hmem using hn
  have hind : LinearIndependent ℤ (fun k : ι => n k • Finsupp.single k (1 : ℤ)) := by
    rw [linearIndependent_iff']
    intro s c hs i hi
    have := congrArg (fun f : ι →₀ ℤ => f i) hs
    simp only [Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Finsupp.coe_zero, Pi.zero_apply] at this
    rw [Finset.sum_eq_single i] at this
    · simp only [if_true, mul_one] at this
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hn0 i)
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd hi h
  let w : ι → Submodule.span ℤ b := fun k => ⟨n k • Finsupp.single k (1 : ℤ), hmem k⟩
  have hw : LinearIndependent ℤ w :=
    LinearIndependent.of_comp (Submodule.span ℤ b).subtype hind
  have h2 : Fintype.card ι ≤ Fintype.card b := by
    have := hw.fintype_card_le_finrank
    rw [finrank_span_set_eq_card hb, Set.toFinset_card] at this
    convert this
  let e : ι ≃ b := Fintype.equivOfCardEq (le_antisymm h2 h1)
  refine ⟨fun k => (e k : ι →₀ ℤ), hli.comp e e.injective, ?_⟩
  ext y
  constructor
  · rintro ⟨k, rfl⟩
    exact (e k).2
  · intro hy
    exact ⟨e.symm ⟨y, hy⟩, by simp⟩
