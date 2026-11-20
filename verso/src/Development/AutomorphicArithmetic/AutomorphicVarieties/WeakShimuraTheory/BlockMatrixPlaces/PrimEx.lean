import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.DivStep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.RedMem

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Introduce `A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL hfin hcard n hn`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Establish `hA : ∀ k, ∀ z ∈ Zn ρ c N H P (n + k), ¬Prim z`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact hne`. Consider the case `succ k ih`. Introduce `z hz hpz`.

Take `⟨y, hy⟩` from `hz`. Establish `hr` using `redMem A T Γ ρ c N H P (n + k) z y hy`. Conclude with `ih _ ⟨_, hr.1⟩ (hr.2.1 hpz (by omega))`. Establish `hB : ∀ k, Nat.card (Zn ρ c N H P (n + k + 1)) ≤ Nat.card (Zn ρ c N H P (n + k))`. Introduce `k`.

Use `haveI := (hfin (n + k)).to_subtype`. Establish `key : ∀ z : Zn ρ c N H P (n + k + 1), ∃ z' : Zn ρ c N H P (n + k), ∀ g x, (lev A T (n + k)).mkQ x = z'.1 g → (lev A T (n + k + 1)).mkQ (t • x) = z.1 g`. Introduce `z`. Take `⟨z', hz', h⟩` from `divStep A T Γ ρ c N H P hL t ht (n + k) z.1 z.2 (hA (k + 1) z.1 z.2)`. Conclude with `⟨⟨z', hz'⟩, h⟩`.

Use `choose f hf using key`. Use `Nat.card_le_card_of_injective f ?_` and prove the remaining obligations. Introduce `z1 z2 h12`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Take `⟨x, hx⟩` from `Submodule.mkQ_surjective (lev A T (n + k)) ((f z1).1 g)`. Rewrite using `[← hf z1 g x hx, hf z2 g x (by rw [hx, h12])]`. Establish `hC : ∀ k, Nat.card (Zn ρ c N H P (n + k)) ≤ Nat.card (Zn ρ c N H P n)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => exact le_rfl`. Consider the case `succ k ih => exact (hB k).trans ih`. Establish `h1` using `hcard (n + (Nat.card (Zn ρ c N H P n) + 1))`. Establish `h2` using `hC (Nat.card (Zn ρ c N H P n) + 1)`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.V.Ws.Bl.primEx :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), Lat ρ H P → (∀ n, (Zn ρ c N H P n).Finite) → (∀ n, n ≤ Nat.card (Zn ρ c N H P n)) → ∀ n, 0 < n → ∃ z ∈ Zn ρ c N H P n, Prim z := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hL hfin hcard n hn
  by_contra hne
  push_neg at hne
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hA : ∀ k, ∀ z ∈ Zn ρ c N H P (n + k), ¬Prim z := by
    intro k
    induction k with
    | zero => exact hne
    | succ k ih =>
      intro z hz hpz
      obtain ⟨y, hy⟩ := hz
      have hr := redMem A T Γ ρ c N H P (n + k) z y hy
      exact ih _ ⟨_, hr.1⟩ (hr.2.1 hpz (by omega))
  have hB : ∀ k, Nat.card (Zn ρ c N H P (n + k + 1)) ≤ Nat.card (Zn ρ c N H P (n + k)) := by
    intro k
    haveI := (hfin (n + k)).to_subtype
    have key : ∀ z : Zn ρ c N H P (n + k + 1), ∃ z' : Zn ρ c N H P (n + k),
        ∀ g x, (lev A T (n + k)).mkQ x = z'.1 g → (lev A T (n + k + 1)).mkQ (t • x) = z.1 g := by
      intro z
      obtain ⟨z', hz', h⟩ := divStep A T Γ ρ c N H P hL t ht (n + k) z.1 z.2 (hA (k + 1) z.1 z.2)
      exact ⟨⟨z', hz'⟩, h⟩
    choose f hf using key
    refine Nat.card_le_card_of_injective f ?_
    intro z1 z2 h12
    apply Subtype.ext
    funext g
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (lev A T (n + k)) ((f z1).1 g)
    rw [← hf z1 g x hx, hf z2 g x (by rw [hx, h12])]
  have hC : ∀ k, Nat.card (Zn ρ c N H P (n + k)) ≤ Nat.card (Zn ρ c N H P n) := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hB k).trans ih
  have h1 := hcard (n + (Nat.card (Zn ρ c N H P n) + 1))
  have h2 := hC (Nat.card (Zn ρ c N H P n) + 1)
  omega
