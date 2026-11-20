import Mathlib

namespace GlobalTheory.InvariantSupremum

/- English proof (translation)
Set `Q : Subrepresentation σ` to `{ toSubmodule := P apply_mem_toSubmodule := by`. Introduce `g v hv`. Conclude with `hP g v hv }`. Break down `@IsSimpleOrder.eq_bot_or_eq_top _ _ _ hσ Q with h | h` into its components or cases. Conclude with `Or.inl (congrArg Subrepresentation.toSubmodule h)`.

Conclude with `Or.inr (congrArg Subrepresentation.toSubmodule h)`.
-/
theorem eq_bot_or_eq_top_of_invariant {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (P : Submodule ℂ W)
    (hP : ∀ g : G, ∀ w ∈ P, σ g w ∈ P) : P = ⊥ ∨ P = ⊤ := by
  let Q : Subrepresentation σ :=
    { toSubmodule := P
      apply_mem_toSubmodule := by
        intro g v hv
        exact hP g v hv }
  rcases @IsSimpleOrder.eq_bot_or_eq_top _ _ _ hσ Q with h | h
  · exact Or.inl (congrArg Subrepresentation.toSubmodule h)
  · exact Or.inr (congrArg Subrepresentation.toSubmodule h)

/- English proof (translation)
Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.mp hmem`. Use `clear hmem`. Establish `inv : ∀ (t : Finset ι) (g : G), ∀ z ∈ ⨆ i ∈ t, LinearMap.range (f i), ρ g z ∈ ⨆ i ∈ t, LinearMap.range (f i)`. Introduce `t g z hz`. Establish `hle : (⨆ i ∈ t, LinearMap.range (f i)) ≤ (⨆ i ∈ t, LinearMap.range (f i)).comap (ρ g)`.

Use `iSup₂_le fun i hi => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[Submodule.mem_comap, ← hf i g w]`. Conclude with `(le_iSup₂ (f := fun i (_ : i ∈ t) => LinearMap.range (f i)) i hi) (LinearMap.mem_range_self _ _)`. Conclude with `hle hz`.

Proceed by induction on `s using Finset.induction_on generalizing φ with`. Consider the case `empty`. Simplify using `only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hs`. Rewrite using `[hs]`. Conclude with `Z.zero_mem`.

Consider the case `@insert j s hj ih`. Rewrite `hs` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨y, ⟨u, rfl⟩, z, hz, rfl⟩` from `hs`. Break down `eq_bot_or_eq_top_of_invariant σ hσ ((⨆ i ∈ s, LinearMap.range (f i)).comap (f j)) (by` into its components or cases. Introduce `g w hw`.

Rewrite `hw`, the goal using `[Submodule.mem_comap]`. Rewrite using `[hf]`. Conclude with `inv s g _ hw) with hN | hN`. Establish `hu : ∀ k ∈ K, σ k u = u`. Introduce `k hk`.

Establish `e : ρ k (f j u) - f j u = z - ρ k z`. Rewrite using `[sub_eq_sub_iff_add_eq_add, ← map_add, hφ k hk, add_comm]`. Establish `h1 : σ k u - u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j)`. Rewrite using `[Submodule.mem_comap, map_sub, hf, e]`. Conclude with `Submodule.sub_mem _ hz (inv s k z hz)`.

Rewrite `h1` using `[hN, Submodule.mem_bot, sub_eq_zero]`. Conclude with `h1`. Establish `hzfix : ∀ k ∈ K, ρ k z = z`. Introduce `k hk`. Establish `h2` using `hφ k hk`.

Rewrite `h2` using `[map_add, ← hf, hu k hk]`. Conclude with `add_left_cancel h2`. Conclude with `Z.add_mem (hZ j u hu) (ih z hzfix hz)`. Establish `hu : f j u ∈ ⨆ i ∈ s, LinearMap.range (f i)`. Establish `h3 : u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j)`.

Rewrite using `[hN]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `h3`. Conclude with `ih _ hφ (Submodule.add_mem _ hu hz)`.
-/
theorem fixed_mem_of_mem_iSup_range {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] {ι : Type} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (hσ : Representation.IsIrreducible σ) (f : ι → W →ₗ[ℂ] V)
    (hf : ∀ (i : ι) (g : G) (u : W), f i (σ g u) = ρ g (f i u)) (K : Set G)
    (Z : Submodule ℂ V) (hZ : ∀ (i : ι) (v : W), (∀ k ∈ K, σ k v = v) → f i v ∈ Z)
    (_hfix : ∀ z ∈ Z, ∀ k ∈ K, ρ k z = z) (φ : V) (hφ : ∀ k ∈ K, ρ k φ = φ)
    (hmem : φ ∈ ⨆ i : ι, LinearMap.range (f i)) : φ ∈ Z := by
  classical
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  clear hmem

  have inv : ∀ (t : Finset ι) (g : G), ∀ z ∈ ⨆ i ∈ t, LinearMap.range (f i),
      ρ g z ∈ ⨆ i ∈ t, LinearMap.range (f i) := by
    intro t g z hz
    have hle : (⨆ i ∈ t, LinearMap.range (f i)) ≤
        (⨆ i ∈ t, LinearMap.range (f i)).comap (ρ g) := by
      refine iSup₂_le fun i hi => ?_
      rintro _ ⟨w, rfl⟩
      rw [Submodule.mem_comap, ← hf i g w]
      exact (le_iSup₂ (f := fun i (_ : i ∈ t) => LinearMap.range (f i)) i hi)
        (LinearMap.mem_range_self _ _)
    exact hle hz
  induction s using Finset.induction_on generalizing φ with
  | empty =>
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hs
    rw [hs]
    exact Z.zero_mem
  | @insert j s hj ih =>
    rw [Finset.iSup_insert, Submodule.mem_sup] at hs
    obtain ⟨y, ⟨u, rfl⟩, z, hz, rfl⟩ := hs

    rcases eq_bot_or_eq_top_of_invariant σ hσ ((⨆ i ∈ s, LinearMap.range (f i)).comap (f j)) (by
        intro g w hw
        rw [Submodule.mem_comap] at hw ⊢
        rw [hf]
        exact inv s g _ hw) with hN | hN
    ·
      have hu : ∀ k ∈ K, σ k u = u := by
        intro k hk
        have e : ρ k (f j u) - f j u = z - ρ k z := by
          rw [sub_eq_sub_iff_add_eq_add, ← map_add, hφ k hk, add_comm]
        have h1 : σ k u - u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [Submodule.mem_comap, map_sub, hf, e]
          exact Submodule.sub_mem _ hz (inv s k z hz)
        rw [hN, Submodule.mem_bot, sub_eq_zero] at h1
        exact h1
      have hzfix : ∀ k ∈ K, ρ k z = z := by
        intro k hk
        have h2 := hφ k hk
        rw [map_add, ← hf, hu k hk] at h2
        exact add_left_cancel h2
      exact Z.add_mem (hZ j u hu) (ih z hzfix hz)
    ·
      have hu : f j u ∈ ⨆ i ∈ s, LinearMap.range (f i) := by
        have h3 : u ∈ (⨆ i ∈ s, LinearMap.range (f i)).comap (f j) := by
          rw [hN]
          trivial
        exact h3
      exact ih _ hφ (Submodule.add_mem _ hu hz)

end GlobalTheory.InvariantSupremum
