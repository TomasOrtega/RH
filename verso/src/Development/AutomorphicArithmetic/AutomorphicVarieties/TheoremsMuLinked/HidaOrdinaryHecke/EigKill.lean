import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `K V _ _ _ φ k F hF hk`. Establish `hdisj` using `Module.End.eigenspaces_iSupIndep φ 0`. Use `set S := ⨆ (μ : K) (_ : μ ≠ 0), φ.eigenspace μ with hS`. Establish `hinv : ∀ z ∈ S, φ z ∈ S`. Establish `hle : S ≤ S.comap φ`.

Use `iSup₂_le fun μ hμ => ?_` and prove the remaining obligations. Introduce `v hv`. Rewrite using `[Submodule.mem_comap, Module.End.mem_eigenspace_iff.1 hv]`. Conclude with `Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ (Submodule.smul_mem _ _ hv))`. Conclude with `fun z hz => hle hz`.

Establish `hinj : ∀ z ∈ S, φ z = 0 → z = 0`. Introduce `z hz h0`. Establish `hz0 : z ∈ φ.eigenspace 0`. Rewrite using `[Module.End.mem_eigenspace_iff, zero_smul]`. Conclude with `h0`.

Conclude with `Submodule.disjoint_def.1 hdisj z hz0 hz`. Establish `hpow : ∀ n : ℕ, ∀ z ∈ S, (φ ^ n) z = 0 → z = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`.

Introduce `z _ h`. Simplify using `using h`. Consider the case `succ n ih`. Introduce `z hz h`. Rewrite `h` using `[pow_succ, Module.End.mul_apply]`.

Conclude with `hinj z hz (ih _ (hinv z hz) h)`. Rewrite `hF` using `[iSup_split_single _ (0 : K)]`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hF`. Establish `hy' : φ y = 0`. Rewrite `hy` using `[Module.End.mem_eigenspace_iff, zero_smul]`.

Conclude with `hy`. Consider the cases of `k with`. Consider the case `zero`. Establish `h0 : y + z = 0` using `by simpa using hk`. Rewrite using `[h0, map_zero]`.

Consider the case `succ k`. Establish `hyk : (φ ^ (k + 1)) y = 0`. Rewrite using `[pow_succ, Module.End.mul_apply, hy', map_zero]`. Rewrite `hk` using `[map_add, hyk, zero_add]`. Rewrite using `[map_add, hy', hpow _ z hz hk, map_zero, add_zero]`.
-/
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill :
    ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (φ : Module.End K V) (k : ℕ) (F : V), F ∈ ⨆ μ : K, φ.eigenspace μ → (φ ^ k) F = 0 → φ F = 0 := by
  intro K V _ _ _ φ k F hF hk
  have hdisj := Module.End.eigenspaces_iSupIndep φ 0
  set S := ⨆ (μ : K) (_ : μ ≠ 0), φ.eigenspace μ with hS
  have hinv : ∀ z ∈ S, φ z ∈ S := by
    have hle : S ≤ S.comap φ := by
      refine iSup₂_le fun μ hμ => ?_
      intro v hv
      rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.1 hv]
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ (Submodule.smul_mem _ _ hv))
    exact fun z hz => hle hz
  have hinj : ∀ z ∈ S, φ z = 0 → z = 0 := by
    intro z hz h0
    have hz0 : z ∈ φ.eigenspace 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact h0
    exact Submodule.disjoint_def.1 hdisj z hz0 hz
  have hpow : ∀ n : ℕ, ∀ z ∈ S, (φ ^ n) z = 0 → z = 0 := by
    intro n
    induction n with
    | zero =>
      intro z _ h
      simpa using h
    | succ n ih =>
      intro z hz h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hinj z hz (ih _ (hinv z hz) h)
  rw [iSup_split_single _ (0 : K)] at hF
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hF
  have hy' : φ y = 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hy
    exact hy
  cases k with
  | zero =>
    have h0 : y + z = 0 := by simpa using hk
    rw [h0, map_zero]
  | succ k =>
    have hyk : (φ ^ (k + 1)) y = 0 := by
      rw [pow_succ, Module.End.mul_apply, hy', map_zero]
    rw [map_add, hyk, zero_add] at hk
    rw [map_add, hy', hpow _ z hz hk, map_zero, add_zero]
