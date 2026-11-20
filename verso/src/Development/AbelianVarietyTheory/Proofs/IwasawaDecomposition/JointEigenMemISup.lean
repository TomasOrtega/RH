import Mathlib

namespace GlobalTheory.JointEigenSupremum

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hstab : ∀ (s : Finset κ) (i : ι), ∀ z ∈ ⨆ k ∈ s, E k, (op i : M → M) z ∈ ⨆ k ∈ s, E k`. Introduce `s i z hz`. Establish `hle : (⨆ k ∈ s, E k) ≤ (⨆ k ∈ s, E k).comap (op i)`.

Use `iSup₂_le fun k hk y hy => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, hE k y hy i]`. Conclude with `Submodule.smul_mem _ _ ((le_iSup₂ (f := fun k (_ : k ∈ s) => E k) k hk) hy)`. Conclude with `hle hz`. Establish `key : ∀ s : Finset κ, ∀ x : M, (∀ i, (op i : M → M) x = ψ i • x) → x ∈ ⨆ k ∈ s, E k → x = 0`.

Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => intro x _ h`. Simplify using `using h`. Consider the case `insert k0 s hk0 ih`.

Introduce `x hx h`. Rewrite `h` using `[Finset.iSup_insert, Submodule.mem_sup]`. Take `⟨y, hy, z, hz, rfl⟩` from `h`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, χ k0 i ≠ ψ i := by`. Assume the negation of the conclusion as `h'`.

Use `push_neg at h'`. Conclude with `hne k0 (funext h')`. Establish `hw : (op i : M → M) z - χ k0 i • z ∈ ⨆ k ∈ s, E k` using `Submodule.sub_mem _ (hstab s i z hz) (Submodule.smul_mem _ _ hz)`. Establish `h1` using `hx i`. Rewrite `h1` using `[map_add, hE k0 y hy i, smul_add]`.

Establish `h2 : (op i : M → M) z = ψ i • y + ψ i • z - χ k0 i • y`. Rewrite using `[← h1]`. Normalize the expressions using the abelian group laws. Establish `hw' : (op i : M → M) z - χ k0 i • z = (ψ i - χ k0 i) • (y + z)`. Rewrite using `[h2]`.

Use `module`. Rewrite `hw` using `[hw']`. Establish `heig : ∀ j, (op j : M → M) ((ψ i - χ k0 i) • (y + z)) = ψ j • ((ψ i - χ k0 i) • (y + z))`. Introduce `j`. Rewrite using `[map_smul, hx j, smul_comm]`.

Establish `h0` using `ih _ heig hw`. Break down `smul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.mp h).symm hi`. Conclude with `h`. Take `⟨s, hs⟩` from `Submodule.mem_iSup_iff_exists_finset.mp hmem`.

Conclude with `hx0 (key s x hx hs)`.
-/
theorem joint_eigen_mem_iSup {ι κ M : Type} [AddCommGroup M] [Module ℂ M]
    (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M)
    (hE : ∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y)
    (ψ : ι → ℂ) (x : M) (hx0 : x ≠ (0 : M)) (hx : ∀ i, (op i : M → M) x = ψ i • x)
    (hmem : x ∈ ⨆ k, E k) : ∃ k, χ k = ψ := by
  classical
  by_contra hne
  push_neg at hne
  have hstab : ∀ (s : Finset κ) (i : ι), ∀ z ∈ ⨆ k ∈ s, E k, (op i : M → M) z ∈ ⨆ k ∈ s, E k := by
    intro s i z hz
    have hle : (⨆ k ∈ s, E k) ≤ (⨆ k ∈ s, E k).comap (op i) := by
      refine iSup₂_le fun k hk y hy => ?_
      rw [Submodule.mem_comap, hE k y hy i]
      exact Submodule.smul_mem _ _ ((le_iSup₂ (f := fun k (_ : k ∈ s) => E k) k hk) hy)
    exact hle hz
  have key : ∀ s : Finset κ, ∀ x : M, (∀ i, (op i : M → M) x = ψ i • x) →
      x ∈ ⨆ k ∈ s, E k → x = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x _ h; simpa using h
    | insert k0 s hk0 ih =>
      intro x hx h
      rw [Finset.iSup_insert, Submodule.mem_sup] at h
      obtain ⟨y, hy, z, hz, rfl⟩ := h
      obtain ⟨i, hi⟩ : ∃ i, χ k0 i ≠ ψ i := by
        by_contra h'
        push_neg at h'
        exact hne k0 (funext h')
      have hw : (op i : M → M) z - χ k0 i • z ∈ ⨆ k ∈ s, E k :=
        Submodule.sub_mem _ (hstab s i z hz) (Submodule.smul_mem _ _ hz)
      have h1 := hx i
      rw [map_add, hE k0 y hy i, smul_add] at h1
      have h2 : (op i : M → M) z = ψ i • y + ψ i • z - χ k0 i • y := by
        rw [← h1]; abel
      have hw' : (op i : M → M) z - χ k0 i • z = (ψ i - χ k0 i) • (y + z) := by
        rw [h2]; module
      rw [hw'] at hw
      have heig : ∀ j, (op j : M → M) ((ψ i - χ k0 i) • (y + z)) = ψ j • ((ψ i - χ k0 i) • (y + z)) := by
        intro j
        rw [map_smul, hx j, smul_comm]
      have h0 := ih _ heig hw
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hi
      · exact h
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hmem
  exact hx0 (key s x hx hs)

end GlobalTheory.JointEigenSupremum

/- English proof (translation)
Introduce `op χ E hE ψ x hx0 hx hmem` and use `GlobalTheory.JointEigenSupremum.joint_eigen_mem_iSup op χ E hE ψ x hx0 hx hmem`.
-/
theorem GlobalTheory.JointEigenSupremum.target : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (op : ι → Module.End ℂ M) (χ : κ → ι → ℂ) (E : κ → Submodule ℂ M), (∀ (k : κ), ∀ y ∈ E k, ∀ (i : ι), (op i : M → M) y = χ k i • y) → ∀ (ψ : ι → ℂ) (x : M), x ≠ (0 : M) → (∀ (i : ι), (op i : M → M) x = ψ i • x) → x ∈ ⨆ (k : κ), E k → ∃ (k : κ), χ k = ψ :=
  fun op χ E hE ψ x hx0 hx hmem => GlobalTheory.JointEigenSupremum.joint_eigen_mem_iSup op χ E hE ψ x hx0 hx hmem
