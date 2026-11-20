import Mathlib

namespace GlobalTheory.IsolatedTheoremThree

/- English proof (translation)
Introduce `d1 R A _ _ _ hfac ξ γ hγ N w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨n, rfl⟩` from `hw`. Distinguish the cases in `hn : n < N`.

Conclude with `⟨γ n, Submodule.subset_span ⟨n, hn, rfl⟩, by simp⟩`. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_zero]`. Take `⟨u, hu⟩` from `hfac n`. Establish `hg : γ n = ↑u⁻¹ * algebraMap R A ξ ^ n`.

Rewrite using `[← hγ n, ← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Establish `hp : algebraMap R A ξ ^ n = algebraMap R A ξ ^ N * algebraMap R A ξ ^ (n - N)`. Rewrite using `[← pow_add]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hg, hp]`. Conclude with `Dvd.intro (↑u⁻¹ * algebraMap R A ξ ^ (n - N)) (by ring)`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hda⟩` from `hx`.

Take `⟨b, hb, hdb⟩` from `hy`. Use `⟨a + b, Submodule.add_mem _ ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[show x + y - (a + b) = (x - a) + (y - b) by ring]`. Conclude with `dvd_add hda hdb`. Consider the case `smul r x _ hx`.

Take `⟨a, ha, hda⟩` from `hx`. Use `⟨r • a, Submodule.smul_mem _ r ha, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_sub, Algebra.smul_def]`. Conclude with `Dvd.dvd.mul_left hda _`.
-/
theorem main : (let d1 : (R : Type) → {A : Type} → [inst : CommRing R] → [inst_1 : CommRing A] → [inst_2 : Algebra R A] → (ℕ → A) → ℕ → Submodule R A := @(fun (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) ↦ Submodule.span R (γ '' {m : ℕ | m < N})); ∀ {R A : Type} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A], (∀ (n : ℕ), IsUnit (↑(Nat.factorial n) : A)) → ∀ (ξ : R) (γ : ℕ → A), (∀ (n : ℕ), (↑(Nat.factorial n) : A) * γ n = (Algebra.algebraMap R A : R → A) ξ ^ n) → ∀ (N : ℕ), ∀ w ∈ Submodule.span R (Set.range γ), ∃ w₁ ∈ d1 R γ N, (Algebra.algebraMap R A : R → A) ξ ^ N ∣ w - w₁) := by
  intro d1 R A _ _ _ hfac ξ γ hγ N w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, rfl⟩ := hw
    by_cases hn : n < N
    · exact ⟨γ n, Submodule.subset_span ⟨n, hn, rfl⟩, by simp⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [sub_zero]
      obtain ⟨u, hu⟩ := hfac n
      have hg : γ n = ↑u⁻¹ * algebraMap R A ξ ^ n := by
        rw [← hγ n, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
      have hp : algebraMap R A ξ ^ n = algebraMap R A ξ ^ N * algebraMap R A ξ ^ (n - N) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hg, hp]
      exact Dvd.intro (↑u⁻¹ * algebraMap R A ξ ^ (n - N)) (by ring)
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hda⟩ := hx
    obtain ⟨b, hb, hdb⟩ := hy
    refine ⟨a + b, Submodule.add_mem _ ha hb, ?_⟩
    rw [show x + y - (a + b) = (x - a) + (y - b) by ring]
    exact dvd_add hda hdb
  | smul r x _ hx =>
    obtain ⟨a, ha, hda⟩ := hx
    refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
    rw [← smul_sub, Algebra.smul_def]
    exact Dvd.dvd.mul_left hda _

end GlobalTheory.IsolatedTheoremThree
