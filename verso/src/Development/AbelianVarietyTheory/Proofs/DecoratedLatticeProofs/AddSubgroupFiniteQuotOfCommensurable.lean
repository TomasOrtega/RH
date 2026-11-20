import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `V _ A L N M hN hM htf hAL hLA hfin k hk`. Take `⟨R₀, hR₀⟩` from `hfin (k * N * M) (by positivity)`. Set `P : V → Prop` to `fun r₀ => ∃ a ∈ A, ∃ w ∈ L, N • a = r₀ + (k * N * M) • w`. Set `f : V → V` to `fun r₀ => if h : P r₀ then h.choose else 0`. Use `⟨R₀.image f, ?_⟩` and prove the remaining obligations.

Introduce `u hu`. Take `⟨r₀, hr₀, v, hv, huv⟩` from `hR₀ (N • u) (hAL u hu)`. Establish `hP : P r₀` using `⟨u, hu, v, hv, huv⟩`. Establish `hf : f r₀ = hP.choose` using `dif_pos hP`. Take `⟨haA, w, hwL, haw⟩` from `hP.choose_spec`.

Use `⟨f r₀, Finset.mem_image_of_mem f hr₀, M • (v - w), hLA _ (L.sub_mem hv hwL), ?_⟩` and prove the remaining obligations. Rewrite using `[hf]`. Establish `key : N • (u - (hP.choose + k • M • (v - w))) = 0`. Establish `e : N • k • M • (v - w) = (k * N * M) • (v - w)`. Rewrite using `[smul_smul, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_sub, smul_add, huv, haw, e, smul_sub]`. Normalize the expressions using the abelian group laws. Conclude with `sub_eq_zero.mp (htf _ key)`.
-/
theorem addSubgroup_finite_quot_of_commensurable : ∀ (V : Type) [AddCommGroup V] (A L : AddSubgroup V) (N M : ℕ), 0 < N → 0 < M → (∀ v : V, N • v = 0 → v = 0) → (∀ a ∈ A, N • a ∈ L) → (∀ l ∈ L, M • l ∈ A) → (∀ j : ℕ, 0 < j → ∃ R : Finset V, ∀ u ∈ L, ∃ r ∈ R, ∃ v ∈ L, u = r + j • v) → ∀ k : ℕ, 0 < k → ∃ R : Finset V, ∀ u ∈ A, ∃ r ∈ R, ∃ v ∈ A, u = r + k • v := by
  classical
  intro V _ A L N M hN hM htf hAL hLA hfin k hk
  obtain ⟨R₀, hR₀⟩ := hfin (k * N * M) (by positivity)
  let P : V → Prop := fun r₀ => ∃ a ∈ A, ∃ w ∈ L, N • a = r₀ + (k * N * M) • w
  let f : V → V := fun r₀ => if h : P r₀ then h.choose else 0
  refine ⟨R₀.image f, ?_⟩
  intro u hu
  obtain ⟨r₀, hr₀, v, hv, huv⟩ := hR₀ (N • u) (hAL u hu)
  have hP : P r₀ := ⟨u, hu, v, hv, huv⟩
  have hf : f r₀ = hP.choose := dif_pos hP
  obtain ⟨haA, w, hwL, haw⟩ := hP.choose_spec
  refine ⟨f r₀, Finset.mem_image_of_mem f hr₀, M • (v - w), hLA _ (L.sub_mem hv hwL), ?_⟩
  rw [hf]
  have key : N • (u - (hP.choose + k • M • (v - w))) = 0 := by
    have e : N • k • M • (v - w) = (k * N * M) • (v - w) := by
      rw [smul_smul, smul_smul]
      congr 1
      ring
    rw [smul_sub, smul_add, huv, haw, e, smul_sub]
    abel
  exact sub_eq_zero.mp (htf _ key)

end GlobalTheory
