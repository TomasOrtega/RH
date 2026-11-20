import Mathlib

namespace GlobalTheory.InvariantBotOrTop

open Matrix

/- English proof (translation)
Establish `hA : A ∈ Submodule.span k (Set.range M)`. Rewrite using `[hM]`. Conclude with `Submodule.mem_top`. Proceed by induction on `hA using Submodule.span_induction with`. Consider the case `mem A hA`.

Take `⟨g, rfl⟩` from `hA`. Conclude with `hW g`. Consider the case `zero`. Introduce `x _`. Rewrite using `[Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]`.

Conclude with `W.zero_mem`. Consider the case `add A B _ _ hA hB`. Introduce `x hx`. Rewrite using `[Matrix.map_add _ (map_add _), Matrix.add_mulVec]`. Conclude with `W.add_mem (hA x hx) (hB x hx)`.

Consider the case `smul c A _ hA`. Introduce `x hx`. Rewrite using `[Matrix.map_smul _ c (fun a => by rw [smul_eq_mul, map_mul, Algebra.smul_def])]`. Use `first`. Consider the case `rw [Matrix.smul_mulVec]`.

Consider the case `rw [Matrix.smul_mulVec_assoc]`. Conclude with `W.smul_of_tower_mem c (hA x hx)`.
-/
theorem invariant_all {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) (A : Matrix (Fin r) (Fin r) k) :
    ∀ x ∈ W, A.map (algebraMap k K) *ᵥ x ∈ W := by
  have hA : A ∈ Submodule.span k (Set.range M) := by
    rw [hM]
    exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨g, rfl⟩ := hA
    exact hW g
  | zero =>
    intro x _
    rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
    exact W.zero_mem
  | add A B _ _ hA hB =>
    intro x hx
    rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
    exact W.add_mem (hA x hx) (hB x hx)
  | smul c A _ hA =>
    intro x hx
    rw [Matrix.map_smul _ c (fun a => by rw [smul_eq_mul, map_mul, Algebra.smul_def])]
    first
      | rw [Matrix.smul_mulVec]
      | rw [Matrix.smul_mulVec_assoc]
    exact W.smul_of_tower_mem c (hA x hx)

/- English proof (translation)
Distinguish the cases in `hbot : W = ⊥`. Conclude with `Or.inl hbot`. Use `right`. Take `⟨x, hxW, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hbot`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, x j ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx0 (funext h)`. Establish `he : ∀ i, (Pi.single i (1 : K) : Fin r → K) ∈ W`. Introduce `i`.

Establish `h1` using `invariant_all M hM W hW (Matrix.single i j 1) x hxW`. Establish `h2 : (Matrix.single i j (1 : k)).map (algebraMap k K) *ᵥ x = x j • Pi.single i 1`. Use extensionality with `a`. Rewrite using `[Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hai : a = i`.

Substitute `hai` using the available equality. Rewrite using `[Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb]) (by simp)]`. Simplify using `[Matrix.single_apply]`. Rewrite using `[Finset.sum_eq_zero (fun b _ => by simp [Matrix.single_apply, hai, Ne.symm hai])]`. Simplify using `[Pi.single_apply, hai]`.

Rewrite `h1` using `[h2]`. Establish `h3` using `W.smul_mem (x j)⁻¹ h1`. Rewrite `h3` using `[smul_smul, inv_mul_cancel₀ hj, one_smul]`. Then use the resulting hypothesis. Rewrite using `[eq_top_iff]`. Introduce `y _`.

Establish `hy : y = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K)`. Use extensionality with `a`. Simplify using `[Pi.single_apply]`. Rewrite using `[hy]`. Conclude with `W.sum_mem fun i _ => W.smul_mem _ (he i)`.
-/
theorem bot_or_top {Γ k K : Type} [Field k] [Field K] [Algebra k K] {r : ℕ}
    (M : Γ → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (W : Submodule K (Fin r → K))
    (hW : ∀ g, ∀ x ∈ W, (M g).map (algebraMap k K) *ᵥ x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (funext h)

  have he : ∀ i, (Pi.single i (1 : K) : Fin r → K) ∈ W := by
    intro i
    have h1 := invariant_all M hM W hW (Matrix.single i j 1) x hxW
    have h2 : (Matrix.single i j (1 : k)).map (algebraMap k K) *ᵥ x = x j • Pi.single i 1 := by
      ext a
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      by_cases hai : a = i
      · subst hai
        rw [Finset.sum_eq_single j (fun b _ hb => by simp [Matrix.single_apply, hb, Ne.symm hb]) (by simp)]
        simp [Matrix.single_apply]
      · rw [Finset.sum_eq_zero (fun b _ => by simp [Matrix.single_apply, hai, Ne.symm hai])]
        simp [Pi.single_apply, hai]
    rw [h2] at h1
    have h3 := W.smul_mem (x j)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hj, one_smul] at h3
  rw [eq_top_iff]
  intro y _
  have hy : y = ∑ i, y i • (Pi.single i (1 : K) : Fin r → K) := by
    ext a
    simp [Pi.single_apply]
  rw [hy]
  exact W.sum_mem fun i _ => W.smul_mem _ (he i)

/- English proof (translation)
Introduce `Γ k K _ _ _ r M hM W hW`. Conclude with `bot_or_top M hM W hW`.
-/
theorem main : ∀ {Γ k K : Type} [inst : Field k] [inst_1 : Field K] [inst_2 : Algebra k K] {r : ℕ} (M : Γ → Matrix (Fin r) (Fin r) k), Submodule.span k (Set.range M) = ⊤ → ∀ (W : Submodule K (Fin r → K)), (∀ (g : Γ), ∀ x ∈ W, Matrix.mulVec (Matrix.map (M g) (⇑(Algebra.algebraMap k K) : k → K)) x ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro Γ k K _ _ _ r M hM W hW
  exact bot_or_top M hM W hW

end GlobalTheory.InvariantBotOrTop
