import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Introduce `R _ p B _ _ _ h n`. Establish `hnoeth` using `h.noeth`. Establish `hle : p.map (algebraMap R B) ≤ maximalIdeal B`. Rewrite using `[Ideal.map_le_iff_le_comap, h.comap_eq]`. Establish `heq : p.map (algebraMap R B) = maximalIdeal B`.

Use `le_antisymm hle ?_` and prove the remaining obligations. Apply `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge` to reduce the goal to its premises. Introduce `b hb`. Take `⟨a, s, hs, hsa⟩` from `h.dense 2 b`. Establish `hsu : IsUnit (algebraMap R B s)`.

Assume the negation of the conclusion as `hn`. Apply `hs` to reduce the goal to its premises. Rewrite using `[← h.comap_eq, Ideal.mem_comap]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr hn`. Establish `hm2 : maximalIdeal B ^ 2 ≤ maximalIdeal B` using `Ideal.pow_le_self two_ne_zero`.

Establish `ha : a ∈ p`. Rewrite using `[← h.comap_eq, Ideal.mem_comap]`. Establish `: algebraMap R B a = algebraMap R B s * b - (algebraMap R B s * b - algebraMap R B a)` using `by ring`. Rewrite using `[this]`. Conclude with `sub_mem (Ideal.mul_mem_left _ _ hb) (hm2 hsa)`.

Take `⟨u, hu⟩` from `hsu`. Establish `hb' : b = (↑u⁻¹ : B) * (algebraMap R B a + (algebraMap R B s * b - algebraMap R B a))`. Rewrite using `[← hu]`. Simplify using the standard rewrite rules. Rewrite using `[hb', smul_eq_mul, ← pow_two]`.

Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Conclude with `add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)) (Ideal.mem_sup_right hsa)`. Rewrite using `[Ideal.map_pow, heq]`.
-/
theorem UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → ∀ n : ℕ, (p ^ n).map (algebraMap R B) = maximalIdeal B ^ n := by
  intro R _ p B _ _ _ h n
  have hnoeth := h.noeth
  have hle : p.map (algebraMap R B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, h.comap_eq]
  have heq : p.map (algebraMap R B) = maximalIdeal B := by
    refine le_antisymm hle ?_
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
    intro b hb
    obtain ⟨a, s, hs, hsa⟩ := h.dense 2 b
    have hsu : IsUnit (algebraMap R B s) := by
      by_contra hn
      apply hs
      rw [← h.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hm2 : maximalIdeal B ^ 2 ≤ maximalIdeal B := Ideal.pow_le_self two_ne_zero
    have ha : a ∈ p := by
      rw [← h.comap_eq, Ideal.mem_comap]
      have : algebraMap R B a = algebraMap R B s * b - (algebraMap R B s * b - algebraMap R B a) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ hb) (hm2 hsa)
    obtain ⟨u, hu⟩ := hsu
    have hb' : b = (↑u⁻¹ : B) * (algebraMap R B a + (algebraMap R B s * b - algebraMap R B a)) := by
      rw [← hu]
      simp
    rw [hb', smul_eq_mul, ← pow_two]
    apply Ideal.mul_mem_left
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)) (Ideal.mem_sup_right hsa)
  rw [Ideal.map_pow, heq]
