import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R B _ _ _ _ _ _ N h`. Use `set J : Ideal R := N.colon (Set.univ : Set B) with hJ`. Establish `hmem : ∀ r : R, r ∈ J ↔ ∀ b : B, r • b ∈ N`. Introduce `r`. Rewrite using `[hJ, Submodule.mem_colon]`.

Simplify using the standard rewrite rules. Establish `hrad : maximalIdeal R ≤ J.radical`. Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hJp, hp⟩`.

Distinguish the cases in `hpm : p = maximalIdeal R`. Conclude with `hpm.ge`. It suffices to derive a contradiction. Take `⟨s, hs⟩` from `(Module.Finite.fg_top : (⊤ : Submodule R B).FG)`. Establish `hg : ∀ g : B, ∃ t ∉ p, t • g ∈ N` using `h p hp hpm`.

Use `choose t ht1 ht2 using hg`. Use `set u : R := ∏ g ∈ s, t g with hu`. Establish `hu_notin : u ∉ p`. Rewrite using `[hu, Ideal.IsPrime.prod_mem_iff]`. Introduce and unpack `⟨i, -, hi⟩`.

Conclude with `ht1 i hi`. Apply `hu_notin` to reduce the goal to its premises. Apply `hJp` to reduce the goal to its premises. Rewrite using `[hmem]`. Introduce `b`.

Establish `hb : b ∈ Submodule.span R (s : Set B)` using `by rw [hs]; trivial`. Establish `hle : Submodule.span R (s : Set B) ≤ N.comap (u • LinearMap.id)`. Rewrite using `[Submodule.span_le]`. Introduce `g hgs`. Simplify using `only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]`.

Rewrite using `[hu, ← Finset.prod_erase_mul s t hgs, mul_smul]`. Conclude with `N.smul_mem _ (ht2 g)`. Use `hle hb` as an intermediate fact. Simplify using `using this`. Take `⟨k, hk⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian (maximalIdeal R))`.

Conclude with `⟨k, fun x hx b => (hmem x).1 (hk hx) b⟩`.
-/
theorem smul_mem_of_maximalIdeal_pow_of_locally_eq :
    ∀ (R B : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup B] [Module R B]
      [Module.Finite R B] (N : Submodule R B),
      (∀ (p : Ideal R), p.IsPrime → p ≠ maximalIdeal R → ∀ b : B, ∃ t ∉ p, t • b ∈ N) →
      ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ N := by
  intro R B _ _ _ _ _ _ N h
  classical
  set J : Ideal R := N.colon (Set.univ : Set B) with hJ
  have hmem : ∀ r : R, r ∈ J ↔ ∀ b : B, r • b ∈ N := by
    intro r
    rw [hJ, Submodule.mem_colon]
    simp
  have hrad : maximalIdeal R ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro p ⟨hJp, hp⟩
    by_cases hpm : p = maximalIdeal R
    · exact hpm.ge
    exfalso
    obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R B).FG)
    have hg : ∀ g : B, ∃ t ∉ p, t • g ∈ N := h p hp hpm
    choose t ht1 ht2 using hg
    set u : R := ∏ g ∈ s, t g with hu
    have hu_notin : u ∉ p := by
      rw [hu, Ideal.IsPrime.prod_mem_iff]
      rintro ⟨i, -, hi⟩
      exact ht1 i hi
    apply hu_notin
    apply hJp
    rw [hmem]
    intro b
    have hb : b ∈ Submodule.span R (s : Set B) := by rw [hs]; trivial
    have hle : Submodule.span R (s : Set B) ≤ N.comap (u • LinearMap.id) := by
      rw [Submodule.span_le]
      intro g hgs
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [hu, ← Finset.prod_erase_mul s t hgs, mul_smul]
      exact N.smul_mem _ (ht2 g)
    have := hle hb
    simpa using this
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (maximalIdeal R))
  exact ⟨k, fun x hx b => (hmem x).1 (hk hx) b⟩

end GlobalTheory
