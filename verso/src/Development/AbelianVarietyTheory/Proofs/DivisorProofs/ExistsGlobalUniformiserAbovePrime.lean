import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp F _ _`. Use `set J : Ideal (𝓞 F) := (Ideal.span {(p : 𝓞 F)}).radical with hJdef`. Establish `hp0 : (p : 𝓞 F) ≠ 0`. Conclude with `(Nat.cast_ne_zero (R := 𝓞 F)).mpr hp.out.ne_zero` after adjusting the coercions. Establish `hI0 : Ideal.span {(p : 𝓞 F) ^ 2} ≠ 0`.

Rewrite using `[Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `pow_ne_zero _ hp0`. Establish `hpJ : (p : 𝓞 F) ∈ J` using `Ideal.le_radical (Ideal.mem_span_singleton_self _)`. Establish `hIJ : Ideal.span {(p : 𝓞 F) ^ 2} ≤ J`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `J.pow_mem_of_mem hpJ 2 two_pos`. Take `⟨ϖ, hϖ⟩` from `IsDedekindDomain.exists_sup_span_eq hIJ hI0`. Establish `hϖJ : ϖ ∈ J` using `hϖ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Use `⟨ϖ, ?_⟩` and prove the remaining obligations. Establish `hp' : (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ⊔ Ideal.span {ϖ}` using `hϖ ▸ hpJ`.

Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp hp'`. Take `⟨z, rfl⟩` from `Ideal.mem_span_singleton'.mp hb`. Use `⟨z, ?_, hϖJ, ?_⟩` and prove the remaining obligations. Establish `: ϖ * z - (p : 𝓞 F) = -a` using `by rw [← hab]; ring`. Rewrite using `[this]`.

Conclude with `neg_mem ha`. Establish `hK : Ideal.span {(p : 𝓞 F), ϖ} = J`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce `x hx`.

Break down `hx with rfl | hx` into its components or cases. Conclude with `hpJ`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality. Conclude with `hϖJ`.

Rewrite using `[← hϖ]`. Apply `sup_le` to reduce the goal to its premises. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))`.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.subset_span (by simp)`. Rewrite using `[hK]`. Conclude with `(Ideal.isRadical_iff_quotient_reduced J).mp (Ideal.radical_isRadical _)`.
-/
theorem exists_global_uniformiser_above_prime :
    ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F], ∃ ϖ z : 𝓞 F,
      ϖ * z - (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ∧ (∃ n : ℕ, ϖ ^ n ∈ Ideal.span {(p : 𝓞 F)}) ∧
      IsReduced (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
  intro p hp F _ _
  set J : Ideal (𝓞 F) := (Ideal.span {(p : 𝓞 F)}).radical with hJdef
  have hp0 : (p : 𝓞 F) ≠ 0 := by
    exact_mod_cast (Nat.cast_ne_zero (R := 𝓞 F)).mpr hp.out.ne_zero
  have hI0 : Ideal.span {(p : 𝓞 F) ^ 2} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hp0
  have hpJ : (p : 𝓞 F) ∈ J := Ideal.le_radical (Ideal.mem_span_singleton_self _)
  have hIJ : Ideal.span {(p : 𝓞 F) ^ 2} ≤ J := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact J.pow_mem_of_mem hpJ 2 two_pos
  obtain ⟨ϖ, hϖ⟩ := IsDedekindDomain.exists_sup_span_eq hIJ hI0
  have hϖJ : ϖ ∈ J := hϖ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  refine ⟨ϖ, ?_⟩

  have hp' : (p : 𝓞 F) ∈ Ideal.span {(p : 𝓞 F) ^ 2} ⊔ Ideal.span {ϖ} := hϖ ▸ hpJ
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hp'
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp hb
  refine ⟨z, ?_, hϖJ, ?_⟩
  · have : ϖ * z - (p : 𝓞 F) = -a := by rw [← hab]; ring
    rw [this]; exact neg_mem ha
  · have hK : Ideal.span {(p : 𝓞 F), ϖ} = J := by
      apply le_antisymm
      · rw [Ideal.span_le]
        intro x hx
        rcases hx with rfl | hx
        · exact hpJ
        · rw [Set.mem_singleton_iff] at hx; subst hx; exact hϖJ
      · rw [← hϖ]
        apply sup_le
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          rw [pow_two]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
        · rw [Ideal.span_le, Set.singleton_subset_iff]
          exact Ideal.subset_span (by simp)
    rw [hK]
    exact (Ideal.isRadical_iff_quotient_reduced J).mp (Ideal.radical_isRadical _)

end GlobalTheory
