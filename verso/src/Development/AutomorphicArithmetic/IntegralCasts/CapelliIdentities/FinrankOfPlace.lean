import Mathlib

/- English proof (translation)
Introduce `M V _ _ _ _ _ j hj hs`. Set `b` to `Module.Free.chooseBasis ℤ M`. Establish `h1 : LinearIndependent ℤ (j.toIntLinearMap ∘ b)` using `b.linearIndependent.map' j.toIntLinearMap (LinearMap.ker_eq_bot.mpr hj)`. Establish `h2 : LinearIndependent ℚ (j.toIntLinearMap ∘ b)` using `(LinearIndependent.iff_fractionRing ℤ ℚ).mp h1`. Establish `key : ∀ u : M, j u ∈ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b))`.

Introduce `u`. Establish `hu : j u = ∑ i, (b.repr u i) • j (b i)` using `by conv_lhs => rw [← b.sum_repr u]`. Simplify using `only [map_sum, map_zsmul]`. Rewrite using `[hu]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Conclude with `zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _`. Establish `h3 : ⊤ ≤ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b))`. Introduce `w _`. Take `⟨m, u, hm, hw⟩` from `hs w`. Establish `hm' : (m : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr hm`.

Establish `: w = (m : ℚ)⁻¹ • j u`. Rewrite using `[← hw, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (key u)`. Rewrite using `[Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis (Module.Basis.mk h2 h3)]`.
-/
theorem UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place :
    ∀ {M V : Type} [inst : AddCommGroup M]
    [Module.Free ℤ M] [Module.Finite ℤ M] [inst_3 : AddCommGroup V] [inst_4 : _root_.Module ℚ V] (j : M →+ V),
    Function.Injective (⇑j : M → V) →
      (∀ (w : V), ∃ (m : ℕ) (u : M), m ≠ (0 : ℕ) ∧ m • w = (j : M → V) u) → Module.finrank ℤ M = Module.finrank ℚ V := by
  intro M V _ _ _ _ _ j hj hs
  classical
  let b := Module.Free.chooseBasis ℤ M
  have h1 : LinearIndependent ℤ (j.toIntLinearMap ∘ b) :=
    b.linearIndependent.map' j.toIntLinearMap (LinearMap.ker_eq_bot.mpr hj)
  have h2 : LinearIndependent ℚ (j.toIntLinearMap ∘ b) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp h1
  have key : ∀ u : M, j u ∈ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b)) := by
    intro u
    have hu : j u = ∑ i, (b.repr u i) • j (b i) := by
      conv_lhs => rw [← b.sum_repr u]
      simp only [map_sum, map_zsmul]
    rw [hu]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have h3 : ⊤ ≤ Submodule.span ℚ (Set.range (j.toIntLinearMap ∘ b)) := by
    intro w _
    obtain ⟨m, u, hm, hw⟩ := hs w
    have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have : w = (m : ℚ)⁻¹ • j u := by
      rw [← hw, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hm', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (key u)
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis (Module.Basis.mk h2 h3)]
