import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hr : Module.finrank ℤ H ≤ N`. Use `Submodule.finrank_le H` as an intermediate fact. Simplify using `using this`. Set `b` to `Module.finBasis ℤ H`. Use `⟨fun i => if h : i.val < Module.finrank ℤ H then (b ⟨i.val, h⟩ : Fin N → ℤ) else 0, ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Distinguish the cases in `h : i.val < Module.finrank ℤ H`. Simplify using `[h]`.

Simplify using `[h]`. Introduce `x hx`. Establish `h1 : x = ∑ j, (b.repr ⟨x, hx⟩ j) • (b j : Fin N → ℤ)`. Use `congrArg (fun v : H => (v : Fin N → ℤ)) (b.sum_repr ⟨x, hx⟩)` as an intermediate fact. Use `beta_reduce at this`.

Rewrite `this` using `[Submodule.coe_sum]`. Conclude with `this.symm`. Rewrite using `[h1]`. Use `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Conclude with `⟨⟨j.val, lt_of_lt_of_le j.2 hr⟩, by simp⟩`.
-/
theorem exists_fin_span_eq_of_submodule_pi_int (N : ℕ) (H : Submodule ℤ (Fin N → ℤ)) :
    ∃ s : Fin N → (Fin N → ℤ), Submodule.span ℤ (Set.range s) = H := by
  classical
  have hr : Module.finrank ℤ H ≤ N := by
    have := Submodule.finrank_le H
    simpa using this
  let b := Module.finBasis ℤ H
  refine ⟨fun i => if h : i.val < Module.finrank ℤ H then (b ⟨i.val, h⟩ : Fin N → ℤ) else 0, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    by_cases h : i.val < Module.finrank ℤ H
    · simp [h]
    · simp [h]
  · intro x hx
    have h1 : x = ∑ j, (b.repr ⟨x, hx⟩ j) • (b j : Fin N → ℤ) := by
      have := congrArg (fun v : H => (v : Fin N → ℤ)) (b.sum_repr ⟨x, hx⟩)
      beta_reduce at this
      rw [Submodule.coe_sum] at this
      exact this.symm
    rw [h1]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨⟨j.val, lt_of_lt_of_le j.2 hr⟩, by simp⟩

/- English proof (translation)
Take `⟨N, π, hπ⟩` from `Module.Finite.exists_fin' ℤ A`. Use `⟨N * N, fun M hM => ?_⟩` and prove the remaining obligations. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Set `G : (Fin N → Fin N → ZMod M) → AddSubgroup A` to `fun f => AddSubgroup.closure (Set.range (fun i => π (fun j => ((f i j).val : ℤ))) ∪ Set.range (fun x : A => M • x))`. Use `⟨Finset.univ.image G, ?_, fun H hH => ?_⟩` and prove the remaining obligations.

Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Simplify using `[ZMod.card, pow_mul]`. Take `⟨s, hs⟩` from `exists_fin_span_eq_of_submodule_pi_int N ((AddSubgroup.toIntSubmodule H).comap π)`. Rewrite using `[Finset.mem_image]`. Use `⟨fun i j => ((s i j : ℤ) : ZMod M), Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Establish `key : ∀ i, π (s i) = π (fun j => ((((s i j : ℤ) : ZMod M)).val : ℤ)) + M • π (fun j => s i j / M)`. Introduce `i`. Rewrite using `[← map_nsmul, ← map_add]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, ZMod.val_intCast, nsmul_eq_mul]`. Conclude with `(Int.emod_add_mul_ediv _ _).symm`. Establish `hsH : ∀ i, π (s i) ∈ H`. Introduce `i`. Establish `: s i ∈ (AddSubgroup.toIntSubmodule H).comap π`.

Rewrite using `[← hs]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Conclude with `this`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ (⟨i, rfl⟩ | ⟨x, rfl⟩)`. Establish `h1` using `H.sub_mem (hsH i) (hH (π (fun j => s i j / M)))`. Rewrite `h1` using `[key i, add_sub_cancel_right]`. Conclude with `h1`. Conclude with `hH x`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `hπ x`. Establish `hy : y ∈ Submodule.span ℤ (Set.range s)`. Rewrite using `[hs]`. Conclude with `hx`.

Use `clear hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Rewrite using `[key i]`.

Conclude with `AddSubgroup.add_mem _ (AddSubgroup.subset_closure (Or.inl ⟨i, rfl⟩)) (AddSubgroup.subset_closure (Or.inr ⟨_, rfl⟩))`. Consider the case `zero => rw [map_zero]`. Conclude with `AddSubgroup.zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `AddSubgroup.add_mem _ ha hb`.

Consider the case `smul a b _ hb => rw [map_smul]`. Conclude with `AddSubgroup.zsmul_mem _ hb a`.
-/
theorem exists_card_subgroups_containing_nsmul_le (A : Type) [AddCommGroup A] [Module.Finite ℤ A] :
    ∃ c : ℕ, ∀ M : ℕ, 0 < M →
      ∃ T : Finset (AddSubgroup A), T.card ≤ M ^ c ∧
        ∀ H : AddSubgroup A, (∀ x : A, M • x ∈ H) → H ∈ T := by
  classical
  obtain ⟨N, π, hπ⟩ := Module.Finite.exists_fin' ℤ A
  refine ⟨N * N, fun M hM => ?_⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  let G : (Fin N → Fin N → ZMod M) → AddSubgroup A := fun f =>
    AddSubgroup.closure (Set.range (fun i => π (fun j => ((f i j).val : ℤ))) ∪
      Set.range (fun x : A => M • x))
  refine ⟨Finset.univ.image G, ?_, fun H hH => ?_⟩
  · refine Finset.card_image_le.trans ?_
    simp [ZMod.card, pow_mul]
  · obtain ⟨s, hs⟩ := exists_fin_span_eq_of_submodule_pi_int N
      ((AddSubgroup.toIntSubmodule H).comap π)
    rw [Finset.mem_image]
    refine ⟨fun i j => ((s i j : ℤ) : ZMod M), Finset.mem_univ _, ?_⟩
    have key : ∀ i, π (s i) = π (fun j => ((((s i j : ℤ) : ZMod M)).val : ℤ))
        + M • π (fun j => s i j / M) := by
      intro i
      rw [← map_nsmul, ← map_add]
      congr 1
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, ZMod.val_intCast, nsmul_eq_mul]
      exact (Int.emod_add_mul_ediv _ _).symm
    have hsH : ∀ i, π (s i) ∈ H := by
      intro i
      have : s i ∈ (AddSubgroup.toIntSubmodule H).comap π := by
        rw [← hs]; exact Submodule.subset_span ⟨i, rfl⟩
      exact this
    apply le_antisymm
    · rw [AddSubgroup.closure_le]
      rintro _ (⟨i, rfl⟩ | ⟨x, rfl⟩)
      · have h1 := H.sub_mem (hsH i) (hH (π (fun j => s i j / M)))
        rw [key i, add_sub_cancel_right] at h1
        exact h1
      · exact hH x
    · intro x hx
      obtain ⟨y, rfl⟩ := hπ x
      have hy : y ∈ Submodule.span ℤ (Set.range s) := by
        rw [hs]; exact hx
      clear hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [key i]
        exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure (Or.inl ⟨i, rfl⟩))
          (AddSubgroup.subset_closure (Or.inr ⟨_, rfl⟩))
      | zero => rw [map_zero]; exact AddSubgroup.zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact AddSubgroup.add_mem _ ha hb
      | smul a b _ hb => rw [map_smul]; exact AddSubgroup.zsmul_mem _ hb a

end GlobalTheory
