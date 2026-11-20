import Mathlib

/- English proof (translation)
Introduce `R Q _ _ _ _ _`. Use `haveI : Finite (Submodule R Q) := Finite.of_injective (fun N : Submodule R Q => (N : Set Q)) SetLike.coe_injective`. Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧ (IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)) = IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := by`. Take `⟨i, j, hne, h⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R Q))`. Break down `lt_or_gt_of_ne hne with hlt | hlt` into its components or cases.

Conclude with `⟨i, j, hlt, h⟩`. Conclude with `⟨j, i, hlt, h.symm⟩`. Establish `hbot : IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) = ⊥`. Use `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _ (Submodule.fg_def.2 ⟨_, Set.toFinite _, Submodule.span_eq _⟩) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `⟨i, fun a ha z => ?_⟩` and prove the remaining obligations. Establish `hz : a • z ∈ IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)` using `Submodule.smul_mem_smul ha Submodule.mem_top`. Rewrite `hz` using `[hbot, Submodule.mem_bot]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero :
    ∀ (R Q : Type) [inst : CommRing R] [inst_1 : IsLocalRing R]
    [inst_2 : AddCommGroup Q] [inst_3 : _root_.Module R Q] [Finite Q],
    ∃ (c : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ c, ∀ (z : Q), a • z = (0 : Q) := by
  intro R Q _ _ _ _ _
  haveI : Finite (Submodule R Q) :=
    Finite.of_injective (fun N : Submodule R Q => (N : Set Q)) SetLike.coe_injective
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧
      (IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)) =
        IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R Q))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, h⟩
    · exact ⟨j, i, hlt, h.symm⟩
  have hbot : IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (Submodule.fg_def.2 ⟨_, Set.toFinite _, Submodule.span_eq _⟩) ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    calc IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)
        = IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := h
      _ ≤ IsLocalRing.maximalIdeal R ^ (i + 1) • (⊤ : Submodule R Q) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)
      _ = _ := by rw [pow_succ', Submodule.mul_smul]
  refine ⟨i, fun a ha z => ?_⟩
  have hz : a • z ∈ IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hz
