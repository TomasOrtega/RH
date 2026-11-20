import Mathlib

/- English proof (translation)
Introduce `l _ M _ _ hM f`. Take `⟨S, hS⟩` from `hM.fg_top`. Establish `hfin : (f '' (S : Set M)).Finite` using `S.finite_toSet.image _`. Use `haveI : Finite (f '' (S : Set M)) := hfin.to_subtype`. Use `⟨IntermediateField.adjoin ℚ_[l] (f '' (S : Set M)), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Introduce `x`. Establish `hx : x ∈ Submodule.span ℤ_[l] (S : Set M)`. Rewrite using `[hS]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[map_smul, ← IsScalarTower.algebraMap_smul ℚ_[l] c (f a)]`. Conclude with `IntermediateField.smul_mem _ ha`.
-/
theorem UpperTheory.Reformulated.B.FiniteModuleImageInFiniteExtension.qb_fdmod :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {M : Type}
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (f : M →ₗ[ℤ_[l]] PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
      FiniteDimensional ℚ_[l] ↥K ∧ ∀ (x : M), (f : M → PadicAlgCl l) x ∈ K := by
  intro l _ M _ _ hM f
  obtain ⟨S, hS⟩ := hM.fg_top
  have hfin : (f '' (S : Set M)).Finite := S.finite_toSet.image _
  haveI : Finite (f '' (S : Set M)) := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (f '' (S : Set M)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  · intro x
    have hx : x ∈ Submodule.span ℤ_[l] (S : Set M) := by
      rw [hS]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← IsScalarTower.algebraMap_smul ℚ_[l] c (f a)]
      exact IntermediateField.smul_mem _ ha
