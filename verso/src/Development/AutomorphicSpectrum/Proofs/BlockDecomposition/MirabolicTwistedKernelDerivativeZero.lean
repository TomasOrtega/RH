import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Proceed by induction.

Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem mem_MirUin_iff_mem_derUnipM (k : Type) [Field k] (n : ℕ) (g : Mir k n) :
    g ∈ MirUin k n ↔ g ∈ derUnipM k n n := by
  rw [MirUin, derUnipM, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, derUnip, Subgroup.mem_inf]
  constructor
  · rintro ⟨v, hv⟩
    rw [← hv]
    refine ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i hi => ?_⟩
    · have hj : j ≠ Fin.last n := fun h => by
        subst h; exact absurd hji (not_lt.2 (Fin.le_last i))
      have hij : i ≠ j := (ne_of_lt hji).symm
      simp [unip, colMat, one_apply, hj, hij]
    · by_cases hi : i = Fin.last n
      · subst hi; simp [unip, colMat]
      · simp [unip, colMat, hi]
    · have hi' : i ≠ Fin.last n := fun h => by subst h; simp at hi
      ext l
      simp [unip, colMat, hi', Matrix.col, one_apply, Pi.single_apply, eq_comm]
  · rintro ⟨hB, hC⟩
    refine ⟨Multiplicative.ofAdd (fun i => (g : GL (Fin (n + 1)) k).val (Fin.castSucc i) (Fin.last n)), ?_⟩
    ext i j
    show (1 + colMat k n _) i j = _
    induction j using Fin.lastCases with
    | last =>
      induction i using Fin.lastCases with
      | last => simp [colMat, ((mem_unipB k).1 hB).2]
      | cast i => simp [colMat, one_apply, Fin.castSucc_ne_last]
    | cast j =>
      have h := congrFun (hC (Fin.castSucc j) (by simp)) i
      rw [mulVec_single_one] at h
      simp only [Matrix.col_apply] at h
      rw [h]
      simp [colMat, Fin.castSucc_ne_last, one_apply, Pi.single_apply]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem derCharM_self_apply {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ψ : AddChar k Circle) (n : ℕ) (x : derUnipM k n n) : derCharM k ψ n n x = 1 := by
  change Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter
    (fun p : Fin (n + 1) × Fin (n + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)), _)) = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  have h := (Finset.mem_filter.1 hp).2
  have := p.2.isLt
  omega

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem twKer_MirUin_eq_derUnipM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k n) V) :
    twKer τ (MirUin k n) 1 = twKer τ (derUnipM k n n) (derCharM k ψ n n) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).1 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]
  · refine Submodule.span_le.2 ?_
    rintro w ⟨u, v, rfl⟩
    refine Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).2 u.2⟩, v, ?_⟩
    simp [derCharM_self_apply]

end GlobalTheory.CompanionTheory.BZMir
