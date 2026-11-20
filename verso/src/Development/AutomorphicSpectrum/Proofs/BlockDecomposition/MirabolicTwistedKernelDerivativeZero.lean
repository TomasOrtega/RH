import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir

/- English proof (translation)
Rewrite using `[MirUin, derUnipM, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, derUnip, Subgroup.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv⟩`. Rewrite using `[← hv]`. Use `⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩, fun i hi => ?_⟩` and prove the remaining obligations.

Establish `hj : j ≠ Fin.last n` using `fun h => by`. Substitute `h` using the available equality. Conclude with `absurd hji (not_lt.2 (Fin.le_last i))`. Establish `hij : i ≠ j` using `(ne_of_lt hji).symm`. Simplify using `[unip, colMat, one_apply, hj, hij]`.

Distinguish the cases in `hi : i = Fin.last n`. Substitute `hi` using the available equality. Simplify using `[unip, colMat]`. Simplify using `[unip, colMat, hi]`. Establish `hi' : i ≠ Fin.last n` using `fun h => by subst h; simp at hi`.

Use extensionality with `l`. Simplify using `[unip, colMat, hi', Matrix.col, one_apply, Pi.single_apply, eq_comm]`. Introduce and unpack `⟨hB, hC⟩`. Use `⟨Multiplicative.ofAdd (fun i => (g : GL (Fin (n + 1)) k).val (Fin.castSucc i) (Fin.last n)), ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Use `show (1 + colMat k n _) i j = _`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [colMat, ((mem_unipB k).1 hB).2]`.

Consider the case `cast i => simp [colMat, one_apply, Fin.castSucc_ne_last]`. Consider the case `cast j`. Establish `h` using `congrFun (hC (Fin.castSucc j) (by simp)) i`. Rewrite `h` using `[mulVec_single_one]`. Simplify using `only [Matrix.col_apply] at h`.

Rewrite using `[h]`. Simplify using `[colMat, Fin.castSucc_ne_last, one_apply, Pi.single_apply]`.
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
Express the relevant statement in the definitionally equal form `Circle.toUnits (ψ (∑ p ∈ Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => (p.2 : ℕ) = p.1 + 1 ∧ n ≤ (p.1 : ℕ)), _)) = 1`. Rewrite using `[Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]`. Introduce `p hp`. Establish `h` using `(Finset.mem_filter.1 hp).2`. Use `p.2.isLt` as an intermediate fact.

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
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, v, rfl⟩`. Use `Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).1 u.2⟩, v, ?_⟩` and prove the remaining obligations. Simplify using `[derCharM_self_apply]`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, v, rfl⟩`. Use `Submodule.subset_span ⟨⟨u, (mem_MirUin_iff_mem_derUnipM k n u).2 u.2⟩, v, ?_⟩` and prove the remaining obligations. Simplify using `[derCharM_self_apply]`.
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
