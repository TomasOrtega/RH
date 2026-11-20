import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

/- English proof (translation)
Establish `hsep : (X ^ N - C (1 : k) : k[X]).Separable` using `separable_X_pow_sub_C 1 hN one_ne_zero`. Establish `hss : g.IsSemisimple` using `Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hg])`. Establish `hdim : ∀ μ, Module.finrank k (Module.End.eigenspace g μ) = (LinearMap.charpoly g).roots.count μ`. Introduce `μ`. Rewrite using `[← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ, LinearMap.finrank_maxGenEigenspace_eq, count_roots]`.

Rewrite using `[Finset.sum_multiset_map_count]`. Rewrite using `[finsum_mem_eq_sum_of_inter_support_eq _ (t := (LinearMap.charpoly g).roots.toFinset)]`. Use `Finset.sum_congr rfl fun μ _ => ?_` and prove the remaining obligations. Rewrite using `[hdim, nsmul_eq_mul]`. Use extensionality with `μ`.

Simplify using `only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, Finset.mem_coe, Multiset.mem_toFinset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Apply `h2` to reduce the goal to its premises. Rewrite using `[hdim, Multiset.count_eq_zero_of_notMem hc]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations.

Establish `hev : g.HasEigenvalue μ`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly]`. Conclude with `isRoot_of_mem_roots h1`. Establish `h3` using `hev.pow N`. Rewrite `h3` using `[hg]`.

Take `⟨v, hv⟩` from `h3.exists_hasEigenvector`. Establish `h4` using `hv.apply_eq_smul`. Establish `h5 : (μ ^ N - 1) • v = 0`. Rewrite using `[sub_smul, ← h4]`. Simplify using the standard rewrite rules.

Conclude with `sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv.2)`.
-/
theorem sum_roots_charpoly_eq_finsum_eigenspace (k : Type) [Field k] [IsAlgClosed k] (V : Type)
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (g : Module.End k V) (N : ℕ)
    (hN : (N : k) ≠ 0) (hg : g ^ N = 1) (h : k → ℂ) :
    ((LinearMap.charpoly g).roots.map h).sum =
      ∑ᶠ μ ∈ {μ : k | μ ^ N = 1}, (Module.finrank k (Module.End.eigenspace g μ) : ℂ) * h μ := by
  classical
  have hsep : (X ^ N - C (1 : k) : k[X]).Separable := separable_X_pow_sub_C 1 hN one_ne_zero
  have hss : g.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree (by simp [hg])
  have hdim : ∀ μ, Module.finrank k (Module.End.eigenspace g μ) =
      (LinearMap.charpoly g).roots.count μ := by
    intro μ
    rw [← hss.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ,
      LinearMap.finrank_maxGenEigenspace_eq, count_roots]
  rw [Finset.sum_multiset_map_count]
  rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := (LinearMap.charpoly g).roots.toFinset)]
  · refine Finset.sum_congr rfl fun μ _ => ?_
    rw [hdim, nsmul_eq_mul]
  · ext μ
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Function.mem_support, Finset.mem_coe,
      Multiset.mem_toFinset]
    constructor
    · rintro ⟨-, h2⟩
      refine ⟨?_, h2⟩
      by_contra hc
      apply h2
      rw [hdim, Multiset.count_eq_zero_of_notMem hc]
      simp
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have hev : g.HasEigenvalue μ := by
        rw [Module.End.hasEigenvalue_iff_isRoot_charpoly]
        exact isRoot_of_mem_roots h1
      have h3 := hev.pow N
      rw [hg] at h3
      obtain ⟨v, hv⟩ := h3.exists_hasEigenvector
      have h4 := hv.apply_eq_smul
      have h5 : (μ ^ N - 1) • v = 0 := by
        rw [sub_smul, ← h4]; simp
      exact sub_eq_zero.mp ((smul_eq_zero.mp h5).resolve_right hv.2)

end GlobalTheory.CuspGL
