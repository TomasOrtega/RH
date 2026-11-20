import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `K _ n α hα t hcard hmem hprod`. Distinguish the cases in `hn : Nonempty (Fin n)`. Set `g` to `Function.invFun α`. Establish `hg : ∀ x ∈ t, α (g x) = x` using `fun x hx => by`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.1 (hmem x hx)`.

Conclude with `Function.invFun_eq ⟨i, rfl⟩`. Set `u` to `t.map g`. Establish `hu : u.map α = t`. Rewrite using `[Multiset.map_map]`. Use `conv_rhs => rw [← Multiset.map_id t]`.

Conclude with `Multiset.map_congr rfl hg`. Establish `key` using `hα (fun i => u.count i) ?_ ?_`. Establish `hu1 : u = Finset.univ.val` using `Multiset.ext.2 fun i => by`. Rewrite using `[key i, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ i)]`. Rewrite using `[← hu, hu1]`.

Rewrite using `[Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]`. Simplify using `[u, hcard]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_multiset_map_count]`. Conclude with `(Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by`.

Rewrite using `[Multiset.count_eq_zero.2 (by simpa using hi), pow_zero])).symm`. Use `_ = t.prod := by rw [hu]`. Use `_ = ∏ i, α i := by rw [hprod, Finset.prod_eq_multiset_prod]`. Establish `h0 : (Finset.univ : Finset (Fin n)).val = 0`. Rewrite using `[Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn)]`.

Both sides reduce to the same expression. Rewrite `hcard`, the goal using `[h0, Multiset.map_zero]`. Conclude with `Multiset.card_eq_zero.1 hcard`.
-/
theorem UpperTheory.Gal.crystallineComparison.genMul_of :
    GenericMulOfProd := by
  intro K _ n α hα t hcard hmem hprod
  classical
  by_cases hn : Nonempty (Fin n)
  · let g := Function.invFun α
    have hg : ∀ x ∈ t, α (g x) = x := fun x hx => by
      obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 (hmem x hx)
      exact Function.invFun_eq ⟨i, rfl⟩
    let u := t.map g
    have hu : u.map α = t := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id t]
      exact Multiset.map_congr rfl hg
    have key := hα (fun i => u.count i) ?_ ?_
    · have hu1 : u = Finset.univ.val := Multiset.ext.2 fun i => by
        rw [key i, Multiset.count_eq_one_of_mem Finset.univ.nodup (Finset.mem_univ i)]
      rw [← hu, hu1]
    · rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
      simp [u, hcard]
    · calc ∏ i, α i ^ u.count i = (u.map α).prod := by
            rw [Finset.prod_multiset_map_count]
            exact (Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by
              rw [Multiset.count_eq_zero.2 (by simpa using hi), pow_zero])).symm
        _ = t.prod := by rw [hu]
        _ = ∏ i, α i := by rw [hprod, Finset.prod_eq_multiset_prod]
  · have h0 : (Finset.univ : Finset (Fin n)).val = 0 := by
      rw [Finset.univ_eq_empty_iff.2 (not_nonempty_iff.1 hn)]
      rfl
    rw [h0, Multiset.map_zero] at hcard ⊢
    exact Multiset.card_eq_zero.1 hcard
