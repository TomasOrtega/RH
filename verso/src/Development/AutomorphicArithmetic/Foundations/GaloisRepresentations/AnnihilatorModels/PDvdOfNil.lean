import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PhiKOfNil

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `K W _ _ _ _ _ M s u hu hnil`. Take `⟨n, hn⟩` from `hnil`. Establish `hroot : ∀ r ∈ (LinearMap.charpoly M).roots, r ∈ s`. Introduce `r hr`. Establish `hev : M.HasEigenvalue r` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly M r).2 ((Polynomial.mem_roots (LinearMap.charpoly_monic M).ne_zero).1 hr)`.

Take `⟨v, hv⟩` from `hev.exists_hasEigenvector`. Establish `h1` using `Module.End.aeval_apply_of_hasEigenvector (p := (Polynomial.C u * rootPol s) ^ n) hv`. Rewrite `h1` using `[map_pow, hn, LinearMap.zero_apply]`. Establish `h2 : ((Polynomial.C u * rootPol s) ^ n).eval r = 0` using `(smul_eq_zero.1 h1.symm).resolve_right hv.2`. Rewrite `h2` using `[Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C]`.

Establish `h3 : (rootPol s).eval r = 0` using `(mul_eq_zero.1 (pow_eq_zero_iff'.1 h2).1).resolve_left hu`. Unfold `rootPol at h3`. Rewrite `h3` using `[Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map]`. Take `⟨a, ha, hra⟩` from `Multiset.mem_map.1 h3`. Simplify using `only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hra`.

Rewrite using `[sub_eq_zero.1 hra]`. Conclude with `ha`. Use `set m := (LinearMap.charpoly M).roots.card with hm`. Use `⟨m, ?_⟩` and prove the remaining obligations. Establish `hcp : ((LinearMap.charpoly M).roots.map fun a => Polynomial.X - Polynomial.C a).prod = LinearMap.charpoly M` using `Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic M) IsAlgClosed.card_roots_eq_natDegree`.

Establish `hpow : rootPol s ^ m = ((m • s).map fun a => Polynomial.X - Polynomial.C a).prod`. Unfold `rootPol`. Rewrite using `[Multiset.map_nsmul, Multiset.prod_nsmul]`. Rewrite using `[← hcp, hpow]`. Apply `Multiset.prod_dvd_prod_of_le` to reduce the goal to its premises.

Apply `Multiset.map_le_map` to reduce the goal to its premises. Rewrite using `[Multiset.le_iff_count]`. Introduce `a`. Rewrite using `[Multiset.count_nsmul]`. Distinguish the cases in `ha : a ∈ (LinearMap.charpoly M).roots`.

Establish `hs : 1 ≤ s.count a` using `Multiset.one_le_count_iff_mem.2 (hroot a ha)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Multiset.count_eq_zero.2 ha]`. Conclude with `Nat.zero_le _`.
-/
theorem UpperTheory.Gal.crystallineComparison.dvdOfNil_of :
    DvdOfNil := by
  classical
  intro K W _ _ _ _ _ M s u hu hnil
  obtain ⟨n, hn⟩ := hnil
  have hroot : ∀ r ∈ (LinearMap.charpoly M).roots, r ∈ s := by
    intro r hr
    have hev : M.HasEigenvalue r := (Module.End.hasEigenvalue_iff_isRoot_charpoly M r).2
      ((Polynomial.mem_roots (LinearMap.charpoly_monic M).ne_zero).1 hr)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector
      (p := (Polynomial.C u * rootPol s) ^ n) hv
    rw [map_pow, hn, LinearMap.zero_apply] at h1
    have h2 : ((Polynomial.C u * rootPol s) ^ n).eval r = 0 :=
      (smul_eq_zero.1 h1.symm).resolve_right hv.2
    rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C] at h2
    have h3 : (rootPol s).eval r = 0 :=
      (mul_eq_zero.1 (pow_eq_zero_iff'.1 h2).1).resolve_left hu
    unfold rootPol at h3
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at h3
    obtain ⟨a, ha, hra⟩ := Multiset.mem_map.1 h3
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hra
    rw [sub_eq_zero.1 hra]
    exact ha
  set m := (LinearMap.charpoly M).roots.card with hm
  refine ⟨m, ?_⟩
  have hcp : ((LinearMap.charpoly M).roots.map fun a => Polynomial.X - Polynomial.C a).prod
      = LinearMap.charpoly M :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic M)
      IsAlgClosed.card_roots_eq_natDegree
  have hpow : rootPol s ^ m = ((m • s).map fun a => Polynomial.X - Polynomial.C a).prod := by
    unfold rootPol
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
  rw [← hcp, hpow]
  apply Multiset.prod_dvd_prod_of_le
  apply Multiset.map_le_map
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul]
  by_cases ha : a ∈ (LinearMap.charpoly M).roots
  · have hs : 1 ≤ s.count a := Multiset.one_le_count_iff_mem.2 (hroot a ha)
    calc (LinearMap.charpoly M).roots.count a ≤ m := Multiset.count_le_card _ _
      _ = m * 1 := (mul_one m).symm
      _ ≤ m * s.count a := Nat.mul_le_mul_left m hs
  · rw [Multiset.count_eq_zero.2 ha]
    exact Nat.zero_le _
