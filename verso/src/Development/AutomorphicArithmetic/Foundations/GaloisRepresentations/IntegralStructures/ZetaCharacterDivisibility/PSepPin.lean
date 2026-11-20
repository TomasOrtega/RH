import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open Polynomial

namespace UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `k _ a M Q hQm hQd hQ hsep`. Establish `key : M.charpoly ∣ Q`. Rewrite using `[← Polynomial.map_dvd_map (algebraMap k (AlgebraicClosure k)) (algebraMap k (AlgebraicClosure k)).injective M.charpoly_monic]`. Rewrite using `[← M.charpoly_map]`. Establish `hQ' : aeval (M.map (algebraMap k (AlgebraicClosure k))) Q = 0`.

Establish `e : M.map (algebraMap k (AlgebraicClosure k)) = (Algebra.ofId k (AlgebraicClosure k)).mapMatrix M` using `rfl`. Rewrite using `[e, Polynomial.aeval_algHom_apply, hQ, map_zero]`. Establish `hf : aeval (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k)))) Q = 0`. Establish `e : Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k))) = Matrix.toLinAlgEquiv' (M.map (algebraMap k (AlgebraicClosure k)))` using `rfl`. Rewrite using `[e, ← Polynomial.aeval_map_algebraMap (AlgebraicClosure k), Polynomial.aeval_algHom_apply, Polynomial.aeval_map_algebraMap, hQ', map_zero]`.

Establish `hmon` using `(M.map (algebraMap k (AlgebraicClosure k))).charpoly_monic`. Use `dvd_trans ?_ (prod_multiset_X_sub_C_dvd (Q.map (algebraMap k (AlgebraicClosure k))))` and prove the remaining obligations. Rewrite using `[(IsAlgClosed.splits (M.map (algebraMap k (AlgebraicClosure k))).charpoly).eq_prod_roots_of_monic hmon]`. Apply `Multiset.prod_dvd_prod_of_le` to reduce the goal to its premises. Apply `Multiset.map_le_map` to reduce the goal to its premises.

Establish `hnd : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.roots.Nodup`. Rewrite using `[M.charpoly_map]`. Conclude with `nodup_roots hsep.map`. Rewrite using `[Multiset.le_iff_subset hnd]`. Introduce `μ hμ`.

Establish `hroot : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.IsRoot μ` using `(mem_roots hmon.ne_zero).mp hμ`. Rewrite `hroot` using `[← Matrix.charpoly_toLin']`. Establish `he` using `(Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot`. Take `⟨v, hv⟩` from `he.exists_hasEigenvector`. Establish `hv'` using `Module.End.aeval_apply_of_hasEigenvector (p := Q.map (algebraMap k (AlgebraicClosure k))) hv`.

Rewrite `hv'` using `[Polynomial.aeval_map_algebraMap, hf, LinearMap.zero_apply]`. Establish `h0 : (Q.map (algebraMap k (AlgebraicClosure k))).eval μ = 0` using `(smul_eq_zero.mp hv'.symm).resolve_right hv.2`. Rewrite using `[mem_roots (Polynomial.map_monic_ne_zero hQm)]`. Conclude with `h0`. Conclude with `(eq_of_monic_of_dvd_of_natDegree_le M.charpoly_monic hQm key (by rw [hQd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])).symm`.
-/
theorem sepPin_of : SepPin := by
  intro k _ a M Q hQm hQd hQ hsep
  have key : M.charpoly ∣ Q := by
    rw [← Polynomial.map_dvd_map (algebraMap k (AlgebraicClosure k))
      (algebraMap k (AlgebraicClosure k)).injective M.charpoly_monic]
    rw [← M.charpoly_map]
    have hQ' : aeval (M.map (algebraMap k (AlgebraicClosure k))) Q = 0 := by
      have e : M.map (algebraMap k (AlgebraicClosure k)) =
          (Algebra.ofId k (AlgebraicClosure k)).mapMatrix M := rfl
      rw [e, Polynomial.aeval_algHom_apply, hQ, map_zero]
    have hf : aeval (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k)))) Q = 0 := by
      have e : Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k))) =
          Matrix.toLinAlgEquiv' (M.map (algebraMap k (AlgebraicClosure k))) := rfl
      rw [e, ← Polynomial.aeval_map_algebraMap (AlgebraicClosure k), Polynomial.aeval_algHom_apply,
        Polynomial.aeval_map_algebraMap, hQ', map_zero]
    have hmon := (M.map (algebraMap k (AlgebraicClosure k))).charpoly_monic
    refine dvd_trans ?_ (prod_multiset_X_sub_C_dvd (Q.map (algebraMap k (AlgebraicClosure k))))
    rw [(IsAlgClosed.splits (M.map (algebraMap k (AlgebraicClosure k))).charpoly).eq_prod_roots_of_monic hmon]
    apply Multiset.prod_dvd_prod_of_le
    apply Multiset.map_le_map
    have hnd : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.roots.Nodup := by
      rw [M.charpoly_map]
      exact nodup_roots hsep.map
    rw [Multiset.le_iff_subset hnd]
    intro μ hμ
    have hroot : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.IsRoot μ :=
      (mem_roots hmon.ne_zero).mp hμ
    rw [← Matrix.charpoly_toLin'] at hroot
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hv' := Module.End.aeval_apply_of_hasEigenvector (p := Q.map (algebraMap k (AlgebraicClosure k))) hv
    rw [Polynomial.aeval_map_algebraMap, hf, LinearMap.zero_apply] at hv'
    have h0 : (Q.map (algebraMap k (AlgebraicClosure k))).eval μ = 0 :=
      (smul_eq_zero.mp hv'.symm).resolve_right hv.2
    rw [mem_roots (Polynomial.map_monic_ne_zero hQm)]
    exact h0
  exact (eq_of_monic_of_dvd_of_natDegree_le M.charpoly_monic hQm key
    (by rw [hQd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])).symm

end UpperTheory.Gal.Int.Div
