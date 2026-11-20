import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Coinv

noncomputable section

/- English proof (translation)
Introduce `K _ _ β ι _ _ _ _ o H hH`. Set `ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι)` to `(Fintype.equivFin β).prodCongr o`. Establish `hR : (rename ψ H).IsHomogeneous (coinvTop (Fintype.card β) (Fintype.card ι))` using `hH.rename_isHomogeneous`. Take `⟨c, hc⟩` from `h1 K _ _ (rename ψ H) hR`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Use `set I : Ideal (MvPolynomial (β × ι) K) := Ideal.span {P | ∃ (m : ℕ) (b : β), 1 ≤ m ∧ m ≤ Fintype.card ι ∧ P = ∑ i : ι, X (b, i) ^ m} with hI`. Establish `hle : psumIdeal K (Fintype.card β) (Fintype.card ι) ≤ I.comap (rename ψ.symm : MvPolynomial _ K →ₐ[K] MvPolynomial (β × ι) K)`. Use `Ideal.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `P ⟨m, b, hm1, hm2, rfl⟩`. Use `Ideal.subset_span ⟨m, (Fintype.equivFin β).symm b, hm1, hm2, ?_⟩` and prove the remaining obligations.

Simplify using `only [bps, map_sum, map_pow, rename_X]`. Use `Fintype.sum_equiv o.symm _ _ (fun i => ?_)` and prove the remaining obligations. Simplify using `[ψ]`. Establish `hH' : rename ψ.symm (rename ψ H) = H`. Rewrite using `[rename_rename]`.

Simplify using the standard rewrite rules. Establish `hst : rename ψ.symm (monomial (staircase (Fintype.card β) (Fintype.card ι)) (1 : K)) = ∏ b : β, ∏ i : ι, X (b, i) ^ (o i : ℕ)`. Rewrite using `[monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Simplify using `only [map_one, one_mul, map_prod, map_pow, rename_X]`. Rewrite using `[← Fintype.prod_prod_type']`.

Use `Fintype.prod_equiv ψ.symm _ _ (fun v => ?_)` and prove the remaining obligations. Simplify using `[staircase, ψ, Prod.map]`. Establish `key` using `hle hc`. Rewrite `key` using `[Ideal.mem_comap, map_sub, map_mul, algHom_C, hH', hst]`. Simplify using `using key`.
-/
theorem CoinvAtTopGeneral.proof (h1 : CoinvAtTop.Statement) : CoinvAtTopGeneral.Statement := by
  intro K _ _ β ι _ _ _ _ o H hH
  let ψ : β × ι ≃ Fin (Fintype.card β) × Fin (Fintype.card ι) :=
    (Fintype.equivFin β).prodCongr o
  have hR : (rename ψ H).IsHomogeneous (coinvTop (Fintype.card β) (Fintype.card ι)) :=
    hH.rename_isHomogeneous
  obtain ⟨c, hc⟩ := h1 K _ _ (rename ψ H) hR
  refine ⟨c, ?_⟩
  set I : Ideal (MvPolynomial (β × ι) K) := Ideal.span {P | ∃ (m : ℕ) (b : β), 1 ≤ m ∧
    m ≤ Fintype.card ι ∧ P = ∑ i : ι, X (b, i) ^ m} with hI
  have hle : psumIdeal K (Fintype.card β) (Fintype.card ι) ≤
      I.comap (rename ψ.symm : MvPolynomial _ K →ₐ[K] MvPolynomial (β × ι) K) := by
    refine Ideal.span_le.mpr ?_
    rintro P ⟨m, b, hm1, hm2, rfl⟩
    refine Ideal.subset_span ⟨m, (Fintype.equivFin β).symm b, hm1, hm2, ?_⟩
    simp only [bps, map_sum, map_pow, rename_X]
    refine Fintype.sum_equiv o.symm _ _ (fun i => ?_)
    simp [ψ]
  have hH' : rename ψ.symm (rename ψ H) = H := by
    rw [rename_rename]
    simp
  have hst : rename ψ.symm (monomial (staircase (Fintype.card β) (Fintype.card ι)) (1 : K)) =
      ∏ b : β, ∏ i : ι, X (b, i) ^ (o i : ℕ) := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp only [map_one, one_mul, map_prod, map_pow, rename_X]
    rw [← Fintype.prod_prod_type']
    refine Fintype.prod_equiv ψ.symm _ _ (fun v => ?_)
    simp [staircase, ψ, Prod.map]
  have key := hle hc
  rw [Ideal.mem_comap, map_sub, map_mul, algHom_C, hH', hst] at key
  simpa using key

end

end GroundTheory.Heights₂.Heights.RestTerms
