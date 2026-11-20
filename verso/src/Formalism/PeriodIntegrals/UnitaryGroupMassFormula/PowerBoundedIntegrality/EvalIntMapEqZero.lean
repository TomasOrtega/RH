import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerBoundedIntegrality.Development

namespace PI.PowBddIntWork

open Matrix Polynomial

/- English proof (translation)
Establish `e : ψ.comp (algebraMap ℤ A) = algebraMap ℤ B` using `RingHom.ext_int _ _`. Rewrite using `[← e, ← Polynomial.hom_eval₂, h, map_zero]`.
-/
theorem eval₂_int_map_eq_zero {A B : Type*} [Ring A] [Ring B] (ψ : A →+* B) (p : ℤ[X]) (a : A)
    (h : p.eval₂ (algebraMap ℤ A) a = 0) : p.eval₂ (algebraMap ℤ B) (ψ a) = 0 := by
  have e : ψ.comp (algebraMap ℤ A) = algebraMap ℤ B := RingHom.ext_int _ _
  rw [← e, ← Polynomial.hom_eval₂, h, map_zero]

/- English proof (translation)
Introduce `E _ k γ hγ i`. Take `⟨p, hpm, hp⟩` from `hγ`. Set `F` to `AlgebraicClosure E`. Set `γ' : Matrix (Fin k) (Fin k) F` to `γ.map (algebraMap E F)`. Establish `hp' : p.eval₂ (algebraMap ℤ (Matrix (Fin k) (Fin k) F)) γ' = 0` using `eval₂_int_map_eq_zero (algebraMap E F).mapMatrix p γ hp`.

Establish `hroot : ∀ μ ∈ γ'.charpoly.roots, IsIntegral ℤ μ`. Introduce `μ hμ`. Establish `hs : μ ∈ spectrum F γ'`. Rewrite using `[Matrix.mem_spectrum_iff_isRoot_charpoly]`. Conclude with `(Polynomial.mem_roots (Matrix.charpoly_monic γ').ne_zero).1 hμ`.

Establish `h1` using `spectrum.subset_polynomial_aeval γ' (p.map (algebraMap ℤ F)) ⟨μ, hs, rfl⟩`. Establish `h2 : Polynomial.aeval γ' (p.map (algebraMap ℤ F)) = 0`. Rewrite using `[Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp']`. Rewrite `h1` using `[h2]`. Use `⟨p, hpm, ?_⟩` and prove the remaining obligations.

Establish `h3 : (p.map (algebraMap ℤ F)).eval μ = p.eval₂ (algebraMap ℤ F) μ` using `Polynomial.eval_map _ _`. Rewrite using `[← h3]`. Assume the negation of the conclusion as `hne`. Rewrite `h1` using `[spectrum.mem_iff, sub_zero]`. Conclude with `h1 ((Ne.isUnit hne).map _)`.

Establish `hcp : γ'.charpoly = γ.charpoly.map (algebraMap E F)` using `Matrix.charpoly_map γ _`. Establish `hinj : Function.Injective ((algebraMap E F).toIntAlgHom)` using `(algebraMap E F).injective`. Rewrite using `[← isIntegral_algHom_iff _ hinj]`. Use `show IsIntegral ℤ (algebraMap E F (γ.charpoly.coeff i))`. Rewrite using `[← Polynomial.coeff_map, ← hcp]`.

Establish `hq : γ'.charpoly.Monic` using `Matrix.charpoly_monic _`. Establish `hcard : Multiset.card γ'.charpoly.roots = γ'.charpoly.natDegree` using `Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)`. Distinguish the cases in `hi : i ≤ γ'.charpoly.natDegree`. Rewrite using `[Polynomial.coeff_eq_esymm_roots_of_card hcard hi, hq.leadingCoeff, one_mul]`. Use `IsIntegral.mul (IsIntegral.pow (IsIntegral.neg isIntegral_one) _) ?_` and prove the remaining obligations.

Use `show _ ∈ integralClosure ℤ F`. Unfold `Multiset.esymm`. Use `Subalgebra.multiset_sum_mem _ ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨s, hs, rfl⟩` from `Multiset.mem_map.1 hy`.

Use `Subalgebra.multiset_prod_mem _ ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `hroot x (Multiset.mem_of_le (Multiset.mem_powersetCard.1 hs).1 hx)`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]`. Conclude with `isIntegral_zero`.
-/
theorem stepB : StepB := by
  intro E _ k γ hγ i
  obtain ⟨p, hpm, hp⟩ := hγ
  let F := AlgebraicClosure E
  let γ' : Matrix (Fin k) (Fin k) F := γ.map (algebraMap E F)
  have hp' : p.eval₂ (algebraMap ℤ (Matrix (Fin k) (Fin k) F)) γ' = 0 :=
    eval₂_int_map_eq_zero (algebraMap E F).mapMatrix p γ hp

  have hroot : ∀ μ ∈ γ'.charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have hs : μ ∈ spectrum F γ' := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic γ').ne_zero).1 hμ
    have h1 := spectrum.subset_polynomial_aeval γ' (p.map (algebraMap ℤ F)) ⟨μ, hs, rfl⟩
    have h2 : Polynomial.aeval γ' (p.map (algebraMap ℤ F)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def, hp']
    rw [h2] at h1
    refine ⟨p, hpm, ?_⟩
    have h3 : (p.map (algebraMap ℤ F)).eval μ = p.eval₂ (algebraMap ℤ F) μ := Polynomial.eval_map _ _
    rw [← h3]
    by_contra hne
    rw [spectrum.mem_iff, sub_zero] at h1
    exact h1 ((Ne.isUnit hne).map _)
  have hcp : γ'.charpoly = γ.charpoly.map (algebraMap E F) := Matrix.charpoly_map γ _
  have hinj : Function.Injective ((algebraMap E F).toIntAlgHom) := (algebraMap E F).injective
  rw [← isIntegral_algHom_iff _ hinj]
  show IsIntegral ℤ (algebraMap E F (γ.charpoly.coeff i))
  rw [← Polynomial.coeff_map, ← hcp]

  have hq : γ'.charpoly.Monic := Matrix.charpoly_monic _
  have hcard : Multiset.card γ'.charpoly.roots = γ'.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits _)
  by_cases hi : i ≤ γ'.charpoly.natDegree
  · rw [Polynomial.coeff_eq_esymm_roots_of_card hcard hi, hq.leadingCoeff, one_mul]
    refine IsIntegral.mul (IsIntegral.pow (IsIntegral.neg isIntegral_one) _) ?_
    show _ ∈ integralClosure ℤ F
    unfold Multiset.esymm
    refine Subalgebra.multiset_sum_mem _ ?_
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.1 hy
    refine Subalgebra.multiset_prod_mem _ ?_
    intro x hx
    exact hroot x (Multiset.mem_of_le (Multiset.mem_powersetCard.1 hs).1 hx)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact isIntegral_zero

end PI.PowBddIntWork
