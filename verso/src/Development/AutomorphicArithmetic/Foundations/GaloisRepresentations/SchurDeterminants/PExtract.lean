import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PairSplit

noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

/- English proof (translation)
Introduce `K σ A M _ _ _ x hx e he w`. Use `set v : A → M → K := fun a m => ∏ p, x a p ^ e m p with hvdef`. Establish `htop : Submodule.span K (Set.range v) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ, hmap⟩` from `Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance`.

Establish `hφv : ∀ u : M → K, φ u = ∑ m, u m * φ (Pi.single m 1)`. Introduce `u`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ φ u]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul]`.

Use `congr 2`. Use extensionality with `s`. Simplify using `[Pi.single_apply, eq_comm]`. Set `E : M → σ →₀ ℕ` to `fun m => Finsupp.equivFunOnFinite.symm (e m)`. Establish `hE : Function.Injective E` using `fun a b h => he (by simpa [E] using h)`.

Set `Q : MvPolynomial σ K` to `∑ m, monomial (E m) (φ (Pi.single m 1))`. Establish `hQ : Q = 0`. Use `hx Q ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `h1 : φ (v a) = 0`.

Establish `h2` using `Submodule.mem_map_of_mem (f := φ) (Submodule.subset_span ⟨a, rfl⟩ : v a ∈ Submodule.span K (Set.range v))`. Rewrite `h2` using `[hmap, Submodule.mem_bot]`. Conclude with `h2`. Rewrite `h1` using `[hφv]`. Rewrite using `[← h1]`.

Simplify using `only [Q, map_sum, eval_monomial]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.prod_fintype _ _ (fun i => pow_zero _), mul_comm]`. Both sides reduce to the same expression. Apply `hφ` to reduce the goal to its premises.

Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Rewrite using `[hφv, LinearMap.zero_apply]`. Use `Finset.sum_eq_zero fun m _ => ?_` and prove the remaining obligations. Establish `hc` using `congrArg (coeff (E m)) hQ`. Simplify using `only [Q, coeff_sum, coeff_monomial, coeff_zero, hE.eq_iff] at hc`.

Simplify using `at hc`. Rewrite using `[hc, mul_zero]`. Establish `hw : w ∈ Submodule.span K (Set.range v)` using `by rw [htop]; exact Submodule.mem_top`. Take `⟨c, hc⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 hw`. Use `⟨c, fun m => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hc]`. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hvdef]`.
-/
theorem extract : Extract := by
  classical
  intro K σ A M _ _ _ x hx e he w
  set v : A → M → K := fun a m => ∏ p, x a p ^ e m p with hvdef
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
    have hφv : ∀ u : M → K, φ u = ∑ m, u m * φ (Pi.single m 1) := by
      intro u
      rw [LinearMap.pi_apply_eq_sum_univ φ u]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eq_mul]
      congr 2
      ext s
      simp [Pi.single_apply, eq_comm]
    let E : M → σ →₀ ℕ := fun m => Finsupp.equivFunOnFinite.symm (e m)
    have hE : Function.Injective E := fun a b h => he (by simpa [E] using h)
    let Q : MvPolynomial σ K := ∑ m, monomial (E m) (φ (Pi.single m 1))
    have hQ : Q = 0 := by
      refine hx Q ?_
      rintro _ ⟨a, rfl⟩
      have h1 : φ (v a) = 0 := by
        have h2 := Submodule.mem_map_of_mem (f := φ) (Submodule.subset_span ⟨a, rfl⟩ : v a ∈ Submodule.span K (Set.range v))
        rw [hmap, Submodule.mem_bot] at h2
        exact h2
      rw [hφv] at h1
      rw [← h1]
      simp only [Q, map_sum, eval_monomial]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), mul_comm]
      rfl
    apply hφ
    refine LinearMap.ext fun u => ?_
    rw [hφv, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    have hc := congrArg (coeff (E m)) hQ
    simp only [Q, coeff_sum, coeff_monomial, coeff_zero, hE.eq_iff] at hc
    simp at hc
    rw [hc, mul_zero]
  have hw : w ∈ Submodule.span K (Set.range v) := by rw [htop]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hw
  refine ⟨c, fun m => ?_⟩
  rw [← hc]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hvdef]

end UpperTheory.Gal.Schur
