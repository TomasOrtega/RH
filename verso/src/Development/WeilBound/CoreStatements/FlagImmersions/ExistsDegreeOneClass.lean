import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.L3

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

/- English proof (translation)
Simplify using `[permExp]`.
-/
theorem permExp_apply (σ : Ψ → Equiv.Perm (Fin N)) (x : Ψ × Fin N) :
    permExp σ x = N - 1 - ((σ x.1 x.2 : Fin N) : ℕ) := by
  simp [permExp]

/- English proof (translation)
Introduce `σ σ' h`. Use function extensionality and compare the values at `τ`. Use extensionality with `i`. Establish `h1` using `DFunLike.congr_fun h (τ, i)`. Rewrite `h1` using `[permExp_apply, permExp_apply]`.

Establish `h2` using `(σ τ i).2`. Establish `h3` using `(σ' τ i).2`. Simplify using `only at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem permExp_injective :
    Function.Injective (permExp : (Ψ → Equiv.Perm (Fin N)) → (Ψ × Fin N) →₀ ℕ) := by
  intro σ σ' h
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, i)
  rw [permExp_apply, permExp_apply] at h1
  have h2 := (σ τ i).2
  have h3 := (σ' τ i).2
  dsimp only at h1
  omega

/- English proof (translation)
Rewrite using `[Finsupp.degree_eq_sum, Fintype.sum_prod_type]`. Simplify using `only [permExp_apply, Pi.one_apply, Equiv.Perm.one_apply]`. Rewrite using `[Finset.sum_const, Finset.card_univ, smul_eq_mul, dimFl, Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id]`.
-/
theorem degree_permExp_one :
    (permExp (1 : Ψ → Equiv.Perm (Fin N))).degree = dimFl Ψ N := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [permExp_apply, Pi.one_apply, Equiv.Perm.one_apply]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, dimFl,
    Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N, Finset.sum_range_reflect (fun i => i) N,
    Finset.sum_range_id]

/- English proof (translation)
Unfold `degFl`. Rewrite using `[Finset.sum_eq_single (1 : Ψ → Equiv.Perm (Fin N))]`. Simplify using `[← mul_pow]`. Introduce `σ _ hσ`. Rewrite using `[coeff_monomial, if_neg (fun h => hσ (permExp_injective h).symm), mul_zero]`.

Simplify using the standard rewrite rules.
-/
theorem degFl_monomial_one [DecidableEq Ψ] :
    degFl (monomial (permExp (1 : Ψ → Equiv.Perm (Fin N))) ((-1 : ℝ) ^ dimFl Ψ N)) = 1 := by
  unfold degFl
  rw [Finset.sum_eq_single (1 : Ψ → Equiv.Perm (Fin N))]
  · simp [← mul_pow]
  · intro σ _ hσ
    rw [coeff_monomial, if_neg (fun h => hσ (permExp_injective h).symm), mul_zero]
  · simp

end RootFieldNumerics.L3

/- English proof (translation)
Introduce `Ψ _ _ N j τ h1 hj`. Use `⟨⟨_, isHomogeneous_monomial _ RootFieldNumerics.L3.degree_permExp_one, RootFieldNumerics.L3.degFl_monomial_one⟩, ?_⟩` and prove the remaining obligations. Set `i0 : Fin N` to `⟨j - 1, by omega⟩`. Set `i1 : Fin N` to `⟨j, hj⟩`. Set `m : (Ψ × Fin N) →₀ ℕ` to `permExp (1 : Ψ → Equiv.Perm (Fin N)) - Finsupp.single (τ, i0) 1`.

Establish `hm : Finsupp.single (τ, i0) 1 + m = permExp (1 : Ψ → Equiv.Perm (Fin N))`. Apply `add_tsub_cancel_of_le` to reduce the goal to its premises. Rewrite using `[Finsupp.single_le_iff, RootFieldNumerics.L3.permExp_apply]`. Simplify using `only [Pi.one_apply, Equiv.Perm.one_apply, i0]`. Use linear arithmetic over natural numbers and integers.

Establish `hdeg : m.degree = dimFl Ψ N - 1`. Rewrite using `[← RootFieldNumerics.L3.degree_permExp_one, ← hm, map_add, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers. Establish `h01 : i0 ≠ i1`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [i0, i1] at this`. Use linear arithmetic over natural numbers and integers. Establish `hm0 : m (τ, i0) = N - 1 - j`. Simplify using `only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, Finsupp.single_eq_same, Pi.one_apply, Equiv.Perm.one_apply, i0]`.

Use linear arithmetic over natural numbers and integers. Establish `hm1 : m (τ, i1) = N - 1 - j`. Establish `: (Finsupp.single (τ, i0) 1 : (Ψ × Fin N) →₀ ℕ) (τ, i1) = 0` using `Finsupp.single_eq_of_ne' (by simpa using h01)`. Simplify using `only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, this, Pi.one_apply, Equiv.Perm.one_apply, i1]`. Use linear arithmetic over natural numbers and integers.

Use `⟨monomial m ((-1 : ℝ) ^ dimFl Ψ N), isHomogeneous_monomial _ hdeg, ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ (RootFieldNumerics.L3.degFl_monomial_one (Ψ := Ψ) (N := N))` and prove the remaining obligations. Unfold `degFl`. Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[pkLow, Finset.sum_mul, coeff_sum, Finset.sum_eq_single i0]`. Rewrite using `[X_pow_eq_monomial, monomial_mul, one_mul, hm]`. Introduce `i hi hi0`. Rewrite using `[X_pow_eq_monomial, monomial_mul, coeff_monomial, if_neg]`.

Introduce `h`. Establish `hi1 : i ≠ i1`. Introduce `h'`. Rewrite `hi` using `[Finset.mem_filter, h']`. Simplify using `[i1] at hi`.

Establish `e0` using `DFunLike.congr_fun h (τ, i0)`. Establish `e1` using `DFunLike.congr_fun h (τ, i1)`. Rewrite `e0` using `[Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi0), hm0, RootFieldNumerics.L3.permExp_apply]`. Rewrite `e1` using `[Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi1), hm1, RootFieldNumerics.L3.permExp_apply]`. Simplify using `only at e0 e1`.

Establish `h2` using `(σ τ i0).2`. Establish `h3` using `(σ τ i1).2`. Conclude with `h01 ((σ τ).injective (Fin.ext (by omega)))`. Introduce `h`. Conclude with `absurd (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, i0]; omega) h`.
-/
theorem RootFieldNumerics.exists_degree_one_class : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ), 1 ≤ j → j < N → (∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N) ∧ degFl Q = 1) ∧ ∃ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N - 1) ∧ degFl (pkLow j τ 1 * Q) = 1 := by
  intro Ψ _ _ N j τ h1 hj
  refine ⟨⟨_, isHomogeneous_monomial _ RootFieldNumerics.L3.degree_permExp_one, RootFieldNumerics.L3.degFl_monomial_one⟩, ?_⟩
  let i0 : Fin N := ⟨j - 1, by omega⟩
  let i1 : Fin N := ⟨j, hj⟩
  let m : (Ψ × Fin N) →₀ ℕ := permExp (1 : Ψ → Equiv.Perm (Fin N)) - Finsupp.single (τ, i0) 1
  have hm : Finsupp.single (τ, i0) 1 + m = permExp (1 : Ψ → Equiv.Perm (Fin N)) := by
    apply add_tsub_cancel_of_le
    rw [Finsupp.single_le_iff, RootFieldNumerics.L3.permExp_apply]
    simp only [Pi.one_apply, Equiv.Perm.one_apply, i0]
    omega
  have hdeg : m.degree = dimFl Ψ N - 1 := by
    rw [← RootFieldNumerics.L3.degree_permExp_one, ← hm, map_add, Finsupp.degree_single]
    omega
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp only [i0, i1] at this
    omega
  have hm0 : m (τ, i0) = N - 1 - j := by
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, Finsupp.single_eq_same, Pi.one_apply,
      Equiv.Perm.one_apply, i0]
    omega
  have hm1 : m (τ, i1) = N - 1 - j := by
    have : (Finsupp.single (τ, i0) 1 : (Ψ × Fin N) →₀ ℕ) (τ, i1) = 0 :=
      Finsupp.single_eq_of_ne' (by simpa using h01)
    simp only [m, Finsupp.tsub_apply, RootFieldNumerics.L3.permExp_apply, this, Pi.one_apply,
      Equiv.Perm.one_apply, i1]
    omega
  refine ⟨monomial m ((-1 : ℝ) ^ dimFl Ψ N), isHomogeneous_monomial _ hdeg, ?_⟩
  refine Eq.trans ?_ (RootFieldNumerics.L3.degFl_monomial_one (Ψ := Ψ) (N := N))
  unfold degFl
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  rw [pkLow, Finset.sum_mul, coeff_sum, Finset.sum_eq_single i0]
  · rw [X_pow_eq_monomial, monomial_mul, one_mul, hm]
  · intro i hi hi0
    rw [X_pow_eq_monomial, monomial_mul, coeff_monomial, if_neg]
    intro h
    have hi1 : i ≠ i1 := by
      intro h'
      rw [Finset.mem_filter, h'] at hi
      simp [i1] at hi
    have e0 := DFunLike.congr_fun h (τ, i0)
    have e1 := DFunLike.congr_fun h (τ, i1)
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi0), hm0,
      RootFieldNumerics.L3.permExp_apply] at e0
    rw [Finsupp.add_apply, Finsupp.single_eq_of_ne' (by simpa using hi1), hm1,
      RootFieldNumerics.L3.permExp_apply] at e1
    dsimp only at e0 e1
    have h2 := (σ τ i0).2
    have h3 := (σ τ i1).2
    exact h01 ((σ τ).injective (Fin.ext (by omega)))
  · intro h
    exact absurd (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, i0]; omega) h
