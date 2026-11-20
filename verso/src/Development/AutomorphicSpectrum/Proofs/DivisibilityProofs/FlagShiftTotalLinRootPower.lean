import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LinPow

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Unfold `degFl`. Repeatedly rewrite using `[coeff_C_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun σ _ => by ring`.
-/
theorem degFl_C_mul (c : ℝ) (F : RP Ψ N) : degFl (C c * F) = c * degFl F := by
  unfold degFl
  simp_rw [coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

/- English proof (translation)
Simplify using `[linRoot, pderiv_X, Pi.single_apply]`.
-/
theorem pderiv_linRoot (u : Wt Ψ N) (τ : Ψ) (i : Fin N) :
    pderiv (τ, i) (linRoot u) = -C (u τ i) := by
  simp [linRoot, pderiv_X, Pi.single_apply]

/- English proof (translation)
Rewrite using `[Derivation.leibniz_pow, pderiv_linRoot]`. Simplify using `only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]`. Simplify using `only [map_neg, map_mul, map_add, map_natCast, map_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pderiv_linRoot_pow (u : Wt Ψ N) (τ : Ψ) (i : Fin N) (D : ℕ) :
    pderiv (τ, i) (linRoot u ^ (D + 1)) =
      C (-(((D : ℝ) + 1) * u τ i)) * linRoot u ^ D := by
  rw [Derivation.leibniz_pow, pderiv_linRoot]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
  simp only [map_neg, map_mul, map_add, map_natCast, map_one]
  push_cast
  ring

/- English proof (translation)
Unfold `degFl`. Repeatedly rewrite using `[coeff_sum, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
private lemma degFl_sum' {ι : Type*} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  unfold degFl
  simp_rw [coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[degFl_sum']`. Repeatedly rewrite using `[pderiv_linRoot_pow, degFl_C_mul]`. Simplify using `only [flagDeg]`. Rewrite using `[Finset.mul_sum, ← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem degFl_sum_pderiv (u : Wt Ψ N) (τ : Ψ) (s : Finset (Fin N)) :
    degFl (∑ i ∈ s, pderiv (τ, i) (linRoot u ^ (dimFl Ψ N + 1))) =
      -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ s, u τ i) := by
  rw [degFl_sum']
  simp_rw [pderiv_linRoot_pow, degFl_C_mul]
  simp only [flagDeg]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.Ar.Top.LinPow

/- English proof (translation)
Introduce `Ψ _ _ N j τ u`. Conclude with `⟨GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ _, GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ Finset.univ⟩`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ) (u : Wt Ψ N), Sh j τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i) ∧ Tot τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i, u τ i) := by
  intro Ψ _ _ N j τ u
  exact ⟨GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ _,
    GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ Finset.univ⟩
