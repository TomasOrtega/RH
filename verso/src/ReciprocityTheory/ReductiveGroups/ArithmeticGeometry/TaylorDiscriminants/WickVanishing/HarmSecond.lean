import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB

/- English proof (translation)
Establish `h : ⁅(MvPolynomial.pderiv i : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)), MvPolynomial.pderiv j⁆ = (0 : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `n`. Rewrite using `[Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X, Pi.single_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `h'` using `congrArg (fun D => D p) h`. Simplify using `only [Derivation.commutator_apply, Derivation.zero_apply] at h'`. Conclude with `sub_eq_zero.mp h'`.
-/
theorem mvpoly_pderiv_comm {k σ : Type} [CommRing k] (i j : σ) (p : MvPolynomial σ k) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) = MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  have h : ⁅(MvPolynomial.pderiv i : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)), MvPolynomial.pderiv j⁆ =
      (0 : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)) := by
    apply MvPolynomial.derivation_ext
    intro n
    rw [Derivation.commutator_apply, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X, Pi.single_apply,
      Pi.single_apply]
    split_ifs <;> simp
  have h' := congrArg (fun D => D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h'
  exact sub_eq_zero.mp h'

/- English proof (translation)
Introduce `k _ T _ r cc isX hcc hX n c hc P hP`. Use `set S : (Σ τ : T, Fin (r τ)) → (Σ τ : T, Fin (r τ)) → MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k := fun l l' => ∑ b : Fin n, MvPolynomial.pderiv (l, b) (MvPolynomial.pderiv (l', b) P) with hS`. Establish `hsymm : ∀ l l', S l l' = S l' l`. Introduce `l l'`. Simplify using `only [hS]`.

Conclude with `Finset.sum_congr rfl fun b _ => mvpoly_pderiv_comm _ _ _`. Establish `hzero1 : ∀ l l' : (Σ τ : T, Fin (r τ)), isX l.1 → l'.1 = cc l.1 → S l l' = 0`. Introduce and unpack `⟨σ, i⟩ ⟨σ', i'⟩ hXσ h`. Simplify using `only at h hXσ`. Substitute `h` using the available equality.

Conclude with `hP σ hXσ i i'`. Establish `hzero : ∀ l l' : (Σ τ : T, Fin (r τ)), l'.1 = cc l.1 → S l l' = 0`. Introduce `l l' h`. Break down `hX l.1 with h1 | h1` into its components or cases. Conclude with `hzero1 l l' h1 h`.

Rewrite using `[hsymm]`. Use `hzero1 l' l (by rw [h]; exact h1) ?_` and prove the remaining obligations. Rewrite using `[h, hcc]`. Establish `hterm : ∀ l l', MvPolynomial.C (c l l') * S l l' = 0`. Introduce `l l'`.

Distinguish the cases in `h : l'.1 = cc l.1`. Rewrite using `[hzero l l' h, mul_zero]`. Rewrite using `[hc l l' h, map_zero, zero_mul]`. Unfold `secondOrder`. Repeatedly rewrite using `[Fintype.sum_prod_type]`.

Simplify using `only [apply_ite MvPolynomial.C, ite_mul, map_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[Finset.sum_comm]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `l' _`. Rewrite using `[← Finset.mul_sum]`. Conclude with `hterm l l'`.
-/
theorem harmSecond_holds : HarmSecondSt := by
  intro k _ T _ r cc isX hcc hX n c hc P hP
  classical
  set S : (Σ τ : T, Fin (r τ)) → (Σ τ : T, Fin (r τ)) → MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
    fun l l' => ∑ b : Fin n, MvPolynomial.pderiv (l, b) (MvPolynomial.pderiv (l', b) P) with hS
  have hsymm : ∀ l l', S l l' = S l' l := by
    intro l l'
    simp only [hS]
    exact Finset.sum_congr rfl fun b _ => mvpoly_pderiv_comm _ _ _
  have hzero1 : ∀ l l' : (Σ τ : T, Fin (r τ)), isX l.1 → l'.1 = cc l.1 → S l l' = 0 := by
    rintro ⟨σ, i⟩ ⟨σ', i'⟩ hXσ h
    dsimp only at h hXσ
    subst h
    exact hP σ hXσ i i'
  have hzero : ∀ l l' : (Σ τ : T, Fin (r τ)), l'.1 = cc l.1 → S l l' = 0 := by
    intro l l' h
    rcases hX l.1 with h1 | h1
    · exact hzero1 l l' h1 h
    · rw [hsymm]
      refine hzero1 l' l (by rw [h]; exact h1) ?_
      rw [h, hcc]
  have hterm : ∀ l l', MvPolynomial.C (c l l') * S l l' = 0 := by
    intro l l'
    by_cases h : l'.1 = cc l.1
    · rw [hzero l l' h, mul_zero]
    · rw [hc l l' h, map_zero, zero_mul]
  unfold secondOrder
  simp_rw [Fintype.sum_prod_type]
  simp only [apply_ite MvPolynomial.C, ite_mul, map_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  apply Finset.sum_eq_zero
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l' _
  rw [← Finset.mul_sum]
  exact hterm l l'

end ReciprocityTheory.ChartRestriction.G.TB
