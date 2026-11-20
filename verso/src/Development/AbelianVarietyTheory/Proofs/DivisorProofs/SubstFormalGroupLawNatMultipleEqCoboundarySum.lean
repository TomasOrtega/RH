import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.NmulSubst

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem subst_zero_fun {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (g : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) g = C (constantCoeff g) := by
  have ha : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, finsum_eq_single _ 0]
  · classical
    rw [Finsupp.prod_zero_index, coeff_one, coeff_C, coeff_zero_eq_constantCoeff_apply]
    split_ifs <;> simp
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hc
      exact hx (Finsupp.ext hc)
    have : (x.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0 :=
      Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.2 hi) (zero_pow hi)
    rw [this, map_zero, smul_zero]

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (k : ℕ) : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  exact Function.iterate_succ_apply' _ _ _

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

end GlobalTheory.QLog.NmulSubst

open GlobalTheory.QLog.NmulSubst in

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Substitute using the available equality. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem GlobalTheory.QLog.subst_nmul_eq (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  induction n with
  | zero =>
    have : nmul μ 0 = fun _ => 0 := rfl
    rw [this, subst_zero_fun]
    simp
  | succ k ih =>
    have hE : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ k j
      · exact constantCoeff_X _
    have hsE := hasSubst_of_constantCoeff_zero hE
    have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
    have hX : ∀ (f : Fin d → Fin d ⊕ Fin d),
        HasSubst (fun i => (X (f i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
      fun _ => hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [nmul_succ]
    change subst (fun i => subst (Sum.elim (nmul μ k) fun i => X i) (μ i)) g = _
    rw [← subst_comp_subst_apply hμs hsE]
    have hsplit : subst μ g = cob1 μ g + inL g + inR g := by unfold cob1; abel
    have hL : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inL g) =
        subst (nmul μ k) g := by
      unfold inL
      rw [subst_comp_subst_apply (hX Sum.inl) hsE]
      congr 1
      funext i
      rw [subst_X hsE]
      rfl
    have hR : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inR g) = g := by
      unfold inR
      rw [subst_comp_subst_apply (hX Sum.inr) hsE]
      have : (fun i => subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R))
          (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) = X := by
        funext i
        rw [subst_X hsE]
        rfl
      rw [this, subst_self]
      rfl
    rw [hsplit, subst_add hsE, subst_add hsE, hL, hR, ih, Finset.sum_range_succ]
    change _ = _ + _ + (_ + subst (Sum.elim (nmul μ k) fun i => X i) (cob1 μ g))
    push_cast
    rw [add_smul, one_smul]
    abel
