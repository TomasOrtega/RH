import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components.

Establish an intermediate fact. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Stick.comb :
    ∀ (M : ℕ) [NeZero M] (A : Type) [CommGroup A] (x : (ZMod M)ˣ → A),
    (∀ k : ℕ, ∏ t : (ZMod M)ˣ, x t ^ (k * (t : ZMod M).val / M) = 1) →
    ∀ β γ : (ZMod M)ˣ → ℤ, (∀ t, (M : ℤ) * γ t = ∑ s, β s * (((s : ZMod M) * (t : ZMod M)).val : ℤ)) →
    ∏ t, x t ^ γ t = 1 := by
  intro M _ A _ x hx β γ hγ
  classical
  set F : (ZMod M)ˣ → ℤ := fun t =>
    ∑ s, β s * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ) with hF
  set B : ℤ := ∑ s, β s * ((s : ZMod M).val : ℤ) with hB
  have key : ∀ t, (M : ℤ) * (γ t + F t) = B * ((t : ZMod M).val : ℤ) := by
    intro t
    rw [mul_add, hγ t, hF, hB]
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ZMod.val_mul]
    have h0 := Nat.mod_add_div ((s : ZMod M).val * (t : ZMod M).val) M
    have h' : ((((s : ZMod M).val * (t : ZMod M).val % M : ℕ)) : ℤ)
        + (M : ℤ) * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ)
        = ((s : ZMod M).val : ℤ) * ((t : ZMod M).val : ℤ) := by exact_mod_cast h0
    linear_combination β s * h'
  have hdiv : (M : ℤ) ∣ B := by
    rcases Nat.lt_or_ge 1 M with hM | hM
    · haveI : Fact (1 < M) := ⟨hM⟩
      have h1 := key 1
      rw [Units.val_one, ZMod.val_one, Nat.cast_one, mul_one] at h1
      exact ⟨_, h1.symm⟩
    · have hM1 : M = 1 := le_antisymm hM (NeZero.pos M)
      subst hM1
      refine ⟨0, ?_⟩
      rw [hB, mul_zero]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [Nat.lt_one_iff.mp (ZMod.val_lt (s : ZMod 1))]
      simp
  obtain ⟨b, hb⟩ := hdiv
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hγ' : ∀ t, γ t = b * ((t : ZMod M).val : ℤ) - F t := by
    intro t
    have h1 := key t
    rw [hb, mul_assoc] at h1
    have h2 := mul_left_cancel₀ hM h1
    linarith
  have h1 : ∏ t, x t ^ ((t : ZMod M).val : ℤ) = 1 := by
    have h3 := hx M
    simp only [Nat.mul_div_cancel_left _ (NeZero.pos M)] at h3
    simpa only [zpow_natCast] using h3
  have h2 : ∀ s : (ZMod M)ˣ,
      ∏ t, x t ^ ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ) = 1 := by
    intro s
    simpa only [zpow_natCast] using hx (s : ZMod M).val
  have hzs : ∀ (a : A) (g : (ZMod M)ˣ → ℤ) (u : Finset (ZMod M)ˣ),
      a ^ (∑ s ∈ u, g s) = ∏ s ∈ u, a ^ g s := by
    intro a g u
    induction u using Finset.induction_on with
    | empty => simp
    | insert i u hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]
  have hFprod : ∏ t, x t ^ F t = 1 := by
    simp only [hF, hzs]
    rw [Finset.prod_comm]
    have h4 : ∀ s : (ZMod M)ˣ, ∏ t, x t ^ (β s * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ))
        = (∏ t, x t ^ ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ)) ^ β s := by
      intro s
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [← zpow_mul, mul_comm]
    simp only [h4, h2, one_zpow, Finset.prod_const_one]
  calc ∏ t, x t ^ γ t
      = ∏ t, (x t ^ ((t : ZMod M).val : ℤ)) ^ b / x t ^ F t := by
        refine Finset.prod_congr rfl fun t _ => ?_
        rw [hγ' t, zpow_sub, ← zpow_mul, mul_comm b, div_eq_mul_inv]
    _ = 1 := by
        rw [Finset.prod_div_distrib, Finset.prod_zpow, h1, hFprod]
        simp
