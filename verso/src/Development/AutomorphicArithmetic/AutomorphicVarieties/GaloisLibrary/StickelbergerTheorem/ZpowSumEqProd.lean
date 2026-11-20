import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.StickelbergerTheorem.StickelbergerAt

open NumberField IsDedekindDomain UpperTheory.V.Kum UpperTheory.V.Stick
open scoped nonZeroDivisors

/- English proof (translation)
Introduce `M _ A _ x hx β γ hγ`. Use `set F : (ZMod M)ˣ → ℤ := fun t => ∑ s, β s * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ) with hF`. Use `set B : ℤ := ∑ s, β s * ((s : ZMod M).val : ℤ) with hB`. Establish `key : ∀ t, (M : ℤ) * (γ t + F t) = B * ((t : ZMod M).val : ℤ)`. Introduce `t`.

Rewrite using `[mul_add, hγ t, hF, hB]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[ZMod.val_mul]`. Establish `h0` using `Nat.mod_add_div ((s : ZMod M).val * (t : ZMod M).val) M`.

Establish `h' : ((((s : ZMod M).val * (t : ZMod M).val % M : ℕ)) : ℤ) + (M : ℤ) * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ) = ((s : ZMod M).val : ℤ) * ((t : ZMod M).val : ℤ)` using `by exact_mod_cast h0`. Take the linear combination `β s * h'`. Establish `hdiv : (M : ℤ) ∣ B`. Break down `Nat.lt_or_ge 1 M with hM | hM` into its components or cases. Use `haveI : Fact (1 < M) := ⟨hM⟩`.

Establish `h1` using `key 1`. Rewrite `h1` using `[Units.val_one, ZMod.val_one, Nat.cast_one, mul_one]`. Conclude with `⟨_, h1.symm⟩`. Establish `hM1 : M = 1` using `le_antisymm hM (NeZero.pos M)`. Substitute `hM1` using the available equality.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[hB, mul_zero]`. Use `Finset.sum_eq_zero fun s _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.lt_one_iff.mp (ZMod.val_lt (s : ZMod 1))]`. Simplify using the standard rewrite rules.

Take `⟨b, hb⟩` from `hdiv`. Establish `hM : (M : ℤ) ≠ 0` using `by exact_mod_cast NeZero.ne M`. Establish `hγ' : ∀ t, γ t = b * ((t : ZMod M).val : ℤ) - F t`. Introduce `t`. Establish `h1` using `key t`.

Rewrite `h1` using `[hb, mul_assoc]`. Establish `h2` using `mul_left_cancel₀ hM h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ∏ t, x t ^ ((t : ZMod M).val : ℤ) = 1`. Establish `h3` using `hx M`.

Simplify using `only [Nat.mul_div_cancel_left _ (NeZero.pos M)] at h3`. Simplify `h3` using `only [zpow_natCast]`. Establish `h2 : ∀ s : (ZMod M)ˣ, ∏ t, x t ^ ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ) = 1`. Introduce `s`. Simplify `hx (s : ZMod M).val` using `only [zpow_natCast]`.

Establish `hzs : ∀ (a : A) (g : (ZMod M)ˣ → ℤ) (u : Finset (ZMod M)ˣ), a ^ (∑ s ∈ u, g s) = ∏ s ∈ u, a ^ g s`. Introduce `a g u`. Proceed by induction on `u using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i u hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]`.

Establish `hFprod : ∏ t, x t ^ F t = 1`. Simplify using `only [hF, hzs]`. Rewrite using `[Finset.prod_comm]`. Establish `h4 : ∀ s : (ZMod M)ˣ, ∏ t, x t ^ (β s * ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ)) = (∏ t, x t ^ ((((s : ZMod M).val * (t : ZMod M).val / M : ℕ)) : ℤ)) ^ β s`. Introduce `s`.

Rewrite using `[← Finset.prod_zpow]`. Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_mul, mul_comm]`. Simplify using `only [h4, h2, one_zpow, Finset.prod_const_one]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.prod_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hγ' t, zpow_sub, ← zpow_mul, mul_comm b, div_eq_mul_inv]`. Use `_ = 1 := by`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_zpow, h1, hFprod]`. Simplify using the standard rewrite rules.
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
