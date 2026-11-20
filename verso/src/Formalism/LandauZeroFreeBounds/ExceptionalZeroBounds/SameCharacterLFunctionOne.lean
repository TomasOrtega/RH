import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

open Complex

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on_max with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Establish `hs : ∀ p ∈ s, 2 ≤ p` using `fun p hp => hS p (Finset.mem_insert_of_mem hp)`. Establish `ha2 : 2 ≤ a` using `hS a (Finset.mem_insert_self a s)`.

Establish `has : a ∉ s` using `fun h => lt_irrefl a (ha a h)`. Establish `hsub : s ⊆ Finset.Ico 2 a` using `fun p hp => Finset.mem_Ico.mpr ⟨hs p hp, ha p hp⟩`. Establish `hcard : s.card + 2 ≤ a`. Establish `h1` using `Finset.card_le_card hsub`. Rewrite `h1` using `[Nat.card_Ico]`.

Use linear arithmetic over natural numbers and integers. Establish `hc : (insert a s).card = s.card + 1` using `by simp [has]`. Rewrite using `[Finset.prod_insert has, hc]`. Use `push_cast`. Establish `ih'` using `ih hs`.

Establish `ha0 : (0 : ℝ) < a` using `by exact_mod_cast (show 0 < a by omega)`. Establish `ha' : (s.card : ℝ) + 2 ≤ a` using `by exact_mod_cast hcard`. Establish `hk : (0 : ℝ) < (s.card : ℝ) + 1` using `by positivity`. Establish `hpos : (0 : ℝ) ≤ 1 - 1 / (a : ℝ)`. Establish `h1 : (1 : ℝ) / a ≤ 1` using `by rw [div_le_one ha0]; linarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) - 1 / ((s.card : ℝ) + 1 + 1) = ((a : ℝ) - ((s.card : ℝ) + 2)) / ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2))`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : 0 ≤ ((a : ℝ) - ((s.card : ℝ) + 2)) / ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2))` using `div_nonneg (by linarith) (by positivity)`.

Establish `e3 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) ≤ (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ))` using `mul_le_mul_of_nonneg_left ih' hpos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem prod_one_sub_inv_ge_inv_card_succ (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p : ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a s)
    have has : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hsub : s ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨hs p hp, ha p hp⟩
    have hcard : s.card + 2 ≤ a := by
      have h1 := Finset.card_le_card hsub
      rw [Nat.card_Ico] at h1
      omega
    have hc : (insert a s).card = s.card + 1 := by simp [has]
    rw [Finset.prod_insert has, hc]
    push_cast
    have ih' := ih hs
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have ha' : (s.card : ℝ) + 2 ≤ a := by exact_mod_cast hcard
    have hk : (0 : ℝ) < (s.card : ℝ) + 1 := by positivity
    have hpos : (0 : ℝ) ≤ 1 - 1 / (a : ℝ) := by
      have h1 : (1 : ℝ) / a ≤ 1 := by rw [div_le_one ha0]; linarith
      linarith
    have e1 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) - 1 / ((s.card : ℝ) + 1 + 1) =
        ((a : ℝ) - ((s.card : ℝ) + 2)) / ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) := by
      field_simp
      ring
    have e2 : 0 ≤ ((a : ℝ) - ((s.card : ℝ) + 2)) /
        ((a : ℝ) * ((s.card : ℝ) + 1) * ((s.card : ℝ) + 2)) :=
      div_nonneg (by linarith) (by positivity)
    have e3 : (1 - 1 / (a : ℝ)) * (1 / ((s.card : ℝ) + 1)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left ih' hpos
    linarith

/- English proof (translation)
Use `haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩`. Use extensionality with `a`. Rewrite using `[DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd, ZMod.cast_eq_val, ZMod.cast_eq_val]`. Conclude with `h _ (ZMod.val_coe_unit_coprime a)`.
-/
theorem changeLevel_eq_of_agree_coprime {q₁ q : ℕ} [NeZero q₁] [NeZero q] (χ₁ : DirichletCharacter ℂ q₁)
    (χ : DirichletCharacter ℂ q)
    (h : ∀ n : ℕ, Nat.Coprime n (q₁ * q) → χ₁ (n : ZMod q₁) = χ (n : ZMod q)) :
    DirichletCharacter.changeLevel (dvd_mul_right q₁ q) χ₁ =
      DirichletCharacter.changeLevel (dvd_mul_left q q₁) χ := by
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  ext a
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
    ZMod.cast_eq_val, ZMod.cast_eq_val]
  exact h _ (ZMod.val_coe_unit_coprime a)

/- English proof (translation)
Rewrite using `[norm_mul]`. Break down `Nat.eq_zero_or_pos p with rfl | hp` into its components or cases. Simplify using the standard rewrite rules. Establish `h1 : ‖(p : ℂ) ^ (-(1 : ℂ))‖ = 1 / (p : ℝ)`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hp]`.

Simplify using `[Real.rpow_neg_one]`. Rewrite using `[h1]`. Conclude with `mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one φ _)`.
-/
theorem euler_factor_term_norm_le {M : ℕ} (φ : DirichletCharacter ℂ M) (p : ℕ) :
    ‖φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 / (p : ℝ) := by
  rw [norm_mul]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  · have h1 : ‖(p : ℂ) ^ (-(1 : ℂ))‖ = 1 / (p : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hp]
      simp [Real.rpow_neg_one]
    rw [h1]
    exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one φ _)

/- English proof (translation)
Rewrite using `[norm_prod]`. Use `Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_` and prove the remaining obligations. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_one]`. Combine the linear relations using `[euler_factor_term_norm_le φ p]`.
-/
theorem euler_factor_product_upper {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ) :
    ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤ ∏ p ∈ S, (1 + 1 / (p : ℝ)) := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one]
  linarith [euler_factor_term_norm_le φ p]

/- English proof (translation)
Rewrite using `[norm_prod]`. Use `Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_` and prove the remaining obligations. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hS p hp`. Establish `h1 : (1 : ℝ) / p ≤ 1` using `by rw [div_le_one (by linarith)]; linarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `euler_factor_term_norm_le φ p`. Establish `h2` using `norm_sub_norm_le (1 : ℂ) (φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))`. Rewrite `h2` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem euler_factor_product_lower {M : ℕ} (φ : DirichletCharacter ℂ M) (S : Finset ℕ)
    (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ ‖∏ p ∈ S, (1 - φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
  rw [norm_prod]
  refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  · have h1 := euler_factor_term_norm_le φ p
    have h2 := norm_sub_norm_le (1 : ℂ) (φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ)))
    rw [norm_one] at h2
    linarith

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_le_one (fun p hp => ?_) fun p hp => ?_` and prove the remaining obligations. Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hS p hp`. Establish `h1 : (1 : ℝ) / p ≤ 1` using `by rw [div_le_one (by linarith)]; linarith`. Establish `h2 : (0 : ℝ) ≤ 1 / p` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (0 : ℝ) ≤ 1 / (p : ℝ)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem prod_one_add_mul_one_sub_le_one (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∏ p ∈ S, (1 + 1 / (p : ℝ))) * ∏ p ∈ S, (1 - 1 / (p : ℝ)) ≤ 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_one (fun p hp => ?_) fun p hp => ?_
  · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hS p hp
    have h1 : (1 : ℝ) / p ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have h2 : (0 : ℝ) ≤ 1 / p := by positivity
    nlinarith
  · have h2 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
    nlinarith

/- English proof (translation)
Introduce `q₁ q _ _ χ₁ χ hχ₁ hχ h`. Use `haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩`. Establish `hS : ∀ p ∈ (q₁ * q).primeFactors, 2 ≤ p` using `fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le`. Establish `hL₁` using `DirichletCharacter.LFunction_changeLevel (dvd_mul_right q₁ q) χ₁ (s := 1) (Or.inl hχ₁)`. Establish `hL` using `DirichletCharacter.LFunction_changeLevel (dvd_mul_left q q₁) χ (s := 1) (Or.inl hχ)`.

Rewrite `hL₁` using `[changeLevel_eq_of_agree_coprime χ₁ χ h, hL]`. Establish `hnorm : ‖DirichletCharacter.LFunction χ₁ 1‖ * ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ = ‖DirichletCharacter.LFunction χ 1‖ * ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(1 : ℂ)))‖`. Rewrite using `[← norm_mul, ← norm_mul, hL₁]`. Establish `hlow` using `euler_factor_product_lower χ₁ _ hS`. Establish `hup` using `euler_factor_product_upper χ (q₁ * q).primeFactors`.

Establish `hge` using `prod_one_sub_inv_ge_inv_card_succ _ hS`. Establish `hAB` using `prod_one_add_mul_one_sub_le_one _ hS`. Establish `hk : (0 : ℝ) < ((q₁ * q).primeFactors.card : ℝ) + 1` using `by positivity`. Establish `hA0 : (0 : ℝ) ≤ ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ))` using `Finset.prod_nonneg fun p _ => by positivity`. Establish `hB' : 1 ≤ (∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) * (((q₁ * q).primeFactors.card : ℝ) + 1)`.

Establish `h1` using `mul_le_mul_of_nonneg_right hge hk.le`. Rewrite `h1` using `[one_div, inv_mul_cancel₀ hk.ne']`. Then use the resulting hypothesis. Establish `hx` using `norm_nonneg (DirichletCharacter.LFunction χ₁ 1)`. Establish `hy` using `norm_nonneg (DirichletCharacter.LFunction χ 1)`. Establish `h1 : ‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ)) ≤ ‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ))`.

Combine the equalities or inequalities in the displayed calculation. Establish `hA : ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) ≤ ((q₁ * q).primeFactors.card : ℝ) + 1` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lfunction_one_same_character : SameCharacterLFunctionOne := by
  intro q₁ q _ _ χ₁ χ hχ₁ hχ h
  haveI : NeZero (q₁ * q) := ⟨mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have hS : ∀ p ∈ (q₁ * q).primeFactors, 2 ≤ p := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le
  have hL₁ := DirichletCharacter.LFunction_changeLevel (dvd_mul_right q₁ q) χ₁ (s := 1)
    (Or.inl hχ₁)
  have hL := DirichletCharacter.LFunction_changeLevel (dvd_mul_left q q₁) χ (s := 1) (Or.inl hχ)
  rw [changeLevel_eq_of_agree_coprime χ₁ χ h, hL] at hL₁
  have hnorm : ‖DirichletCharacter.LFunction χ₁ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ =
      ‖DirichletCharacter.LFunction χ 1‖ *
      ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ (p : ZMod q) * (p : ℂ) ^ (-(1 : ℂ)))‖ := by
    rw [← norm_mul, ← norm_mul, hL₁]
  have hlow := euler_factor_product_lower χ₁ _ hS
  have hup := euler_factor_product_upper χ (q₁ * q).primeFactors
  have hge := prod_one_sub_inv_ge_inv_card_succ _ hS
  have hAB := prod_one_add_mul_one_sub_le_one _ hS
  have hk : (0 : ℝ) < ((q₁ * q).primeFactors.card : ℝ) + 1 := by positivity
  have hA0 : (0 : ℝ) ≤ ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hB' : 1 ≤ (∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
      (((q₁ * q).primeFactors.card : ℝ) + 1) := by
    have h1 := mul_le_mul_of_nonneg_right hge hk.le
    rwa [one_div, inv_mul_cancel₀ hk.ne'] at h1
  have hx := norm_nonneg (DirichletCharacter.LFunction χ₁ 1)
  have hy := norm_nonneg (DirichletCharacter.LFunction χ 1)
  have h1 : ‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ)) ≤
      ‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) := by
    calc _ ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ *
          ‖∏ p ∈ (q₁ * q).primeFactors, (1 - χ₁ (p : ZMod q₁) * (p : ℂ) ^ (-(1 : ℂ)))‖ :=
          mul_le_mul_of_nonneg_left hlow hx
      _ = _ := hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hup hy
  have hA : ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ)) ≤
      ((q₁ * q).primeFactors.card : ℝ) + 1 := by nlinarith
  calc ‖DirichletCharacter.LFunction χ₁ 1‖
        ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ * ((∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1)) := le_mul_of_one_le_right hx hB'
    _ = (‖DirichletCharacter.LFunction χ₁ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 - 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := by ring
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * ∏ p ∈ (q₁ * q).primeFactors, (1 + 1 / (p : ℝ))) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) := mul_le_mul_of_nonneg_right h1 hk.le
    _ ≤ (‖DirichletCharacter.LFunction χ 1‖ * (((q₁ * q).primeFactors.card : ℝ) + 1)) *
          (((q₁ * q).primeFactors.card : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hy) hk.le
    _ = (((q₁ * q).primeFactors.card : ℝ) + 1) ^ 2 * ‖DirichletCharacter.LFunction χ 1‖ := by ring

end Formalism.ZeroFreeDirichlet
