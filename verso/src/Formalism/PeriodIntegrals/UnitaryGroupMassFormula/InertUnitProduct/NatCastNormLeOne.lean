import Mathlib

noncomputable section

namespace PI.UnitaryGroupMassFormula.ProdUnitInert

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Introduce `h`. Establish `hmem : t ^ 2 + (d : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p` using `p)) := by`. Rewrite using `[PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]`. Conclude with `h`. Rewrite `hmem` using `[RingHom.mem_ker, map_add, map_pow, map_natCast]`.

Apply `hd` to reduce the goal to its premises. Use `⟨PadicInt.toZMod t, ?_⟩` and prove the remaining obligations. Use `push_cast`. Take the linear combination `(-1 : ZMod p) * hmem`.
-/
lemma not_small_sq_add (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (t : ℤ_[p]) :
    ¬ ‖t ^ 2 + (d : ℤ_[p])‖ < 1 := by
  intro h
  have hmem : t ^ 2 + (d : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]; exact h
  rw [RingHom.mem_ker, map_add, map_pow, map_natCast] at hmem
  apply hd
  refine ⟨PadicInt.toZMod t, ?_⟩
  push_cast
  linear_combination (-1 : ZMod p) * hmem

/- English proof (translation)
Simplify using `using Padic.norm_int_le_one (p := p) (d : ℤ)`.
-/
lemma natCast_norm_le_one (d : ℕ) : ‖(d : ℚ_[p])‖ ≤ 1 := by
  simpa using Padic.norm_int_le_one (p := p) (d : ℤ)

/- English proof (translation)
Assume the negation of the conclusion as `hY`. Use `push Not at hY`. Establish `hY0 : Y ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hY`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : (X / Y) ^ 2 + d = 1 / Y ^ 2`. Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`.

Establish `hsmall : ‖(X / Y) ^ 2 + (d : ℚ_[p])‖ < 1`. Rewrite using `[key, norm_div, norm_one, norm_pow]`. Establish `: 1 < ‖Y‖ ^ 2` using `by nlinarith`. Rewrite using `[div_lt_one (by linarith)]`. Conclude with `this`.

Establish `ht1 : ‖X / Y‖ ≤ 1`. Assume the negation of the conclusion as `ht1`. Use `push Not at ht1`. Establish `h2 : 1 < ‖(X / Y) ^ 2‖` using `by rw [norm_pow]; nlinarith`. Establish `hd1` using `natCast_norm_le_one (p := p) d`.

Establish `hne : ‖(X / Y) ^ 2‖ ≠ ‖(d : ℚ_[p])‖` using `by intro h'; linarith`. Rewrite `hsmall` using `[Padic.add_eq_max_of_ne hne]`. Use `le_max_left ‖(X / Y) ^ 2‖ ‖(d : ℚ_[p])‖` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Set `T : ℤ_[p]` to `⟨X / Y, ht1⟩`.

Apply `not_small_sq_add d hd T` to reduce the goal to its premises. Establish `hc : (((T ^ 2 + (d : ℤ_[p]) : ℤ_[p])) : ℚ_[p]) = (X / Y) ^ 2 + d`. Establish `hT : (T : ℚ_[p]) = X / Y` using `rfl`. Rewrite using `[PadicInt.coe_add, PadicInt.coe_pow, hT, PadicInt.coe_natCast]`. Rewrite using `[PadicInt.norm_def, hc]`.

Conclude with `hsmall`.
-/
lemma y_norm_le_one (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (X Y : ℚ_[p])
    (h : X ^ 2 + d * Y ^ 2 = 1) : ‖Y‖ ≤ 1 := by
  by_contra hY
  push Not at hY
  have hY0 : Y ≠ 0 := by
    rintro rfl
    simp at hY
    linarith
  have key : (X / Y) ^ 2 + d = 1 / Y ^ 2 := by
    rw [div_pow]
    field_simp
    linear_combination h
  have hsmall : ‖(X / Y) ^ 2 + (d : ℚ_[p])‖ < 1 := by
    rw [key, norm_div, norm_one, norm_pow]
    have : 1 < ‖Y‖ ^ 2 := by nlinarith
    rw [div_lt_one (by linarith)]
    exact this
  have ht1 : ‖X / Y‖ ≤ 1 := by
    by_contra ht1
    push Not at ht1
    have h2 : 1 < ‖(X / Y) ^ 2‖ := by rw [norm_pow]; nlinarith
    have hd1 := natCast_norm_le_one (p := p) d
    have hne : ‖(X / Y) ^ 2‖ ≠ ‖(d : ℚ_[p])‖ := by intro h'; linarith
    rw [Padic.add_eq_max_of_ne hne] at hsmall
    have := le_max_left ‖(X / Y) ^ 2‖ ‖(d : ℚ_[p])‖
    linarith
  let T : ℤ_[p] := ⟨X / Y, ht1⟩
  apply not_small_sq_add d hd T
  have hc : (((T ^ 2 + (d : ℤ_[p]) : ℤ_[p])) : ℚ_[p]) = (X / Y) ^ 2 + d := by
    have hT : (T : ℚ_[p]) = X / Y := rfl
    rw [PadicInt.coe_add, PadicInt.coe_pow, hT, PadicInt.coe_natCast]
  rw [PadicInt.norm_def, hc]
  exact hsmall

/- English proof (translation)
Establish `hX2 : X ^ 2 = 1 + (-(d * Y ^ 2))` using `by linear_combination h`. Establish `hd1` using `natCast_norm_le_one (p := p) d`. Establish `hle : ‖X‖ ^ 2 ≤ 1`. Rewrite using `[← norm_pow, hX2]`. Use `(Padic.nonarchimedean _ _).trans (max_le (le_of_eq norm_one) ?_)` and prove the remaining obligations.

Rewrite using `[norm_neg, norm_mul, norm_pow]`. Establish `h0 : ‖Y‖ ^ 2 ≤ 1` using `by nlinarith [norm_nonneg Y]`. Use polynomial arithmetic with `[norm_nonneg (d : ℚ_[p]), norm_nonneg Y, sq_nonneg ‖Y‖]`. Use polynomial arithmetic with `[norm_nonneg X]`.
-/
lemma x_norm_le_one (d : ℕ) (X Y : ℚ_[p]) (hY : ‖Y‖ ≤ 1)
    (h : X ^ 2 + d * Y ^ 2 = 1) : ‖X‖ ≤ 1 := by
  have hX2 : X ^ 2 = 1 + (-(d * Y ^ 2)) := by linear_combination h
  have hd1 := natCast_norm_le_one (p := p) d
  have hle : ‖X‖ ^ 2 ≤ 1 := by
    rw [← norm_pow, hX2]
    refine (Padic.nonarchimedean _ _).trans (max_le (le_of_eq norm_one) ?_)
    rw [norm_neg, norm_mul, norm_pow]
    have h0 : ‖Y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg Y]
    nlinarith [norm_nonneg (d : ℚ_[p]), norm_nonneg Y, sq_nonneg ‖Y‖]
  nlinarith [norm_nonneg X]

/- English proof (translation)
Establish `hc : (((q : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (q : ℂ_[p])`. Simplify using `only [PadicComplex.coe_eq, map_ratCast]`. Rewrite using `[← hc, PadicComplex.norm_extends, PadicAlgCl.norm_extends]`.
-/
lemma normC_ratCast (q : ℚ) : ‖(q : ℂ_[p])‖ = ‖(q : ℚ_[p])‖ := by
  have hc : (((q : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (q : ℂ_[p]) := by
    simp only [PadicComplex.coe_eq, map_ratCast]
  rw [← hc, PadicComplex.norm_extends, PadicAlgCl.norm_extends]

/- English proof (translation)
Establish `hQ : (x : ℚ_[p]) ^ 2 + d * (y : ℚ_[p]) ^ 2 = 1`. Conclude with `congrArg (fun q : ℚ => (q : ℚ_[p])) hxy` after adjusting the coercions. Establish `hy` using `y_norm_le_one d hd _ _ hQ`. Establish `hx` using `x_norm_le_one d _ _ hy hQ`. Establish `hy' : ‖(y : ℂ_[p])‖ ≤ 1` using `by rw [normC_ratCast]; exact hy`.

Establish `hx' : ‖(x : ℂ_[p])‖ ≤ 1` using `by rw [normC_ratCast]; exact hx`. Establish `hdC : ‖(d : ℂ_[p])‖ ≤ 1`. Establish `h1` using `normC_ratCast (p := p) (d : ℚ)`. Move the coercions through the operations in `at h1`. Rewrite using `[h1]`.

Conclude with `natCast_norm_le_one d`. Establish `hγ1 : ‖γ‖ ≤ 1`. Establish `h2 : ‖γ‖ ^ 2 ≤ 1` using `by rw [← norm_pow, hγ, norm_neg]; exact hdC`. Use polynomial arithmetic with `[norm_nonneg γ]`. Establish `hC : (x : ℂ_[p]) ^ 2 + d * (y : ℂ_[p]) ^ 2 = 1`.

Conclude with `congrArg (fun q : ℚ => (q : ℂ_[p])) hxy` after adjusting the coercions. Establish `hprod : ((x : ℂ_[p]) + y * γ) * ((x : ℂ_[p]) - y * γ) = 1`. Take the linear combination `hC - (y : ℂ_[p]) ^ 2 * hγ`. Establish `hyγ : ‖(y : ℂ_[p]) * γ‖ ≤ 1`. Rewrite using `[norm_mul]`.

Use polynomial arithmetic with `[norm_nonneg (y : ℂ_[p]), norm_nonneg γ]`. Establish `hA : ‖(x : ℂ_[p]) + y * γ‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hyγ)`. Establish `hB : ‖(x : ℂ_[p]) - y * γ‖ ≤ 1` using `sub_eq_add_neg (x : ℂ_[p]) (y * γ) ▸ (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' (by rwa [norm_neg]))`. Establish `hAB : ‖(x : ℂ_[p]) + y * γ‖ * ‖(x : ℂ_[p]) - y * γ‖ = 1`. Rewrite using `[← norm_mul, hprod, norm_one]`.

Use `le_antisymm hA ?_` and prove the remaining obligations. Use polynomial arithmetic with `[norm_nonneg ((x : ℂ_[p]) + y * γ), norm_nonneg ((x : ℂ_[p]) - y * γ)]`.
-/
theorem norm_conic_eq_one (d : ℕ) (hd : ¬ IsSquare (((-(d : ℤ) : ℤ) : ZMod p))) (x y : ℚ)
    (hxy : x ^ 2 + d * y ^ 2 = 1) (γ : ℂ_[p]) (hγ : γ ^ 2 = -(d : ℂ_[p])) :
    ‖(x : ℂ_[p]) + y * γ‖ = 1 := by
  have hQ : (x : ℚ_[p]) ^ 2 + d * (y : ℚ_[p]) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℚ_[p])) hxy
  have hy := y_norm_le_one d hd _ _ hQ
  have hx := x_norm_le_one d _ _ hy hQ
  have hy' : ‖(y : ℂ_[p])‖ ≤ 1 := by rw [normC_ratCast]; exact hy
  have hx' : ‖(x : ℂ_[p])‖ ≤ 1 := by rw [normC_ratCast]; exact hx
  have hdC : ‖(d : ℂ_[p])‖ ≤ 1 := by
    have h1 := normC_ratCast (p := p) (d : ℚ)
    push_cast at h1
    rw [h1]
    exact natCast_norm_le_one d
  have hγ1 : ‖γ‖ ≤ 1 := by
    have h2 : ‖γ‖ ^ 2 ≤ 1 := by rw [← norm_pow, hγ, norm_neg]; exact hdC
    nlinarith [norm_nonneg γ]
  have hC : (x : ℂ_[p]) ^ 2 + d * (y : ℂ_[p]) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℂ_[p])) hxy
  have hprod : ((x : ℂ_[p]) + y * γ) * ((x : ℂ_[p]) - y * γ) = 1 := by
    linear_combination hC - (y : ℂ_[p]) ^ 2 * hγ
  have hyγ : ‖(y : ℂ_[p]) * γ‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg (y : ℂ_[p]), norm_nonneg γ]
  have hA : ‖(x : ℂ_[p]) + y * γ‖ ≤ 1 :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hyγ)
  have hB : ‖(x : ℂ_[p]) - y * γ‖ ≤ 1 :=
    sub_eq_add_neg (x : ℂ_[p]) (y * γ) ▸
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' (by rwa [norm_neg]))
  have hAB : ‖(x : ℂ_[p]) + y * γ‖ * ‖(x : ℂ_[p]) - y * γ‖ = 1 := by
    rw [← norm_mul, hprod, norm_one]
  refine le_antisymm hA ?_
  nlinarith [norm_nonneg ((x : ℂ_[p]) + y * γ), norm_nonneg ((x : ℂ_[p]) - y * γ)]

end PI.UnitaryGroupMassFormula.ProdUnitInert
