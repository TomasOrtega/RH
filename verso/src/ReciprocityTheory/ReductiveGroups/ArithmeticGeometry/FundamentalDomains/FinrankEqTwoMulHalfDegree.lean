import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicOutsideLine

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hf : fdeg E = Module.finrank ℚ E / 2` using `rfl`. Rewrite using `[hf, NumberField.IsTotallyComplex.finrank (K := E), Nat.mul_div_cancel_left _ two_pos]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_eq_two_mul_half_degree : (Module.finrank ℚ E : ℝ) = 2 * (fdeg E : ℝ) := by
  have hf : fdeg E = Module.finrank ℚ E / 2 := rfl
  rw [hf, NumberField.IsTotallyComplex.finrank (K := E), Nat.mul_div_cancel_left _ two_pos]
  push_cast
  ring

/- English proof (translation)
Establish `h0 : 0 < Module.finrank ℚ E` using `Module.finrank_pos`. Establish `h0' : (0 : ℝ) < Module.finrank ℚ E` using `by exact_mod_cast h0`. Establish `hr : (0 : ℝ) < fdeg E`. Use `finrank_eq_two_mul_half_degree (E := E)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hn : 0 < fdeg E` using `by exact_mod_cast hr`. Conclude with `Nat.succ_le_of_lt hn` after adjusting the coercions.
-/
theorem one_le_field_half_degree : 1 ≤ (fdeg E : ℝ) := by
  have h0 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have h0' : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast h0
  have hr : (0 : ℝ) < fdeg E := by
    have := finrank_eq_two_mul_half_degree (E := E)
    linarith
  have hn : 0 < fdeg E := by exact_mod_cast hr
  exact_mod_cast Nat.succ_le_of_lt hn

/- English proof (translation)
Unfold `dE`. Conclude with `abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (K := E))`.
-/
theorem field_discr_constant_pos : 0 < dE E := by
  unfold dE
  exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero (K := E))

/- English proof (translation)
Unfold `rdE`. Rewrite using `[finrank_eq_two_mul_half_degree]`.
-/
theorem rootDiscriminant_eq_rpow : rdE E = dE E ^ (1 / (2 * (fdeg E : ℝ))) := by
  unfold rdE
  rw [finrank_eq_two_mul_half_degree]

namespace Data

variable {r : ℕ} (X : Data E r)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem orthogonal_component_apply (z : Frame X.Ψ r) (ξ x : Fin r → E) (τ : X.Ψ) :
    X.ucomp z ξ (X.embV x) τ = Data.emb τ.1 x -
      (X.Hf z τ (Data.emb τ.1 x) (Data.emb τ.1 ξ) / X.Hf z τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
        Data.emb τ.1 ξ := rfl

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[orthogonal_component_apply]`. Take `⟨c, hb⟩ : ∃ c : ℂ, ∀ b, τ.1 (x b) = c * τ.1 (ξ b)` from `⟨_, fun b => by`. Establish `hb` using `congrFun h b`. Simplify using `only [Data.emb, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb`.

Conclude with `sub_eq_zero.mp hb⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `hξ (funext hcon)`.

Establish `hτa : τ.1 (ξ a) ≠ 0` using `(map_ne_zero τ.1).mpr ha`. Apply `hx (x a / ξ a)` to reduce the goal to its premises. Use function extensionality and compare the values at `b`. Apply `τ.1.injective` to reduce the goal to its premises. Rewrite using `[Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hb a, hb b]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem orthogonal_component_ne_zero (z : Frame X.Ψ r) {ξ x : Fin r → E} (hξ : ξ ≠ 0) (hx : ∀ e : E, x ≠ e • ξ)
    (τ : X.Ψ) : X.ucomp z ξ (X.embV x) τ ≠ 0 := by
  intro h
  rw [orthogonal_component_apply] at h

  obtain ⟨c, hb⟩ : ∃ c : ℂ, ∀ b, τ.1 (x b) = c * τ.1 (ξ b) := ⟨_, fun b => by
    have hb := congrFun h b
    simp only [Data.emb, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
    exact sub_eq_zero.mp hb⟩
  obtain ⟨a, ha⟩ : ∃ a, ξ a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hξ (funext hcon)
  have hτa : τ.1 (ξ a) ≠ 0 := (map_ne_zero τ.1).mpr ha

  apply hx (x a / ξ a)
  funext b
  apply τ.1.injective
  rw [Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hb a, hb b]
  field_simp

end Data

end

end ReciprocityTheory.ChartRestriction.G.FD
