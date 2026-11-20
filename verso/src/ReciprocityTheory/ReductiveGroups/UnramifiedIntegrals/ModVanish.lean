import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModHnf

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Unfold `fac`. Establish `h1 : AA τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * AA (pt t.1 t.2.1 t.2.2 τ)`. Rewrite using `[← AA_smul, h]`. Establish `h2 : DD τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * DD (pt t.1 t.2.1 t.2.2 τ)`. Rewrite using `[← DD_smul, h]`.

Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fac_eq_zero_of_smul (t : ℕ × ℕ × ℕ) (τ : ℍ) (γ : SL(2, ℤ))
    (h : γ • pt t.1 t.2.1 t.2.2 τ = τ) : fac t τ = 0 := by
  unfold fac
  have h1 : AA τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * AA (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← AA_smul, h]
  have h2 : DD τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * DD (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← DD_smul, h]
  rw [h1, h2]
  ring

/- English proof (translation)
Establish `hAC : A ≠ 0 ∨ C ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h0 : (m : ℤ) = 0` using `by rw [← hdet, hc.1, hc.2]; ring`. Use linear arithmetic over natural numbers and integers.

Take `⟨G, hG⟩ : ∃ G : ℕ, G = Int.gcd A C` from `⟨_, rfl⟩`. Establish `hGpos : 0 < G`. Rewrite using `[hG]`. Use `first`. Consider the case `exact Int.gcd_pos_iff.mpr hAC`.

Consider the case `(rcases hAC with h | h`. Conclude with `Int.gcd_pos_of_ne_zero_left C h`. Conclude with `Int.gcd_pos_of_ne_zero_right A h)`. Choose the witnesses or unpack the hypotheses as in `⟨a0, ha0⟩ : (G : ℤ) ∣ A := by`. Rewrite using `[hG]`.

Apply the tactic sequence `first | exact Int.gcd_dvd_left | exact Int.gcd_dvd_left A C | exact Int.gcd_dvd_left _ _`. Choose the witnesses or unpack the hypotheses as in `⟨c0, hc0⟩ : (G : ℤ) ∣ C := by`. Rewrite using `[hG]`. Apply the tactic sequence `first | exact Int.gcd_dvd_right | exact Int.gcd_dvd_right A C | exact Int.gcd_dvd_right _ _`. Take `⟨x, y, hbez⟩ : ∃ x y : ℤ, (G : ℤ) = A * x + C * y` from `⟨_, _, by rw [hG]; exact Int.gcd_eq_gcd_ab A C⟩`.

Establish `hG0 : (G : ℤ) ≠ 0` using `by exact_mod_cast hGpos.ne'`. Establish `h1 : a0 * x + c0 * y = 1`. Apply `mul_left_cancel₀ hG0` to reduce the goal to its premises. Take the linear combination `-hbez - x * ha0 - y * hc0`. Take `⟨d, hd⟩ : ∃ d : ℤ, d = a0 * D - c0 * B` from `⟨_, rfl⟩`.

Establish `hGd : (G : ℤ) * d = m`. Rewrite using `[hd]`. Take the linear combination `hdet - D * ha0 + B * hc0`. Establish `hdpos : 0 < d`. Establish `h2 : 0 < (G : ℤ) * d` using `by rw [hGd]; exact_mod_cast hm`.

Establish `h3 : (0 : ℤ) < G` using `by exact_mod_cast hGpos`. Assume the negation of the conclusion as `h4`. Use `push_neg at h4`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨q, b, hdiv, hb0, hbd⟩ : ∃ q b : ℤ, d * q + b = x * B + y * D ∧ 0 ≤ b ∧ b < d` from `⟨(x * B + y * D) / d, (x * B + y * D) % d, (by first`.

Consider the case `(have h5 := Int.emod_add_ediv (x * B + y * D) d; linarith)`. Consider the case `(have h5 := Int.ediv_add_emod' (x * B + y * D) d; linarith)`. Consider the case `(have h5 := Int.mul_ediv_add_emod (x * B + y * D) d; linarith)), Int.emod_nonneg _ hdpos.ne',`. Use the proof step `Int.emod_lt_of_pos _ hdpos⟩`. Establish `hdet1 : (x + q * c0) * a0 - (y - q * a0) * -c0 = 1` using `by linear_combination h1`.

Establish `e1 : (x + q * c0) * A + (y - q * a0) * C = (G : ℤ)`. Take the linear combination `-hbez + q * c0 * ha0 - q * a0 * hc0`. Establish `e2 : (x + q * c0) * B + (y - q * a0) * D = b`. Take the linear combination `-hdiv + q * hd`. Establish `e3 : -c0 * A + a0 * C = 0`.

Take the linear combination `-c0 * ha0 + a0 * hc0`. Establish `e4 : -c0 * B + a0 * D = d`. Take the linear combination `-hd`. Use `lift d to ℕ using hdpos.le`. Use `lift b to ℕ using hb0`.

Establish `hGdn : G * d = m` using `by exact_mod_cast hGd`. Establish `hmd : m / G = d` using `by rw [← hGdn, Nat.mul_div_cancel_left _ hGpos]`. Use `⟨⟨!![x + q * c0, y - q * a0; -c0, a0], by rw [Matrix.det_fin_two_of]; exact hdet1⟩, (G, b, d), ?_, by show 0 < d; exact_mod_cast hdpos, ?_⟩` and prove the remaining obligations. Simplify using `only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]`. Use `⟨⟨G, b⟩, ⟨⟨⟨d, hGdn.symm⟩, hm.ne'⟩, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmd]`. Conclude with `hbd` after adjusting the coercions. Simplify using `[hmd]`. Use `show !![x + q * c0, y - q * a0; -c0, a0] * !![A, B; C, D] = Tmat (G, b, d)`. Rewrite using `[Matrix.mul_fin_two, e1, e2, e3, e4]`.

Apply the tactic sequence `all_goals first | rfl | (unfold Tmat; rfl) | simp [Tmat]`.
-/
private lemma exists_SL2_mul_eq_Tmat_of_det_eq {m : ℕ} (hm : 0 < m) (A B C D : ℤ) (hdet : A * D - B * C = m) :
    ∃ g : SL(2, ℤ), ∃ s ∈ Tm m, 0 < s.2.2 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) * !![A, B; C, D] = Tmat s := by
  have hAC : A ≠ 0 ∨ C ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (m : ℤ) = 0 := by rw [← hdet, hc.1, hc.2]; ring
    omega
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = Int.gcd A C := ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    first
    | exact Int.gcd_pos_iff.mpr hAC
    | (rcases hAC with h | h
       · exact Int.gcd_pos_of_ne_zero_left C h
       · exact Int.gcd_pos_of_ne_zero_right A h)
  obtain ⟨a0, ha0⟩ : (G : ℤ) ∣ A := by
    rw [hG]
    first | exact Int.gcd_dvd_left | exact Int.gcd_dvd_left A C | exact Int.gcd_dvd_left _ _
  obtain ⟨c0, hc0⟩ : (G : ℤ) ∣ C := by
    rw [hG]
    first | exact Int.gcd_dvd_right | exact Int.gcd_dvd_right A C | exact Int.gcd_dvd_right _ _
  obtain ⟨x, y, hbez⟩ : ∃ x y : ℤ, (G : ℤ) = A * x + C * y :=
    ⟨_, _, by rw [hG]; exact Int.gcd_eq_gcd_ab A C⟩
  have hG0 : (G : ℤ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have h1 : a0 * x + c0 * y = 1 := by
    apply mul_left_cancel₀ hG0
    linear_combination -hbez - x * ha0 - y * hc0
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = a0 * D - c0 * B := ⟨_, rfl⟩
  have hGd : (G : ℤ) * d = m := by
    rw [hd]
    linear_combination hdet - D * ha0 + B * hc0
  have hdpos : 0 < d := by
    have h2 : 0 < (G : ℤ) * d := by rw [hGd]; exact_mod_cast hm
    have h3 : (0 : ℤ) < G := by exact_mod_cast hGpos
    by_contra h4
    push_neg at h4
    nlinarith
  obtain ⟨q, b, hdiv, hb0, hbd⟩ : ∃ q b : ℤ, d * q + b = x * B + y * D ∧ 0 ≤ b ∧ b < d :=
    ⟨(x * B + y * D) / d, (x * B + y * D) % d,
      (by first
          | (have h5 := Int.emod_add_ediv (x * B + y * D) d; linarith)
          | (have h5 := Int.ediv_add_emod' (x * B + y * D) d; linarith)
          | (have h5 := Int.mul_ediv_add_emod (x * B + y * D) d; linarith)), Int.emod_nonneg _ hdpos.ne',
      Int.emod_lt_of_pos _ hdpos⟩
  have hdet1 : (x + q * c0) * a0 - (y - q * a0) * -c0 = 1 := by linear_combination h1
  have e1 : (x + q * c0) * A + (y - q * a0) * C = (G : ℤ) := by
    linear_combination -hbez + q * c0 * ha0 - q * a0 * hc0
  have e2 : (x + q * c0) * B + (y - q * a0) * D = b := by
    linear_combination -hdiv + q * hd
  have e3 : -c0 * A + a0 * C = 0 := by
    linear_combination -c0 * ha0 + a0 * hc0
  have e4 : -c0 * B + a0 * D = d := by
    linear_combination -hd
  lift d to ℕ using hdpos.le
  lift b to ℕ using hb0
  have hGdn : G * d = m := by exact_mod_cast hGd
  have hmd : m / G = d := by rw [← hGdn, Nat.mul_div_cancel_left _ hGpos]
  refine ⟨⟨!![x + q * c0, y - q * a0; -c0, a0], by rw [Matrix.det_fin_two_of]; exact hdet1⟩, (G, b, d), ?_, by show 0 < d; exact_mod_cast hdpos, ?_⟩
  · simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
    refine ⟨⟨G, b⟩, ⟨⟨⟨d, hGdn.symm⟩, hm.ne'⟩, ?_⟩, ?_⟩
    · rw [hmd]; exact_mod_cast hbd
    · simp [hmd]
  · show !![x + q * c0, y - q * a0; -c0, a0] * !![A, B; C, D] = Tmat (G, b, d)
    rw [Matrix.mul_fin_two, e1, e2, e3, e4]
    all_goals first | rfl | (unfold Tmat; rfl) | simp [Tmat]

/- English proof (translation)
Take `⟨g, s, hs, he, hgs⟩` from `exists_SL2_mul_eq_Tmat_of_det_eq hm A B C D hdet`. Take `⟨p, q, r, w, hg⟩ : ∃ p q r w : ℤ, (g : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, w]` from `⟨_, _, _, _, Matrix.eta_fin_two _⟩`. Establish `hdg : p * w - q * r = 1`. Establish `h0` using `Matrix.SpecialLinearGroup.det_coe g`. Rewrite `h0` using `[hg, Matrix.det_fin_two_of]`.

Conclude with `h0`. Establish `hp : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p` using `by rw [hg]; rfl`. Establish `hq : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q` using `by rw [hg]; rfl`. Establish `hr : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r` using `by rw [hg]; rfl`. Establish `hw : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = w` using `by rw [hg]; rfl`.

Rewrite `hgs` using `[hg]`. Unfold `Tmat at hgs`. Rewrite `hgs` using `[Matrix.mul_fin_two]`. Establish `e00 : p * A + q * C = ((s.1 : ℕ) : ℤ)` using `congrFun (congrFun hgs 0) 0`. Establish `e01 : p * B + q * D = ((s.2.1 : ℕ) : ℤ)` using `congrFun (congrFun hgs 0) 1`.

Establish `e10 : r * A + w * C = 0` using `congrFun (congrFun hgs 1) 0`. Establish `e11 : r * B + w * D = ((s.2.2 : ℕ) : ℤ)` using `congrFun (congrFun hgs 1) 1`. Establish `ea : (s.1 : ℂ) = p * A + q * C` using `by exact_mod_cast e00.symm`. Establish `eb : (s.2.1 : ℂ) = p * B + q * D` using `by exact_mod_cast e01.symm`. Establish `ez : (r : ℂ) * A + w * C = 0` using `by exact_mod_cast e10`.

Establish `ee : (s.2.2 : ℂ) = r * B + w * D` using `by exact_mod_cast e11.symm`. Establish `hE : (s.2.2 : ℂ) ≠ 0` using `by exact_mod_cast he.ne'`. Establish `hden : (r : ℂ) * τ + w ≠ 0`. Introduce `h0`. Establish `him : (r : ℝ) * τ.im = 0`.

Establish `h3` using `congrArg Complex.im h0`. Simplify using `using h3`. Establish `hτ` using `τ.im_pos`. Establish `hr0 : r = 0`. Break down `mul_eq_zero.mp him with h4 | h4` into its components or cases.

Conclude with `h4` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h0` using `[hr0]`. Establish `hw0 : w = 0`. Establish `h3` using `congrArg Complex.re h0`.

Simplify using `at h3`. Conclude with `h3` after adjusting the coercions. Rewrite `hdg` using `[hr0, hw0]`. Simplify using `at hdg`. Establish `c1 : ∀ z : ℤ, (((algebraMap ℤ ℝ) z : ℝ) : ℂ) = (z : ℂ)`.

Introduce `z`. Rewrite using `[eq_intCast]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hform : ((g • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w)`.

Simplify using `[UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom, UpperHalfPlane.σ, hp, hq, hr, hw]`. Apply the tactic sequence `try rw [c1 p, c1 q, c1 r, c1 w]`. Establish `hX : ((s.1 : ℂ) * τ + (s.2.1 : ℂ)) / (s.2.2 : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w)`. Rewrite using `[div_eq_div_iff hE hden]`. Take the linear combination `((τ : ℂ) * (r * τ + w)) * ea + ((r : ℂ) * τ + w) * eb + ((p : ℂ) * (r * τ + w) - (p * τ + q) * r) * hfix + ((p : ℂ) * τ + q) * τ * ez - ((p : ℂ) * τ + q) * ee`.

Establish `hpt : pt s.1 s.2.1 s.2.2 τ = g • τ`. Unfold `pt`. Rewrite using `[hX, ← hform]`. Use `first`. Consider the case `exact UpperHalfPlane.ofComplex_apply (g • τ)`.

Consider the case `simp`. Unfold `Gm`. Apply `Finset.prod_eq_zero hs` to reduce the goal to its premises. Apply `fac_eq_zero_of_smul s τ g⁻¹` to reduce the goal to its premises. Rewrite using `[hpt, inv_smul_smul]`.
-/
theorem Gm_vanish {m : ℕ} (hm : 0 < m) (τ : ℍ) (A B C D : ℤ) (hdet : A * D - B * C = m)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : Gm m τ = 0 := by
  obtain ⟨g, s, hs, he, hgs⟩ := exists_SL2_mul_eq_Tmat_of_det_eq hm A B C D hdet
  obtain ⟨p, q, r, w, hg⟩ : ∃ p q r w : ℤ, (g : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdg : p * w - q * r = 1 := by
    have h0 := Matrix.SpecialLinearGroup.det_coe g
    rw [hg, Matrix.det_fin_two_of] at h0
    exact h0
  have hp : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by rw [hg]; rfl
  have hq : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q := by rw [hg]; rfl
  have hr : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by rw [hg]; rfl
  have hw : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = w := by rw [hg]; rfl
  rw [hg] at hgs
  unfold Tmat at hgs
  rw [Matrix.mul_fin_two] at hgs
  have e00 : p * A + q * C = ((s.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 0
  have e01 : p * B + q * D = ((s.2.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 1
  have e10 : r * A + w * C = 0 := congrFun (congrFun hgs 1) 0
  have e11 : r * B + w * D = ((s.2.2 : ℕ) : ℤ) := congrFun (congrFun hgs 1) 1
  have ea : (s.1 : ℂ) = p * A + q * C := by exact_mod_cast e00.symm
  have eb : (s.2.1 : ℂ) = p * B + q * D := by exact_mod_cast e01.symm
  have ez : (r : ℂ) * A + w * C = 0 := by exact_mod_cast e10
  have ee : (s.2.2 : ℂ) = r * B + w * D := by exact_mod_cast e11.symm
  have hE : (s.2.2 : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hden : (r : ℂ) * τ + w ≠ 0 := by
    intro h0
    have him : (r : ℝ) * τ.im = 0 := by
      have h3 := congrArg Complex.im h0
      simpa using h3
    have hτ := τ.im_pos
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp him with h4 | h4
      · exact_mod_cast h4
      · linarith
    rw [hr0] at h0
    have hw0 : w = 0 := by
      have h3 := congrArg Complex.re h0
      simp at h3
      exact_mod_cast h3
    rw [hr0, hw0] at hdg
    simp at hdg
  have c1 : ∀ z : ℤ, (((algebraMap ℤ ℝ) z : ℝ) : ℂ) = (z : ℂ) := by
    intro z
    rw [eq_intCast]
    push_cast
    rfl
  have hform : ((g • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hp, hq, hr, hw]
    try rw [c1 p, c1 q, c1 r, c1 w]
  have hX : ((s.1 : ℂ) * τ + (s.2.1 : ℂ)) / (s.2.2 : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    rw [div_eq_div_iff hE hden]
    linear_combination ((τ : ℂ) * (r * τ + w)) * ea + ((r : ℂ) * τ + w) * eb
      + ((p : ℂ) * (r * τ + w) - (p * τ + q) * r) * hfix + ((p : ℂ) * τ + q) * τ * ez
      - ((p : ℂ) * τ + q) * ee
  have hpt : pt s.1 s.2.1 s.2.2 τ = g • τ := by
    unfold pt
    rw [hX, ← hform]
    first
    | exact UpperHalfPlane.ofComplex_apply (g • τ)
    | simp
  unfold Gm
  apply Finset.prod_eq_zero hs
  apply fac_eq_zero_of_smul s τ g⁻¹
  rw [hpt, inv_smul_smul]

end ReciprocityTheory.ChartRestriction.L1
