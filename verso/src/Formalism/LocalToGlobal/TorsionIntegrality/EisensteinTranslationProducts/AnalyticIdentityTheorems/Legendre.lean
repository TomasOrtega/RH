import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

noncomputable section
open UpperHalfPlane hiding I
open EisensteinSeries Complex SummationFilter ModularGroup
open scoped Real

namespace Formalism.L2.Th1.F.LegendreModelEllipticTorsion

/- English proof (translation)
Establish `hw : 0 < (((a : ℂ) + 1) * (z : ℂ)).im`. Establish `e : (((a : ℂ) + 1) * (z : ℂ)).im = ((a : ℝ) + 1) * (z : ℂ).im`. Simplify using `[Complex.mul_im]`. Rewrite using `[e]`. Conclude with `mul_pos (by positivity) z.im_pos`.

Establish `H` using `EisensteinSeries.qExpansion_identity_pnat (k := 1) le_rfl ⟨((a : ℂ) + 1) * (z : ℂ), hw⟩`. Establish `hc : ((⟨((a : ℂ) + 1) * (z : ℂ), hw⟩ : ℍ) : ℂ) = ((a : ℂ) + 1) * (z : ℂ)` using `rfl`. Rewrite `H` using `[hc]`. Unfold `EisensteinSeries.e2Summand`. Establish `e1 : ∀ n : ℤ, eisSummand 2 ![(a : ℤ) + 1, n] z = 1 / (((a : ℂ) + 1) * (z : ℂ) + n) ^ (1 + 1)`.

Introduce `n`. Simplify using `[eisSummand, zpow_neg]`. Establish `hq : ∀ n : ℕ+, cexp (2 * π * I * (((a : ℂ) + 1) * (z : ℂ))) ^ (n : ℕ) = cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ))`. Introduce `n`. Rewrite using `[← Complex.exp_nat_mul, ← Complex.exp_nat_mul]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1]`. Rewrite using `[H]`.

Simplify using `only [hq, pow_one]`. Use `set S := ∑' n : ℕ+, ((n : ℕ) : ℂ) * cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ))`. Simplify using `only [Nat.factorial, Nat.cast_one, div_one, Nat.mul_one, Nat.succ_eq_add_one, zero_add]`. Take the linear combination `(4 * (π : ℂ) ^ 2 * S) * Complex.I_sq`.
-/
lemma e2Summand_succ (z : ℍ) (a : ℕ) : e2Summand ((a : ℤ) + 1) z =
    -4 * π ^ 2 * ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((a + 1) * n : ℕ) := by
  have hw : 0 < (((a : ℂ) + 1) * (z : ℂ)).im := by
    have e : (((a : ℂ) + 1) * (z : ℂ)).im = ((a : ℝ) + 1) * (z : ℂ).im := by
      simp [Complex.mul_im]
    rw [e]
    exact mul_pos (by positivity) z.im_pos
  have H := EisensteinSeries.qExpansion_identity_pnat (k := 1) le_rfl ⟨((a : ℂ) + 1) * (z : ℂ), hw⟩
  have hc : ((⟨((a : ℂ) + 1) * (z : ℂ), hw⟩ : ℍ) : ℂ) = ((a : ℂ) + 1) * (z : ℂ) := rfl
  rw [hc] at H
  unfold EisensteinSeries.e2Summand
  have e1 : ∀ n : ℤ, eisSummand 2 ![(a : ℤ) + 1, n] z
      = 1 / (((a : ℂ) + 1) * (z : ℂ) + n) ^ (1 + 1) := by
    intro n
    simp [eisSummand, zpow_neg]
  have hq : ∀ n : ℕ+, cexp (2 * π * I * (((a : ℂ) + 1) * (z : ℂ))) ^ (n : ℕ)
      = cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ)) := by
    intro n
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [e1]
  rw [H]
  simp only [hq, pow_one]
  set S := ∑' n : ℕ+, ((n : ℕ) : ℂ) * cexp (2 * π * I * z) ^ ((a + 1) * (n : ℕ))
  simp only [Nat.factorial, Nat.cast_one, div_one, Nat.mul_one, Nat.succ_eq_add_one, zero_add]
  linear_combination (4 * (π : ℂ) ^ 2 * S) * Complex.I_sq

/- English proof (translation)
Use `set r := cexp (2 * π * I * (z : ℂ)) with hr`. Use `set ρ := ‖r‖ with hρdef`. Establish `hρ : ρ < 1` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one z`. Establish `hρ0 : 0 ≤ ρ` using `norm_nonneg _`. Establish `hsum : Summable fun n : ℕ => (n : ℝ) ^ 1 * ρ ^ n` using `summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hρ0])`.

Establish `hsumP : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * ρ ^ (n : ℕ)`. Use `hsum.comp_injective PNat.coe_injective` as an intermediate fact. Simplify using `only [pow_one] at this`. Conclude with `this`. Use `set C := ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ)`.

Establish `hpt : ∀ (a : ℕ) (n : ℕ+), ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖ ≤ ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) * ρ ^ a`. Introduce `a n`. Rewrite using `[norm_mul, norm_pow, Complex.norm_natCast, mul_assoc, ← pow_add]`. Apply `mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Apply `pow_le_pow_of_le_one hρ0 hρ.le` to reduce the goal to its premises.

Use `n.pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hb : ∀ a : ℕ, ‖e2Summand ((a : ℤ) + 1) z‖ ≤ 4 * π ^ 2 * C * ρ ^ a`. Introduce `a`. Rewrite using `[e2Summand_succ, norm_mul]`.

Establish `h4 : ‖(-4 * (π : ℂ) ^ 2)‖ = 4 * π ^ 2`. Rewrite using `[norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]`. Evaluate the numerical expressions. Rewrite using `[h4, mul_assoc (4 * π ^ 2)]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises.

Establish `hs : Summable fun n : ℕ+ => ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖` using `Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hpt a) (hsumP.mul_right _)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Summable.of_norm_bounded (g := fun a : ℕ => 4 * π ^ 2 * C * ρ ^ a) ((summable_geometric_of_lt_one hρ0 hρ).mul_left _) hb`.
-/
lemma summable_e2Summand_succ (z : ℍ) : Summable fun a : ℕ => e2Summand ((a : ℤ) + 1) z := by
  set r := cexp (2 * π * I * (z : ℂ)) with hr
  set ρ := ‖r‖ with hρdef
  have hρ : ρ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hsum : Summable fun n : ℕ => (n : ℝ) ^ 1 * ρ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_of_nonneg hρ0])
  have hsumP : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) := by
    have := hsum.comp_injective PNat.coe_injective
    simp only [pow_one] at this
    exact this
  set C := ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ)
  have hpt : ∀ (a : ℕ) (n : ℕ+), ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖
      ≤ ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) * ρ ^ a := by
    intro a n
    rw [norm_mul, norm_pow, Complex.norm_natCast, mul_assoc, ← pow_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply pow_le_pow_of_le_one hρ0 hρ.le
    have := n.pos
    nlinarith
  have hb : ∀ a : ℕ, ‖e2Summand ((a : ℤ) + 1) z‖ ≤ 4 * π ^ 2 * C * ρ ^ a := by
    intro a
    rw [e2Summand_succ, norm_mul]
    have h4 : ‖(-4 * (π : ℂ) ^ 2)‖ = 4 * π ^ 2 := by
      rw [norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      norm_num
    rw [h4, mul_assoc (4 * π ^ 2)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hs : Summable fun n : ℕ+ => ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hpt a) (hsumP.mul_right _)
    calc ‖∑' n : ℕ+, ((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖
        ≤ ∑' n : ℕ+, ‖((n : ℕ) : ℂ) * r ^ ((a + 1) * (n : ℕ))‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ+, ((n : ℕ) : ℝ) * ρ ^ (n : ℕ) * ρ ^ a :=
          Summable.tsum_le_tsum (hpt a) hs (hsumP.mul_right _)
      _ = C * ρ ^ a := tsum_mul_right
  exact Summable.of_norm_bounded (g := fun a : ℕ => 4 * π ^ 2 * C * ρ ^ a)
    ((summable_geometric_of_lt_one hρ0 hρ).mul_left _) hb

/- English proof (translation)
Establish `hev` using `EisensteinSeries.e2Summand_even z`. Establish `h0 : Summable fun n : ℕ => e2Summand (n : ℤ) z`. Rewrite using `[← summable_nat_add_iff 1]`. Use `(summable_e2Summand_succ z).congr ?_` and prove the remaining obligations. Introduce `a`.

Use `push_cast`. Both sides reduce to the same expression. Use `Summable.of_nat_of_neg h0 ?_` and prove the remaining obligations. Use `h0.congr ?_` and prove the remaining obligations. Introduce `n`.

Conclude with `(hev (n : ℤ)).symm`.
-/
lemma summable_e2Summand (z : ℍ) : Summable fun n : ℤ => e2Summand n z := by
  have hev := EisensteinSeries.e2Summand_even z
  have h0 : Summable fun n : ℕ => e2Summand (n : ℤ) z := by
    rw [← summable_nat_add_iff 1]
    refine (summable_e2Summand_succ z).congr ?_
    intro a
    push_cast
    rfl
  refine Summable.of_nat_of_neg h0 ?_
  refine h0.congr ?_
  intro n
  exact (hev (n : ℤ)).symm

/- English proof (translation)
Unfold `EisensteinSeries.G2`. Conclude with `(tsum_eq_of_summable_unconditional (summable_e2Summand z)).symm`.
-/
lemma tsum_e2Summand (z : ℍ) : ∑' n : ℤ, e2Summand n z = G2 z := by
  unfold EisensteinSeries.G2
  exact (tsum_eq_of_summable_unconditional (summable_e2Summand z)).symm

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[mul_pow, one_div, mul_inv, zpow_neg]`. Use `norm_cast`.
-/
private lemma one_div_sq_eq_of_eq_mul (X Y c : ℂ) (h : X = c * Y) :
    1 / X ^ 2 = (c ^ 2)⁻¹ * Y ^ (-2 : ℤ) := by
  subst h
  rw [mul_pow, one_div, mul_inv, zpow_neg]
  norm_cast

/- English proof (translation)
Establish `hu : u ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u` using `rfl`. Rewrite using `[← tsum_e2Summand, ← tsum_mul_left]`.

Use `congr 1`. Use function extensionality and compare the values at `n`. Unfold `EisensteinSeries.e2Summand`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`.

Use function extensionality and compare the values at `m`. Simplify using `only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hc]`. Apply `one_div_sq_eq_of_eq_mul` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sumA (u v : ℂ) (h : 0 < (v / u).im) :
    ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 = (u ^ 2)⁻¹ * G2 ⟨v / u, h⟩ := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u := rfl
  rw [← tsum_e2Summand, ← tsum_mul_left]
  congr 1
  funext n
  unfold EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  congr 1
  funext m
  simp only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hc]
  apply one_div_sq_eq_of_eq_mul
  field_simp
  ring

/- English proof (translation)
Establish `hu : u ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `hv : v ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h`. Establish `hw : ((S • (⟨v / u, h⟩ : ℍ) : ℍ) : ℂ) = -(u / v)`. Rewrite using `[UpperHalfPlane.modular_S_smul]`. Express the relevant statement in the definitionally equal form `(-(v / u))⁻¹ = -(u / v)`. Rewrite using `[inv_neg, inv_div]`.

Rewrite using `[← tsum_e2Summand, ← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `m`. Establish `he : e2Summand (-m) (S • (⟨v / u, h⟩ : ℍ)) = e2Summand m (S • (⟨v / u, h⟩ : ℍ))` using `EisensteinSeries.e2Summand_even _ m`. Rewrite using `[← he]`.

Unfold `EisensteinSeries.e2Summand`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `n`. Simplify using `only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hw]`.

Apply `one_div_sq_eq_of_eq_mul` to reduce the goal to its premises. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sumB (u v : ℂ) (h : 0 < (v / u).im) :
    ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 = (v ^ 2)⁻¹ * G2 (S • ⟨v / u, h⟩) := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h
  have hw : ((S • (⟨v / u, h⟩ : ℍ) : ℍ) : ℂ) = -(u / v) := by
    rw [UpperHalfPlane.modular_S_smul]
    change (-(v / u))⁻¹ = -(u / v)
    rw [inv_neg, inv_div]
  rw [← tsum_e2Summand, ← tsum_mul_left]
  congr 1
  funext m
  have he : e2Summand (-m) (S • (⟨v / u, h⟩ : ℍ)) = e2Summand m (S • (⟨v / u, h⟩ : ℍ)) :=
    EisensteinSeries.e2Summand_even _ m
  rw [← he]
  unfold EisensteinSeries.e2Summand
  rw [← tsum_mul_left]
  congr 1
  funext n
  simp only [eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hw]
  apply one_div_sq_eq_of_eq_mul
  field_simp
  push_cast
  ring

/- English proof (translation)
Establish `hu : u ≠ 0`. Introduce and unpack `rfl`. Simplify using `at h`. Establish `hv : v ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h`. Rewrite using `[sumA u v h, sumB u v h]`. Establish `hT` using `EisensteinSeries.G2_S_transform ⟨v / u, h⟩`. Establish `hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u` using `rfl`. Rewrite `hT` using `[hc]`.

Rewrite using `[hT]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma key (u v : ℂ) (h : 0 < (v / u).im) :
    (u * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * v
      - (v * ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) * u = 2 * π * I := by
  have hu : u ≠ 0 := by
    rintro rfl
    simp at h
  have hv : v ≠ 0 := by
    rintro rfl
    simp at h
  rw [sumA u v h, sumB u v h]
  have hT := EisensteinSeries.G2_S_transform ⟨v / u, h⟩
  have hc : ((⟨v / u, h⟩ : ℍ) : ℂ) = v / u := rfl
  rw [hc] at hT
  rw [hT]
  field_simp
  ring

end Formalism.L2.Th1.F.LegendreModelEllipticTorsion

namespace Formalism.L2.Th1.F

/- English proof (translation)
Establish `hind` using `L.indep`. Establish `ha : L.ω₁ ≠ 0` using `by simpa using hind.ne_zero 0`. Establish `hb : L.ω₂ ≠ 0` using `by simpa using hind.ne_zero 1`. Establish `hne : (L.ω₂ / L.ω₁).im ≠ 0`. Introduce `him`.

Establish `hr : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ)` using `Complex.ext (by simp) (by simp [him])`. Establish `hbr : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁`. Rewrite using `[← hr]`. Clear the denominators using the available nonvanishing facts. Establish `h2` using `(LinearIndependent.pair_iff.mp hind) (L.ω₂ / L.ω₁).re (-1) (by`.

Rewrite using `[Complex.real_smul, Complex.real_smul]`. Use `nth_rewrite 2 [hbr]`. Use `push_cast`. Use the proof step `ring)`. Evaluate the numerical expressions using `at h2`.

Establish `hlt : (L.ω₂ / L.ω₁).im < 0` using `lt_of_le_of_ne (not_lt.mp h) hne`. Rewrite using `[show L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ from (inv_div _ _).symm, Complex.inv_im]`. Conclude with `div_pos (neg_pos.mpr hlt) (Complex.normSq_pos.mpr (div_ne_zero hb ha))`.
-/
lemma LegendreModelEllipticTorsion.im_pos_of_not (L : PeriodPair) (h : ¬ 0 < (L.ω₂ / L.ω₁).im) :
    0 < (L.ω₁ / L.ω₂).im := by
  have hind := L.indep
  have ha : L.ω₁ ≠ 0 := by simpa using hind.ne_zero 0
  have hb : L.ω₂ ≠ 0 := by simpa using hind.ne_zero 1
  have hne : (L.ω₂ / L.ω₁).im ≠ 0 := by
    intro him
    have hr : L.ω₂ / L.ω₁ = ((L.ω₂ / L.ω₁).re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hbr : L.ω₂ = ((L.ω₂ / L.ω₁).re : ℂ) * L.ω₁ := by
      rw [← hr]
      field_simp
    have h2 := (LinearIndependent.pair_iff.mp hind) (L.ω₂ / L.ω₁).re (-1) (by
      rw [Complex.real_smul, Complex.real_smul]
      nth_rewrite 2 [hbr]
      push_cast
      ring)
    norm_num at h2
  have hlt : (L.ω₂ / L.ω₁).im < 0 := lt_of_le_of_ne (not_lt.mp h) hne
  rw [show L.ω₁ / L.ω₂ = (L.ω₂ / L.ω₁)⁻¹ from (inv_div _ _).symm, Complex.inv_im]
  exact div_pos (neg_pos.mpr hlt) (Complex.normSq_pos.mpr (div_ne_zero hb ha))

/- English proof (translation)
Introduce `L`. Take `⟨h1, h2⟩` from `h L`. Rewrite using `[h1, h2]`. Use `split_ifs with hp`. Rewrite using `[one_mul]`.

Conclude with `LegendreModelEllipticTorsion.key L.ω₁ L.ω₂ hp`. Establish `hp'` using `LegendreModelEllipticTorsion.im_pos_of_not L hp`. Establish `k` using `LegendreModelEllipticTorsion.key L.ω₂ L.ω₁ hp'`. Establish `e1 : (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2) = ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Use `congr 1`. Use function extensionality and compare the values at `b`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2) = ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Use `congr 1`. Use function extensionality and compare the values at `b`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `k` using `[e1, e2]`. Take the linear combination `-k`.
-/
theorem legendre_of (h : EtaEisenstein) : Legendre := by
  intro L
  obtain ⟨h1, h2⟩ := h L
  rw [h1, h2]
  split_ifs with hp
  · rw [one_mul]
    exact LegendreModelEllipticTorsion.key L.ω₁ L.ω₂ hp
  · have hp' := LegendreModelEllipticTorsion.im_pos_of_not L hp
    have k := LegendreModelEllipticTorsion.key L.ω₂ L.ω₁ hp'
    have e1 : (∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
        = ∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
      congr 1; funext a; congr 1; funext b; ring
    have e2 : (∑' m : ℤ, ∑' n : ℤ, 1 / ((m : ℂ) * L.ω₂ + (n : ℂ) * L.ω₁) ^ 2)
        = ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) ^ 2 := by
      congr 1; funext a; congr 1; funext b; ring
    rw [e1, e2] at k
    linear_combination -k

end Formalism.L2.Th1.F
