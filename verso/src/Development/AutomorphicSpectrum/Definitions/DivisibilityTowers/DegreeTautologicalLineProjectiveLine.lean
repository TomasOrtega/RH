import Mathlib
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

noncomputable section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.Top.Model

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dimFl_eq : dimFl Ψ N = Formalism.DegreeFormula.dimFl Ψ N := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem degFl_eq (F : RP Ψ N) : degFl F = Formalism.DegreeFormula.degFl Ψ N F := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem linRoot_eq (lam : Wt Ψ N) : linRoot lam = Formalism.DegreeFormula.linRoot lam := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem flagDeg_eq (lam : Wt Ψ N) : flagDeg lam = Formalism.DegreeFormula.flagDeg Ψ N lam := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pk_eq (τ : Ψ) (k : ℕ) : (pk τ k : RP Ψ N) = GlobalTheory.FlagPoly.pSum τ k := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pkLow_eq (j : ℕ) (τ : Ψ) (k : ℕ) : (pkLow j τ k : RP Ψ N) = GlobalTheory.FlagPoly.pLow j τ k := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Sh_eq (j : ℕ) (τ : Ψ) (F : RP Ψ N) : Sh j τ F = GlobalTheory.FlagPoly.shF j τ F := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Tot_eq (τ : Ψ) (F : RP Ψ N) : Tot τ F = GlobalTheory.FlagPoly.totF τ F := rfl

/- English proof (translation)
The claim follows from `Formalism.DegreeFormula.degreePowerSumMulEqZero Ψ N τ k Q hk`.
-/
theorem degFl_pk_mul (τ : Ψ) (k : ℕ) (hk : 1 ≤ k) (Q : RP Ψ N) : degFl (pk τ k * Q) = 0 :=
  Formalism.DegreeFormula.degreePowerSumMulEqZero Ψ N τ k Q hk

/- English proof (translation)
The claim follows from `Formalism.DegreeFormula.degreePoint Ψ N`.
-/
theorem degFl_point : degFl (∏ x : Ψ × Fin N, (-X x : RP Ψ N) ^ (N - 1 - (x.2 : ℕ))) = 1 :=
  Formalism.DegreeFormula.degreePoint Ψ N

/- English proof (translation)
Simplify using `only [degFl, coeff_C_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem degFl_C_mul (c : ℝ) (Q : RP Ψ N) : degFl (C c * Q) = c * degFl Q := by
  simp only [degFl, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Establish `h` using `degFl_point (Ψ := Unit) (N := 2)`. Establish `e : (∏ x : Unit × Fin 2, (-X x : RP Unit 2) ^ (2 - 1 - (x.2 : ℕ))) = C (-1) * X ((), 0)`. Simplify using `[Fintype.prod_prod_type, Fin.prod_univ_two]`. Rewrite `h` using `[e, degFl_C_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degree_tautological_line_projective_line : degFl (X ((), 0) : RP Unit 2) = -1 := by
  have h := degFl_point (Ψ := Unit) (N := 2)
  have e : (∏ x : Unit × Fin 2, (-X x : RP Unit 2) ^ (2 - 1 - (x.2 : ℕ))) = C (-1) * X ((), 0) := by
    simp [Fintype.prod_prod_type, Fin.prod_univ_two]
  rw [e, degFl_C_mul] at h
  linarith

/- English proof (translation)
Simplify using `only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem degFl_add (P Q : RP Ψ N) : degFl (P + Q) = degFl P + degFl Q := by
  simp only [degFl, coeff_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Establish `h` using `degFl_pk_mul (Ψ := Unit) (N := 2) () 1 le_rfl 1`. Simplify using `only [pk, Fin.sum_univ_two, pow_one, mul_one] at h`. Rewrite `h` using `[degFl_add, degree_tautological_line_projective_line]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem degree_quotient_line_projective_line : degFl (X ((), 1) : RP Unit 2) = 1 := by
  have h := degFl_pk_mul (Ψ := Unit) (N := 2) () 1 le_rfl 1
  simp only [pk, Fin.sum_univ_two, pow_one, mul_one] at h
  rw [degFl_add, degree_tautological_line_projective_line] at h
  linarith

/- English proof (translation)
Establish `hd : dimFl Unit 2 = 1` using `by simp [dimFl]`. Establish `e : linRoot u = C (-u () 0) * X ((), 0) + C (-u () 1) * X ((), 1)`. Simplify using `[linRoot, Fintype.sum_prod_type, Fin.sum_univ_two]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[flagDeg, hd, pow_one, e, degFl_add, degFl_C_mul, degFl_C_mul, degree_tautological_line_projective_line, degree_quotient_line_projective_line]`.

Simplify using `[gap, ent]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flagDeg_two (u : Wt Unit 2) : flagDeg u = gap 1 u () := by
  have hd : dimFl Unit 2 = 1 := by simp [dimFl]
  have e : linRoot u = C (-u () 0) * X ((), 0) + C (-u () 1) * X ((), 1) := by
    simp [linRoot, Fintype.sum_prod_type, Fin.sum_univ_two]; ring
  rw [flagDeg, hd, pow_one, e, degFl_add, degFl_C_mul, degFl_C_mul, degree_tautological_line_projective_line, degree_quotient_line_projective_line]
  simp [gap, ent]; ring

/- English proof (translation)
Introduce `τ a b h`. Establish `: ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast h`. Simplify using `only [rhoWt]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rho_regDominant : RegDominant (rhoWt : Wt Ψ N) := by
  intro τ a b h
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h
  simp only [rhoWt]; linarith

/- English proof (translation)
Establish `h3 : j - 1 < N` using `by omega`. Simplify using `only [gap, ent, dif_pos h2, dif_pos h3, rhoWt]`. Rewrite using `[Nat.cast_sub h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gap_rho {j : ℕ} (h1 : 1 ≤ j) (h2 : j < N) (τ : Ψ) : gap j (rhoWt : Wt Ψ N) τ = 1 := by
  have h3 : j - 1 < N := by omega
  simp only [gap, ent, dif_pos h2, dif_pos h3, rhoWt]
  rw [Nat.cast_sub h1]; push_cast; ring

/- English proof (translation)
Use `⟨one_pos, rho_regDominant, fun τ => (gap_rho h1 h2 τ).ge, fun τ a b _ hab => ?_⟩` and prove the remaining obligations. Simplify using `only [rhoWt]`. Establish `hne : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ≠ 0`. Introduce `h`. Apply `hab` to reduce the goal to its premises.

Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Establish `h` using `Int.one_le_abs hne`. Establish `e : ((N : ℝ) - 1 - ((a : ℕ) : ℝ)) - ((N : ℝ) - 1 - ((b : ℕ) : ℝ)) = ((((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) : ℤ) : ℝ)` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `h` after adjusting the coercions.
-/
theorem weightHyp_rho {j : ℕ} (h1 : 1 ≤ j) (h2 : j < N) : WeightHyp j (rhoWt : Wt Ψ N) 1 := by
  refine ⟨one_pos, rho_regDominant, fun τ => (gap_rho h1 h2 τ).ge, fun τ a b _ hab => ?_⟩
  simp only [rhoWt]
  have hne : ((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) ≠ 0 := by
    intro h; apply hab; apply Fin.ext; omega
  have h := Int.one_le_abs hne
  have e : ((N : ℝ) - 1 - ((a : ℕ) : ℝ)) - ((N : ℝ) - 1 - ((b : ℕ) : ℝ)) =
      ((((b : ℕ) : ℤ) - ((a : ℕ) : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [e]; exact_mod_cast h

/- English proof (translation)
Introduce `τ i h _`. Establish `h3 : i < N` using `by omega`. Simplify using `only [ent, dif_pos h, dif_pos h3, rhoWt]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem compactGaps_rho (j : ℕ) : CompactGapsGE j 1 (rhoWt : Wt Ψ N) := by
  intro τ i h _
  have h3 : i < N := by omega
  simp only [ent, dif_pos h, dif_pos h3, rhoWt]
  push_cast; linarith

/- English proof (translation)
Take `⟨hg, -, hgap, -⟩` from `h`. Introduce `τ`. Establish `hf : (1 : ℝ) ≤ Fintype.card Ψ` using `by exact_mod_cast Fintype.card_pos`. Establish `hn : (1 : ℝ) ≤ (N : ℝ) ^ 2` using `one_le_pow₀ (by exact_mod_cast hN)`. Establish `hu` using `norm_nonneg u`.

Take `⟨f, hf0⟩ : ∃ f : ℝ, f = (Fintype.card Ψ : ℝ)` from `⟨_, rfl⟩`. Take `⟨n, hn0⟩ : ∃ n : ℝ, n = (N : ℝ) ^ 2` from `⟨_, rfl⟩`. Rewrite `hf`, the goal using `[← hf0]`. Rewrite `hn` using `[← hn0]`. Establish `hfn : 1 ≤ f * n` using `one_le_mul_of_one_le_of_one_le hf hn`.

Establish `e : (bigB0 u g - 2) * g = 4 * (f * n) * g + 4 * (f * n) * ‖u‖ - 2 * g`. Simplify using `only [bigB0, ← hf0, ← hn0]`. Clear the denominators using the available nonvanishing facts. Establish `hb : 0 ≤ bigB0 u g - 2`. Establish `: 0 ≤ (bigB0 u g - 2) * g` using `by rw [e]; nlinarith [mul_nonneg (by linarith : 0 ≤ f * n) hu]`.

Conclude with `nonneg_of_mul_nonneg_left this hg`. Establish `h1 : 4 * f * ‖u‖ ≤ (bigB0 u g - 2) * g`. Rewrite using `[e]`. Establish `: f * ‖u‖ ≤ f * n * ‖u‖`. Apply `mul_le_mul_of_nonneg_right _ hu` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h1.trans (mul_le_mul_of_nonneg_left (hgap τ) hb)`.
-/
theorem nef_threshold_at_base_bound [Nonempty Ψ] {j : ℕ} (hN : 1 ≤ N) {u : Wt Ψ N} {g : ℝ} (h : WeightHyp j u g) :
    NefThreshold j (bigB0 u g) u := by
  obtain ⟨hg, -, hgap, -⟩ := h
  intro τ
  have hf : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hn : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hN)
  have hu := norm_nonneg u
  obtain ⟨f, hf0⟩ : ∃ f : ℝ, f = (Fintype.card Ψ : ℝ) := ⟨_, rfl⟩
  obtain ⟨n, hn0⟩ : ∃ n : ℝ, n = (N : ℝ) ^ 2 := ⟨_, rfl⟩
  rw [← hf0] at hf ⊢
  rw [← hn0] at hn
  have hfn : 1 ≤ f * n := one_le_mul_of_one_le_of_one_le hf hn
  have e : (bigB0 u g - 2) * g = 4 * (f * n) * g + 4 * (f * n) * ‖u‖ - 2 * g := by
    simp only [bigB0, ← hf0, ← hn0]; field_simp
  have hb : 0 ≤ bigB0 u g - 2 := by
    have : 0 ≤ (bigB0 u g - 2) * g := by rw [e]; nlinarith [mul_nonneg (by linarith : 0 ≤ f * n) hu]
    exact nonneg_of_mul_nonneg_left this hg
  have h1 : 4 * f * ‖u‖ ≤ (bigB0 u g - 2) * g := by
    rw [e]
    have : f * ‖u‖ ≤ f * n * ‖u‖ := by
      apply mul_le_mul_of_nonneg_right _ hu; nlinarith
    nlinarith
  exact h1.trans (mul_le_mul_of_nonneg_left (hgap τ) hb)

/- English proof (translation)
Simplify using `only [pkLow, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]`. Rewrite using `[Fin.card_filter_val_lt, min_eq_right hj]`. Simplify using the standard rewrite rules.
-/
theorem pkLow_zero {j : ℕ} (hj : j ≤ N) (τ : Ψ) : (pkLow j τ 0 : RP Ψ N) = C (j : ℝ) := by
  simp only [pkLow, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Fin.card_filter_val_lt, min_eq_right hj]
  simp

/- English proof (translation)
Simplify using `only [pLie, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]`. Establish `h` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)`. Rewrite `h` using `[Fin.card_filter_val_lt, min_eq_right hj]`. Simplify using `only [not_lt, Finset.card_univ, Fintype.card_fin] at h`. Establish `: (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j` using `by omega`.

Rewrite using `[this, ← Nat.cast_sub hj]`. Simplify using the standard rewrite rules.
-/
theorem pLie_inr_zero {j : ℕ} (hj : j ≤ N) (τ : Ψ) : (pLie j 0 (Sum.inr τ) : RP Ψ N) = C ((N : ℝ) - j) := by
  simp only [pLie, pow_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N))) (fun i : Fin N => (i : ℕ) < j)
  rw [Fin.card_filter_val_lt, min_eq_right hj] at h
  simp only [not_lt, Finset.card_univ, Fintype.card_fin] at h
  have : (Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ))).card = N - j := by omega
  rw [this, ← Nat.cast_sub hj]
  simp

/- English proof (translation)
Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `h0 : (0 : ℝ) ≤ (p : ℝ)⁻¹` using `by positivity`. Establish `h1 : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`. Simplify using `only [deltaTerm, pLie, Nat.sub_self, pkLow_zero hj, degFl_C_mul, pow_one, pow_succ, pow_zero, one_mul]`. Rewrite using `[tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one h0 h1]`.

Establish `: (p : ℝ) - 1 ≠ 0` using `by linarith`. Establish `: (p : ℝ) ≠ 0` using `by linarith`. Establish `: 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p` using `by field_simp`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem deltaTerm_split {j p : ℕ} (hj : j ≤ N) (hp : 2 ≤ p) (τ : Ψ) (fr : ℕ → Ψ) (Q : RP Ψ N) :
    deltaTerm j p τ (fun n => Sum.inl (fr n)) 1 Q = 0 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have h1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simp only [deltaTerm, pLie, Nat.sub_self, pkLow_zero hj, degFl_C_mul, pow_one, pow_succ, pow_zero, one_mul]
  rw [tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one h0 h1]
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  have : (p : ℝ) ≠ 0 := by linarith
  have : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
  rw [this]; field_simp; ring

/- English proof (translation)
Establish `hp' : (2 : ℝ) ≤ p` using `by exact_mod_cast hp`. Use `set r : ℝ := (p : ℝ)⁻¹ with hr`. Establish `h0 : (0 : ℝ) ≤ r` using `by positivity`. Establish `h1 : r < 1` using `inv_lt_one_of_one_lt₀ (by linarith)`. Establish `h2 : r ^ 2 < 1` using `by nlinarith`.

Establish `hg` using `hasSum_geometric_of_lt_one (sq_nonneg r) h2`. Establish `hs : HasSum (fun n : ℕ => ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) * degFl ((pLie j (1 - 1) (if Even n then Sum.inr (fr n) else Sum.inl (fr n)) : RP Ψ N) * Q)) ((1 - r ^ 2)⁻¹ * (r * (((N : ℝ) - j) * degFl Q)) + (1 - r ^ 2)⁻¹ * (r ^ 2 * (j * degFl Q)))`. Apply `HasSum.even_add_odd` to reduce the goal to its premises. Use `Eq.mp (congrArg (fun F => HasSum F _) (funext fun k => Eq.symm ?_)) (hg.mul_right (r * (((N : ℝ) - j) * degFl Q))) beta_reduce` and prove the remaining obligations. Rewrite using `[if_pos (even_two_mul k), Nat.sub_self, pLie_inr_zero hj, degFl_C_mul, pow_one, ← hr]`.

Expand and normalize the polynomial expressions, which then agree. Use `Eq.mp (congrArg (fun F => HasSum F _) (funext fun k => Eq.symm ?_)) (hg.mul_right (r ^ 2 * (j * degFl Q))) beta_reduce` and prove the remaining obligations. Rewrite using `[if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)), Nat.sub_self]`. Simplify using `only [pLie]`. Rewrite using `[pkLow_zero hj, degFl_C_mul, pow_one, ← hr]`.

Expand and normalize the polynomial expressions, which then agree. Unfold `deltaTerm`. Rewrite using `[hs.tsum_eq, Nat.sub_self, pkLow_zero hj, degFl_C_mul]`. Establish `a1 : (p : ℝ) - 1 ≠ 0` using `by linarith`. Establish `a2 : (p : ℝ) ≠ 0` using `by linarith`.

Establish `a3 : (p : ℝ) ^ 2 - 1 ≠ 0` using `by nlinarith`. Establish `: 1 - r ^ 2 = ((p : ℝ) ^ 2 - 1) / p ^ 2` using `by rw [hr]; field_simp`. Rewrite using `[this, hr]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem deltaTerm_inert {j p : ℕ} (hj : j ≤ N) (hp : 2 ≤ p) (τ : Ψ) (fr : ℕ → Ψ) (Q : RP Ψ N) :
    deltaTerm j p τ (fun n => if Even n then Sum.inr (fr n) else Sum.inl (fr n)) 1 Q =
      Real.log p * (((N : ℝ) - 2 * j) * p / ((p : ℝ) ^ 2 - 1)) * degFl Q := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  set r : ℝ := (p : ℝ)⁻¹ with hr
  have h0 : (0 : ℝ) ≤ r := by positivity
  have h1 : r < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h2 : r ^ 2 < 1 := by nlinarith
  have hg := hasSum_geometric_of_lt_one (sq_nonneg r) h2
  have hs : HasSum (fun n : ℕ => ((p : ℝ) ^ 1)⁻¹ ^ (n + 1) *
      degFl ((pLie j (1 - 1) (if Even n then Sum.inr (fr n) else Sum.inl (fr n)) : RP Ψ N) * Q))
      ((1 - r ^ 2)⁻¹ * (r * (((N : ℝ) - j) * degFl Q)) + (1 - r ^ 2)⁻¹ * (r ^ 2 * (j * degFl Q))) := by
    apply HasSum.even_add_odd
    · refine Eq.mp (congrArg (fun F => HasSum F _) (funext fun k => Eq.symm ?_)) (hg.mul_right (r * (((N : ℝ) - j) * degFl Q)))
      beta_reduce
      rw [if_pos (even_two_mul k), Nat.sub_self, pLie_inr_zero hj, degFl_C_mul, pow_one, ← hr]
      ring
    · refine Eq.mp (congrArg (fun F => HasSum F _) (funext fun k => Eq.symm ?_)) (hg.mul_right (r ^ 2 * (j * degFl Q)))
      beta_reduce
      rw [if_neg (Nat.not_even_iff_odd.2 (odd_two_mul_add_one k)), Nat.sub_self]
      simp only [pLie]
      rw [pkLow_zero hj, degFl_C_mul, pow_one, ← hr]
      ring
  unfold deltaTerm
  rw [hs.tsum_eq, Nat.sub_self, pkLow_zero hj, degFl_C_mul]
  have a1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have a2 : (p : ℝ) ≠ 0 := by linarith
  have a3 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have : 1 - r ^ 2 = ((p : ℝ) ^ 2 - 1) / p ^ 2 := by rw [hr]; field_simp
  rw [this, hr]; field_simp; ring

/- English proof (translation)
Simplify using `[gap]`.
-/
theorem gap_zero (u : Wt Ψ N) (τ : Ψ) : gap 0 u τ = 0 := by simp [gap]

/- English proof (translation)
Simplify using `[gap, ent, Fin.last]`.
-/
theorem gap_top (u : Wt Ψ (N + 1)) (τ : Ψ) : gap (N + 1) u τ = u τ (Fin.last N) := by
  simp [gap, ent, Fin.last]

/- English proof (translation)
Establish `h01 : u () 1 ≤ u () 0` using `h () 0 1 (by decide)`. Establish `hs : (⨆ i, u () i) = u () 0`. Apply `le_antisymm (ciSup_le fun i => h () 0 i (Fin.zero_le i))` to reduce the goal to its premises. Conclude with `le_ciSup (Set.finite_range _).bddAbove 0`. Establish `hi : (⨅ i, u () i) = u () 1`.

Apply `le_antisymm (ciInf_le (Set.finite_range _).bddBelow 1)` to reduce the goal to its premises. Conclude with `le_ciInf fun i => h () i 1 (Fin.le_last i)`. Simplify using `[spread, hs, hi]`.
-/
theorem spread_two (u : Wt Unit 2) (h : Dominant u) : spread u = u () 0 - u () 1 := by
  have h01 : u () 1 ≤ u () 0 := h () 0 1 (by decide)
  have hs : (⨆ i, u () i) = u () 0 := by
    apply le_antisymm (ciSup_le fun i => h () 0 i (Fin.zero_le i))
    exact le_ciSup (Set.finite_range _).bddAbove 0
  have hi : (⨅ i, u () i) = u () 1 := by
    apply le_antisymm (ciInf_le (Set.finite_range _).bddBelow 1)
    exact le_ciInf fun i => h () i 1 (Fin.le_last i)
  simp [spread, hs, hi]

end GlobalTheory.CompanionTheory.Ar.Top.Model
