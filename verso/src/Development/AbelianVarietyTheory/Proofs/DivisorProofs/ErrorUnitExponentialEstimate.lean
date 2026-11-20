import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement

noncomputable section

namespace GlobalTheory.ColNorms.NumMean

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms

/- English proof (translation)
Break down `hy.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0, Real.log_zero]`. Conclude with `hX`. Conclude with `(Real.log_le_iff_le_exp h0).2 h`.
-/
theorem log_le_of_le_exp {y X : ℝ} (hy : 0 ≤ y) (hX : 0 ≤ X) (h : y ≤ Real.exp X) : Real.log y ≤ X := by
  rcases hy.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]; exact hX
  · exact (Real.log_le_iff_le_exp h0).2 h

/- English proof (translation)
Use `log_le_of_le_exp (by positivity) (by linarith) ?_` and prove the remaining obligations. Rewrite using `[two_mul, Real.exp_add]`. Conclude with `mul_le_mul h1 h2 (by positivity) (by positivity)`.
-/
theorem log_mul_le {h h' : ℕ} {X : ℝ} (hX : 0 ≤ X) (h1 : (h : ℝ) ≤ Real.exp X) (h2 : (h' : ℝ) ≤ Real.exp X) :
    Real.log ((h : ℝ) * h') ≤ 2 * X := by
  refine log_le_of_le_exp (by positivity) (by linarith) ?_
  rw [two_mul, Real.exp_add]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

/- English proof (translation)
Establish `h : (4 * N.R.ord : ℝ) ≤ N.rd ^ 2` using `N.H.der.rd_sq_ge`. Establish `h0 : (0 : ℝ) ≤ N.rd`. Unfold `NumDatum.rd Formalism.HC.HostRaw.rd`. Check the signs of the components of the expression. Establish `ho : (1 : ℝ) ≤ N.R.ord` using `by exact_mod_cast N.R.ord_pos`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_rd (N : NumDatum) : 1 ≤ N.rd := by
  have h : (4 * N.R.ord : ℝ) ≤ N.rd ^ 2 := N.H.der.rd_sq_ge
  have h0 : (0 : ℝ) ≤ N.rd := by
    unfold NumDatum.rd Formalism.HC.HostRaw.rd
    positivity
  have ho : (1 : ℝ) ≤ N.R.ord := by exact_mod_cast N.R.ord_pos
  nlinarith

/- English proof (translation)
The claim follows from `Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le`.
-/
theorem one_le_L (s : Scale) : 1 ≤ s.L := Real.one_le_rpow s.one_lt_alt.le s.eps_pos.le

/- English proof (translation)
Use `Real.add_one_le_exp s.L` as an intermediate fact. Use `one_le_L s` as an intermediate fact. Unfold `Scale.b`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_le_b (s : Scale) : 2 ≤ s.b := by
  have := Real.add_one_le_exp s.L
  have := one_le_L s
  unfold Scale.b; linarith

/- English proof (translation)
Establish `h : Fintype.card R.A = R.ord` using `R.card_A`. Simplify using `[RPl, Ranks.f, Ranks.n, h]`.
-/
theorem card_RPl (R : Ranks) : (Fintype.card (RPl R) : ℝ) = R.f := by
  have h : Fintype.card R.A = R.ord := R.card_A
  simp [RPl, Ranks.f, Ranks.n, h]

/- English proof (translation)
Establish `: N.R.N j ≤ N.Nm`. Unfold `NumDatum.Nm Ranks.N`. Conclude with `Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _`. Conclude with `this` after adjusting the coercions.
-/
theorem N_le (N : NumDatum) {j : ℕ} (hj : j ≤ N.R.m) : (N.R.N j : ℝ) ≤ N.Nm := by
  have : N.R.N j ≤ N.Nm := by
    unfold NumDatum.Nm Ranks.N
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  exact_mod_cast this

/- English proof (translation)
Use `one_le_L s` as an intermediate fact. Use `log_le_of_le_exp hy (by positivity) ?_` and prove the remaining obligations. Rewrite using `[Real.exp_nat_mul]`. Conclude with `h`.
-/
theorem log_le_mul (s : Scale) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) (h : y ≤ s.b ^ k) : Real.log y ≤ k * s.L := by
  have := one_le_L s
  refine log_le_of_le_exp hy (by positivity) ?_
  rw [Real.exp_nat_mul]; exact h

end GlobalTheory.ColNorms.NumMean
