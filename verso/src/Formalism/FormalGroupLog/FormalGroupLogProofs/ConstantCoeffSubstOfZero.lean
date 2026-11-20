import Formalism.FormalGroupLog.Statement
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule

noncomputable section

open MvPowerSeries

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

/- English proof (translation)
Apply the tactic sequence `exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv])`.
-/
theorem hs2 {σ : Type*} {u v : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) : MvPowerSeries.HasSubst ![u, v] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv])

/- English proof (translation)
Apply the tactic sequence `exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv, hw])`.
-/
theorem hs3 {σ : Type*} {u v w : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (hv : constantCoeff v = 0) (hw : constantCoeff w = 0) : MvPowerSeries.HasSubst ![u, v, w] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hu, hv, hw])

/- English proof (translation)
Rewrite using `[MvPowerSeries.subst_comp_subst_apply (hs2 hu hv) hb]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`.
-/
theorem subst2_subst {σ τ : Type*} (Φ : MvPowerSeries (Fin 2) R) {u v : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) {b : σ → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    (Φ.subst ![u, v]).subst b = Φ.subst ![u.subst b, v.subst b] := by
  rw [MvPowerSeries.subst_comp_subst_apply (hs2 hu hv) hb]
  congr 1
  funext i
  fin_cases i <;> rfl

/- English proof (translation)
Establish `hu' : MvPowerSeries.HasSubst (fun _ : Unit => u)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)`. Unfold `PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hu' hb]`.
-/
theorem psubst_subst {σ τ : Type*} (φ : PowerSeries R) {u : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (φ.subst u).subst b = φ.subst (u.subst b) := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hu' hb]

/- English proof (translation)
Establish `hb' : MvPowerSeries.HasSubst b` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hb`. Rewrite using `[MvPowerSeries.constantCoeff_subst hb', finsum_eq_single _ 0]`. Simplify using the standard rewrite rules. Introduce `d hd`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, d i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hd (Finsupp.ext h)`. Establish `h0 : constantCoeff (d.prod fun s e => b s ^ e) = 0`. Rewrite using `[Finsupp.prod, map_prod]`.

Apply `Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)` to reduce the goal to its premises. Rewrite using `[map_pow, hb i, zero_pow hi]`. Rewrite using `[h0, smul_zero]`.
-/
theorem constantCoeff_subst_of_zero {σ τ : Type*} [Finite σ] [Finite τ]
    (Φ : MvPowerSeries σ R) {b : σ → MvPowerSeries τ R} (hb : ∀ i, constantCoeff (b i) = 0) :
    constantCoeff (Φ.subst b) = constantCoeff Φ := by
  have hb' : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [MvPowerSeries.constantCoeff_subst hb', finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : constantCoeff (d.prod fun s e => b s ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      rw [map_pow, hb i, zero_pow hi]
    rw [h0, smul_zero]

/- English proof (translation)
Establish `h : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1)` using `by simp`. Rewrite using `[h]`. Conclude with `IsUnit.map _ (isUnit_iff_ne_zero.2 (by positivity))`.
-/
theorem isUnit_natCast_succ [Algebra ℚ R] (n : ℕ) : IsUnit ((n : R) + 1) := by
  have h : ((n : R) + 1) = algebraMap ℚ R ((n : ℚ) + 1) := by simp
  rw [h]
  exact IsUnit.map _ (isUnit_iff_ne_zero.2 (by positivity))

variable (F : FormalGroup R)

def omegaF : PowerSeries R :=
  MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]
    (MvPowerSeries.pderiv R 1 F.toPowerSeries)

/- English proof (translation)
Apply the tactic sequence `have := constantCoeff_subst_of_zero (MvPowerSeries.pderiv R 1 F.toPowerSeries) (b := ![(PowerSeries.X : PowerSeries R), 0]) (fun i => by fin_cases i <;> simp [PowerSeries.X])`. Rewrite using `[omegaF, PowerSeries.constantCoeff, this, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]`. Simplify using `using F.lin_coeff_Y`.
-/
theorem constantCoeff_omega : PowerSeries.constantCoeff (omegaF F) = 1 := by
  have := constantCoeff_subst_of_zero (MvPowerSeries.pderiv R 1 F.toPowerSeries)
    (b := ![(PowerSeries.X : PowerSeries R), 0]) (fun i => by fin_cases i <;> simp [PowerSeries.X])
  rw [omegaF, PowerSeries.constantCoeff, this, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simpa using F.lin_coeff_Y

/- English proof (translation)
Apply the tactic sequence `exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [PowerSeries.X])`.
-/
theorem hb0 : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries R), 0] := by
  exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [PowerSeries.X])

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hX0 : constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = 0 := by
  simp
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hX1 : constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = 0 := by
  simp

/- English proof (translation)
Rewrite using `[psubst_subst φ F.zero_constantCoeff hb0]`. Establish `: MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] F.toPowerSeries = PowerSeries.X` using `F.Xzero_eq_X`. Rewrite using `[this, PowerSeries.X_subst]`.
-/
theorem eval_zero_subst_law (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (φ.subst F.toPowerSeries) = φ := by
  rw [psubst_subst φ F.zero_constantCoeff hb0]
  have : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] F.toPowerSeries =
      PowerSeries.X := F.Xzero_eq_X
  rw [this, PowerSeries.X_subst]

/- English proof (translation)
Rewrite using `[atY, psubst_subst φ hX1 hb0, subst_X hb0]`. Simplify using `[PowerSeries.subst_zero_eq_C_constantCoeff]`. Both sides reduce to the same expression.
-/
theorem evalYZero_atY (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (atY φ) =
      PowerSeries.C (PowerSeries.constantCoeff φ) := by
  rw [atY, psubst_subst φ hX1 hb0, subst_X hb0]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff]
  rfl

/- English proof (translation)
Use `congrArg (MvPowerSeries.pderiv R 1) hg.2.2` as an intermediate fact. Rewrite `this` using `[pderiv_psubst F.zero_constantCoeff, map_add, atX, atY, pderiv_psubst hX0, pderiv_psubst hX1]`. Simplify `this` using `[pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]`.
-/
theorem pderiv_log {g : PowerSeries R} (hg : IsLog F g) :
    (PowerSeries.derivative R g).subst F.toPowerSeries * MvPowerSeries.pderiv R 1 F.toPowerSeries =
      atY (PowerSeries.derivative R g) := by
  have := congrArg (MvPowerSeries.pderiv R 1) hg.2.2
  rw [pderiv_psubst F.zero_constantCoeff, map_add, atX, atY, pderiv_psubst hX0,
    pderiv_psubst hX1] at this
  simpa [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)] using this

/- English proof (translation)
Use `congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]) (pderiv_log F hg)` as an intermediate fact. Rewrite `this` using `[subst_mul hb0, eval_zero_subst_law, evalYZero_atY]`. Rewrite using `[omegaF, this]`. Establish `h1 : PowerSeries.constantCoeff (PowerSeries.derivative R g) = 1`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, hg.2.1]`.

Simplify using the standard rewrite rules. Rewrite using `[h1, map_one]`.
-/
theorem derivative_log_mul_omega {g : PowerSeries R} (hg : IsLog F g) :
    PowerSeries.derivative R g * omegaF F = 1 := by
  have := congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]) (pderiv_log F hg)
  rw [subst_mul hb0, eval_zero_subst_law, evalYZero_atY] at this
  rw [omegaF, this]
  have h1 : PowerSeries.constantCoeff (PowerSeries.derivative R g) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, hg.2.1]
    simp
  rw [h1, map_one]

/- English proof (translation)
Establish `hd : PowerSeries.derivative R f = PowerSeries.derivative R g`. Establish `hu` using `PowerSeries.mul_invOfUnit (omegaF F) 1 (by simp [constantCoeff_omega])`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, hu, mul_one]`. Use `_ = PowerSeries.derivative R g * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by`.

Rewrite using `[derivative_log_mul_omega F hf, derivative_log_mul_omega F hg]`. Use `_ = PowerSeries.derivative R g := by rw [mul_assoc, hu, mul_one]`. Use extensionality with `n`. Consider the cases of `n with`. Consider the case `zero => simpa using hf.1.trans hg.1.symm`.

Consider the case `succ n`. Use `congrArg (PowerSeries.coeff n) hd` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]`. Conclude with `(isUnit_natCast_succ (R := R) n).mul_left_cancel (by`. Rewrite using `[mul_comm, this, mul_comm])`.
-/
theorem log_unique [Algebra ℚ R] {f g : PowerSeries R} (hf : IsLog F f) (hg : IsLog F g) :
    f = g := by
  have hd : PowerSeries.derivative R f = PowerSeries.derivative R g := by
    have hu := PowerSeries.mul_invOfUnit (omegaF F) 1 (by simp [constantCoeff_omega])
    calc PowerSeries.derivative R f
        = PowerSeries.derivative R f * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
          rw [mul_assoc, hu, mul_one]
      _ = PowerSeries.derivative R g * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
          rw [derivative_log_mul_omega F hf, derivative_log_mul_omega F hg]
      _ = PowerSeries.derivative R g := by rw [mul_assoc, hu, mul_one]
  ext n
  cases n with
  | zero => simpa using hf.1.trans hg.1.symm
  | succ n =>
    have := congrArg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at this
    exact (isUnit_natCast_succ (R := R) n).mul_left_cancel (by
      rw [mul_comm, this, mul_comm])

end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

/- English proof (translation)
Rewrite using `[← MvPowerSeries.coe_substAlgHom hb, map_zero]`.
-/
theorem subst_zero' {σ τ : Type*} {b : σ → MvPowerSeries τ R} (hb : MvPowerSeries.HasSubst b) :
    (0 : MvPowerSeries σ R).subst b = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom hb, map_zero]

/- English proof (translation)
Establish `h : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = MvPowerSeries.X`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> rfl`. Rewrite using `[h, MvPowerSeries.subst_self, id]`.
-/
theorem subst_XX (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = Φ := by
  have h : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1] = MvPowerSeries.X := by
    funext i
    fin_cases i <;> rfl
  rw [h, MvPowerSeries.subst_self, id]

/- English proof (translation)
Establish `hu' : MvPowerSeries.HasSubst (fun _ : Unit => u)` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)`. Unfold `omegaF`. Unfold `PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hb0 hu']`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `MvPowerSeries.subst_X hu' ()`. Conclude with `subst_zero' hu'`.
-/
theorem omega_subst {σ : Type*} {u : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (F : FormalGroup R) :
    (omegaF F).subst u = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst ![u, 0] := by
  have hu' : MvPowerSeries.HasSubst (fun _ : Unit => u) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hu)
  unfold omegaF
  unfold PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hb0 hu']
  congr 1
  funext i
  fin_cases i
  · exact MvPowerSeries.subst_X hu' ()
  · exact subst_zero' hu'

variable (F : FormalGroup R)

/- English proof (translation)
Establish `hFc : constantCoeff F.toPowerSeries = 0` using `F.zero_constantCoeff`. Establish `hY : ∀ i, constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = 0` using `fun i => by`. Simplify using the standard rewrite rules. Establish `hG : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 1]) = 0`. Apply the tactic sequence `rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]`.

Establish `hH : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2]) = 0`. Apply the tactic sequence `rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]`. Establish `dG : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 1]) = 0`. Apply the tactic sequence `rw [pderiv_subst (fun i => by fin_cases i <;> simp)]`. Simplify using `[Fin.sum_univ_two, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide), pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]`.

Establish `dH : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2]) = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2]`. Apply the tactic sequence `rw [pderiv_subst (fun i => by fin_cases i <;> simp)]`. Simplify using `[Fin.sum_univ_two, pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]`. Establish `E` using `congrArg (MvPowerSeries.pderiv R 2) F.assoc`. Apply the tactic sequence `rw [pderiv_subst (fun i => by fin_cases i <;> simp [hG]), pderiv_subst (fun i => by fin_cases i <;> simp [hH])] at E`.

Simplify using `only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, dG, dH, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide), mul_zero, zero_add, mul_one] at E`. Establish `hc3 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0]` using `hs3 (by simp) (by simp) (by simp)`. Establish `E'` using `congrArg (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0]) E`. Rewrite `E'` using `[subst_mul hc3, subst2_subst _ hG (hY 2) hc3, subst2_subst _ (hY 0) hH hc3, subst2_subst _ (hY 1) (hY 2) hc3, subst2_subst _ (hY 0) (hY 1) hc3, subst2_subst _ (hY 1) (hY 2) hc3]`. Simplify using `only [subst_X hc3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at E'`.

Rewrite `E'` using `[subst_XX, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX1), subst_XX]`. Rewrite using `[omega_subst hFc, atY, omega_subst hX1]`. Conclude with `E'`.
-/
theorem omega_key :
    (omegaF F).subst F.toPowerSeries =
      MvPowerSeries.pderiv R 1 F.toPowerSeries * atY (omegaF F) := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hY : ∀ i, constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) R) = 0 := fun i => by
    simp
  have hG : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have hH : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = 0 := by
    rw [constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have dG : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 1]) = 0 := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp)]
    simp [Fin.sum_univ_two, pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide),
      pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  have dH : MvPowerSeries.pderiv R 2 (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R),
      MvPowerSeries.X 2]) = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) R), MvPowerSeries.X 2] := by
    rw [pderiv_subst (fun i => by fin_cases i <;> simp)]
    simp [Fin.sum_univ_two, pderiv_X_of_ne (show (1 : Fin 3) ≠ 2 by decide)]
  have E := congrArg (MvPowerSeries.pderiv R 2) F.assoc
  rw [pderiv_subst (fun i => by fin_cases i <;> simp [hG]),
    pderiv_subst (fun i => by fin_cases i <;> simp [hH])] at E
  simp only [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, dG, dH, pderiv_X_self,
    pderiv_X_of_ne (show (0 : Fin 3) ≠ 2 by decide), mul_zero, zero_add, mul_one] at E
  have hc3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0] :=
    hs3 (by simp) (by simp) (by simp)
  have E' := congrArg (MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 1, 0]) E
  rw [subst_mul hc3, subst2_subst _ hG (hY 2) hc3, subst2_subst _ (hY 0) hH hc3,
    subst2_subst _ (hY 1) (hY 2) hc3, subst2_subst _ (hY 0) (hY 1) hc3,
    subst2_subst _ (hY 1) (hY 2) hc3] at E'
  simp only [subst_X hc3, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at E'
  rw [subst_XX, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX1), subst_XX] at E'
  rw [omega_subst hFc, atY, omega_subst hX1]
  exact E'

end Formalism.G.LogP

namespace Formalism.G.LogP

open Formalism.G.LogCR

variable {R : Type*} [CommRing R]

/- English proof (translation)
Rewrite using `[← PowerSeries.coe_substAlgHom ha, map_one]`.
-/
theorem psubst_one {σ : Type*} {a : MvPowerSeries σ R} (ha : PowerSeries.HasSubst a) :
    (1 : PowerSeries R).subst a = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha, map_one]

/- English proof (translation)
Rewrite using `[MvPowerSeries.rescale_eq_subst]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `fin_cases s <;> simp`.
-/
theorem subst_X0_zero_eq_rescale (Φ : MvPowerSeries (Fin 2) R) :
    Φ.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = rescale ![1, 0] Φ := by
  rw [MvPowerSeries.rescale_eq_subst]
  congr 1
  funext s
  fin_cases s <;> simp

/- English proof (translation)
Rewrite `h0` using `[subst_X0_zero_eq_rescale]`. Use extensionality with `n`. Rewrite using `[map_zero]`. Distinguish the cases in `hn : n 1 = 0`. Establish `h1` using `congrArg (MvPowerSeries.coeff n) h0`.

Rewrite `h1` using `[MvPowerSeries.coeff_rescale, map_zero]`. Establish `hprod : (n.prod fun s m => (![1, 0] : Fin 2 → R) s ^ m) = 1`. Rewrite using `[Finsupp.prod]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `s hs`.

Use `fin_cases s`. Simplify using the standard rewrite rules. Conclude with `absurd hn (Finsupp.mem_support_iff.mp hs)`. Rewrite `h1` using `[hprod, one_mul]`. Conclude with `h1`.

Establish `hm : n = (n - Finsupp.single 1 1) + Finsupp.single 1 1`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp <;> omega`. Establish `h1` using `congrArg (MvPowerSeries.coeff (n - Finsupp.single 1 1)) hD`. Rewrite `h1` using `[MvPowerSeries.coeff_pderiv, map_zero, ← hm]`.

Establish `hu : IsUnit ((((n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 : ℕ) : R) + 1)` using `isUnit_natCast_succ _`. Conclude with `(hu.mul_left_eq_zero).mp h1`.
-/
theorem eq_zero_of_pderiv_one [Algebra ℚ R] {h : MvPowerSeries (Fin 2) R}
    (hD : MvPowerSeries.pderiv R 1 h = 0)
    (h0 : h.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0) : h = 0 := by
  rw [subst_X0_zero_eq_rescale] at h0
  ext n
  rw [map_zero]
  by_cases hn : n 1 = 0
  · have h1 := congrArg (MvPowerSeries.coeff n) h0
    rw [MvPowerSeries.coeff_rescale, map_zero] at h1
    have hprod : (n.prod fun s m => (![1, 0] : Fin 2 → R) s ^ m) = 1 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_one
      intro s hs
      fin_cases s
      · simp
      · exact absurd hn (Finsupp.mem_support_iff.mp hs)
    rw [hprod, one_mul] at h1
    exact h1
  · have hm : n = (n - Finsupp.single 1 1) + Finsupp.single 1 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    have h1 := congrArg (MvPowerSeries.coeff (n - Finsupp.single 1 1)) hD
    rw [MvPowerSeries.coeff_pderiv, map_zero, ← hm] at h1
    have hu : IsUnit ((((n - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 : ℕ) : R) + 1) := isUnit_natCast_succ _
    exact (hu.mul_left_eq_zero).mp h1

variable (F : FormalGroup R)

def lam : PowerSeries R := PowerSeries.invOfUnit (omegaF F) 1

/- English proof (translation)
Conclude with `PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_omega, Units.val_one])`.
-/
theorem omega_mul_lam : omegaF F * lam F = 1 := by
  exact PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_omega, Units.val_one])

variable [Algebra ℚ R]

def logF : PowerSeries R :=
  PowerSeries.mk fun n => if n = 0 then 0 else
    algebraMap ℚ R (1 / (n : ℚ)) * PowerSeries.coeff (n - 1) (lam F)

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_derivative]`. Unfold `logF`. Rewrite using `[PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, mul_comm, ← mul_assoc]`. Establish `h : ((n : R) + 1) * algebraMap ℚ R (1 / ((n + 1 : ℕ) : ℚ)) = 1`.

Rewrite using `[show ((n : R) + 1) = algebraMap ℚ R ((n + 1 : ℕ) : ℚ) by simp, ← map_mul, mul_one_div_cancel (by positivity), map_one]`. Rewrite using `[h, one_mul]`.
-/
theorem derivative_logF : PowerSeries.derivative R (logF F) = lam F := by
  ext n
  rw [PowerSeries.coeff_derivative]
  unfold logF
  rw [PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero n), Nat.add_sub_cancel, mul_comm, ← mul_assoc]
  have h : ((n : R) + 1) * algebraMap ℚ R (1 / ((n + 1 : ℕ) : ℚ)) = 1 := by
    rw [show ((n : R) + 1) = algebraMap ℚ R ((n + 1 : ℕ) : ℚ) by simp, ← map_mul,
      mul_one_div_cancel (by positivity), map_one]
  rw [h, one_mul]

/- English proof (translation)
Establish `hFc : constantCoeff F.toPowerSeries = 0` using `F.zero_constantCoeff`. Establish `hFs : PowerSeries.HasSubst F.toPowerSeries` using `PowerSeries.HasSubst.of_constantCoeff_zero hFc`. Establish `hX1s : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R)` using `PowerSeries.HasSubst.of_constantCoeff_zero hX1`. Establish `hc0 : PowerSeries.constantCoeff (logF F) = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk, if_pos rfl]`.

Use `⟨hc0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[logF, PowerSeries.coeff_mk, if_neg one_ne_zero, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, lam, PowerSeries.constantCoeff_invOfUnit]`. Simplify using the standard rewrite rules. Establish `hω` using `omega_mul_lam F`. Establish `hF1 : (lam F).subst F.toPowerSeries * (omegaF F).subst F.toPowerSeries = 1`.

Rewrite using `[← PowerSeries.subst_mul hFs, mul_comm, hω, psubst_one hFs]`. Establish `hY1 : atY (lam F) * atY (omegaF F) = 1`. Rewrite using `[atY, atY, ← PowerSeries.subst_mul hX1s, mul_comm, hω, psubst_one hX1s]`. Establish `hk` using `omega_key F`. Establish `hD : MvPowerSeries.pderiv R 1 ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)) = 0`.

Rewrite using `[map_sub, map_sub, pderiv_psubst hFc, atX, atY, pderiv_psubst hX0, pderiv_psubst hX1, derivative_logF, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]`. Take the linear combination `(-((lam F).subst F.toPowerSeries * MvPowerSeries.pderiv R 1 F.toPowerSeries)) * hY1 + atY (lam F) * hF1 - (lam F).subst F.toPowerSeries * atY (lam F) * hk`. Establish `hc2 : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0]` using `hs2 (by simp) (by simp)`. Establish `h0 : ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)).subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0`. Rewrite using `[subst_sub hc2, subst_sub hc2, atX, atY, psubst_subst _ hFc hc2, psubst_subst _ hX0 hc2, psubst_subst _ hX1 hc2, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX0), subst_X hc2, subst_X hc2]`.

Simplify using `[PowerSeries.subst_zero_of_constantCoeff_zero hc0]`. Use `eq_zero_of_pderiv_one hD h0` as an intermediate fact. Rewrite `this` using `[sub_sub, sub_eq_zero]`. Conclude with `this`.
-/
theorem logF_isLog : IsLog F (logF F) := by
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hFs : PowerSeries.HasSubst F.toPowerSeries := PowerSeries.HasSubst.of_constantCoeff_zero hFc
  have hX1s : PowerSeries.HasSubst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX1
  have hc0 : PowerSeries.constantCoeff (logF F) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, logF, PowerSeries.coeff_mk, if_pos rfl]
  refine ⟨hc0, ?_, ?_⟩
  · rw [logF, PowerSeries.coeff_mk, if_neg one_ne_zero, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, lam, PowerSeries.constantCoeff_invOfUnit]
    simp
  · have hω := omega_mul_lam F
    have hF1 : (lam F).subst F.toPowerSeries * (omegaF F).subst F.toPowerSeries = 1 := by
      rw [← PowerSeries.subst_mul hFs, mul_comm, hω, psubst_one hFs]
    have hY1 : atY (lam F) * atY (omegaF F) = 1 := by
      rw [atY, atY, ← PowerSeries.subst_mul hX1s, mul_comm, hω, psubst_one hX1s]
    have hk := omega_key F
    have hD : MvPowerSeries.pderiv R 1
        ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)) = 0 := by
      rw [map_sub, map_sub, pderiv_psubst hFc, atX, atY, pderiv_psubst hX0, pderiv_psubst hX1,
        derivative_logF, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      linear_combination (-((lam F).subst F.toPowerSeries *
        MvPowerSeries.pderiv R 1 F.toPowerSeries)) * hY1 + atY (lam F) * hF1 -
        (lam F).subst F.toPowerSeries * atY (lam F) * hk
    have hc2 : MvPowerSeries.HasSubst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] := hs2 (by simp) (by simp)
    have h0 : ((logF F).subst F.toPowerSeries - atX (logF F) - atY (logF F)).subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R), 0] = 0 := by
      rw [subst_sub hc2, subst_sub hc2, atX, atY, psubst_subst _ hFc hc2, psubst_subst _ hX0 hc2,
        psubst_subst _ hX1 hc2, F.add_zero (PowerSeries.HasSubst.of_constantCoeff_zero hX0),
        subst_X hc2, subst_X hc2]
      simp [PowerSeries.subst_zero_of_constantCoeff_zero hc0]
    have := eq_zero_of_pderiv_one hD h0
    rw [sub_sub, sub_eq_zero] at this
    exact this

end Formalism.G.LogP

namespace Formalism.G.LogP

variable {R : Type*} [CommRing R]

/- English proof (translation)
Establish `: Invertible (PowerSeries.coeff 1 f)` using `hf1 ▸ invertibleOne`. Establish `hfs : PowerSeries.HasSubst f` using `PowerSeries.HasSubst.of_constantCoeff_zero' hf0`. Establish `inv : ∀ c : MvPowerSeries σ R, constantCoeff c = 0 → f.substInv.subst (f.subst c) = c`. Introduce `c hc`. Establish `hcs : PowerSeries.HasSubst c` using `PowerSeries.HasSubst.of_constantCoeff_zero hc`.

Rewrite using `[← PowerSeries.subst_comp_subst_apply hfs hcs, PowerSeries.subst_substInv_left f hf0, PowerSeries.subst_X hcs]`. Rewrite using `[← inv a ha, h, inv b hb]`.
-/
theorem psubst_injective {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : PowerSeries.coeff 1 f = 1) {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (h : f.subst a = f.subst b) : a = b := by
  have : Invertible (PowerSeries.coeff 1 f) := hf1 ▸ invertibleOne
  have hfs : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have inv : ∀ c : MvPowerSeries σ R, constantCoeff c = 0 → f.substInv.subst (f.subst c) = c := by
    intro c hc
    have hcs : PowerSeries.HasSubst c := PowerSeries.HasSubst.of_constantCoeff_zero hc
    rw [← PowerSeries.subst_comp_subst_apply hfs hcs, PowerSeries.subst_substInv_left f hf0,
      PowerSeries.subst_X hcs]
  rw [← inv a ha, h, inv b hb]

end Formalism.G.LogP

/- English proof (translation)
Introduce `R _ _ F`. Conclude with `⟨Formalism.G.LogP.logF F, Formalism.G.LogP.logF_isLog F, fun g hg => Formalism.G.LogP.log_unique F hg (Formalism.G.LogP.logF_isLog F)⟩`.
-/
theorem Formalism.G.log_exists_unique : Formalism.G.LogExistsUnique := by
  intro R _ _ F
  exact ⟨Formalism.G.LogP.logF F, Formalism.G.LogP.logF_isLog F,
    fun g hg => Formalism.G.LogP.log_unique F hg (Formalism.G.LogP.logF_isLog F)⟩

/- English proof (translation)
Introduce `R _ _ F`. Use `⟨?_⟩` and prove the remaining obligations. Establish `hf` using `Formalism.G.LogP.logF_isLog F`. Use `set f := Formalism.G.LogP.logF F`. Establish `hFc : constantCoeff F.toPowerSeries = 0` using `F.zero_constantCoeff`.

Establish `hc : MvPowerSeries.HasSubst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]` using `Formalism.G.LogP.hs2 (by simp) (by simp)`. Establish `hFs : constantCoeff (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) = 0`. Apply the tactic sequence `rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]`. Establish `h1 : f.subst (F.toPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) = f.subst F.toPowerSeries`. Rewrite using `[← Formalism.G.LogP.psubst_subst f hFc hc, hf.2.2, subst_add hc, Formalism.G.atX, Formalism.G.atY, Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX0 hc, Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX1 hc, subst_X hc, subst_X hc]`.

Simplify using `only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Rewrite using `[add_comm]`. Conclude with `(Formalism.G.LogP.psubst_injective hf.1 hf.2.1 hFs hFc h1).symm`.
-/
theorem Formalism.G.is_comm_of_rat : Formalism.G.IsCommOfRat := by
  intro R _ _ F
  refine ⟨?_⟩
  have hf := Formalism.G.LogP.logF_isLog F
  set f := Formalism.G.LogP.logF F
  have hFc : constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
  have hc : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0] :=
    Formalism.G.LogP.hs2 (by simp) (by simp)
  have hFs : constantCoeff (F.toPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (fun i => by fin_cases i <;> simp), hFc]
  have h1 : f.subst (F.toPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R), MvPowerSeries.X 0]) =
      f.subst F.toPowerSeries := by
    rw [← Formalism.G.LogP.psubst_subst f hFc hc, hf.2.2, subst_add hc, Formalism.G.atX, Formalism.G.atY,
      Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX0 hc, Formalism.G.LogP.psubst_subst f Formalism.G.LogP.hX1 hc,
      subst_X hc, subst_X hc]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [add_comm]
  exact (Formalism.G.LogP.psubst_injective hf.1 hf.2.1 hFs hFc h1).symm
