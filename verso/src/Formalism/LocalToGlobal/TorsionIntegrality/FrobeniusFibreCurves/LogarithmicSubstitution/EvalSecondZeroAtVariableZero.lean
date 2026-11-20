import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementA
import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartA

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.InvariantFactorPaths.G7 (at1 coeff_single_variable_series)
open MvPowerSeries (coeff constantCoeff)

section

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
The claim follows from `MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by fin_cases s · first | exact PowerSeries.constantCoeff_X | exact MvPowerSeries.constantCoeff_X () | (simp [PowerSeries.X]; done) | rfl · simp`.
-/
theorem hasSubst_eval_second_zero : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries K), 0] :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
    fin_cases s
    · first
        | exact PowerSeries.constantCoeff_X
        | exact MvPowerSeries.constantCoeff_X ()
        | (simp [PowerSeries.X]; done)
        | rfl
    · simp

/- English proof (translation)
Rewrite using `[MvPowerSeries.coe_substAlgHom]`. Both sides reduce to the same expression.
-/
theorem eval_second_zero_eq_algHom (h : MvPowerSeries (Fin 2) K) :
    ev0 h = MvPowerSeries.substAlgHom (hasSubst_eval_second_zero (K := K)) h := by
  rw [MvPowerSeries.coe_substAlgHom]
  rfl

/- English proof (translation)
Rewrite using `[eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_add]`.
-/
theorem evalYZero_add (g h : MvPowerSeries (Fin 2) K) : ev0 (g + h) = ev0 g + ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_add]

/- English proof (translation)
Rewrite using `[eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_sub]`.
-/
theorem eval_second_zero_sub (g h : MvPowerSeries (Fin 2) K) : ev0 (g - h) = ev0 g - ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_sub]

/- English proof (translation)
Rewrite using `[eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_neg]`.
-/
theorem eval_second_zero_neg (h : MvPowerSeries (Fin 2) K) : ev0 (-h) = -ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_neg]

/- English proof (translation)
Rewrite using `[eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_mul]`.
-/
theorem evalYZero_mul (g h : MvPowerSeries (Fin 2) K) : ev0 (g * h) = ev0 g * ev0 h := by
  rw [eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, eval_second_zero_eq_algHom, map_mul]

/- English proof (translation)
Unfold `ev0`. Rewrite using `[MvPowerSeries.subst_X hasSubst_eval_second_zero]`. Both sides reduce to the same expression.
-/
theorem eval_second_zero_X_zero : ev0 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = PowerSeries.X := by
  unfold ev0
  rw [MvPowerSeries.subst_X hasSubst_eval_second_zero]
  rfl

/- English proof (translation)
Unfold `ev0`. Rewrite using `[MvPowerSeries.subst_X hasSubst_eval_second_zero]`. Both sides reduce to the same expression.
-/
theorem eval_second_zero_X_one : ev0 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
  unfold ev0
  rw [MvPowerSeries.subst_X hasSubst_eval_second_zero]
  rfl

/- English proof (translation)
Establish `hu' : PowerSeries.HasSubst u` using `PowerSeries.HasSubst.of_constantCoeff_zero hu`. Unfold `ev0 PowerSeries.subst`. Rewrite using `[MvPowerSeries.subst_comp_subst_apply hu'.const hasSubst_eval_second_zero]`.
-/
theorem evalYZero_subst (f : PowerSeries K) {u : MvPowerSeries (Fin 2) K} (hu : constantCoeff u = 0) :
    ev0 (PowerSeries.subst u f) = PowerSeries.subst (ev0 u) f := by
  have hu' : PowerSeries.HasSubst u := PowerSeries.HasSubst.of_constantCoeff_zero hu
  unfold ev0 PowerSeries.subst
  rw [MvPowerSeries.subst_comp_subst_apply hu'.const hasSubst_eval_second_zero]

/- English proof (translation)
Unfold `PowerSeries.subst`. Establish `: (fun _ : Unit => (PowerSeries.X : PowerSeries K)) = MvPowerSeries.X`. Use function extensionality and compare the values at `u`. Consider the cases of `u`. Both sides reduce to the same expression.

Rewrite using `[this, MvPowerSeries.subst_self]`. Both sides reduce to the same expression.
-/
theorem psubst_X (f : PowerSeries K) : PowerSeries.subst (PowerSeries.X : PowerSeries K) f = f := by
  unfold PowerSeries.subst
  have : (fun _ : Unit => (PowerSeries.X : PowerSeries K)) = MvPowerSeries.X := by
    funext u
    cases u
    rfl
  rw [this, MvPowerSeries.subst_self]
  rfl

/- English proof (translation)
Unfold `atS`. Rewrite using `[evalYZero_subst _ (by simp), evalYZero_add, eval_second_zero_X_zero, eval_second_zero_X_one, add_zero, psubst_X]`.
-/
theorem eval_second_zero_at_sum (f : PowerSeries K) : ev0 (atS f) = f := by
  unfold atS
  rw [evalYZero_subst _ (by simp), evalYZero_add, eval_second_zero_X_zero, eval_second_zero_X_one, add_zero, psubst_X]

/- English proof (translation)
Unfold `atD`. Rewrite using `[evalYZero_subst _ (by simp), eval_second_zero_sub, eval_second_zero_X_zero, eval_second_zero_X_one, sub_zero, psubst_X]`.
-/
theorem eval_second_zero_at_difference (f : PowerSeries K) : ev0 (atD f) = f := by
  unfold atD
  rw [evalYZero_subst _ (by simp), eval_second_zero_sub, eval_second_zero_X_zero, eval_second_zero_X_one, sub_zero, psubst_X]

/- English proof (translation)
Unfold `at1`. Rewrite using `[evalYZero_subst _ (by simp), eval_second_zero_X_zero, psubst_X]`.
-/
theorem eval_second_zero_at_variable_zero (f : PowerSeries K) : ev0 (at1 0 f) = f := by
  unfold at1
  rw [evalYZero_subst _ (by simp), eval_second_zero_X_zero, psubst_X]

/- English proof (translation)
Establish `hc : ∀ m : ℕ, MvPowerSeries.coeff (Finsupp.single () k) ((PowerSeries.X : PowerSeries K) ^ m) = if k = m then 1 else 0` using `fun m => PowerSeries.coeff_X_pow k m`. Use `show MvPowerSeries.coeff (Finsupp.single () k) (ev0 h) = _`. Unfold `ev0`. Rewrite using `[MvPowerSeries.coeff_subst hasSubst_eval_second_zero, finsum_eq_single _ (Finsupp.single 0 k)]`. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Simplify using `only [Matrix.cons_val_zero, hc, if_true, smul_eq_mul, mul_one]`. Introduce `d hd`. Rewrite using `[Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Distinguish the cases in `h1 : d 1 = 0`.

Establish `hd0 : k ≠ d 0`. Introduce `hk`. Apply `hd` to reduce the goal to its premises. Use extensionality with `a`. Apply the tactic sequence `fin_cases a <;> simp [h1, hk]`.

Rewrite using `[h1, pow_zero, mul_one, hc, if_neg hd0, smul_zero]`. Rewrite using `[zero_pow h1, mul_zero, map_zero, smul_zero]`.
-/
private theorem coeff_ev0_eq_coeff_single_zero (h : MvPowerSeries (Fin 2) K) (k : ℕ) :
    PowerSeries.coeff k (ev0 h) = coeff (Finsupp.single 0 k) h := by
  have hc : ∀ m : ℕ, MvPowerSeries.coeff (Finsupp.single () k) ((PowerSeries.X : PowerSeries K) ^ m) =
      if k = m then 1 else 0 := fun m => PowerSeries.coeff_X_pow k m
  show MvPowerSeries.coeff (Finsupp.single () k) (ev0 h) = _
  unfold ev0
  rw [MvPowerSeries.coeff_subst hasSubst_eval_second_zero, finsum_eq_single _ (Finsupp.single 0 k)]
  · rw [Finsupp.prod_single_index (by simp)]
    simp only [Matrix.cons_val_zero, hc, if_true, smul_eq_mul, mul_one]
  · intro d hd
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    by_cases h1 : d 1 = 0
    · have hd0 : k ≠ d 0 := by
        intro hk
        apply hd
        ext a
        fin_cases a <;> simp [h1, hk]
      rw [h1, pow_zero, mul_one, hc, if_neg hd0, smul_zero]
    · rw [zero_pow h1, mul_zero, map_zero, smul_zero]

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[coeff_ev0_eq_coeff_single_zero, coeff_single_variable_series, PowerSeries.coeff_C]`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Simplify using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`.

Rewrite using `[if_neg hk, if_neg]`. Introduce `h`. Use `congrArg (fun n : Fin 2 →₀ ℕ => n 0) h` as an intermediate fact. Simplify using `at this`. Conclude with `hk this`.
-/
theorem restrictSecondZero_inVar_one (f : PowerSeries K) :
    ev0 (at1 1 f) = PowerSeries.C (PowerSeries.constantCoeff f) := by
  ext k
  rw [coeff_ev0_eq_coeff_single_zero, coeff_single_variable_series, PowerSeries.coeff_C]
  by_cases hk : k = 0
  · subst hk
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [if_neg hk, if_neg]
    intro h
    have := congrArg (fun n : Fin 2 →₀ ℕ => n 0) h
    simp at this
    exact hk this

/- English proof (translation)
Establish `hc : ∀ m : ℕ, MvPowerSeries.coeff (Finsupp.single () k) ((PowerSeries.X : PowerSeries K) ^ m) = if k = m then 1 else 0` using `fun m => PowerSeries.coeff_X_pow k m`. Use `show MvPowerSeries.coeff (Finsupp.single () k) (ev0 h) = _`. Unfold `ev0`. Rewrite using `[MvPowerSeries.coeff_subst hasSubst_eval_second_zero, finsum_eq_single _ (Finsupp.single 0 k)]`. Rewrite using `[Finsupp.prod_single_index (by simp)]`.

Simplify using `only [Matrix.cons_val_zero, hc, if_true, smul_eq_mul, mul_one]`. Introduce `d hd`. Rewrite using `[Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]`. Distinguish the cases in `h1 : d 1 = 0`.

Establish `hd0 : k ≠ d 0`. Introduce `hk`. Apply `hd` to reduce the goal to its premises. Use extensionality with `a`. Apply the tactic sequence `fin_cases a <;> simp [h1, hk]`.

Rewrite using `[h1, pow_zero, mul_one, hc, if_neg hd0, smul_zero]`. Rewrite using `[zero_pow h1, mul_zero, map_zero, smul_zero]`.
-/
theorem coeff_evalYZero (h : MvPowerSeries (Fin 2) K) (k : ℕ) :
    PowerSeries.coeff k (ev0 h) = coeff (Finsupp.single 0 k) h := by
  have hc : ∀ m : ℕ, MvPowerSeries.coeff (Finsupp.single () k) ((PowerSeries.X : PowerSeries K) ^ m) =
      if k = m then 1 else 0 := fun m => PowerSeries.coeff_X_pow k m
  show MvPowerSeries.coeff (Finsupp.single () k) (ev0 h) = _
  unfold ev0
  rw [MvPowerSeries.coeff_subst hasSubst_eval_second_zero, finsum_eq_single _ (Finsupp.single 0 k)]
  · rw [Finsupp.prod_single_index (by simp)]
    simp only [Matrix.cons_val_zero, hc, if_true, smul_eq_mul, mul_one]
  · intro d hd
    rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    by_cases h1 : d 1 = 0
    · have hd0 : k ≠ d 0 := by
        intro hk
        apply hd
        ext a
        fin_cases a <;> simp [h1, hk]
      rw [h1, pow_zero, mul_one, hc, if_neg hd0, smul_zero]
    · rw [zero_pow h1, mul_zero, map_zero, smul_zero]

/- English proof (translation)
Establish `hn' : n = Finsupp.single 0 (n 0)`. Use extensionality with `a`. Apply the tactic sequence `fin_cases a <;> simp [hn]`. Rewrite using `[hn', ← coeff_evalYZero, h0, map_zero]`.
-/
theorem coeff_eq_zero_of_eval_second_zero {h : MvPowerSeries (Fin 2) K} (h0 : ev0 h = 0) (n : Fin 2 →₀ ℕ)
    (hn : n 1 = 0) : coeff n h = 0 := by
  have hn' : n = Finsupp.single 0 (n 0) := by
    ext a
    fin_cases a <;> simp [hn]
  rw [hn', ← coeff_evalYZero, h0, map_zero]

end

/- English proof (translation)
Introduce `K _ _ h hw h0 h1`. Establish `hpp : ∀ (a : Fin 2) (m : Fin 2 →₀ ℕ), coeff m (pd a (pd a h)) = coeff (m + Finsupp.single a 2) h * (((m a : ℕ) : K) + 2) * (((m a : ℕ) : K) + 1)`. Introduce `a m`. Unfold `pd`. Rewrite using `[MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]`.

Establish `: m + Finsupp.single a 1 + Finsupp.single a 1 = m + Finsupp.single a 2`. Rewrite using `[add_assoc, ← Finsupp.single_add]`. Rewrite using `[this]`. Simplify using `only [Finsupp.add_apply, Finsupp.single_eq_same]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ j i : ℕ, coeff (Finsupp.single 0 i + Finsupp.single 1 j) h = 0`. Introduce `j`. Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`.

Introduce `i`. Break down `j with _ | _ | j` into its components or cases. Conclude with `coeff_eq_zero_of_eval_second_zero h0 _ (by simp)`. Use `congrArg (PowerSeries.coeff i) h1` as an intermediate fact. Unfold `pd at this`.

Rewrite `this` using `[coeff_evalYZero, map_zero, MvPowerSeries.coeff_pderiv]`. Simplify using `using this`. Establish `e` using `congrArg (coeff (Finsupp.single 0 i + Finsupp.single 1 j)) hw`. Rewrite `e` using `[hpp, hpp]`. Establish `e1 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (0 : Fin 2) 2 = Finsupp.single 0 (i + 2) + Finsupp.single 1 j`.

Apply the tactic sequence `ext a; fin_cases a <;> simp`. Establish `e2 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (1 : Fin 2) 2 = Finsupp.single 0 i + Finsupp.single 1 (j + 2)`. Apply the tactic sequence `ext a; fin_cases a <;> simp`. Rewrite `e` using `[e1, e2, ih j (by omega) (i + 2), zero_mul, zero_mul]`. Establish `hA : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2 ≠ 0`.

Establish `: ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2 = ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 + 1 : ℕ) : K) + 1` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `Nat.cast_add_one_ne_zero _`. Establish `hB : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero _`. Break down `mul_eq_zero.1 e.symm with e' | e'` into its components or cases.

Break down `mul_eq_zero.1 e' with e'' | e''` into its components or cases. Conclude with `e''`. Conclude with `absurd e'' hA`. Conclude with `absurd e' hB`. Use extensionality with `n`.

Establish `hn : n = Finsupp.single 0 (n 0) + Finsupp.single 1 (n 1)`. Apply the tactic sequence `ext a; fin_cases a <;> simp`. Rewrite using `[hn, key, map_zero]`.
-/
theorem wave_equation_unique : WaveUnique := by
  intro K _ _ h hw h0 h1
  have hpp : ∀ (a : Fin 2) (m : Fin 2 →₀ ℕ), coeff m (pd a (pd a h)) =
      coeff (m + Finsupp.single a 2) h * (((m a : ℕ) : K) + 2) * (((m a : ℕ) : K) + 1) := by
    intro a m
    unfold pd
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]
    have : m + Finsupp.single a 1 + Finsupp.single a 1 = m + Finsupp.single a 2 := by
      rw [add_assoc, ← Finsupp.single_add]
    rw [this]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    push_cast
    ring
  have key : ∀ j i : ℕ, coeff (Finsupp.single 0 i + Finsupp.single 1 j) h = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro i
      rcases j with _ | _ | j
      · exact coeff_eq_zero_of_eval_second_zero h0 _ (by simp)
      · have := congrArg (PowerSeries.coeff i) h1
        unfold pd at this
        rw [coeff_evalYZero, map_zero, MvPowerSeries.coeff_pderiv] at this
        simpa using this
      · have e := congrArg (coeff (Finsupp.single 0 i + Finsupp.single 1 j)) hw
        rw [hpp, hpp] at e
        have e1 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (0 : Fin 2) 2
            = Finsupp.single 0 (i + 2) + Finsupp.single 1 j := by
          ext a; fin_cases a <;> simp
        have e2 : Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single (1 : Fin 2) 2
            = Finsupp.single 0 i + Finsupp.single 1 (j + 2) := by
          ext a; fin_cases a <;> simp
        rw [e1, e2, ih j (by omega) (i + 2), zero_mul, zero_mul] at e
        have hA : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2 ≠ 0 := by
          have : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 2
              = ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 + 1 : ℕ) : K) + 1 := by push_cast; ring
          rw [this]; exact Nat.cast_add_one_ne_zero _
        have hB : ((((Finsupp.single 0 i + Finsupp.single 1 j : Fin 2 →₀ ℕ)) 1 : ℕ) : K) + 1 ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        rcases mul_eq_zero.1 e.symm with e' | e'
        · rcases mul_eq_zero.1 e' with e'' | e''
          · exact e''
          · exact absurd e'' hA
        · exact absurd e' hB
  ext n
  have hn : n = Finsupp.single 0 (n 0) + Finsupp.single 1 (n 1) := by
    ext a; fin_cases a <;> simp
  rw [hn, key, map_zero]

section

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Unfold `atS`. Unfold `pd`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst (by simp), map_add, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]`. Apply the tactic sequence `fin_cases i <;> simp`.
-/
theorem pd_atS (i : Fin 2) (f : PowerSeries K) : pd i (atS f) = atS (dz f) := by
  unfold atS
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst (by simp), map_add, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]
  fin_cases i <;> simp

/- English proof (translation)
Unfold `atD`. Unfold `pd`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst (by simp), map_sub, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_zero_series_at_difference (f : PowerSeries K) : pd 0 (atD f) = atD (dz f) := by
  unfold atD
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst (by simp), map_sub, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]
  simp

/- English proof (translation)
Unfold `atD`. Unfold `pd`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst (by simp), map_sub, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_one_series_at_difference (f : PowerSeries K) : pd 1 (atD f) = -atD (dz f) := by
  unfold atD
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst (by simp), map_sub, MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_X]
  simp

/- English proof (translation)
Unfold `at1`. Unfold `pd`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst (by simp), MvPowerSeries.pderiv_X]`. Simplify using the standard rewrite rules.
-/
theorem partialDeriv_inVar_self (i : Fin 2) (f : PowerSeries K) : pd i (at1 i f) = at1 i (dz f) := by
  unfold at1
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst (by simp), MvPowerSeries.pderiv_X]
  simp

/- English proof (translation)
Unfold `at1`. Unfold `pd`. Rewrite using `[Formalism.G.LogCR.pderiv_psubst (by simp), MvPowerSeries.pderiv_X, Pi.single_eq_of_ne hij, mul_zero]`.
-/
theorem pderiv_at_variable_of_ne {i j : Fin 2} (hij : j ≠ i) (f : PowerSeries K) : pd i (at1 j f) = 0 := by
  unfold at1
  unfold pd
  rw [Formalism.G.LogCR.pderiv_psubst (by simp), MvPowerSeries.pderiv_X, Pi.single_eq_of_ne hij, mul_zero]

/- English proof (translation)
Simplify using `only [par0, two_mul, map_add, map_sub, pd_atS, pderiv_zero_series_at_difference, partialDeriv_inVar_self, pderiv_at_variable_of_ne (show (1 : Fin 2) ≠ 0 by decide)]`. Normalize the expressions using the abelian group laws.
-/
theorem pderiv_zero_parallelogram_defect (f : PowerSeries K) :
    pd 0 (par0 f) = atS (dz f) + atD (dz f) - 2 * at1 0 (dz f) := by
  simp only [par0, two_mul, map_add, map_sub, pd_atS, pderiv_zero_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  abel

/- English proof (translation)
Simplify using `only [par0, two_mul, map_add, map_sub, pd_atS, pderiv_one_series_at_difference, partialDeriv_inVar_self, pderiv_at_variable_of_ne (show (0 : Fin 2) ≠ 1 by decide)]`. Normalize the expressions using the abelian group laws.
-/
theorem pderiv_one_parallelogram_defect (f : PowerSeries K) :
    pd 1 (par0 f) = atS (dz f) - atD (dz f) - 2 * at1 1 (dz f) := by
  simp only [par0, two_mul, map_add, map_sub, pd_atS, pderiv_one_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  abel

end

/- English proof (translation)
Introduce `K _ _ f`. Rewrite using `[pderiv_zero_parallelogram_defect, pderiv_one_parallelogram_defect]`. Simplify using `only [two_mul, map_add, map_sub, map_neg, pd_atS, pderiv_zero_series_at_difference, pderiv_one_series_at_difference, partialDeriv_inVar_self, pderiv_at_variable_of_ne (show (1 : Fin 2) ≠ 0 by decide), pderiv_at_variable_of_ne (show (0 : Fin 2) ≠ 1 by decide)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wave_operator_kills : WaveKills := by
  intro K _ _ f
  rw [pderiv_zero_parallelogram_defect, pderiv_one_parallelogram_defect]
  simp only [two_mul, map_add, map_sub, map_neg, pd_atS, pderiv_zero_series_at_difference, pderiv_one_series_at_difference, partialDeriv_inVar_self,
    pderiv_at_variable_of_ne (show (1 : Fin 2) ≠ 0 by decide), pderiv_at_variable_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
  ring

/- English proof (translation)
Introduce `K _ _ f hf0 hf1`. Establish `hd0 : PowerSeries.constantCoeff (dz f) = 0`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add, hf1, zero_mul]`. Prove the components needed by the constructor for the conclusion. Simplify using `only [par0, two_mul]`.

Rewrite using `[eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, evalYZero_add, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, hf0, map_zero]`. Normalize the expressions using the abelian group laws. Rewrite using `[pderiv_one_parallelogram_defect]`. Simplify using `only [two_mul]`. Rewrite using `[eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, restrictSecondZero_inVar_one, hd0, map_zero]`.

Normalize the expressions using the abelian group laws.
-/
theorem parallelogram_cauchy_equation : ParCauchy := by
  intro K _ _ f hf0 hf1
  have hd0 : PowerSeries.constantCoeff (dz f) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, zero_add, hf1,
      zero_mul]
  constructor
  · simp only [par0, two_mul]
    rw [eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, evalYZero_add, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, eval_second_zero_at_variable_zero, restrictSecondZero_inVar_one, hf0,
      map_zero]
    abel
  · rw [pderiv_one_parallelogram_defect]
    simp only [two_mul]
    rw [eval_second_zero_sub, eval_second_zero_sub, evalYZero_add, eval_second_zero_at_sum, eval_second_zero_at_difference, restrictSecondZero_inVar_one, hd0, map_zero]
    abel

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_dq {K : Type} [Field K] [CharZero K] (P : PowerSeries K) (n : Fin 2 →₀ ℕ) :
    coeff n (dq P) =
      if Even (n 0) ∧ Even (n 1) then PowerSeries.coeff (n 0 + n 1 + 2) P else 0 := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Introduce `h`.

Use extensionality with `a`. Apply the tactic sequence `fin_cases a <;> simp [h]`.
-/
theorem eq_single_zero_iff (n : Fin 2 →₀ ℕ) : n = Finsupp.single 0 (n 0) ↔ n 1 = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    ext a
    fin_cases a <;> simp [h]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Introduce `h`.

Use extensionality with `a`. Apply the tactic sequence `fin_cases a <;> simp [h]`.
-/
theorem eq_single_one_iff (n : Fin 2 →₀ ℕ) : n = Finsupp.single 1 (n 1) ↔ n 0 = 0 := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    ext a
    fin_cases a <;> simp [h]

/- English proof (translation)
Introduce `K _ _ P hodd`. Establish `hc : ∀ m, ¬ Even m → PowerSeries.coeff m P = 0` using `fun m hm => hodd m (Nat.not_even_iff_odd.1 hm)`. Establish `hev : ∀ m, 2 ≤ m → (Even (m - 2) ↔ Even m)`. Introduce `m hm`. Rewrite using `[Nat.even_sub hm]`.

Simplify using the standard rewrite rules. Establish `main : ∀ i j : ℕ, (if j = 0 then PowerSeries.coeff i P else 0) - (if i = 0 then PowerSeries.coeff j P else 0) = (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P else 0) else 0) - (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + …`. Introduce `i j`. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Rewrite using `[if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), sub_zero]`.

Break down `Nat.lt_or_ge i 2 with hi | hi` into its components or cases. Rewrite using `[if_neg (by omega : ¬ 2 ≤ i)] interval_cases i`. Simplify using the standard rewrite rules. Simplify using `[hc 1 (by decide)]`. Rewrite using `[if_pos hi, if_neg (by omega : i ≠ 0), sub_zero, show i - 2 + 0 + 2 = i by omega]`.

Simplify using `only [hev i hi]`. Distinguish the cases in `he : Even i`. Simplify using `[he]`. Simplify using `[he, hc i he]`. Rewrite using `[if_neg (by omega : j ≠ 0)]`.

Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Rewrite using `[if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), zero_sub, zero_sub]`. Break down `Nat.lt_or_ge j 2 with hj2 | hj2` into its components or cases. Establish `: j = 1` using `by omega`. Substitute `this` using the available equality.

Simplify using `[hc 1 (by decide)]`. Rewrite using `[if_pos hj2, show 0 + (j - 2) + 2 = j by omega]`. Simplify using `only [hev j hj2]`. Distinguish the cases in `he : Even j`. Simplify using `[he]`.

Simplify using `[he, hc j he]`. Rewrite using `[if_neg (by omega : i ≠ 0)]`. Establish `t1 : (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0`. Distinguish the cases in `hi2 : 2 ≤ i`. Rewrite using `[if_pos hi2, show i - 2 + j + 2 = i + j by omega]`.

Simplify using `only [hev i hi2]`. Establish `: i = 1` using `by omega`. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Establish `t2 : (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + (j - 2) + 2) P else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0`.

Distinguish the cases in `hj2 : 2 ≤ j`. Rewrite using `[if_pos hj2, show i + (j - 2) + 2 = i + j by omega]`. Simplify using `only [hev j hj2]`. Establish `: j = 1` using `by omega`. Substitute `this` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[t1, t2]`. Simplify using the standard rewrite rules. Use extensionality with `n`. Rewrite using `[map_sub, coeff_single_variable_series, coeff_single_variable_series, sub_mul, map_sub, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, coeff_dq, coeff_dq]`.

Simplify using `only [eq_single_zero_iff, eq_single_one_iff, Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, one_mul]`. Simplify using `using main (n 0) (n 1)`.
-/
theorem difference_quotient_rule_holds : DqRule := by
  intro K _ _ P hodd
  have hc : ∀ m, ¬ Even m → PowerSeries.coeff m P = 0 := fun m hm => hodd m (Nat.not_even_iff_odd.1 hm)
  have hev : ∀ m, 2 ≤ m → (Even (m - 2) ↔ Even m) := by
    intro m hm
    rw [Nat.even_sub hm]
    simp
  have main : ∀ i j : ℕ, (if j = 0 then PowerSeries.coeff i P else 0) -
      (if i = 0 then PowerSeries.coeff j P else 0) =
      (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P else 0) else 0) -
      (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + (j - 2) + 2) P else 0)
        else 0) := by
    intro i j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), sub_zero]
      rcases Nat.lt_or_ge i 2 with hi | hi
      · rw [if_neg (by omega : ¬ 2 ≤ i)]
        interval_cases i
        · simp
        · simp [hc 1 (by decide)]
      · rw [if_pos hi, if_neg (by omega : i ≠ 0), sub_zero, show i - 2 + 0 + 2 = i by omega]
        simp only [hev i hi]
        by_cases he : Even i
        · simp [he]
        · simp [he, hc i he]
    · rw [if_neg (by omega : j ≠ 0)]
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [if_pos rfl, if_neg (by omega : ¬ 2 ≤ 0), zero_sub, zero_sub]
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · have : j = 1 := by omega
          subst this
          simp [hc 1 (by decide)]
        · rw [if_pos hj2, show 0 + (j - 2) + 2 = j by omega]
          simp only [hev j hj2]
          by_cases he : Even j
          · simp [he]
          · simp [he, hc j he]
      · rw [if_neg (by omega : i ≠ 0)]
        have t1 : (if 2 ≤ i then (if Even (i - 2) ∧ Even j then PowerSeries.coeff (i - 2 + j + 2) P
            else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0 := by
          by_cases hi2 : 2 ≤ i
          · rw [if_pos hi2, show i - 2 + j + 2 = i + j by omega]
            simp only [hev i hi2]
          · have : i = 1 := by omega
            subst this
            simp
        have t2 : (if 2 ≤ j then (if Even i ∧ Even (j - 2) then PowerSeries.coeff (i + (j - 2) + 2) P
            else 0) else 0) = if Even i ∧ Even j then PowerSeries.coeff (i + j) P else 0 := by
          by_cases hj2 : 2 ≤ j
          · rw [if_pos hj2, show i + (j - 2) + 2 = i + j by omega]
            simp only [hev j hj2]
          · have : j = 1 := by omega
            subst this
            simp
        rw [t1, t2]
        simp
  ext n
  rw [map_sub, coeff_single_variable_series, coeff_single_variable_series, sub_mul, map_sub, MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, coeff_dq, coeff_dq]
  simp only [eq_single_zero_iff, eq_single_one_iff, Finsupp.single_le_iff, Finsupp.tsub_apply,
    Finsupp.single_apply, one_mul]
  simpa using main (n 0) (n 1)

end Formalism.L2.Th1.B
