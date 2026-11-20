import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementB
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Formalism.GL3MeanSquares.HookFormulaTorsion.IntegralInverse

noncomputable section

namespace Formalism.L2.Th1.B

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)
open Formalism.G.LogP (hs2 subst2_subst psubst_subst psubst_injective)

/- English proof (translation)
The claim follows from `psubst_injective h0 h1 hU hV h`.
-/
theorem log_inj {K : Type} [Field K] {ι : Type} (l : PowerSeries K)
    (h0 : PowerSeries.constantCoeff l = 0) (h1 : PowerSeries.coeff 1 l = 1)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (h : PowerSeries.subst U l = PowerSeries.subst V l) :
    U = V :=
  psubst_injective h0 h1 hU hV h

section Alg

variable {K : Type} [Field K] {ι : Type}

/- English proof (translation)
Unfold `at1`. Rewrite using `[psubst_subst f (by simp) hb, MvPowerSeries.subst_X hb]`.
-/
theorem subst_at_variable_eq_subst (f : PowerSeries K) (x : Fin 2) {b : Fin 2 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (at1 x f) = PowerSeries.subst (b x) f := by
  unfold at1
  rw [psubst_subst f (by simp) hb, MvPowerSeries.subst_X hb]

/- English proof (translation)
Establish `hb` using `hs2 hU hV`. Unfold `cob`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb, psubst_subst f hF hb, subst_at_variable_eq_subst f 0 hb, subst_at_variable_eq_subst f 1 hb]`. Both sides reduce to the same expression.
-/
theorem law_cob_subst (F : MvPowerSeries (Fin 2) K) (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] (cob F f) =
      PowerSeries.subst (MvPowerSeries.subst ![U, V] F) f - PowerSeries.subst U f -
        PowerSeries.subst V f := by
  have hb := hs2 hU hV
  unfold cob
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hb,
    psubst_subst f hF hb, subst_at_variable_eq_subst f 0 hb, subst_at_variable_eq_subst f 1 hb]
  rfl

/- English proof (translation)
The claim follows from `MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hU hV) (fun i => by fin_cases i <;> simpa) hF`.
-/
theorem law_constantCoeff_subst2 (F : MvPowerSeries (Fin 2) K)
    (hF : MvPowerSeries.constantCoeff F = 0) (U V : MvPowerSeries ι K)
    (hU : MvPowerSeries.constantCoeff U = 0) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst ![U, V] F) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hs2 hU hV)
    (fun i => by fin_cases i <;> simpa) hF

/- English proof (translation)
Establish `e : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = (![1, 0] : Fin 2 → K) • MvPowerSeries.X`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `fin_cases s <;> simp`. Rewrite using `[e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `[Fin.prod_univ_two, hn]`.
-/
theorem law_coeff_axis0 (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) (hn : n 1 = 0) :
    MvPowerSeries.coeff n H = MvPowerSeries.coeff n
      (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H) := by
  have e : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] =
      (![1, 0] : Fin 2 → K) • MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp
  rw [e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two, hn]

/- English proof (translation)
Establish `e : ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] = (![0, 1] : Fin 2 → K) • MvPowerSeries.X`. Use function extensionality and compare the values at `s`. Apply the tactic sequence `fin_cases s <;> simp`. Rewrite using `[e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `[Fin.prod_univ_two, hn]`.
-/
theorem law_coeff_axis1 (H : MvPowerSeries (Fin 2) K) (n : Fin 2 →₀ ℕ) (hn : n 0 = 0) :
    MvPowerSeries.coeff n H = MvPowerSeries.coeff n
      (MvPowerSeries.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] H) := by
  have e : ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] =
      (![0, 1] : Fin 2 → K) • MvPowerSeries.X := by
    funext s
    fin_cases s <;> simp
  rw [e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (by simp)]
  simp [Fin.prod_univ_two, hn]

end Alg

section Norm

variable {K : Type} [NormedField K] {ι : Type}

/- English proof (translation)
Take `⟨hF, -, -, -, hc⟩` from `h`. Establish `e` using `law_cob_subst F hF l U V hU hV`. Rewrite `e` using `[hc, Formalism.G.LogP.subst_zero' (hs2 hU hV)]`. Take the linear combination `-e`.
-/
theorem law_subst {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![U, V] F) l =
      PowerSeries.subst U l + PowerSeries.subst V l := by
  obtain ⟨hF, -, -, -, hc⟩ := h
  have e := law_cob_subst F hF l U V hU hV
  rw [hc, Formalism.G.LogP.subst_zero' (hs2 hU hV)] at e
  linear_combination -e

/- English proof (translation)
The claim follows from `log_inj l h.2.2.1 h.2.2.2.1 _ _ (law_constantCoeff_subst2 F h.1 U V hU hV) hW ((law_subst h U V hU hV).trans e)`.
-/
theorem law_eq_of_log {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V W : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) (hW : MvPowerSeries.constantCoeff W = 0)
    (e : PowerSeries.subst U l + PowerSeries.subst V l = PowerSeries.subst W l) :
    MvPowerSeries.subst ![U, V] F = W :=
  log_inj l h.2.2.1 h.2.2.2.1 _ _ (law_constantCoeff_subst2 F h.1 U V hU hV) hW
    ((law_subst h U V hU hV).trans e)

/- English proof (translation)
The claim follows from `PowerSeries.subst_zero_of_constantCoeff_zero h0`.
-/
theorem law_subst_zero (l : PowerSeries K) (h0 : PowerSeries.constantCoeff l = 0) :
    PowerSeries.subst (0 : MvPowerSeries ι K) l = 0 :=
  PowerSeries.subst_zero_of_constantCoeff_zero h0

/- English proof (translation)
The claim follows from `law_eq_of_log h U 0 U hU (by simp) hU (by rw [law_subst_zero l h.2.2.1, add_zero])`.
-/
theorem law_right_zero {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0) :
    MvPowerSeries.subst ![U, 0] F = U :=
  law_eq_of_log h U 0 U hU (by simp) hU (by rw [law_subst_zero l h.2.2.1, add_zero])

/- English proof (translation)
The claim follows from `law_eq_of_log h 0 V V (by simp) hV hV (by rw [law_subst_zero l h.2.2.1, zero_add])`.
-/
theorem law_left_zero {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (V : MvPowerSeries ι K) (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![0, V] F = V :=
  law_eq_of_log h 0 V V (by simp) hV hV (by rw [law_subst_zero l h.2.2.1, zero_add])

/- English proof (translation)
The claim follows from `law_eq_of_log h U V _ hU hV (law_constantCoeff_subst2 F h.1 V U hV hU) (by rw [law_subst h V U hV hU, add_comm])`.
-/
theorem law_comm {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (U V : MvPowerSeries ι K) (hU : MvPowerSeries.constantCoeff U = 0)
    (hV : MvPowerSeries.constantCoeff V = 0) :
    MvPowerSeries.subst ![U, V] F = MvPowerSeries.subst ![V, U] F :=
  law_eq_of_log h U V _ hU hV (law_constantCoeff_subst2 F h.1 V U hV hU)
    (by rw [law_subst h V U hV hU, add_comm])

/- English proof (translation)
Use `fin_cases j`. Rewrite using `[law_coeff_axis0 F _ (by simp), law_right_zero h _ (by simp)]`. Simplify using `[MvPowerSeries.coeff_X]`. Rewrite using `[law_coeff_axis1 F _ (by simp), law_left_zero h _ (by simp)]`. Simplify using `[MvPowerSeries.coeff_X]`.
-/
theorem law_coeff_single {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    (j : Fin 2) : MvPowerSeries.coeff (Finsupp.single j 1) F = 1 := by
  fin_cases j
  · rw [law_coeff_axis0 F _ (by simp), law_right_zero h _ (by simp)]
    simp [MvPowerSeries.coeff_X]
  · rw [law_coeff_axis1 F _ (by simp), law_left_zero h _ (by simp)]
    simp [MvPowerSeries.coeff_X]

end Norm

/- English proof (translation)
Introduce `K _ _ _ F l f h hf`. Establish `hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `h00 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Introduce `n hn`. Break down `hn with hn | hn` into its components or cases. Rewrite using `[law_coeff_axis1 _ n hn, law_cob_subst F h.1 f _ _ h00 hX1, law_left_zero h _ hX1, law_subst_zero f hf]`. Simplify using the standard rewrite rules. Rewrite using `[law_coeff_axis0 _ n hn, law_cob_subst F h.1 f _ _ hX0 h00, law_right_zero h _ hX0, law_subst_zero f hf]`.

Simplify using the standard rewrite rules. Unfold `swap2`. Rewrite using `[law_cob_subst F h.1 f _ _ hX1 hX0, law_comm h _ _ hX1 hX0, Formalism.G.LogP.subst_XX]`. Unfold `cob at1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coboundary_rules_hold : CobRules := by
  intro K _ _ _ F l f h hf
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have h00 : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  refine ⟨?_, ?_⟩
  · intro n hn
    rcases hn with hn | hn
    · rw [law_coeff_axis1 _ n hn, law_cob_subst F h.1 f _ _ h00 hX1, law_left_zero h _ hX1,
        law_subst_zero f hf]
      simp
    · rw [law_coeff_axis0 _ n hn, law_cob_subst F h.1 f _ _ hX0 h00, law_right_zero h _ hX0,
        law_subst_zero f hf]
      simp
  · unfold swap2
    rw [law_cob_subst F h.1 f _ _ hX1 hX0, law_comm h _ _ hX1 hX0, Formalism.G.LogP.subst_XX]
    unfold cob at1
    ring

section Ultra

variable {K : Type} [NormedField K]

/- English proof (translation)
Introduce `n`. Rewrite using `[MvPowerSeries.coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem law_integral_X {ι : Type} (x : ι) : Integral (MvPowerSeries.X x : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

/- English proof (translation)
Establish `: PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0` using `by simp`. Conclude with `this`.
-/
theorem law_c0X : MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by
  have : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
  exact this

/- English proof (translation)
Introduce `n`. Simplify using the standard rewrite rules.
-/
theorem law_integral_zero {ι : Type} : Integral (0 : MvPowerSeries ι K) := by
  intro n
  simp

end Ultra

/- English proof (translation)
Introduce `K _ _ _ F l h`. Take `⟨hF, hFi, hl0, hl1, -⟩` from `id h`. Set `T : Fin 2 → MvPowerSeries (Fin 2) K` to `![MvPowerSeries.X 0, F]`. Set `J' : Matrix (Fin 2) (Fin 2) K` to `!![1, 0; -1, 1]`. Apply the tactic sequence `obtain ⟨X', hX0, hXi, hXT, -⟩ := Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement K (Fin 2) T J' (fun i => by fin_cases i <;> simp [T, hF]) (fun i => by fin_cases i`.

Conclude with `law_integral_X 0`. Conclude with `hFi)`. Apply the tactic sequence `(fun i j => by fin_cases i <;> fin_cases j <;> simp [J'])`. Use the proof step `(by`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[T, J', Matrix.mul_apply, Fin.sum_univ_two, law_coeff_single h, MvPowerSeries.coeff_X, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)])`. Establish `hsX : MvPowerSeries.HasSubst X'` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hX0`. Establish `e0 : X' 0 = MvPowerSeries.X 0`. Use `hXT 0` as an intermediate fact.

Simplify `this` using `[T, MvPowerSeries.subst_X hsX]`. Establish `e1 : MvPowerSeries.subst X' F = MvPowerSeries.X 1` using `hXT 1`. Establish `hb : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries K), 0]` using `Formalism.G.LogP.hb0`. Set `i : PowerSeries K` to `MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] (X' 1)`. Establish `hi0 : PowerSeries.constantCoeff i = 0` using `MvPowerSeries.constantCoeff_subst_eq_zero hb (fun k => by fin_cases k`.

Conclude with `law_c0X`. Conclude with `map_zero _) (hX0 1)`. Establish `hii : Integral (ι` using `Unit) i := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun k => by fin_cases k`. Conclude with `law_c0X`. Conclude with `map_zero _)`.

Use the proof step `(fun k => by fin_cases k`. Conclude with `law_integral_X ()`. Conclude with `law_integral_zero) (hXi 1)`. Establish `e2 : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), i] F = 0`. Use `congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0]) e1` as an intermediate fact.

Rewrite `this` using `[MvPowerSeries.subst_comp_subst_apply hsX hb, MvPowerSeries.subst_X hb]`. Establish `this' : _ = (0 : PowerSeries K)` using `this`. Rewrite using `[← this']`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Use `fin_cases k`. Use `show _ = MvPowerSeries.subst _ (X' 0)`. Rewrite using `[e0, MvPowerSeries.subst_X hb]`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Use `⟨i, hi0, hii, ?_⟩` and prove the remaining obligations. Establish `e3` using `law_subst h (PowerSeries.X : PowerSeries K) i law_c0X hi0`. Rewrite `e3` using `[e2, law_subst_zero l hl0]`. Establish `e4 : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l` using `PowerSeries.X_subst l`. Rewrite `e3` using `[e4]`.

Take the linear combination `-e3`.
-/
theorem formal_inverse_exists : InvExists := by
  intro K _ _ _ F l h
  obtain ⟨hF, hFi, hl0, hl1, -⟩ := id h
  let T : Fin 2 → MvPowerSeries (Fin 2) K := ![MvPowerSeries.X 0, F]
  let J' : Matrix (Fin 2) (Fin 2) K := !![1, 0; -1, 1]
  obtain ⟨X', hX0, hXi, hXT, -⟩ := Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement K (Fin 2) T J'
    (fun i => by fin_cases i <;> simp [T, hF])
    (fun i => by
      fin_cases i
      · exact law_integral_X 0
      · exact hFi)
    (fun i j => by fin_cases i <;> fin_cases j <;> simp [J'])
    (by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [T, J', Matrix.mul_apply, Fin.sum_univ_two, law_coeff_single h,
          MvPowerSeries.coeff_X, Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)])
  have hsX : MvPowerSeries.HasSubst X' := MvPowerSeries.hasSubst_of_constantCoeff_zero hX0
  have e0 : X' 0 = MvPowerSeries.X 0 := by
    have := hXT 0
    simpa [T, MvPowerSeries.subst_X hsX] using this
  have e1 : MvPowerSeries.subst X' F = MvPowerSeries.X 1 := hXT 1
  have hb : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries K), 0] := Formalism.G.LogP.hb0
  let i : PowerSeries K := MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0] (X' 1)
  have hi0 : PowerSeries.constantCoeff i = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hb
      (fun k => by
        fin_cases k
        · exact law_c0X
        · exact map_zero _) (hX0 1)
  have hii : Integral (ι := Unit) i :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst'
      (fun k => by
        fin_cases k
        · exact law_c0X
        · exact map_zero _)
      (fun k => by
        fin_cases k
        · exact law_integral_X ()
        · exact law_integral_zero) (hXi 1)
  have e2 : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), i] F = 0 := by
    have := congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), 0]) e1
    rw [MvPowerSeries.subst_comp_subst_apply hsX hb, MvPowerSeries.subst_X hb] at this
    have this' : _ = (0 : PowerSeries K) := this
    rw [← this']
    congr 1
    funext k
    fin_cases k
    · show _ = MvPowerSeries.subst _ (X' 0)
      rw [e0, MvPowerSeries.subst_X hb]
      rfl
    · rfl
  refine ⟨i, hi0, hii, ?_⟩
  have e3 := law_subst h (PowerSeries.X : PowerSeries K) i law_c0X hi0
  rw [e2, law_subst_zero l hl0] at e3
  have e4 : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l := PowerSeries.X_subst l
  rw [e4] at e3
  linear_combination -e3

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst D` using `PowerSeries.HasSubst.of_constantCoeff_zero' hD`. Establish `key : ∀ g : PowerSeries K, PowerSeries.coeff 1 g = PowerSeries.constantCoeff (PowerSeries.derivative K g)`. Introduce `g`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]`. Simplify using the standard rewrite rules.

Establish `hc : ∀ g : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.subst D g : PowerSeries K) = PowerSeries.constantCoeff g`. Introduce `g`. Establish `e : g = PowerSeries.C (PowerSeries.constantCoeff g) + (g - PowerSeries.C (PowerSeries.constantCoeff g))` using `by ring`. Use `conv_lhs => rw [e]`. Rewrite using `[PowerSeries.subst_add hs, map_add, PowerSeries.subst_C]`.

Use `PowerSeries.constantCoeff_subst_eq_zero (a := D) hD (g - PowerSeries.C (PowerSeries.constantCoeff g)) (by simp)` as an intermediate fact. Use `erw [this, add_zero]`. Conclude with `MvPowerSeries.constantCoeff_C _`. Rewrite using `[key, PowerSeries.derivative_subst hs, map_mul, hc, ← key, ← key]`.
-/
theorem law_coeff_one_subst {K : Type} [Field K] (l D : PowerSeries K)
    (hD : PowerSeries.constantCoeff D = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst D l : PowerSeries K) =
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 D := by
  have hs : PowerSeries.HasSubst D := PowerSeries.HasSubst.of_constantCoeff_zero' hD
  have key : ∀ g : PowerSeries K, PowerSeries.coeff 1 g =
      PowerSeries.constantCoeff (PowerSeries.derivative K g) := by
    intro g
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  have hc : ∀ g : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.subst D g : PowerSeries K) =
      PowerSeries.constantCoeff g := by
    intro g
    have e : g = PowerSeries.C (PowerSeries.constantCoeff g) +
        (g - PowerSeries.C (PowerSeries.constantCoeff g)) := by ring
    conv_lhs => rw [e]
    rw [PowerSeries.subst_add hs, map_add, PowerSeries.subst_C]
    have := PowerSeries.constantCoeff_subst_eq_zero (a := D) hD
      (g - PowerSeries.C (PowerSeries.constantCoeff g)) (by simp)
    erw [this, add_zero]
    exact MvPowerSeries.constantCoeff_C _
  rw [key, PowerSeries.derivative_subst hs, map_mul, hc, ← key, ← key]

/- English proof (translation)
Introduce `K _ _ _ F l h h2`. Take `⟨hF, hFi, hl0, hl1, -⟩` from `id h`. Establish `hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0` using `by simp`. Establish `two0 : (2 : K) ≠ 0` using `two_ne_zero`. Set `D : PowerSeries K` to `MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] F`.

Establish `hD0 : PowerSeries.constantCoeff D = 0` using `law_constantCoeff_subst2 F hF _ _ hX hX`. Apply the tactic sequence `have hDi : Integral (ι := Unit) D := Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun k => by fin_cases k <;> exact law_c0X) (fun k => by fin_cases k <;> exact law_integral_X ()) hFi`. Establish `eX : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l` using `PowerSeries.X_subst l`. Establish `hD1 : PowerSeries.coeff 1 D = 2`. Establish `e` using `law_subst h (PowerSeries.X : PowerSeries K) PowerSeries.X hX hX`.

Rewrite `e` using `[eX]`. Establish `e'` using `congrArg (PowerSeries.coeff 1) e`. Rewrite `e'` using `[law_coeff_one_subst l D hD0, map_add, hl1]`. Take the linear combination `e'`. Take `⟨X', hX0, hXi, hXT, -⟩` from `Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement K Unit (fun _ => D) (Matrix.of fun _ _ => (2 : K)⁻¹) (fun _ => hD0) (fun _ => hDi) (fun _ _ => by rw [Matrix.of_apply, norm_inv, h2, inv_one]) (by`.

Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply, Matrix.one_apply]`. Establish `: MvPowerSeries.coeff (Finsupp.single (default : Unit) 1) D = 2` using `hD1`. Rewrite using `[this, mul_inv_cancel₀ two0, if_pos trivial])`. Establish `hsX : MvPowerSeries.HasSubst X'` using `MvPowerSeries.hasSubst_of_constantCoeff_zero hX0`.

Set `g : PowerSeries K` to `X' ()`. Establish `hg0 : PowerSeries.constantCoeff g = 0` using `hX0 ()`. Establish `e1 : MvPowerSeries.subst ![g, g] F = (PowerSeries.X : PowerSeries K)`. Use `hXT ()` as an intermediate fact. Rewrite `this` using `[subst2_subst F hX hX hsX]`.

Establish `eg : MvPowerSeries.subst X' (PowerSeries.X : PowerSeries K) = g` using `MvPowerSeries.subst_X hsX ()`. Rewrite `this` using `[eg]`. Conclude with `this`. Use `⟨g, hg0, hXi (), ?_⟩` and prove the remaining obligations. Establish `e3` using `law_subst h g g hg0 hg0`.

Rewrite `e3` using `[e1, eX]`. Establish `hC : (PowerSeries.C (2 : K)⁻¹ : PowerSeries K) * 2 = 1`. Establish `: (2 : PowerSeries K) = PowerSeries.C (2 : K)` using `(map_ofNat PowerSeries.C 2).symm`. Rewrite using `[this, ← map_mul, inv_mul_cancel₀ two0, map_one]`. Take the linear combination `(-(PowerSeries.C (2 : K)⁻¹ : PowerSeries K)) * e3 + (-(PowerSeries.subst g l : PowerSeries K)) * hC`.
-/
theorem formal_halving_exists : HalfExists := by
  intro K _ _ _ F l h h2
  obtain ⟨hF, hFi, hl0, hl1, -⟩ := id h
  have hX : PowerSeries.constantCoeff (PowerSeries.X : PowerSeries K) = 0 := by simp
  have two0 : (2 : K) ≠ 0 := two_ne_zero
  let D : PowerSeries K := MvPowerSeries.subst ![(PowerSeries.X : PowerSeries K), PowerSeries.X] F
  have hD0 : PowerSeries.constantCoeff D = 0 := law_constantCoeff_subst2 F hF _ _ hX hX
  have hDi : Integral (ι := Unit) D :=
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun k => by fin_cases k <;> exact law_c0X)
      (fun k => by fin_cases k <;> exact law_integral_X ()) hFi
  have eX : PowerSeries.subst (PowerSeries.X : PowerSeries K) l = l := PowerSeries.X_subst l
  have hD1 : PowerSeries.coeff 1 D = 2 := by
    have e := law_subst h (PowerSeries.X : PowerSeries K) PowerSeries.X hX hX
    rw [eX] at e
    have e' := congrArg (PowerSeries.coeff 1) e
    rw [law_coeff_one_subst l D hD0, map_add, hl1] at e'
    linear_combination e'
  obtain ⟨X', hX0, hXi, hXT, -⟩ := Formalism.HermitianLattices.ExpSeriesBivariate.integralInverse_statement K Unit (fun _ => D)
    (Matrix.of fun _ _ => (2 : K)⁻¹) (fun _ => hD0) (fun _ => hDi)
    (fun _ _ => by rw [Matrix.of_apply, norm_inv, h2, inv_one])
    (by
      ext i j
      simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.of_apply,
        Matrix.one_apply]
      have : MvPowerSeries.coeff (Finsupp.single (default : Unit) 1) D = 2 := hD1
      rw [this, mul_inv_cancel₀ two0, if_pos trivial])
  have hsX : MvPowerSeries.HasSubst X' := MvPowerSeries.hasSubst_of_constantCoeff_zero hX0
  let g : PowerSeries K := X' ()
  have hg0 : PowerSeries.constantCoeff g = 0 := hX0 ()
  have e1 : MvPowerSeries.subst ![g, g] F = (PowerSeries.X : PowerSeries K) := by
    have := hXT ()
    rw [subst2_subst F hX hX hsX] at this
    have eg : MvPowerSeries.subst X' (PowerSeries.X : PowerSeries K) = g :=
      MvPowerSeries.subst_X hsX ()
    rw [eg] at this
    exact this
  refine ⟨g, hg0, hXi (), ?_⟩
  have e3 := law_subst h g g hg0 hg0
  rw [e1, eX] at e3
  have hC : (PowerSeries.C (2 : K)⁻¹ : PowerSeries K) * 2 = 1 := by
    have : (2 : PowerSeries K) = PowerSeries.C (2 : K) := (map_ofNat PowerSeries.C 2).symm
    rw [this, ← map_mul, inv_mul_cancel₀ two0, map_one]
  linear_combination (-(PowerSeries.C (2 : K)⁻¹ : PowerSeries K)) * e3 +
    (-(PowerSeries.subst g l : PowerSeries K)) * hC

section Diff

variable {K : Type} [NormedField K]

/- English proof (translation)
The claim follows from `PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf`.
-/
theorem constantCoeff_series_at_variable {ι : Type} (x : ι) (f : PowerSeries K)
    (hf : PowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (at1 x f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf

/- English proof (translation)
The claim follows from `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries ι K)) (fun _ => by simp) (fun _ => law_integral_X x) hf`.
-/
theorem integral_series_at_variable [IsUltrametricDist K] {ι : Type} (x : ι) (f : PowerSeries K)
    (hf : Integral (ι := Unit) f) : Integral (at1 x f) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (φ := fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries ι K))
    (fun _ => by simp) (fun _ => law_integral_X x) hf

/- English proof (translation)
Establish `hs : PowerSeries.HasSubst i` using `PowerSeries.HasSubst.of_constantCoeff_zero' hi.1`. Establish `hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K)` using `PowerSeries.HasSubst.X x`. Unfold `at1`. Rewrite using `[← PowerSeries.subst_comp_subst_apply hs hx, hi.2.2, ← PowerSeries.coe_substAlgHom hx, map_neg]`.
-/
theorem log_subst_formal_inverse {ι : Type} {l i : PowerSeries K} (hi : IsInv l i) (x : ι) :
    PowerSeries.subst (at1 x i) l = -at1 x l := by
  have hs : PowerSeries.HasSubst i := PowerSeries.HasSubst.of_constantCoeff_zero' hi.1
  have hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) :=
    PowerSeries.HasSubst.X x
  unfold at1
  rw [← PowerSeries.subst_comp_subst_apply hs hx, hi.2.2, ← PowerSeries.coe_substAlgHom hx, map_neg]

/- English proof (translation)
The claim follows from `law_constantCoeff_subst2 F h.1 _ _ (by simp) (constantCoeff_series_at_variable 1 i hi.1)`.
-/
theorem law_constantCoeff_FI {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K}
    (h : LawLog F l) (hi : IsInv l i) : MvPowerSeries.constantCoeff (FI F i) = 0 :=
  law_constantCoeff_subst2 F h.1 _ _ (by simp) (constantCoeff_series_at_variable 1 i hi.1)

/- English proof (translation)
The claim follows from `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst' (fun k => by fin_cases k · exact MvPowerSeries.constantCoeff_X 0 · exact constantCoeff_series_at_variable 1 i hi.1) (fun k => by fin_cases k · exact law_integral_X 0 · exact integral_series_at_variable 1 i hi. …`.
-/
theorem law_integral_FI [IsUltrametricDist K] {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K}
    (h : LawLog F l) (hi : IsInv l i) : Integral (FI F i) :=
  Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_subst'
    (fun k => by
      fin_cases k
      · exact MvPowerSeries.constantCoeff_X 0
      · exact constantCoeff_series_at_variable 1 i hi.1)
    (fun k => by
      fin_cases k
      · exact law_integral_X 0
      · exact integral_series_at_variable 1 i hi.2.1) h.2.1

end Diff

end Formalism.L2.Th1.B
