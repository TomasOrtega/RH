import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementD

noncomputable section

namespace Formalism.L2.Th1.B.E2

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')

section Div

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

/- English proof (translation)
Introduce `n`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))`.
-/
theorem integral_add {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f + g) := by
  intro n
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

/- English proof (translation)
Introduce `n`. Rewrite using `[map_neg, norm_neg]`. Conclude with `hf n`.
-/
theorem integral_neg {ι : Type} {f : MvPowerSeries ι K} (hf : Integral f) : Integral (-f) := by
  intro n
  rw [map_neg, norm_neg]
  exact hf n

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `integral_add hf (integral_neg hg)`.
-/
theorem integral_sub {ι : Type} {f g : MvPowerSeries ι K} (hf : Integral f) (hg : Integral g) :
    Integral (f - g) := by
  rw [sub_eq_add_neg]
  exact integral_add hf (integral_neg hg)

/- English proof (translation)
Establish `c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `cs : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `cd : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`.

Establish `i0` using `integral_mvPowerSeries_X (K := K) (0 : Fin 2)`. Establish `i1` using `integral_mvPowerSeries_X (K := K) (1 : Fin 2)`. Take `⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst ![(MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G` from `⟨_, rfl⟩`. Establish `iH : Integral H`. Rewrite using `[hH]`.

Conclude with `integral_subst_two_variables hG _ _ cs c1 (integral_add i0 i1) i1`. Establish `hH0 : MvPowerSeries.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] H = 0`. Establish `hb` using `hs2 cz c1`. Rewrite using `[hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`. Simplify using `using hd`.

Establish `hdvd : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ H`. Rewrite using `[MvPowerSeries.X_dvd_iff]`. Introduce `m hm`. Rewrite using `[law_coeff_axis1 H m hm, hH0, map_zero]`. Take `⟨H1, e1⟩` from `hdvd`.

Establish `iH1 : Integral H1`. Introduce `n`. Use `iH (Finsupp.single 0 1 + n)` as an intermediate fact. Rewrite `this` using `[e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul]`. Then use the resulting hypothesis. Establish `hb` using `hs2 cd c1`.

Use `⟨MvPowerSeries.subst ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H1, integral_subst_two_variables iH1 _ _ cd c1 (integral_sub i0 i1) i1, ?_⟩` and prove the remaining obligations. Establish `e2 : MvPowerSeries.subst ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H = G`. Rewrite using `[hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_add_cancel]`. Conclude with `subst_XX G`.

Rewrite using `[← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]`. Both sides reduce to the same expression.
-/
theorem div_diag {G : MvPowerSeries (Fin 2) K} (hG : Integral G)
    (hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G = 0) :
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ G = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cs : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cd : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  obtain ⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G :=
    ⟨_, rfl⟩
  have iH : Integral H := by
    rw [hH]
    exact integral_subst_two_variables hG _ _ cs c1 (integral_add i0 i1) i1
  have hH0 : MvPowerSeries.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] H = 0 := by
    have hb := hs2 cz c1
    rw [hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
      MvPowerSeries.subst_X hb]
    simpa using hd
  have hdvd : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ H := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [law_coeff_axis1 H m hm, hH0, map_zero]
  obtain ⟨H1, e1⟩ := hdvd
  have iH1 : Integral H1 := by
    intro n
    have := iH (Finsupp.single 0 1 + n)
    rwa [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] at this
  have hb := hs2 cd c1
  refine ⟨MvPowerSeries.subst
    ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H1,
    integral_subst_two_variables iH1 _ _ cd c1 (integral_sub i0 i1) i1, ?_⟩
  have e2 : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H =
      G := by
    rw [hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
      MvPowerSeries.subst_X hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_add_cancel]
    exact subst_XX G
  rw [← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]
  rfl

end Div

/- English proof (translation)
Introduce `K _ _ _ F l i hF hi`. Establish `c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `ci : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0` using `constantCoeff_series_at_variable 1 i hi.1`.

Establish `hd : MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] (FI F i) = 0`. Establish `hb` using `hs2 c1 c1`. Unfold `FI`. Rewrite using `[subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]`. Use `law_eq_of_log hF _ _ 0 c1 (constantCoeff_series_at_variable 1 i hi.1) cz ?_` and prove the remaining obligations.

Rewrite using `[law_subst_zero l hF.2.2.1]`. Use `log_subst_formal_inverse hi (1 : Fin 2)` as an intermediate fact. Express the relevant statement in the definitionally equal form `PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l + PowerSeries.subst (at1 (1 : Fin 2) i) l = 0`. Rewrite using `[this]`. Conclude with `add_neg_cancel _`.

Take `⟨n, hn, e⟩` from `div_diag (law_integral_FI hF hi) hd`. Use `⟨n, hn, ?_, e⟩` and prove the remaining obligations. Establish `h1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (FI F i) = 1`. Establish `hb` using `hs2 c0 cz`. Rewrite using `[law_coeff_axis0 _ _ (by simp)]`.

Unfold `FI`. Rewrite using `[subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]`. Establish `e0 : PowerSeries.subst ((![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) K) 1) i = 0` using `PowerSeries.subst_zero_of_constantCoeff_zero hi.1`. Rewrite using `[e0]`. Express the relevant statement in the definitionally equal form `MvPowerSeries.coeff _ (MvPowerSeries.subst ![MvPowerSeries.X 0, 0] F) = 1`.

Rewrite using `[law_right_zero hF _ c0]`. Simplify using `[MvPowerSeries.coeff_X]`. Rewrite `h1` using `[e, sub_mul, map_sub]`. Establish `a0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 0 * n) = MvPowerSeries.constantCoeff n`. Use `MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (0 : Fin 2) 1) 0 n (1 : K)` as an intermediate fact.

Rewrite `this` using `[add_zero, one_mul]`. Then use the resulting hypothesis. Establish `a1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 1 * n) = 0`. Establish `hx : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 1 * n` using `Dvd.intro _ rfl`. Conclude with `MvPowerSeries.X_dvd_iff.1 hx _ (by simp)`. Rewrite `h1` using `[a0, a1, sub_zero]`.

Conclude with `h1`.
-/
theorem formal_inverse_unit_holds : FIUnit := by
  intro K _ _ _ F l i hF hi
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) i) = 0 := constantCoeff_series_at_variable 1 i hi.1
  have hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] (FI F i) = 0 := by
    have hb := hs2 c1 c1
    unfold FI
    rw [subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]
    refine law_eq_of_log hF _ _ 0 c1 (constantCoeff_series_at_variable 1 i hi.1) cz ?_
    rw [law_subst_zero l hF.2.2.1]
    have := log_subst_formal_inverse hi (1 : Fin 2)
    change PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l +
      PowerSeries.subst (at1 (1 : Fin 2) i) l = 0
    rw [this]
    exact add_neg_cancel _
  obtain ⟨n, hn, e⟩ := div_diag (law_integral_FI hF hi) hd
  refine ⟨n, hn, ?_, e⟩
  have h1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (FI F i) = 1 := by
    have hb := hs2 c0 cz
    rw [law_coeff_axis0 _ _ (by simp)]
    unfold FI
    rw [subst2_subst F c0 ci hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 1 hb]
    have e0 : PowerSeries.subst ((![MvPowerSeries.X 0, 0] : Fin 2 → MvPowerSeries (Fin 2) K) 1) i =
        0 := PowerSeries.subst_zero_of_constantCoeff_zero hi.1
    rw [e0]
    change MvPowerSeries.coeff _ (MvPowerSeries.subst ![MvPowerSeries.X 0, 0] F) = 1
    rw [law_right_zero hF _ c0]
    simp [MvPowerSeries.coeff_X]
  rw [e, sub_mul, map_sub] at h1
  have a0 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 0 * n) =
      MvPowerSeries.constantCoeff n := by
    have := MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (0 : Fin 2) 1) 0 n (1 : K)
    rwa [add_zero, one_mul] at this
  have a1 : MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) (MvPowerSeries.X 1 * n) = 0 := by
    have hx : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 1 * n :=
      Dvd.intro _ rfl
    exact MvPowerSeries.X_dvd_iff.1 hx _ (by simp)
  rw [a0, a1, sub_zero] at h1
  exact h1

section Alg

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Establish `h2 : MvPowerSeries.constantCoeff (f + f) = 0` using `by rw [map_add, hf, add_zero]`. Establish `e : (3 : MvPowerSeries ι K) * f = f + f + f` using `by ring`. Rewrite using `[e, fExp_add h2 hf, fExp_add hf hf]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fExp_three {ι : Type} {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    fExp (3 * f) = fExp f ^ 3 := by
  have h2 : MvPowerSeries.constantCoeff (f + f) = 0 := by rw [map_add, hf, add_zero]
  have e : (3 : MvPowerSeries ι K) * f = f + f + f := by ring
  rw [e, fExp_add h2 hf, fExp_add hf hf]
  ring

/- English proof (translation)
Establish `hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K)` using `PowerSeries.HasSubst.X x`. Establish `e` using `(PowerSeries.substAlgHom hx).commutes c`. Rewrite `e` using `[PowerSeries.coe_substAlgHom]`. Conclude with `e`.
-/
private theorem at1_C_eq_C {ι : Type} (x : ι) (c : K) :
    at1 x (PowerSeries.C c) = (MvPowerSeries.C c : MvPowerSeries ι K) := by
  have hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have e := (PowerSeries.substAlgHom hx).commutes c
  rw [PowerSeries.coe_substAlgHom] at e
  exact e

/- English proof (translation)
Establish `hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K)` using `PowerSeries.HasSubst.X x`. Establish `e` using `congrArg (PowerSeries.substAlgHom hx) h`. Simplify using `only [map_mul, map_add, map_pow, map_neg, map_ofNat, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hx] at e`. Establish `e1 : ∀ f : PowerSeries K, PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) f = at1 x f` using `fun f => rfl`. Simplify using `only [e1, at1_C_eq_C, ParE.subst_inVar x _ hl] at e`.

Conclude with `e`.
-/
theorem curve3_at {ι : Type} {l P ep : PowerSeries K} {a1 a3 : K}
    (hl : PowerSeries.constantCoeff l = 0)
    (h : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative K P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3)) (x : ι) :
    MvPowerSeries.X x ^ 3 * (-2 + at1 x l ^ 3 * PowerSeries.subst (at1 x l) (dz P)) =
      at1 x l ^ 3 * (-2 * at1 x ep + MvPowerSeries.C a1 * MvPowerSeries.X x * at1 x ep +
        MvPowerSeries.C a3 * MvPowerSeries.X x ^ 3) := by
  have hx : PowerSeries.HasSubst (MvPowerSeries.X x : MvPowerSeries ι K) := PowerSeries.HasSubst.X x
  have e := congrArg (PowerSeries.substAlgHom hx) h
  simp only [map_mul, map_add, map_pow, map_neg, map_ofNat, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hx] at e
  have e1 : ∀ f : PowerSeries K,
      PowerSeries.subst (MvPowerSeries.X x : MvPowerSeries ι K) f = at1 x f := fun f => rfl
  simp only [e1, at1_C_eq_C, ParE.subst_inVar x _ hl] at e
  exact e

/- English proof (translation)
Unfold `det3`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hb, AlgHom.map_det]`. Use `congr 1`. Use `Matrix.ext fun j c => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases c <;> simp [-MvPowerSeries.coe_substAlgHom]`.

Use `all_goals`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hb]`. Simplify using `only [map_mul, map_pow, map_add, map_neg, map_one, map_ofNat]`. Simplify using `only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, ParO.subst_inVar _ _ hb]`.
-/
theorem subst_det_three_points {ι : Type} (P : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (det3 P) = Matrix.det (Matrix.of fun j : Fin 3 =>
      ![b j ^ 3, b j * (1 + b j ^ 2 * PowerSeries.subst (b j) P),
        -2 + b j ^ 3 * PowerSeries.subst (b j) (dz P)]) := by
  unfold det3
  rw [← MvPowerSeries.coe_substAlgHom hb, AlgHom.map_det]
  congr 1
  refine Matrix.ext fun j c => ?_
  fin_cases c <;> simp [-MvPowerSeries.coe_substAlgHom]
  all_goals
    rw [← MvPowerSeries.coe_substAlgHom hb]
    simp only [map_mul, map_pow, map_add, map_neg, map_one, map_ofNat]
    simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, ParO.subst_inVar _ _ hb]

/- English proof (translation)
Unfold `evalSumThree`. Rewrite using `[psubst_subst g (u := (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)) (by simp) hb]`. Use `congr 1`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hb, map_add, map_add, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`.
-/
theorem subst_series_at_sum_three {ι : Type} (g : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (evalSumThree g) = PowerSeries.subst (b 0 + b 1 + b 2) g := by
  unfold evalSumThree
  rw [psubst_subst g (u := (MvPowerSeries.X 0 + MvPowerSeries.X 1 + MvPowerSeries.X 2 :
    MvPowerSeries (Fin 3) K)) (by simp) hb]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_add, map_add, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]

/- English proof (translation)
Unfold `evalDiffThree`. Rewrite using `[psubst_subst g (u := (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K)) (by simp) hb]`. Use `congr 1`. Rewrite using `[← MvPowerSeries.coe_substAlgHom hb, map_sub, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`.
-/
theorem subst_series_at_difference_three {ι : Type} (j k : Fin 3) (g : PowerSeries K) {b : Fin 3 → MvPowerSeries ι K}
    (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (evalDiffThree j k g) = PowerSeries.subst (b j - b k) g := by
  unfold evalDiffThree
  rw [psubst_subst g (u := (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K))
    (by simp) hb]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hb, map_sub, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]

/- English proof (translation)
Establish `hA : ∀ j, x j ^ 3 * (L j * A j) = L j ^ 3 * (x j * e j + c0 * x j ^ 3)` using `fun j => by`. Take the linear combination `(x j * L j) * h2 j`. Establish `d1 : Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) = L 0 ^ 3 * (L 1 * A 1) * B 2 - L 0 ^ 3 * B 1 * (L 2 * A 2) - L 0 * A 0 * L 1 ^ 3 * B 2 + L 0 * A 0 * B 1 * L 2 ^ 3 + B 0 * L 1 ^ 3 * (L 2 * A 2) - B 0 * (L 1 * A 1) * L 2 ^ 3`. Rewrite using `[Matrix.det_fin_three]`. Both sides reduce to the same expression.

Establish `d2 : Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) = x 0 ^ 3 * (x 1 * e 1) * -e 2 - x 0 ^ 3 * -e 1 * (x 2 * e 2) - x 0 * e 0 * x 1 ^ 3 * -e 2 + x 0 * e 0 * -e 1 * x 2 ^ 3 + -e 0 * x 1 ^ 3 * (x 2 * e 2) - -e 0 * (x 1 * e 1) * x 2 ^ 3`. Rewrite using `[Matrix.det_fin_three]`. Both sides reduce to the same expression. Rewrite using `[d1, d2]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem det_rows {R : Type} [CommRing R] (x L A B e : Fin 3 → R) (c0 a1 a3 : R)
    (h2 : ∀ j, x j ^ 2 * A j = L j ^ 2 * (e j + c0 * x j ^ 2))
    (h3 : ∀ j, x j ^ 3 * B j = L j ^ 3 * (-2 * e j + a1 * x j * e j + a3 * x j ^ 3)) :
    (x 0 * x 1 * x 2) ^ 3 * Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) =
      2 * (L 0 * L 1 * L 2) ^ 3 *
        Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) := by
  have hA : ∀ j, x j ^ 3 * (L j * A j) = L j ^ 3 * (x j * e j + c0 * x j ^ 3) := fun j => by
    linear_combination (x j * L j) * h2 j
  have d1 : Matrix.det (Matrix.of fun j => ![L j ^ 3, L j * A j, B j]) =
      L 0 ^ 3 * (L 1 * A 1) * B 2 - L 0 ^ 3 * B 1 * (L 2 * A 2) - L 0 * A 0 * L 1 ^ 3 * B 2 +
        L 0 * A 0 * B 1 * L 2 ^ 3 + B 0 * L 1 ^ 3 * (L 2 * A 2) - B 0 * (L 1 * A 1) * L 2 ^ 3 := by
    rw [Matrix.det_fin_three]; rfl
  have d2 : Matrix.det (Matrix.of fun j => ![x j ^ 3, x j * e j, -e j]) =
      x 0 ^ 3 * (x 1 * e 1) * -e 2 - x 0 ^ 3 * -e 1 * (x 2 * e 2) - x 0 * e 0 * x 1 ^ 3 * -e 2 +
        x 0 * e 0 * -e 1 * x 2 ^ 3 + -e 0 * x 1 ^ 3 * (x 2 * e 2) - -e 0 * (x 1 * e 1) * x 2 ^ 3 := by
    rw [Matrix.det_fin_three]; rfl
  rw [d1, d2]
  calc _ = (x 0 ^ 3 * L 0 ^ 3) * (x 1 ^ 3 * (L 1 * A 1)) * (x 2 ^ 3 * B 2) -
        (x 0 ^ 3 * L 0 ^ 3) * (x 1 ^ 3 * B 1) * (x 2 ^ 3 * (L 2 * A 2)) -
        (x 0 ^ 3 * (L 0 * A 0)) * (x 1 ^ 3 * L 1 ^ 3) * (x 2 ^ 3 * B 2) +
        (x 0 ^ 3 * (L 0 * A 0)) * (x 1 ^ 3 * B 1) * (x 2 ^ 3 * L 2 ^ 3) +
        (x 0 ^ 3 * B 0) * (x 1 ^ 3 * L 1 ^ 3) * (x 2 ^ 3 * (L 2 * A 2)) -
        (x 0 ^ 3 * B 0) * (x 1 ^ 3 * (L 1 * A 1)) * (x 2 ^ 3 * L 2 ^ 3) := by ring
    _ = _ := by rw [hA 0, hA 1, hA 2, h3 0, h3 1, h3 2]; ring

/- English proof (translation)
Unfold `at1`. Rewrite using `[PowerSeries.coeff_subst (PowerSeries.HasSubst.X x), finsum_eq_single _ 1]`. Use `split_ifs with hxy`. Substitute `hxy` using the available equality. Simplify using `[MvPowerSeries.coeff_X]`.

Simplify using `[MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, Ne.symm hxy]`. Introduce `d hd`. Rewrite using `[MvPowerSeries.coeff_X_pow, if_neg, smul_zero]`. Introduce `he`. Rewrite `he` using `[Finsupp.single_eq_single_iff]`.

Break down `he with ⟨-, h1⟩ | ⟨h1, -⟩` into its components or cases. Conclude with `hd h1.symm`. Conclude with `one_ne_zero h1`.
-/
private theorem coeff_single_one_at1_eq_ite {ι : Type} [DecidableEq ι] (x y : ι) (l : PowerSeries K) :
    MvPowerSeries.coeff (Finsupp.single y 1) (at1 x l) =
      if x = y then PowerSeries.coeff 1 l else 0 := by
  unfold at1
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X x), finsum_eq_single _ 1]
  · split_ifs with hxy
    · subst hxy
      simp [MvPowerSeries.coeff_X]
    · simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero, Ne.symm hxy]
  · intro d hd
    rw [MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
    intro he
    rw [Finsupp.single_eq_single_iff] at he
    rcases he with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact hd h1.symm
    · exact one_ne_zero h1

/- English proof (translation)
Introduce `h0`. Establish `e` using `coeff_single_one_at1_eq_ite x x l`. Rewrite `e` using `[h0, map_zero, if_pos rfl, hl1]`. Conclude with `zero_ne_one e`.
-/
theorem inVar_ne_zero {ι : Type} {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) (x : ι) :
    at1 x l ≠ 0 := by
  classical
  intro h0
  have e := coeff_single_one_at1_eq_ite x x l
  rw [h0, map_zero, if_pos rfl, hl1] at e
  exact zero_ne_one e

/- English proof (translation)
Introduce `h0`. Establish `e` using `congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h0`. Rewrite `e` using `[map_add, map_add, map_zero, coeff_single_one_at1_eq_ite, coeff_single_one_at1_eq_ite, coeff_single_one_at1_eq_ite]`. Simplify using `[hl1] at e`.
-/
theorem sum_log_three_variables_ne_zero {l : PowerSeries K} (hl1 : PowerSeries.coeff 1 l = 1) :
    at1 (0 : Fin 3) l + at1 1 l + at1 2 l ≠ 0 := by
  intro h0
  have e := congrArg (MvPowerSeries.coeff (Finsupp.single (0 : Fin 3) 1)) h0
  rw [map_add, map_add, map_zero, coeff_single_one_at1_eq_ite, coeff_single_one_at1_eq_ite, coeff_single_one_at1_eq_ite] at e
  simp [hl1] at e

end Alg

section Norm

variable {K : Type} [NormedField K] [CharZero K]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cX (j : Fin 3) :
    MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 := by
  simp

/- English proof (translation)
Unfold `in3`. Conclude with `law_constantCoeff_subst2 F hF _ _ (by simp) (by simp)`.
-/
theorem constantCoeff_law_first_two_of_three {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (in3 F) = 0 := by
  unfold in3
  exact law_constantCoeff_subst2 F hF _ _ (by simp) (by simp)

/- English proof (translation)
Unfold `F3`. Conclude with `law_constantCoeff_subst2 F hF _ _ (constantCoeff_law_first_two_of_three hF) (by simp)`.
-/
theorem constantCoeff_law_three_variables {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (F3 F) = 0 := by
  unfold F3
  exact law_constantCoeff_subst2 F hF _ _ (constantCoeff_law_first_two_of_three hF) (by simp)

/- English proof (translation)
Take `⟨hF0, -, -, -, hc⟩` from `h`. Establish `hF : PowerSeries.subst F l = at1 0 l + at1 1 l`. Unfold `cob at hc`. Take the linear combination `hc`. Rewrite using `[← psubst_subst l hF0 (hs2 hu hv), hF, MvPowerSeries.subst_add (hs2 hu hv), ParO.subst_inVar _ _ (hs2 hu hv), ParO.subst_inVar _ _ (hs2 hu hv)]`.

Both sides reduce to the same expression.
-/
private theorem lawLog_subst_formal_sum_eq_add {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l)
    {u v : MvPowerSeries (Fin 3) K} (hu : MvPowerSeries.constantCoeff u = 0)
    (hv : MvPowerSeries.constantCoeff v = 0) :
    PowerSeries.subst (MvPowerSeries.subst ![u, v] F) l =
      PowerSeries.subst u l + PowerSeries.subst v l := by
  obtain ⟨hF0, -, -, -, hc⟩ := h
  have hF : PowerSeries.subst F l = at1 0 l + at1 1 l := by
    unfold cob at hc
    linear_combination hc
  rw [← psubst_subst l hF0 (hs2 hu hv), hF, MvPowerSeries.subst_add (hs2 hu hv),
    ParO.subst_inVar _ _ (hs2 hu hv), ParO.subst_inVar _ _ (hs2 hu hv)]
  rfl

/- English proof (translation)
Unfold `F3`. Rewrite using `[lawLog_subst_formal_sum_eq_add h (constantCoeff_law_first_two_of_three h.1) (cX 2)]`. Unfold `in3`. Rewrite using `[lawLog_subst_formal_sum_eq_add h (cX 0) (cX 1)]`. Both sides reduce to the same expression.
-/
theorem log_formal_law_three_variables {F : MvPowerSeries (Fin 2) K} {l : PowerSeries K} (h : LawLog F l) :
    PowerSeries.subst (F3 F) l = at1 0 l + at1 1 l + at1 2 l := by
  unfold F3
  rw [lawLog_subst_formal_sum_eq_add h (constantCoeff_law_first_two_of_three h.1) (cX 2)]
  unfold in3
  rw [lawLog_subst_formal_sum_eq_add h (cX 0) (cX 1)]
  rfl

/- English proof (translation)
The claim follows from `(Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) f (b := fun _ => (MvPowerSeries.X k : MvPowerSeries (Fin n) K)) (fun _ => by simp)).trans hf`.
-/
private theorem constantCoeff_at1_fin_eq_zero {n : ℕ} (k : Fin n) {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (at1 k f : MvPowerSeries (Fin n) K) = 0 :=
  (Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) f
    (b := fun _ => (MvPowerSeries.X k : MvPowerSeries (Fin n) K)) (fun _ => by simp)).trans hf

/- English proof (translation)
Unfold `lawDifferenceThree`. Conclude with `law_constantCoeff_subst2 F h.1 _ _ (cX j) (constantCoeff_at1_fin_eq_zero k hi.1)`.
-/
theorem constantCoeff_law_with_inverse_three {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (j k : Fin 3) : MvPowerSeries.constantCoeff (lawDifferenceThree F i j k) = 0 := by
  unfold lawDifferenceThree
  exact law_constantCoeff_subst2 F h.1 _ _ (cX j) (constantCoeff_at1_fin_eq_zero k hi.1)

/- English proof (translation)
Unfold `lawDifferenceThree`. Rewrite using `[lawLog_subst_formal_sum_eq_add h (cX j) (constantCoeff_at1_fin_eq_zero k hi.1), ← ParE.subst_inVar k l hi.1, hi.2.2, sub_eq_add_neg]`. Use `congr 1`. Unfold `at1`. Rewrite using `[← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X k), map_neg]`.
-/
theorem log_law_with_inverse_three {F : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (h : LawLog F l)
    (hi : IsInv l i) (j k : Fin 3) :
    PowerSeries.subst (lawDifferenceThree F i j k) l = at1 j l - at1 k l := by
  unfold lawDifferenceThree
  rw [lawLog_subst_formal_sum_eq_add h (cX j) (constantCoeff_at1_fin_eq_zero k hi.1), ← ParE.subst_inVar k l hi.1, hi.2.2,
    sub_eq_add_neg]
  congr 1
  unfold at1
  rw [← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X k), map_neg]

/- English proof (translation)
Establish `hb` using `hs2 (cX (K := K) j) (cX (K := K) k)`. Unfold `lawDifferenceThree FI`. Rewrite using `[subst2_subst F (u := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (v := at1 1 i) (by simp) (constantCoeff_at1_fin_eq_zero 1 hi) hb, MvPowerSeries.subst_X hb, ParO.subst_inVar _ _ hb]`. Both sides reduce to the same expression.
-/
theorem law_with_inverse_three_eq_subst {F : MvPowerSeries (Fin 2) K} {i : PowerSeries K}
    (hi : PowerSeries.constantCoeff i = 0) (j k : Fin 3) :
    lawDifferenceThree F i j k = MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] (FI F i) := by
  have hb := hs2 (cX (K := K) j) (cX (K := K) k)
  unfold lawDifferenceThree FI
  rw [subst2_subst F (u := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (v := at1 1 i)
    (by simp) (constantCoeff_at1_fin_eq_zero 1 hi) hb, MvPowerSeries.subst_X hb, ParO.subst_inVar _ _ hb]
  rfl

/- English proof (translation)
Establish `hb` using `hs2 (cX (K := K) j) (cX (K := K) k)`. Rewrite using `[law_with_inverse_three_eq_subst hi j k, hn, ← MvPowerSeries.coe_substAlgHom hb, map_mul, map_sub, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]`. Both sides reduce to the same expression.
-/
theorem law_with_inverse_factor_difference {F n : MvPowerSeries (Fin 2) K} {i : PowerSeries K}
    (hi : PowerSeries.constantCoeff i = 0)
    (hn : FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) (j k : Fin 3) :
    lawDifferenceThree F i j k = (MvPowerSeries.X j - MvPowerSeries.X k) * MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n := by
  have hb := hs2 (cX (K := K) j) (cX (K := K) k)
  rw [law_with_inverse_three_eq_subst hi j k, hn, ← MvPowerSeries.coe_substAlgHom hb, map_mul, map_sub,
    MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb]
  rfl

/- English proof (translation)
Introduce `h0`. Establish `h1` using `congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h0`. Rewrite `h1` using `[map_sub, map_zero, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg (fun hh => h (Finsupp.single_left_injective one_ne_zero hh))]`. Simplify using `at h1`.
-/
theorem X_sub_ne_zero {j k : Fin 3} (h : j ≠ k) :
    (MvPowerSeries.X j - MvPowerSeries.X k : MvPowerSeries (Fin 3) K) ≠ 0 := by
  intro h0
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) h0
  rw [map_sub, map_zero, MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl,
    if_neg (fun hh => h (Finsupp.single_left_injective one_ne_zero hh))] at h1
  simp at h1

/- English proof (translation)
Establish `hl0` using `hF.2.2.1`. Establish `hl1` using `hF.2.2.2.1`. Take `⟨hph0, hphe⟩` from `phODef K s2 P l hl0 hl1`. Generalize the expression as in `phO s2 P l = ph at hph0 hphe ⊢`. Establish `cL : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j l) = 0` using `fun j => constantCoeff_series_at_variable j l hl0`.

Establish `hφ : MvPowerSeries.HasSubst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K))` using `MvPowerSeries.hasSubst_of_constantCoeff_zero cL`. Establish `key` using `congrArg (MvPowerSeries.subst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K))) (hA K g2 g3 s2 P hP)`. Rewrite `key` using `[← MvPowerSeries.coe_substAlgHom hφ]`. Simplify using `only [map_mul, map_pow, map_neg, map_ofNat] at key`. Simplify using `only [MvPowerSeries.coe_substAlgHom hφ, MvPowerSeries.subst_X hφ, subst_series_at_sum_three _ hφ, subst_series_at_difference_three _ _ _ hφ, subst_det_three_points _ hφ, ParO.subst_inVar _ _ hφ] at key`.

Establish `cS` using `constantCoeff_law_three_variables hF.1`. Establish `cD` using `constantCoeff_law_with_inverse_three hF hi`. Establish `v : ∀ j : Fin 3, PowerSeries.subst (at1 j l) (sgStar s2 P) = MvPowerSeries.X j * fExp (-at1 j ph)` using `fun j => ParO.value_at hl0 hph0 hphe (cX j)`. Rewrite `key` using `[← log_formal_law_three_variables hF, ← log_law_with_inverse_three hF hi 0 1, ← log_law_with_inverse_three hF hi 0 2, ← log_law_with_inverse_three hF hi 1 2, ParO.value_at hl0 hph0 hphe cS, ParO.value_at hl0 hph0 hphe (cD 0 1), ParO.value_at hl0 hph0 hphe (cD 0 2), ParO.value_at …`. Establish `dr` using `det_rows (fun j : Fin 3 => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) (fun j => at1 j l) (fun j => 1 + at1 j l ^ 2 * PowerSeries.subst (at1 j l) P) (fun j => -2 + at1 j l ^ 3 * PowerSeries.subst (at1 j l) (dz P)) (fun j => at1 j ep) (MvPowerSeries.C c0) (MvPowerSeries.C a1) ( …`.

Simplify using `only [he] at dr`. Establish `cA : MvPowerSeries.constantCoeff (PowerSeries.subst (F3 F) ph) = 0` using `PowerSeries.constantCoeff_subst_eq_zero cS ph hph0`. Establish `cB : ∀ j k, MvPowerSeries.constantCoeff (PowerSeries.subst (lawDifferenceThree F i j k) ph) = 0` using `fun j k => PowerSeries.constantCoeff_subst_eq_zero (cD j k) ph hph0`. Establish `ca : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j ph) = 0` using `fun j => constantCoeff_series_at_variable j ph hph0`. Establish `hpar : -par3 F i ph = -PowerSeries.subst (F3 F) ph + -PowerSeries.subst (lawDifferenceThree F i 0 1) ph + -PowerSeries.subst (lawDifferenceThree F i 0 2) ph + -PowerSeries.subst (lawDifferenceThree F i 1 2) ph + 3 * at1 0 ph + 3 * at1 1 ph + 3 * at1 2 ph`.

Unfold `par3`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : MvPowerSeries.constantCoeff (par3 F i ph) = 0`. Unfold `par3`. Simplify using `[cA, cB, ca]`.

Use `⟨h0, ?_⟩` and prove the remaining obligations. Rewrite using `[hpar, fExp_add (by simp [cA, cB, ca]) (by simp [ca]), fExp_add (by simp [cA, cB, ca]) (by simp [ca]), fExp_add (by simp [cA, cB]) (by simp [ca]), fExp_add (by simp [cA, cB]) (by simp [cB]), fExp_add (by simp [cA, cB]) (by simp [cB]), fExp_add (by simp [cA]) (by simp [cB]), fExp_ …`. Establish `r0` using `ParO.fExp_mul_neg (ca 0)`. Establish `r1` using `ParO.fExp_mul_neg (ca 1)`. Establish `r2` using `ParO.fExp_mul_neg (ca 2)`.

Establish `f01` using `law_with_inverse_factor_difference hi.1 hn 0 1`. Establish `f02` using `law_with_inverse_factor_difference hi.1 hn 0 2`. Establish `f12` using `law_with_inverse_factor_difference hi.1 hn 1 2`. Establish `hF3 : F3 F ≠ 0` using `ParO.ne_zero_of_psubst hl0 (by rw [log_formal_law_three_variables hF]; exact sum_log_three_variables_ne_zero hl1)`. Generalize the expression as in `fExp (-PowerSeries.subst (F3 F) ph) = ES at key ⊢`.

Generalize the expression as in `fExp (-PowerSeries.subst (lawDifferenceThree F i 0 1) ph) = bivariateExponentMonomial at key ⊢`. Generalize the expression as in `fExp (-PowerSeries.subst (lawDifferenceThree F i 0 2) ph) = E02 at key ⊢`. Generalize the expression as in `fExp (-PowerSeries.subst (lawDifferenceThree F i 1 2) ph) = E12 at key ⊢`. Rewrite `key` using `[f01, f02, f12]`. Generalize the expression as in `MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n = n01 at key ⊢`.

Generalize the expression as in `MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n02 at key ⊢`. Generalize the expression as in `MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n12 at key ⊢`. Generalize the expression as in `fExp (-at1 (0 : Fin 3) ph) = E0 at key r0 ⊢`. Generalize the expression as in `fExp (-at1 (1 : Fin 3) ph) = E1 at key r1 ⊢`. Generalize the expression as in `fExp (-at1 (2 : Fin 3) ph) = E2 at key r2 ⊢`.

Generalize the expression as in `fExp (at1 (0 : Fin 3) ph) = G0 at r0 ⊢`. Generalize the expression as in `fExp (at1 (1 : Fin 3) ph) = G1 at r1 ⊢`. Generalize the expression as in `fExp (at1 (2 : Fin 3) ph) = G2 at r2 ⊢`. Establish `h2ne : (2 : MvPowerSeries (Fin 3) K) ≠ 0`. Introduce `h`.

Use `congrArg MvPowerSeries.constantCoeff h` as an intermediate fact. Rewrite `this` using `[map_ofNat, map_zero]`. Conclude with `two_ne_zero this`. Establish `hne : 2 * (at1 (0 : Fin 3) l * at1 1 l * at1 2 l) ^ 3 * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2) ≠ 0`. Use `mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2ne (pow_ne_zero 3 (mul_ne_zero (mul_ne_zero (inVar_ne_zero hl1 0) (inVar_ne_zero hl1 1)) (inVar_ne_zero hl1 2)))) hF3) (X_sub_ne_zero (by decide))) (X_sub_ne_zero (by decide))) (X_sub_ne_zero (by decide))` and prove the remaining obligations.

Establish `E : (E0 * E1 * E2) ^ 3 * e = -(n01 * n02 * n12 * (ES * bivariateExponentMonomial * E02 * E12))`. Use `mul_left_cancel₀ hne ?_` and prove the remaining obligations. Take the linear combination `key - (E0 * E1 * E2) ^ 3 * dr`. Establish `hp : (G0 * G1 * G2) ^ 3 * (E0 * E1 * E2) ^ 3 = 1`. Establish `: G0 * G1 * G2 * (E0 * E1 * E2) = 1`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow, this, one_pow]`. Take the linear combination `(G0 * G1 * G2) ^ 3 * E - e * hp`.
-/
theorem parallelogram_three_weierstrass_key (hA : FrobStickStar) {g2 g3 s2 c0 a1 a3 : K} {P l i ep : PowerSeries K}
    {F n : MvPowerSeries (Fin 2) K} {e : MvPowerSeries (Fin 3) K} (hP : IsWp g2 g3 P)
    (hF : LawLog F l) (hi : IsInv l i)
    (h2 : PowerSeries.X ^ 2 * (1 + l ^ 2 * PowerSeries.subst l P) =
      l ^ 2 * (ep + PowerSeries.C c0 * PowerSeries.X ^ 2))
    (h3 : PowerSeries.X ^ 3 * (-2 + l ^ 3 * PowerSeries.subst l (PowerSeries.derivative K P)) =
      l ^ 3 * (-2 * ep + PowerSeries.C a1 * PowerSeries.X * ep +
        PowerSeries.C a3 * PowerSeries.X ^ 3))
    (he : Matrix.det (Matrix.of fun j : Fin 3 =>
        ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K) ^ 3, MvPowerSeries.X j * at1 j ep,
          -at1 j ep]) =
        e * F3 F * (MvPowerSeries.X 0 - MvPowerSeries.X 1) *
          (MvPowerSeries.X 0 - MvPowerSeries.X 2) * (MvPowerSeries.X 1 - MvPowerSeries.X 2))
    (hn : FI F i = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n) :
    MvPowerSeries.constantCoeff (par3 F i (phO s2 P l)) = 0 ∧
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      fExp (-par3 F i (phO s2 P l)) = -e := by
  have hl0 := hF.2.2.1
  have hl1 := hF.2.2.2.1
  obtain ⟨hph0, hphe⟩ := phODef K s2 P l hl0 hl1
  generalize phO s2 P l = ph at hph0 hphe ⊢
  have cL : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j l) = 0 :=
    fun j => constantCoeff_series_at_variable j l hl0
  have hφ : MvPowerSeries.HasSubst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero cL
  have key := congrArg (MvPowerSeries.subst (fun j : Fin 3 => (at1 j l : MvPowerSeries (Fin 3) K)))
    (hA K g2 g3 s2 P hP)
  rw [← MvPowerSeries.coe_substAlgHom hφ] at key
  simp only [map_mul, map_pow, map_neg, map_ofNat] at key
  simp only [MvPowerSeries.coe_substAlgHom hφ, MvPowerSeries.subst_X hφ, subst_series_at_sum_three _ hφ,
    subst_series_at_difference_three _ _ _ hφ, subst_det_three_points _ hφ, ParO.subst_inVar _ _ hφ] at key
  have cS := constantCoeff_law_three_variables hF.1
  have cD := constantCoeff_law_with_inverse_three hF hi
  have v : ∀ j : Fin 3, PowerSeries.subst (at1 j l) (sgStar s2 P) =
      MvPowerSeries.X j * fExp (-at1 j ph) := fun j => ParO.value_at hl0 hph0 hphe (cX j)
  rw [← log_formal_law_three_variables hF, ← log_law_with_inverse_three hF hi 0 1, ← log_law_with_inverse_three hF hi 0 2, ← log_law_with_inverse_three hF hi 1 2,
    ParO.value_at hl0 hph0 hphe cS, ParO.value_at hl0 hph0 hphe (cD 0 1),
    ParO.value_at hl0 hph0 hphe (cD 0 2), ParO.value_at hl0 hph0 hphe (cD 1 2), v 0, v 1, v 2]
    at key
  have dr := det_rows (fun j : Fin 3 => (MvPowerSeries.X j : MvPowerSeries (Fin 3) K))
    (fun j => at1 j l) (fun j => 1 + at1 j l ^ 2 * PowerSeries.subst (at1 j l) P)
    (fun j => -2 + at1 j l ^ 3 * PowerSeries.subst (at1 j l) (dz P)) (fun j => at1 j ep)
    (MvPowerSeries.C c0) (MvPowerSeries.C a1) (MvPowerSeries.C a3)
    (fun j => ParO.curve_at hl0 h2 j) (fun j => curve3_at hl0 h3 j)
  simp only [he] at dr
  have cA : MvPowerSeries.constantCoeff (PowerSeries.subst (F3 F) ph) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero cS ph hph0
  have cB : ∀ j k, MvPowerSeries.constantCoeff (PowerSeries.subst (lawDifferenceThree F i j k) ph) = 0 :=
    fun j k => PowerSeries.constantCoeff_subst_eq_zero (cD j k) ph hph0
  have ca : ∀ j : Fin 3, MvPowerSeries.constantCoeff (at1 j ph) = 0 :=
    fun j => constantCoeff_series_at_variable j ph hph0
  have hpar : -par3 F i ph = -PowerSeries.subst (F3 F) ph + -PowerSeries.subst (lawDifferenceThree F i 0 1) ph +
      -PowerSeries.subst (lawDifferenceThree F i 0 2) ph + -PowerSeries.subst (lawDifferenceThree F i 1 2) ph +
      3 * at1 0 ph + 3 * at1 1 ph + 3 * at1 2 ph := by
    unfold par3; ring
  have h0 : MvPowerSeries.constantCoeff (par3 F i ph) = 0 := by
    unfold par3; simp [cA, cB, ca]
  refine ⟨h0, ?_⟩
  rw [hpar, fExp_add (by simp [cA, cB, ca]) (by simp [ca]),
    fExp_add (by simp [cA, cB, ca]) (by simp [ca]), fExp_add (by simp [cA, cB]) (by simp [ca]),
    fExp_add (by simp [cA, cB]) (by simp [cB]), fExp_add (by simp [cA, cB]) (by simp [cB]),
    fExp_add (by simp [cA]) (by simp [cB]), fExp_three (ca 0), fExp_three (ca 1),
    fExp_three (ca 2)]
  have r0 := ParO.fExp_mul_neg (ca 0)
  have r1 := ParO.fExp_mul_neg (ca 1)
  have r2 := ParO.fExp_mul_neg (ca 2)
  have f01 := law_with_inverse_factor_difference hi.1 hn 0 1
  have f02 := law_with_inverse_factor_difference hi.1 hn 0 2
  have f12 := law_with_inverse_factor_difference hi.1 hn 1 2
  have hF3 : F3 F ≠ 0 := ParO.ne_zero_of_psubst hl0 (by rw [log_formal_law_three_variables hF]; exact sum_log_three_variables_ne_zero hl1)
  generalize fExp (-PowerSeries.subst (F3 F) ph) = ES at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 0 1) ph) = bivariateExponentMonomial at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 0 2) ph) = E02 at key ⊢
  generalize fExp (-PowerSeries.subst (lawDifferenceThree F i 1 2) ph) = E12 at key ⊢
  rw [f01, f02, f12] at key
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n = n01 at key ⊢
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n02 at key ⊢
  generalize MvPowerSeries.subst
    ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n = n12 at key ⊢
  generalize fExp (-at1 (0 : Fin 3) ph) = E0 at key r0 ⊢
  generalize fExp (-at1 (1 : Fin 3) ph) = E1 at key r1 ⊢
  generalize fExp (-at1 (2 : Fin 3) ph) = E2 at key r2 ⊢
  generalize fExp (at1 (0 : Fin 3) ph) = G0 at r0 ⊢
  generalize fExp (at1 (1 : Fin 3) ph) = G1 at r1 ⊢
  generalize fExp (at1 (2 : Fin 3) ph) = G2 at r2 ⊢
  have h2ne : (2 : MvPowerSeries (Fin 3) K) ≠ 0 := by
    intro h
    have := congrArg MvPowerSeries.constantCoeff h
    rw [map_ofNat, map_zero] at this
    exact two_ne_zero this
  have hne : 2 * (at1 (0 : Fin 3) l * at1 1 l * at1 2 l) ^ 3 * F3 F *
      (MvPowerSeries.X 0 - MvPowerSeries.X 1) * (MvPowerSeries.X 0 - MvPowerSeries.X 2) *
      (MvPowerSeries.X 1 - MvPowerSeries.X 2) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2ne
      (pow_ne_zero 3 (mul_ne_zero (mul_ne_zero (inVar_ne_zero hl1 0) (inVar_ne_zero hl1 1))
        (inVar_ne_zero hl1 2)))) hF3) (X_sub_ne_zero (by decide))) (X_sub_ne_zero (by decide)))
      (X_sub_ne_zero (by decide))
  have E : (E0 * E1 * E2) ^ 3 * e = -(n01 * n02 * n12 * (ES * bivariateExponentMonomial * E02 * E12)) := by
    refine mul_left_cancel₀ hne ?_
    linear_combination key - (E0 * E1 * E2) ^ 3 * dr
  have hp : (G0 * G1 * G2) ^ 3 * (E0 * E1 * E2) ^ 3 = 1 := by
    have : G0 * G1 * G2 * (E0 * E1 * E2) = 1 := by
      calc G0 * G1 * G2 * (E0 * E1 * E2) = (G0 * E0) * (G1 * E1) * (G2 * E2) := by ring
        _ = 1 := by rw [r0, r1, r2]; ring
    rw [← mul_pow, this, one_pow]
  linear_combination (G0 * G1 * G2) ^ 3 * E - e * hp

end Norm

/- English proof (translation)
Introduce `K _ _ _ g2 g3 s2 c0 a1 a3 P l i ep F hP hL hi hC hC3`. Take `⟨-, -, h2, -⟩` from `hC`. Take `⟨h3, e, heI, he0, he⟩` from `hC3`. Take `⟨n, hnI, hn0, hn⟩` from `hU K F l i hL hi`. Take `⟨h0, key⟩` from `parallelogram_three_weierstrass_key (s2 := s2) hF hP hL hi h2 h3 he hn`.

Establish `iN : ∀ j k : Fin 3, Integral (MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n)` using `fun j k => integral_subst_two_variables hnI _ _ (cX j) (cX k) (integral_mvPowerSeries_X j) (integral_mvPowerSeries_X k)`. Establish `cN : ∀ j k : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n) = 1` using `fun j k => by`. Apply the tactic sequence `rw [Formalism.G.LogP.constantCoeff_subst_of_zero n (fun s => by fin_cases s <;> simp), hn0]`. Generalize the expression as in `par3 F i (phO s2 P l) = q at h0 key ⊢`. Take `⟨N, hN⟩ : ∃ N, N = MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n * MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n * MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerS …` from `⟨_, rfl⟩`.

Establish `iNN : Integral N`. Rewrite using `[hN]`. Conclude with `Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (iN 0 1) (iN 0 2)) (iN 1 2)`. Establish `cNN : MvPowerSeries.constantCoeff N = 1`. Rewrite using `[hN, map_mul, map_mul, cN, cN, cN]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[← hN]`. Establish `hq0 : MvPowerSeries.constantCoeff (-q) = 0` using `by rw [map_neg, h0, neg_zero]`. Establish `hlog` using `ParO.fLog_mul cNN (constantCoeff_fExp hq0)`. Rewrite `hlog` using `[key, fLog_fExp hq0]`.

Establish `hq : q = fLog N + -fLog (-e)` using `by linear_combination hlog`. Establish `s1` using `(simeqLog K (Fin 3) N cNN iNN).1`. Establish `s2'` using `(simeqLog K (Fin 3) (-e) (by rw [map_neg, he0, neg_neg]) (integral_neg heI)).2`. Establish `s3` using `(Formalism.InvariantFactorPaths.G7.equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 s2'`. Rewrite `s3` using `[add_zero]`.

Rewrite using `[hq]`. Conclude with `s3`.
-/
theorem ParThree_of (hF : FrobStickStar) (hU : FIUnit) : ParThree := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 P l i ep F hP hL hi hC hC3
  obtain ⟨-, -, h2, -⟩ := hC
  obtain ⟨h3, e, heI, he0, he⟩ := hC3
  obtain ⟨n, hnI, hn0, hn⟩ := hU K F l i hL hi
  obtain ⟨h0, key⟩ := parallelogram_three_weierstrass_key (s2 := s2) hF hP hL hi h2 h3 he hn
  have iN : ∀ j k : Fin 3, Integral (MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n) := fun j k =>
    integral_subst_two_variables hnI _ _ (cX j) (cX k) (integral_mvPowerSeries_X j) (integral_mvPowerSeries_X k)
  have cN : ∀ j k : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n) = 1 := fun j k => by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero n (fun s => by fin_cases s <;> simp), hn0]
  generalize par3 F i (phO s2 P l) = q at h0 key ⊢
  obtain ⟨N, hN⟩ : ∃ N, N = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n :=
    ⟨_, rfl⟩
  have iNN : Integral N := by
    rw [hN]
    exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (iN 0 1) (iN 0 2)) (iN 1 2)
  have cNN : MvPowerSeries.constantCoeff N = 1 := by
    rw [hN, map_mul, map_mul, cN, cN, cN]; ring
  rw [← hN] at key
  have hq0 : MvPowerSeries.constantCoeff (-q) = 0 := by rw [map_neg, h0, neg_zero]
  have hlog := ParO.fLog_mul cNN (constantCoeff_fExp hq0)
  rw [key, fLog_fExp hq0] at hlog
  have hq : q = fLog N + -fLog (-e) := by linear_combination hlog
  have s1 := (simeqLog K (Fin 3) N cNN iNN).1
  have s2' := (simeqLog K (Fin 3) (-e) (by rw [map_neg, he0, neg_neg]) (integral_neg heI)).2
  have s3 := (Formalism.InvariantFactorPaths.G7.equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 s2'
  rw [add_zero] at s3
  rw [hq]
  exact s3

end Formalism.L2.Th1.B.E2
