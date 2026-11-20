import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE

noncomputable section

namespace Formalism.L2.Th1.B.LDiv

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_mul' integral_one' integral_of_mul_eq_one)
open Formalism.L2.Th1.B.ParE (integral_add' integral_sub' integral_C')
open Formalism.G.LogP (hs2 subst2_subst subst_XX)

section Div

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

/- English proof (translation)
Establish `c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0` using `constantCoeff_series_at_variable 0 i hi.1`. Establish `i0` using `integral_mvPowerSeries_X (K := K) (0 : Fin 2)`.

Establish `i1` using `integral_mvPowerSeries_X (K := K) (1 : Fin 2)`. Establish `ii : Integral (at1 (0 : Fin 2) i)` using `integral_series_at_variable 0 i hi.2.1`. Take `⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst ![at1 (0 : Fin 2) i, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] F` from `⟨_, rfl⟩`. Establish `cD : MvPowerSeries.constantCoeff D = 0`. Rewrite using `[hD]`.

Conclude with `law_constantCoeff_subst2 F hF.1 _ _ ci c1`. Establish `iD : Integral D`. Rewrite using `[hD]`. Conclude with `integral_subst_two_variables hF.2.1 _ _ ci c1 ii i1`. Take `⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), D] G` from `⟨_, rfl⟩`.

Establish `iH : Integral H`. Rewrite using `[hH]`. Conclude with `integral_subst_two_variables hG _ _ c0 cD i0 iD`. Establish `hH0 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0`. Establish `hb` using `hs2 c0 cz`.

Rewrite using `[hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`. Express the relevant statement in the definitionally equal form `MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, 0] F] G = 0`. Rewrite using `[law_right_zero hF _ ci]`. Conclude with `hd`.

Establish `hdvd : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H`. Rewrite using `[MvPowerSeries.X_dvd_iff]`. Introduce `m hm`. Rewrite using `[law_coeff_axis0 H m hm, hH0, map_zero]`. Take `⟨H1, e1⟩` from `hdvd`.

Establish `iH1 : Integral H1`. Introduce `n`. Use `iH (Finsupp.single 1 1 + n)` as an intermediate fact. Rewrite `this` using `[e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul]`. Then use the resulting hypothesis. Establish `hb` using `hs2 c0 hF.1`.

Use `⟨MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H1, integral_subst_two_variables iH1 _ _ c0 hF.1 i0 hF.2.1, ?_⟩` and prove the remaining obligations. Establish `e3 : MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F = (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)`. Use `law_eq_of_log hF _ _ _ ci hF.1 c1 ?_` and prove the remaining obligations. Establish `e4` using `law_subst hF (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (MvPowerSeries.X 1) c0 c1`. Rewrite `e4` using `[subst_XX]`.

Rewrite using `[e4, log_subst_formal_inverse hi 0]`. Express the relevant statement in the definitionally equal form `-at1 0 l + (at1 0 l + _) = _`. Rewrite using `[neg_add_cancel_left]`. Establish `e2 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H = G`. Rewrite using `[hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb, MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one]`. Express the relevant statement in the definitionally equal form `MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F] G = G`. Rewrite using `[e3]`. Conclude with `subst_XX G`. Rewrite using `[← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]`.

Both sides reduce to the same expression.
-/
theorem div_law {F G : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (hF : LawLog F l)
    (hi : IsInv l i) (hG : Integral G)
    (hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] G = 0) :
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ G = F * n := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  have ii : Integral (at1 (0 : Fin 2) i) := integral_series_at_variable 0 i hi.2.1
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst
      ![at1 (0 : Fin 2) i, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] F := ⟨_, rfl⟩
  have cD : MvPowerSeries.constantCoeff D = 0 := by
    rw [hD]
    exact law_constantCoeff_subst2 F hF.1 _ _ ci c1
  have iD : Integral D := by
    rw [hD]
    exact integral_subst_two_variables hF.2.1 _ _ ci c1 ii i1
  obtain ⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), D] G := ⟨_, rfl⟩
  have iH : Integral H := by
    rw [hH]
    exact integral_subst_two_variables hG _ _ c0 cD i0 iD
  have hH0 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0 := by
    have hb := hs2 c0 cz
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, 0] F] G
      = 0
    rw [law_right_zero hF _ ci]
    exact hd
  have hdvd : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [law_coeff_axis0 H m hm, hH0, map_zero]
  obtain ⟨H1, e1⟩ := hdvd
  have iH1 : Integral H1 := by
    intro n
    have := iH (Finsupp.single 1 1 + n)
    rwa [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] at this
  have hb := hs2 c0 hF.1
  refine ⟨MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H1,
    integral_subst_two_variables iH1 _ _ c0 hF.1 i0 hF.2.1, ?_⟩
  have e3 : MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F =
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
    refine law_eq_of_log hF _ _ _ ci hF.1 c1 ?_
    have e4 := law_subst hF (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (MvPowerSeries.X 1) c0 c1
    rw [subst_XX] at e4
    rw [e4, log_subst_formal_inverse hi 0]
    change -at1 0 l + (at1 0 l + _) = _
    rw [neg_add_cancel_left]
  have e2 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H = G := by
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F] G
      = G
    rw [e3]
    exact subst_XX G
  rw [← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]
  rfl

end Div

/- English proof (translation)
Introduce `K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT`. Take `⟨hT1, hT2, nx, ny, na, -⟩` from `hT`. Establish `hep` using `hC.1`. Establish `hep0` using `hC.2.1`. Establish `c0' : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`.

Establish `c1' : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0` using `by simp`. Establish `ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0` using `constantCoeff_series_at_variable 0 i hi.1`. Establish `i0` using `integral_mvPowerSeries_X (K := K) (0 : Fin 2)`. Establish `i1` using `integral_mvPowerSeries_X (K := K) (1 : Fin 2)`.

Establish `hX : Integral (ι` using `Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()`. Establish `hX2 : Integral (ι` using `Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by`. Rewrite using `[pow_two]`. Conclude with `integral_mul' hX hX`. Establish `hX3 : Integral (ι` using `Unit) (PowerSeries.X ^ 3 : PowerSeries K) := by`.

Rewrite using `[pow_succ]`. Conclude with `integral_mul' hX2 hX`. Establish `hg0 : PowerSeries.constantCoeff (gT ep xT) = 1` using `by simp [gT, hep0]`. Establish `hgi : Integral (ι` using `Unit) (gT ep xT) := integral_sub' hep (integral_mul' (integral_C' nx) hX2)`. Establish `hinv : (gT ep xT)⁻¹ * gT ep xT = 1` using `PowerSeries.inv_mul_cancel _ (by rw [hg0]; exact one_ne_zero)`.

Establish `hginv : Integral (ι` using `Unit) (gT ep xT)⁻¹ := integral_of_mul_eq_one hgi hg0 hinv`. Establish `hth : Integral (ι` using `Unit) (thT ep xT yT) := integral_mul' (integral_add' hep (integral_mul' (integral_C' ny) hX3)) hginv`. Establish `hth0 : PowerSeries.constantCoeff (thT ep xT yT) = 1`. Establish `e` using `congrArg PowerSeries.constantCoeff hinv`. Rewrite `e` using `[map_mul, hg0, mul_one, map_one]`.

Unfold `thT`. Rewrite using `[map_mul, e]`. Simplify using `[hep0]`. Establish `hL : Integral (LT ep xT yT a1)` using `integral_sub' (integral_add' (integral_mul' i1 (integral_series_at_variable 0 _ hth)) (integral_mul' i0 (integral_series_at_variable 1 _ hth))) (integral_mul' (integral_mul' (integral_C' na) i0) i1)`. Establish `hb` using `hs2 c0' ci`.

Establish `eF : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] F = 0`. Use `law_eq_of_log hF _ _ 0 c0' ci cz ?_` and prove the remaining obligations. Rewrite using `[law_subst_zero l hF.2.2.1, log_subst_formal_inverse hi 0]`. Conclude with `add_neg_cancel _`. Establish `hd : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] (LT ep xT yT a1) = 0`.

Establish `e` using `congrArg (MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i]) (hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hT1 hT2)`. Rewrite `e` using `[MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_pow hb F, eF, psubst_msubst _ hF.1 hb, eF]`. Establish `e5 : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) (gT ep xT) ≠ 0`. Introduce `h`. Rewrite `h` using `[PowerSeries.subst_zero_eq_C_constantCoeff, hg0]`.

Simplify using `at h`. Rewrite `e` using `[MvPowerSeries.subst_pow hb]`. Simplify using `only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul] at e`. Break down `mul_eq_zero.1 e with h | h` into its components or cases. Conclude with `absurd h e5`.

Conclude with `pow_eq_zero_iff (two_ne_zero) |>.1 h`. Take `⟨nu, hnu, e⟩` from `div_law hF hi hL hd`. Use `⟨nu, hnu, ?_, e⟩` and prove the remaining obligations. Establish `a0 : ∀ n : MvPowerSeries (Fin 2) K, MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 1 * n) = MvPowerSeries.constantCoeff n`. Introduce `n`.

Use `MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (1 : Fin 2) 1) 0 n (1 : K)` as an intermediate fact. Rewrite `this` using `[add_zero, one_mul]`. Then use the resulting hypothesis. Establish `a1' : ∀ n : MvPowerSeries (Fin 2) K, MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 0 * n) = 0`. Introduce `n`. Establish `hx : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 0 * n` using `Dvd.intro _ rfl`.

Conclude with `MvPowerSeries.X_dvd_iff.1 hx _ (by simp)`. Establish `h1 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (LT ep xT yT a1) = 1`. Unfold `LT`. Establish `e6 : MvPowerSeries.C a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1 = (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * (MvPowerSeries.C a1 * MvPowerSeries.X 1)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e6, map_sub, map_add, a0, a1', a1', add_zero, sub_zero]`. Conclude with `(Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (thT ep xT yT) (b := fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (fun _ => c0')).trans hth0`. Establish `h2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (F * nu) = MvPowerSeries.constantCoeff nu` using `by classical`. Rewrite using `[MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]`. Simplify using `[Finset.Nat.antidiagonal_succ, law_coeff_single hF 1, hF.1]`.

Rewrite `h1` using `[e, h2]`. Conclude with `h1`.
-/
theorem LDiv_of (hG : GCob) : LDiv := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hT1, hT2, nx, ny, na, -⟩ := hT
  have hep := hC.1
  have hep0 := hC.2.1
  have c0' : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1' : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)

  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hX3 : Integral (ι := Unit) (PowerSeries.X ^ 3 : PowerSeries K) := by
    rw [pow_succ]
    exact integral_mul' hX2 hX
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by simp [gT, hep0]
  have hgi : Integral (ι := Unit) (gT ep xT) :=
    integral_sub' hep (integral_mul' (integral_C' nx) hX2)
  have hinv : (gT ep xT)⁻¹ * gT ep xT = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hg0]; exact one_ne_zero)
  have hginv : Integral (ι := Unit) (gT ep xT)⁻¹ := integral_of_mul_eq_one hgi hg0 hinv
  have hth : Integral (ι := Unit) (thT ep xT yT) :=
    integral_mul' (integral_add' hep (integral_mul' (integral_C' ny) hX3)) hginv
  have hth0 : PowerSeries.constantCoeff (thT ep xT yT) = 1 := by
    have e := congrArg PowerSeries.constantCoeff hinv
    rw [map_mul, hg0, mul_one, map_one] at e
    unfold thT
    rw [map_mul, e]
    simp [hep0]
  have hL : Integral (LT ep xT yT a1) :=
    integral_sub' (integral_add' (integral_mul' i1 (integral_series_at_variable 0 _ hth))
      (integral_mul' i0 (integral_series_at_variable 1 _ hth)))
      (integral_mul' (integral_mul' (integral_C' na) i0) i1)

  have hb := hs2 c0' ci
  have eF : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] F = 0 := by
    refine law_eq_of_log hF _ _ 0 c0' ci cz ?_
    rw [law_subst_zero l hF.2.2.1, log_subst_formal_inverse hi 0]
    exact add_neg_cancel _
  have hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] (LT ep xT yT a1) = 0 := by
    have e := congrArg (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i])
      (hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hT1 hT2)
    rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb,
      MvPowerSeries.subst_pow hb F, eF, psubst_msubst _ hF.1 hb, eF] at e
    have e5 : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) (gT ep xT) ≠ 0 := by
      intro h
      rw [PowerSeries.subst_zero_eq_C_constantCoeff, hg0] at h
      simp at h
    rw [MvPowerSeries.subst_pow hb] at e
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul] at e
    rcases mul_eq_zero.1 e with h | h
    · exact absurd h e5
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  obtain ⟨nu, hnu, e⟩ := div_law hF hi hL hd
  refine ⟨nu, hnu, ?_, e⟩

  have a0 : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 1 * n) =
      MvPowerSeries.constantCoeff n := by
    intro n
    have := MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (1 : Fin 2) 1) 0 n (1 : K)
    rwa [add_zero, one_mul] at this
  have a1' : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 0 * n) = 0 := by
    intro n
    have hx : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 0 * n :=
      Dvd.intro _ rfl
    exact MvPowerSeries.X_dvd_iff.1 hx _ (by simp)
  have h1 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (LT ep xT yT a1) = 1 := by
    unfold LT
    have e6 : MvPowerSeries.C a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1 =
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * (MvPowerSeries.C a1 * MvPowerSeries.X 1) := by
      ring
    rw [e6, map_sub, map_add, a0, a1', a1', add_zero, sub_zero]
    exact (Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (thT ep xT yT)
      (b := fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (fun _ => c0')).trans hth0
  have h2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (F * nu) =
      MvPowerSeries.constantCoeff nu := by
    classical
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
    simp [Finset.Nat.antidiagonal_succ, law_coeff_single hF 1, hF.1]
  rw [e, h2] at h1
  exact h1

end Formalism.L2.Th1.B.LDiv
