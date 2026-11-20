import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegreeStatement

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

/- English proof (translation)
Take `⟨-, -, -, -, hX, -, hsub, -⟩` from `GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit`. Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[nMul_zero]`. Introduce `ν`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Rewrite using `[nMul_succ]`. Establish `hc : PowerSeries.constantCoeff (nMul F n) = 0` using `((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 n).1`. Use `(hsub (Fin 2) ![nMul F n, PowerSeries.X] F.toPowerSeries ?_ ?_).1 hF` and prove the remaining obligations.

Introduce `j fin_cases j`. Conclude with `ih`. Conclude with `(hX ()).1`. Introduce `j fin_cases j`. Conclude with `hc`.

Conclude with `PowerSeries.constantCoeff_X`.
-/
theorem intg_nMul_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (n : ℕ) : Intg (nMul F n) := by
  obtain ⟨-, -, -, -, hX, -, hsub, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  induction n with
  | zero =>
    rw [nMul_zero]
    intro ν
    simp
  | succ n ih =>
    rw [nMul_succ]
    have hc : PowerSeries.constantCoeff (nMul F n) = 0 := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 n).1
    refine (hsub (Fin 2) ![nMul F n, PowerSeries.X] F.toPowerSeries ?_ ?_).1 hF
    · intro j
      fin_cases j
      · exact ih
      · exact (hX ()).1
    · intro j
      fin_cases j
      · exact hc
      · exact PowerSeries.constantCoeff_X

/- English proof (translation)
Establish `hpr : p.Prime` using `Fact.out`. Establish `hI` using `intg_nMul_of_intg K F hF p`. Use `set h := nMul F p with hh`. Take `⟨-, -, hpow, -, -, -, -, -, -, hiff⟩` from `GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit`. Establish `hev` using `fun (x : K) (hx : ‖x‖ < 1) => GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx`.

Establish `hbdd : ∀ f : PowerSeries K, Intg f → Bdd f` using `fun f hf => (hpow f 0).2.2 hf`. Establish `hcoef : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1` using `(hiff h).1.1 hI`. Establish `h0 : PowerSeries.coeff 0 h = 0`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1`.

Establish `h0c : PowerSeries.constantCoeff h = 0` using `((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1`. Establish `h1 : PowerSeries.coeff 1 h = (p : K)` using `((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).2`. Establish `hp0 : (p : K) ≠ 0` using `Nat.cast_ne_zero.mpr hpr.ne_zero`. Establish `hz : ‖(0 : K)‖ < 1` using `by simp`. Take `⟨-, -, -, -, -, -, -, -, -, -, hzero⟩` from `hev 0 hz`.

Establish `hstep : ∀ c : {c : K // ‖c‖ < 1}, ∃ y : {y : K // ‖y‖ < 1}, ev1 h y = c`. Introduce and unpack `⟨c, hc⟩`. Establish `hIc : Intg (h - PowerSeries.C c)`. Rewrite using `[(hiff _).1]`. Introduce `n`.

Break down `n with _ | n` into its components or cases. Simplify using `[h0c, hc.le]`. Rewrite using `[map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), sub_zero]`. Conclude with `hcoef _`. Take `⟨y, hy, hy0⟩` from `GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K (h - PowerSeries.C c) p hpr.pos hIc (by`.

Rewrite using `[map_sub, PowerSeries.coeff_C, if_neg hpr.ne_zero, sub_zero]`. Conclude with `hp) (by`. Introduce `k hk`. Break down `k with _ | k` into its components or cases. Simplify `hc` using `[h0, h0c]`.

Rewrite using `[map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k), sub_zero]`. Conclude with `hlt _ hk)`. Use `⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Take `⟨-, hops, hCe, -⟩` from `hev y hy`. Establish `hCI : Intg (PowerSeries.C c)`.

Rewrite using `[(hiff _).1]`. Introduce `n`. Rewrite using `[PowerSeries.coeff_C]`. Use `split_ifs`. Conclude with `hc.le`.

Simplify using the standard rewrite rules. Establish `e` using `(hops h (PowerSeries.C c) (hbdd h hI) (hbdd _ hCI)).2.1`. Rewrite `e` using `[hy0, hCe]`. Simplify using `only`. Take the linear combination `-e`.

Use `set g : PowerSeries K := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) h with hg`. Establish `hgI : Intg g`. Rewrite using `[(hiff _).1]`. Introduce `n`. Rewrite using `[hg, PowerSeries.coeff_mk]`.

Conclude with `hcoef _`. Establish `hp1 : 0 < p - 1` using `by have := hpr.two_le; omega`. Take `⟨x, hx, hx0⟩` from `GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K g (p - 1) hp1 hgI (by`. Rewrite using `[hg, PowerSeries.coeff_mk, Nat.sub_add_cancel hpr.one_lt.le]`. Conclude with `hp) (by`.

Introduce `k hk`. Rewrite using `[hg, PowerSeries.coeff_mk]`. Conclude with `hlt _ (by omega))`. Establish `hxne : x ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hx0` using `[hzero, hg, PowerSeries.coeff_mk, h1]`. Conclude with `hp0 hx0`. Establish `hXI : Intg (PowerSeries.X : PowerSeries K)`. Rewrite using `[(hiff _).1]`. Introduce `n`.

Rewrite using `[PowerSeries.coeff_X]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hXg : h = PowerSeries.X * g`. Use extensionality with `n`. Break down `n with _ | n` into its components or cases.

Simplify using `[h0]`. Rewrite using `[PowerSeries.coeff_succ_X_mul, hg, PowerSeries.coeff_mk]`. Establish `hxroot : ev1 h x = 0`. Take `⟨-, hops, -, hXe, -⟩` from `hev x hx`. Rewrite using `[hXg, ((hops _ _ (hbdd _ hXI) (hbdd _ hgI)).2.2), hXe, hx0, mul_zero]`.

Use `choose f hf using hstep`. Set `x0 : {y : K // ‖y‖ < 1}` to `⟨x, hx⟩`. Use `⟨fun n => if n = 0 then 0 else ((f^[n - 1] x0 : {y : K // ‖y‖ < 1}) : K), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `n dsimp only split_ifs`. Conclude with `hz`.

Conclude with `(f^[n - 1] x0).2`. Simplify using the standard rewrite rules. Simplify `hxne` using `[x0]`. Introduce `n`. Break down `n with _ | m` into its components or cases.

Simplify `hxroot` using `[x0]`. Simplify using `only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), Function.iterate_succ_apply']`. Conclude with `hf _`.
-/
theorem exists_torsion_tower (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K)
    (hF : Intg F.toPowerSeries) (hp : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (hlt : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧
      ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  classical
  have hpr : p.Prime := Fact.out
  have hI := intg_nMul_of_intg K F hF p
  set h := nMul F p with hh
  obtain ⟨-, -, hpow, -, -, -, -, -, -, hiff⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  have hev := fun (x : K) (hx : ‖x‖ < 1) => GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hbdd : ∀ f : PowerSeries K, Intg f → Bdd f := fun f hf => (hpow f 0).2.2 hf
  have hcoef : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1 := (hiff h).1.1 hI
  have h0 : PowerSeries.coeff 0 h = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h0c : PowerSeries.constantCoeff h = 0 := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).1
  have h1 : PowerSeries.coeff 1 h = (p : K) := ((GlobalTheory.T.formalGroupNatMulSeries_properties K F).1 p).2
  have hp0 : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hpr.ne_zero
  have hz : ‖(0 : K)‖ < 1 := by simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hzero⟩ := hev 0 hz

  have hstep : ∀ c : {c : K // ‖c‖ < 1}, ∃ y : {y : K // ‖y‖ < 1}, ev1 h y = c := by
    rintro ⟨c, hc⟩
    have hIc : Intg (h - PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rcases n with _ | n
      · simp [h0c, hc.le]
      · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n), sub_zero]
        exact hcoef _
    obtain ⟨y, hy, hy0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K (h - PowerSeries.C c) p hpr.pos hIc (by
        rw [map_sub, PowerSeries.coeff_C, if_neg hpr.ne_zero, sub_zero]
        exact hp) (by
        intro k hk
        rcases k with _ | k
        · simpa [h0, h0c] using hc
        · rw [map_sub, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero k), sub_zero]
          exact hlt _ hk)
    refine ⟨⟨y, hy⟩, ?_⟩
    obtain ⟨-, hops, hCe, -⟩ := hev y hy
    have hCI : Intg (PowerSeries.C c) := by
      rw [(hiff _).1]
      intro n
      rw [PowerSeries.coeff_C]
      split_ifs
      · exact hc.le
      · simp
    have e := (hops h (PowerSeries.C c) (hbdd h hI) (hbdd _ hCI)).2.1
    rw [hy0, hCe] at e
    simp only
    linear_combination -e

  set g : PowerSeries K := PowerSeries.mk fun k => PowerSeries.coeff (k + 1) h with hg
  have hgI : Intg g := by
    rw [(hiff _).1]
    intro n
    rw [hg, PowerSeries.coeff_mk]
    exact hcoef _
  have hp1 : 0 < p - 1 := by have := hpr.two_le; omega
  obtain ⟨x, hx, hx0⟩ := GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree K g (p - 1) hp1 hgI (by
      rw [hg, PowerSeries.coeff_mk, Nat.sub_add_cancel hpr.one_lt.le]
      exact hp) (by
      intro k hk
      rw [hg, PowerSeries.coeff_mk]
      exact hlt _ (by omega))
  have hxne : x ≠ 0 := by
    rintro rfl
    rw [hzero, hg, PowerSeries.coeff_mk, h1] at hx0
    exact hp0 hx0
  have hXI : Intg (PowerSeries.X : PowerSeries K) := by
    rw [(hiff _).1]
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs <;> simp
  have hXg : h = PowerSeries.X * g := by
    ext n
    rcases n with _ | n
    · simp [h0]
    · rw [PowerSeries.coeff_succ_X_mul, hg, PowerSeries.coeff_mk]
  have hxroot : ev1 h x = 0 := by
    obtain ⟨-, hops, -, hXe, -⟩ := hev x hx
    rw [hXg, ((hops _ _ (hbdd _ hXI) (hbdd _ hgI)).2.2), hXe, hx0, mul_zero]
  choose f hf using hstep
  let x0 : {y : K // ‖y‖ < 1} := ⟨x, hx⟩
  refine ⟨fun n => if n = 0 then 0 else ((f^[n - 1] x0 : {y : K // ‖y‖ < 1}) : K), ?_, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs
    · exact hz
    · exact (f^[n - 1] x0).2
  · simp
  · simpa [x0] using hxne
  · intro n
    rcases n with _ | m
    · simpa [x0] using hxroot
    · simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _), Function.iterate_succ_apply']
      exact hf _

end GlobalTheory.ConvSer
