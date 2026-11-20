import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.GoodModelAll
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.AnalyticTransOfAdd
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalD

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.CM (HasCMBy omegaK)
open Formalism.L2.Th1.E (IntCurve curveL)
open Formalism.L2.Th1.A (logSer expSer wpReg shortW)
open Formalism.L2.Th1.D (normInt)
open Formalism.G (unitBall)

namespace OrthogonalGaussModelNormLemmas

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Establish `e : a ^ 2 = (t : K) * a - c`. Rewrite using `[← hs, ← hp]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1 : ‖a ^ 2‖ ≤ max ‖(t : K) * a‖ ‖c‖`. Rewrite using `[e, sub_eq_add_neg, ← norm_neg c]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Establish `h2 : ‖(t : K) * a‖ ≤ ‖a‖`. Rewrite using `[norm_mul]`.

Conclude with `mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K t)`. Establish `h3 : ‖c‖ ≤ ‖a‖` using `hc.trans h.le`. Establish `h4 : ‖a‖ ^ 2 ≤ ‖a‖`. Rewrite using `[← norm_pow]`. Conclude with `h1.trans (max_le h2 h3)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_le_one_of_quad {K : Type} [NormedField K] [IsUltrametricDist K] {a b c : K} {t : ℤ}
    (hs : a + b = (t : K)) (hp : a * b = c) (hc : ‖c‖ ≤ 1) : ‖a‖ ≤ 1 := by
  by_contra h
  rw [not_le] at h
  have e : a ^ 2 = (t : K) * a - c := by
    rw [← hs, ← hp]
    ring
  have h1 : ‖a ^ 2‖ ≤ max ‖(t : K) * a‖ ‖c‖ := by
    rw [e, sub_eq_add_neg, ← norm_neg c]
    exact IsUltrametricDist.norm_add_le_max _ _
  have h2 : ‖(t : K) * a‖ ≤ ‖a‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K t)
  have h3 : ‖c‖ ≤ ‖a‖ := hc.trans h.le
  have h4 : ‖a‖ ^ 2 ≤ ‖a‖ := by
    rw [← norm_pow]
    exact h1.trans (max_le h2 h3)
  nlinarith

/- English proof (translation)
Establish `ha` using `norm_le_one_of_quad hs hp hc.le`. Establish `hb` using `norm_le_one_of_quad (a := b) (b := a) (by rw [add_comm]; exact hs) (by rw [mul_comm]; exact hp) hc.le`. Establish `h : ‖a‖ * ‖b‖ = 1` using `by rw [← norm_mul, hp, hc]`. Use `le_antisymm ha ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_eq_one_of_quad {K : Type} [NormedField K] [IsUltrametricDist K] {a b c : K} {t : ℤ}
    (hs : a + b = (t : K)) (hp : a * b = c) (hc : ‖c‖ = 1) : ‖a‖ = 1 := by
  have ha := norm_le_one_of_quad hs hp hc.le
  have hb := norm_le_one_of_quad (a := b) (b := a) (by rw [add_comm]; exact hs)
    (by rw [mul_comm]; exact hp) hc.le
  have h : ‖a‖ * ‖b‖ = 1 := by rw [← norm_mul, hp, hc]
  refine le_antisymm ha ?_
  calc (1 : ℝ) = ‖a‖ * ‖b‖ := h.symm
    _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hb (norm_nonneg a)
    _ = ‖a‖ := mul_one _

/- English proof (translation)
Establish `h1 : ¬ p ∣ z.natAbs` using `fun h2 => h (Int.natCast_dvd.2 h2)`. Establish `h3` using `Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h1`. Break down `Int.natAbs_eq z with e | e` into its components or cases. Rewrite using `[e]`. Simplify using `using h3`.

Rewrite using `[e]`. Simplify using `using h3`.
-/
theorem norm_int (p : ℕ) [Fact p.Prime] {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : ‖(z : ℂ_[p])‖ = 1 := by
  have h1 : ¬ p ∣ z.natAbs := fun h2 => h (Int.natCast_dvd.2 h2)
  have h3 := Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h1
  rcases Int.natAbs_eq z with e | e
  · rw [e]
    simpa using h3
  · rw [e]
    simpa using h3

/- English proof (translation)
Establish `h : ¬ p ∣ 2` using `fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)`. Simplify using `using Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h`.
-/
theorem norm_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ¬ p ∣ 2 := fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  simpa using Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p h

/- English proof (translation)
Rewrite using `[Formalism.L2.Th1.D.CurveNormEndomorphisms.mul_bar]`. Use `congrArg (fun x : ℝ => (x : ℂ)) (Formalism.L2.Th1.D.CurveNormEndomorphisms.normInt_cast hmod m n)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`.
-/
theorem prod_bar {dK : ℕ} (hmod : dK % 4 = 3) (m n : ℤ) :
    ((m : ℂ) + (n : ℂ) * omegaK dK) * ((m : ℂ) + (n : ℂ) * (1 - omegaK dK)) =
      ((normInt dK m n : ℤ) : ℂ) := by
  rw [Formalism.L2.Th1.D.CurveNormEndomorphisms.mul_bar]
  have := congrArg (fun x : ℝ => (x : ℂ)) (Formalism.L2.Th1.D.CurveNormEndomorphisms.normInt_cast hmod m n)
  push_cast at this
  rw [this]

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k` from `⟨((dK : ℤ) + 1) / 4, by omega⟩`. Establish `hdiv : ((dK : ℤ) + 1) / 4 = k` using `by omega`. Unfold `normInt`. Rewrite using `[hdiv]`. Take the linear combination `-hk`.
-/
theorem four_normInt {dK : ℕ} (hmod : dK % 4 = 3) (m : ℤ) :
    4 * normInt dK m 1 = (2 * m + 1) ^ 2 + (dK : ℤ) := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (dK : ℤ) + 1 = 4 * k := ⟨((dK : ℤ) + 1) / 4, by omega⟩
  have hdiv : ((dK : ℤ) + 1) / 4 = k := by omega
  unfold normInt
  rw [hdiv]
  linear_combination -hk

variable {p : ℕ} [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])

/- English proof (translation)
Rewrite using `[← map_add]`. Establish `e : ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) + ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK)) = ((2 * m + 1 : ℤ) : ℂ)`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_intCast]`.
-/
theorem sum_bar (dK : ℕ) (m : ℤ) :
    ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) + ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK)) =
      ((2 * m + 1 : ℤ) : ℂ_[p]) := by
  rw [← map_add]
  have e : ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) + ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK)) =
      ((2 * m + 1 : ℤ) : ℂ) := by
    push_cast
    ring
  rw [e, map_intCast]

/- English proof (translation)
Rewrite using `[← map_sub, ← map_pow]`. Establish `e : (((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) - ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))) ^ 2 = -(dK : ℂ)`. Use `push_cast`. Take the linear combination `4 * Formalism.L2.Th1.D.CurveNormEndomorphisms.omega_sq dK`. Rewrite using `[e, map_neg, map_natCast]`.
-/
theorem diff_sq (dK : ℕ) (m : ℤ) :
    (ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) - ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))) ^ 2 =
      -(dK : ℂ_[p]) := by
  rw [← map_sub, ← map_pow]
  have e : (((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) -
      ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))) ^ 2 = -(dK : ℂ) := by
    push_cast
    linear_combination 4 * Formalism.L2.Th1.D.CurveNormEndomorphisms.omega_sq dK
  rw [e, map_neg, map_natCast]

/- English proof (translation)
Use `norm_eq_one_of_quad (sum_bar ι dK m) (c := ((normInt dK m 1 : ℤ) : ℂ_[p])) ?_ (norm_int p hN)` and prove the remaining obligations. Rewrite using `[← map_mul, prod_bar hmod, map_intCast]`.
-/
theorem norm_al {dK : ℕ} (hmod : dK % 4 = 3) (m : ℤ) (hN : ¬ (p : ℤ) ∣ normInt dK m 1) :
    ‖ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK)‖ = 1 := by
  refine norm_eq_one_of_quad (sum_bar ι dK m) (c := ((normInt dK m 1 : ℤ) : ℂ_[p])) ?_
    (norm_int p hN)
  rw [← map_mul, prod_bar hmod, map_intCast]

/- English proof (translation)
Assemble the required witnesses or components as `⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩`.
-/
theorem coeffIn {W : WeierstrassCurve ℂ_[p]} (hW : IntCurve W) :
    Formalism.L2.Th1.C.CoeffIn (unitBall ℂ_[p]) W :=
  ⟨hW.1, hW.2.1, hW.2.2.1, hW.2.2.2.1, hW.2.2.2.2.1⟩

end OrthogonalGaussModelNormLemmas

/- English proof (translation)
Introduce `dK L hmod hCM p _ ι hW m n hN`. Establish `hN0 : normInt dK m n ≠ 0`. Introduce `h`. Apply `hN` to reduce the goal to its premises. Rewrite using `[h]`.

Conclude with `dvd_zero _`. Take `⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩` from `Formalism.L2.Th1.D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0`. Establish `hpN : ¬ p ∣ (S.card + 1)`. Introduce `h`. Apply `hN` to reduce the goal to its premises.

Rewrite using `[← hcard]`. Conclude with `h` after adjusting the coercions. Establish `hΔ : (curveL p L ι).Δ ≠ 0`. Introduce `h`. Use `hW.2.2.2.2.2` as an intermediate fact.

Rewrite `this` using `[h, norm_zero]`. Conclude with `zero_ne_one this`. Establish `hb2 : (curveL p L ι).b₂ = 0` using `(Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1`. Use `⟨S, neg, fun P => ι (L.weierstrassP (P : ℂ)), fun P => ι (L.derivWeierstrassP (P : ℂ)) / 2, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Formalism.L2.Th1.D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) (curveL p L ι) (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p]) (Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))` to reduce the goal to its premises.

Introduce `P`. Conclude with `(Formalism.L2.Th1.E.ScaledModelNorms.nonsing p L ι hΔ _ (hker P).2).1`. Introduce `P`. Prove the components needed by the constructor for the conclusion. Conclude with `congrArg ι (hnegP P).1`.

Simplify using `only [WeierstrassCurve.Affine.negY, curveL, shortW]`. Rewrite using `[(hnegP P).2, map_neg]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `Formalism.L2.Th1.D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE`. Simplify using `only [PowerSeries.map_id, RingHom.id_apply, hb2, zero_div, add_zero]`.

Rewrite using `[Formalism.L2.Th1.E.wpBridge]`. Conclude with `h`. Introduce `P`. Establish `h` using `(Formalism.L2.Th1.E.ptOfInt p L ι hW (P : ℂ) (S.card + 1) (Nat.succ_pos _) hpN (hker P).1 (hker P).2).1`. Rewrite `h` using `[Formalism.L2.Th1.E.ScaledModelNorms.px_ptOf p L ι hΔ _ (hker P).2]`. Then use the resulting hypothesis.

Introduce `P`. Establish `h` using `(Formalism.L2.Th1.E.ptOfInt p L ι hW (P : ℂ) (S.card + 1) (Nat.succ_pos _) hpN (hker P).1 (hker P).2).2`. Rewrite `h` using `[Formalism.L2.Th1.E.ScaledModelNorms.py_ptOf p L ι hΔ _ (hker P).2]`. Then use the resulting hypothesis. Rewrite using `[← map_mul, hprod, Fintype.card_coe]`. Simplify using the standard rewrite rules.

Rewrite using `[← map_sub, ← map_mul, ← map_mul, hs2C, map_sum, hb2]`. Simplify using the standard rewrite rules.
-/
theorem CMDatum_proof : CMDatum := by
  intro dK L hmod hCM p _ ι hW m n hN
  have hN0 : normInt dK m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, hs2C⟩ :=
    Formalism.L2.Th1.D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  have hΔ : (curveL p L ι).Δ ≠ 0 := by
    intro h
    have := hW.2.2.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  refine ⟨S, neg, fun P => ι (L.weierstrassP (P : ℂ)),
    fun P => ι (L.derivWeierstrassP (P : ℂ)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · apply Formalism.L2.Th1.D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) (curveL p L ι)
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (Formalism.L2.Th1.E.ScaledModelNorms.nonsing p L ι hΔ _ (hker P).2).1
    · intro P
      constructor
      · exact congrArg ι (hnegP P).1
      · simp only [WeierstrassCurve.Affine.negY, curveL, shortW]
        rw [(hnegP P).2, map_neg]
        ring
    · have h := Formalism.L2.Th1.D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, hb2, zero_div, add_zero]
      rw [Formalism.L2.Th1.E.wpBridge]
      exact h
  · intro P
    have h := (Formalism.L2.Th1.E.ptOfInt p L ι hW (P : ℂ) (S.card + 1) (Nat.succ_pos _) hpN
      (hker P).1 (hker P).2).1
    rwa [Formalism.L2.Th1.E.ScaledModelNorms.px_ptOf p L ι hΔ _ (hker P).2] at h
  · intro P
    have h := (Formalism.L2.Th1.E.ptOfInt p L ι hW (P : ℂ) (S.card + 1) (Nat.succ_pos _) hpN
      (hker P).1 (hker P).2).2
    rwa [Formalism.L2.Th1.E.ScaledModelNorms.py_ptOf p L ι hΔ _ (hker P).2] at h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp
  · rw [← map_sub, ← map_mul, ← map_mul, hs2C, map_sum, hb2]
    simp

/- English proof (translation)
Introduce `dK L hmod hCM p _ hpd ι hW`. Establish `hp2 : p ≠ 2`. Introduce `h`. Rewrite `hpd` using `[h]`. Use linear arithmetic over natural numbers and integers.

Establish `hN : ¬ (p : ℤ) ∣ normInt dK 0 1`. Introduce `h`. Establish `h4` using `OrthogonalGaussModelNormLemmas.four_normInt hmod 0`. Establish `h1 : (p : ℤ) ∣ (dK : ℤ)` using `by exact_mod_cast hpd`. Establish `h2 : (p : ℤ) ∣ 1`.

Establish `e : (1 : ℤ) = 4 * normInt dK 0 1 - dK` using `by linarith`. Rewrite using `[e]`. Conclude with `dvd_sub (Dvd.dvd.mul_left h 4) h1`. Establish `h3 : p ∣ 1` using `by exact_mod_cast h2`. Conclude with `(Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)`.

Take `⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩` from `hD dK L hmod hCM p ι hW 0 1 hN`. Establish `hb2 : (curveL p L ι).b₂ = 0` using `(Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1`. Conclude with `Formalism.L2.Th1.G.curveRamified ℂ_[p] (curveL p L ι) (OrthogonalGaussModelNormLemmas.coeffIn hW) (OrthogonalGaussModelNormLemmas.norm_two p hp2) (ι (Formalism.L2.Th1.F.s2 L)) _ _ dK (2 * 0 + 1) S neg xP yP hE hx hy hprod (OrthogonalGaussModelNormLemmas.norm_al ι hmod 0 hN) (Orth …`.
-/
theorem ShapeCM_of (hD : CMDatum) : ShapeCM := by
  intro dK L hmod hCM p _ hpd ι hW
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpd
    omega
  have hN : ¬ (p : ℤ) ∣ normInt dK 0 1 := by
    intro h
    have h4 := OrthogonalGaussModelNormLemmas.four_normInt hmod 0
    have h1 : (p : ℤ) ∣ (dK : ℤ) := by exact_mod_cast hpd
    have h2 : (p : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = 4 * normInt dK 0 1 - dK := by linarith
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_left h 4) h1
    have h3 : p ∣ 1 := by exact_mod_cast h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 h3)
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ := hD dK L hmod hCM p ι hW 0 1 hN
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  exact Formalism.L2.Th1.G.curveRamified ℂ_[p] (curveL p L ι) (OrthogonalGaussModelNormLemmas.coeffIn hW)
    (OrthogonalGaussModelNormLemmas.norm_two p hp2) (ι (Formalism.L2.Th1.F.s2 L)) _ _ dK (2 * 0 + 1) S neg xP yP hE hx hy hprod
    (OrthogonalGaussModelNormLemmas.norm_al ι hmod 0 hN) (OrthogonalGaussModelNormLemmas.sum_bar ι dK 0) (OrthogonalGaussModelNormLemmas.diff_sq ι dK 0)
    (by omega) (by rw [hb2]; simp) hs

/- English proof (translation)
Introduce `dK L hmod hCM p _ hp2 hpd ι hW`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m : ℤ, (p : ℤ) = 2 * m + 1 := by`. Break down `(Fact.out : p.Prime).eq_two_or_odd with h | h` into its components or cases. Conclude with `absurd h hp2`. Conclude with `⟨(p : ℤ) / 2, by omega⟩`.

Establish `hN : ¬ (p : ℤ) ∣ normInt dK m 1`. Introduce `h`. Establish `h4` using `OrthogonalGaussModelNormLemmas.four_normInt hmod m`. Apply `hpd` to reduce the goal to its premises. Establish `h2 : (p : ℤ) ∣ (dK : ℤ)`.

Establish `e : (dK : ℤ) = 4 * normInt dK m 1 - (p : ℤ) * (p : ℤ)`. Rewrite using `[h4, hm]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `dvd_sub (Dvd.dvd.mul_left h 4) (Dvd.intro _ rfl)`.

Conclude with `h2` after adjusting the coercions. Take `⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩` from `hD dK L hmod hCM p ι hW m 1 hN`. Establish `hb2 : (curveL p L ι).b₂ = 0` using `(Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1`. Establish `hdiff : ‖ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) - ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))‖ = 1`. Establish `h1` using `congrArg norm (OrthogonalGaussModelNormLemmas.diff_sq ι dK m)`.

Rewrite `h1` using `[norm_pow, norm_neg, Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p hpd]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1`. Conclude with `Formalism.L2.Th1.G.curveJetsUnramThm ℂ_[p] (curveL p L ι) (OrthogonalGaussModelNormLemmas.coeffIn hW) (OrthogonalGaussModelNormLemmas.norm_two p hp2) (ι (Formalism.L2.Th1.F.s2 L)) _ _ (2 * m + 1) S neg xP yP hE hx hy hprod (OrthogonalGaussModelNormLemmas.norm_al ι hmod m hN) (Ort …`.
-/
theorem JetsCM_of (hD : CMDatum) : JetsCM := by
  intro dK L hmod hCM p _ hp2 hpd ι hW
  obtain ⟨m, hm⟩ : ∃ m : ℤ, (p : ℤ) = 2 * m + 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact ⟨(p : ℤ) / 2, by omega⟩
  have hN : ¬ (p : ℤ) ∣ normInt dK m 1 := by
    intro h
    have h4 := OrthogonalGaussModelNormLemmas.four_normInt hmod m
    apply hpd
    have h2 : (p : ℤ) ∣ (dK : ℤ) := by
      have e : (dK : ℤ) = 4 * normInt dK m 1 - (p : ℤ) * (p : ℤ) := by
        rw [h4, hm]
        ring
      rw [e]
      exact dvd_sub (Dvd.dvd.mul_left h 4) (Dvd.intro _ rfl)
    exact_mod_cast h2
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod, hs⟩ := hD dK L hmod hCM p ι hW m 1 hN
  have hb2 : (curveL p L ι).b₂ = 0 := (Formalism.L2.Th1.A.shortInv ℂ_[p] _ _).1
  have hdiff : ‖ι ((m : ℂ) + ((1 : ℤ) : ℂ) * omegaK dK) -
      ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - omegaK dK))‖ = 1 := by
    have h1 := congrArg norm (OrthogonalGaussModelNormLemmas.diff_sq ι dK m)
    rw [norm_pow, norm_neg, Formalism.L2.Th1.E.ScaledModelNorms.norm_nat p hpd] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h1
  exact Formalism.L2.Th1.G.curveJetsUnramThm ℂ_[p] (curveL p L ι) (OrthogonalGaussModelNormLemmas.coeffIn hW)
    (OrthogonalGaussModelNormLemmas.norm_two p hp2) (ι (Formalism.L2.Th1.F.s2 L)) _ _ (2 * m + 1) S neg xP yP hE hx hy hprod
    (OrthogonalGaussModelNormLemmas.norm_al ι hmod m hN) (OrthogonalGaussModelNormLemmas.sum_bar ι dK m) hdiff (by rw [hb2]; simp) hs

end Formalism.L2.Th1.Top
