import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TaylorShift

variable {K : Type} [Field K] [CharZero K]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n, Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun ij hij => ?_` and prove the remaining obligations.

Rewrite `hij` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Establish `hc : (n.choose ij.2 : K⟦X⟧) = (n.choose ij.1 : K⟦X⟧)`. Rewrite using `[← hij, Nat.choose_symm_add]`. Rewrite using `[hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero, Function.iterate_succ_apply', Function.iterate_succ_apply']`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem iterate_leibniz_ps (D : Derivation K K⟦X⟧ K⟦X⟧) (a b : K⟦X⟧) (n : ℕ) :
    (⇑D)^[n] (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (n.choose ij.1 : K⟦X⟧) * ((⇑D)^[ij.1] a * (⇑D)^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_mul (fun i j => (⇑D)^[i] a * (⇑D)^[j] b) n,
      Function.iterate_succ_apply', ih, map_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hc : (n.choose ij.2 : K⟦X⟧) = (n.choose ij.1 : K⟦X⟧) := by
      rw [← hij, Nat.choose_symm_add]
    rw [hc, Derivation.leibniz, Derivation.leibniz, Derivation.map_natCast, smul_zero, add_zero,
      Function.iterate_succ_apply', Function.iterate_succ_apply']
    simp only [smul_eq_mul]
    ring

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply, map_zero, ih]`.
-/
theorem iterate_derivative_zero (n : ℕ) : (⇑(PowerSeries.derivative K))^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, map_zero, ih]

def shiftFun (f : K⟦X⟧) : K⟦X⟧⟦X⟧ :=
  PowerSeries.mk fun i => ((i.factorial : K)⁻¹) • (⇑(PowerSeries.derivative K))^[i] f

/- English proof (translation)
The claim follows from `coeff_mk _ _`.
-/
theorem coeff_shiftFun (f : K⟦X⟧) (i : ℕ) :
    coeff i (shiftFun f) = ((i.factorial : K)⁻¹) • (⇑(PowerSeries.derivative K))^[i] f :=
  coeff_mk _ _

/- English proof (translation)
Proceed by induction on `n generalizing f g with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_add, ih]`.
-/
theorem iterate_derivative_add (n : ℕ) (f g : K⟦X⟧) :
    (⇑(PowerSeries.derivative K))^[n] (f + g) =
      (⇑(PowerSeries.derivative K))^[n] f + (⇑(PowerSeries.derivative K))^[n] g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_add, ih]

def shift : K⟦X⟧ →+* K⟦X⟧⟦X⟧ where
  toFun := shiftFun
  map_one' := by
    ext i : 1
    rw [coeff_shiftFun, coeff_one]
    rcases i with _ | i
    · simp
    · rw [Function.iterate_succ_apply, Derivation.map_one_eq_zero, iterate_derivative_zero]
      simp
  map_mul' f g := by
    ext i : 1
    rw [coeff_mul, coeff_shiftFun, iterate_leibniz_ps, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [coeff_shiftFun, coeff_shiftFun]
    subst hij
    have hc : ((ij.1 + ij.2).choose ij.1 : K⟦X⟧) =
        C (((ij.1 + ij.2).factorial : K) / ((ij.1.factorial : K) * (ij.2.factorial : K))) := by
      rw [← Nat.cast_add_choose, map_natCast]
    have h0 : ((ij.1 + ij.2).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1 : (ij.1.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (ij.2.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hk : ((ij.1 + ij.2).factorial : K)⁻¹ * (((ij.1 + ij.2).factorial : K) /
        ((ij.1.factorial : K) * (ij.2.factorial : K))) = (ij.1.factorial : K)⁻¹ * (ij.2.factorial : K)⁻¹ := by
      field_simp
    rw [hc, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, ← mul_assoc, ← map_mul, hk, map_mul]
    ring
  map_zero' := by
    ext i : 1
    rw [coeff_shiftFun, iterate_derivative_zero, smul_zero, map_zero]
  map_add' f g := by
    ext i : 1
    rw [coeff_shiftFun, map_add, coeff_shiftFun, coeff_shiftFun, iterate_derivative_add, smul_add]

/- English proof (translation)
The claim follows from `coeff_shiftFun f i`.
-/
theorem coeff_shift (f : K⟦X⟧) (i : ℕ) :
    coeff i (shift f) = ((i.factorial : K)⁻¹) • (⇑(PowerSeries.derivative K))^[i] f :=
  coeff_shiftFun f i

/- English proof (translation)
Use extensionality with `i : 1`. Rewrite using `[coeff_shift, coeff_C]`. Break down `i with _ | i` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[Function.iterate_succ_apply, PowerSeries.derivative_C, iterate_derivative_zero]`.

Simplify using the standard rewrite rules.
-/
theorem shift_C (c : K) : shift (C c) = C (C c : K⟦X⟧) := by
  ext i : 1
  rw [coeff_shift, coeff_C]
  rcases i with _ | i
  · simp
  · rw [Function.iterate_succ_apply, PowerSeries.derivative_C, iterate_derivative_zero]
    simp

/- English proof (translation)
Use extensionality with `i : 1`. Rewrite using `[coeff_shift, map_add, coeff_C, coeff_X]`. Break down `i with _ | _ | i` into its components or cases. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Rewrite using `[Function.iterate_succ_apply, PowerSeries.derivative_X, Function.iterate_succ_apply, Derivation.map_one_eq_zero, iterate_derivative_zero]`. Simplify using the standard rewrite rules.
-/
theorem shift_X : shift (X : K⟦X⟧) = C (X : K⟦X⟧) + X := by
  ext i : 1
  rw [coeff_shift, map_add, coeff_C, coeff_X]
  rcases i with _ | _ | i
  · simp
  · simp
  · rw [Function.iterate_succ_apply, PowerSeries.derivative_X, Function.iterate_succ_apply,
      Derivation.map_one_eq_zero, iterate_derivative_zero]
    simp

end GlobalTheory.TaylorShift

namespace GlobalTheory.TaylorShift

section Frob

attribute [-instance] PowerSeries.algebraPowerSeries MvPowerSeries.algebraMvPowerSeries

variable {K : Type} [NormedField K] (l : ℕ) [Fact l.Prime]

def frobW : K⟦X⟧⟦X⟧ := (C (X : K⟦X⟧) + X) ^ l - C ((X : K⟦X⟧) ^ l)

/- English proof (translation)
Simplify using `[frobW]`.
-/
theorem constantCoeff_frobW : constantCoeff (frobW (K := K) l) = 0 := by
  simp [frobW]

def frob2 : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧ :=
  (PowerSeries.substAlgHom (HasSubst.of_constantCoeff_zero' (constantCoeff_frobW (K := K) l))).toRingHom.comp
    (PowerSeries.map (frob K l).toRingHom)

/- English proof (translation)
Simplify using `only [frob2, RingHom.comp_apply, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Use `(PowerSeries.substAlgHom (HasSubst.of_constantCoeff_zero' (constantCoeff_frobW (K := K) l))).commutes (frob K l f)` as an intermediate fact. Conclude with `this`.
-/
theorem frobeniusTwoVariablePowerSeries_C (f : K⟦X⟧) : frob2 l (C f) = C (frob K l f) := by
  simp only [frob2, RingHom.comp_apply, map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have := (PowerSeries.substAlgHom (HasSubst.of_constantCoeff_zero' (constantCoeff_frobW (K := K) l))).commutes
    (frob K l f)
  exact this

/- English proof (translation)
Simplify using `only [frob2, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Conclude with `PowerSeries.substAlgHom_X _`.
-/
theorem frobeniusTwoVariablePowerSeries_X : frob2 l (X : K⟦X⟧⟦X⟧) = frobW l := by
  simp only [frob2, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  exact PowerSeries.substAlgHom_X _

end Frob

end GlobalTheory.TaylorShift

namespace GlobalTheory.TaylorShift

section Unique

variable {K : Type} [Field K]

def Small (N : ℕ) (y : K⟦X⟧⟦X⟧) : Prop := ∀ i n, i + n < N → coeff n (coeff i y) = 0

/- English proof (translation)
Introduce `i n h`. Rewrite using `[coeff_mul, map_sum]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Rewrite using `[coeff_mul]`. Use `Finset.sum_eq_zero fun q hq => ?_` and prove the remaining obligations.

Rewrite `hp`, `hq` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Distinguish the cases in `h1 : p.1 + q.1 < a`. Rewrite using `[hy _ _ h1, zero_mul]`. Rewrite using `[hz _ _ (by omega), mul_zero]`.
-/
theorem small_mul {a b : ℕ} {y z : K⟦X⟧⟦X⟧} (hy : Small a y) (hz : Small b z) :
    Small (a + b) (y * z) := by
  intro i n h
  rw [coeff_mul, map_sum]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
  by_cases h1 : p.1 + q.1 < a
  · rw [hy _ _ h1, zero_mul]
  · rw [hz _ _ (by omega), mul_zero]

/- English proof (translation)
Introduce `i n h` and use `hy i n (by omega)`.
-/
theorem small_mono {a b : ℕ} {y : K⟦X⟧⟦X⟧} (hy : Small a y) (hab : b ≤ a) : Small b y :=
  fun i n h => hy i n (by omega)

/- English proof (translation)
Introduce `i n h`. Take `⟨rfl, rfl⟩ : i = 0 ∧ n = 0` from `by omega`. Simplify using the standard rewrite rules.
-/
theorem twoVariableSeriesVanishesBelowDegree_one_shiftVariable : Small 1 (C (X : K⟦X⟧) + X : K⟦X⟧⟦X⟧) := by
  intro i n h
  obtain ⟨rfl, rfl⟩ : i = 0 ∧ n = 0 := by omega
  simp

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => intro i n h`. Use linear arithmetic over natural numbers and integers. Consider the case `succ N ih`. Rewrite using `[pow_succ', mul_assoc, add_comm N 1]`.

Conclude with `small_mul twoVariableSeriesVanishesBelowDegree_one_shiftVariable ih`.
-/
theorem small_pow_mul (N : ℕ) (z : K⟦X⟧⟦X⟧) : Small N ((C (X : K⟦X⟧) + X) ^ N * z) := by
  induction N with
  | zero => intro i n h; omega
  | succ N ih =>
    rw [pow_succ', mul_assoc, add_comm N 1]
    exact small_mul twoVariableSeriesVanishesBelowDegree_one_shiftVariable ih

/- English proof (translation)
Use extensionality with `i n`. Rewrite using `[h (i + n + 1) i n (by omega), map_zero, map_zero]`.
-/
theorem eq_zero_of_small {y : K⟦X⟧⟦X⟧} (h : ∀ N, Small N y) : y = 0 := by
  ext i n
  rw [h (i + n + 1) i n (by omega), map_zero, map_zero]

/- English proof (translation)
Establish `hpoly : ∀ p : Polynomial K, α (p : K⟦X⟧) = β (p : K⟦X⟧)`. Use `Polynomial.ringHom_ext (f := α.comp (Polynomial.coeToPowerSeries.ringHom)) (g := β.comp (Polynomial.coeToPowerSeries.ringHom)) (fun a => by simpa using hC a) (by simpa using hX)` as an intermediate fact. Introduce `p`. Conclude with `RingHom.congr_fun this p`. Use `ext1 f`.

Apply `sub_eq_zero.mp` to reduce the goal to its premises. Apply `eq_zero_of_small` to reduce the goal to its premises. Introduce `N`. Choose the witnesses or unpack the hypotheses as in `⟨g, hg⟩ : X ^ N ∣ f - (trunc N f : K⟦X⟧) := by`. Rewrite using `[X_pow_dvd_iff]`.

Introduce `k hk`. Simplify using `[coeff_trunc, hk]`. Establish `hf : f = (trunc N f : K⟦X⟧) + X ^ N * g` using `by rw [← hg]; ring`. Rewrite using `[hf, map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, ← hX, hs, add_sub_add_left_eq_sub, ← mul_sub, ← pow_mul]`. Conclude with `small_mono (small_pow_mul _ _) (Nat.le_mul_of_pos_left N hm)`.
-/
theorem ringHom_eq_of (α β : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (hC : ∀ c : K, α (C c) = β (C c)) (hX : α X = β X)
    (m : ℕ) (hm : 1 ≤ m) (hs : α X = (C (X : K⟦X⟧) + X) ^ m) : α = β := by
  have hpoly : ∀ p : Polynomial K, α (p : K⟦X⟧) = β (p : K⟦X⟧) := by
    have := Polynomial.ringHom_ext (f := α.comp (Polynomial.coeToPowerSeries.ringHom))
      (g := β.comp (Polynomial.coeToPowerSeries.ringHom)) (fun a => by simpa using hC a) (by simpa using hX)
    intro p
    exact RingHom.congr_fun this p
  ext1 f
  apply sub_eq_zero.mp
  apply eq_zero_of_small
  intro N
  obtain ⟨g, hg⟩ : X ^ N ∣ f - (trunc N f : K⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro k hk
    simp [coeff_trunc, hk]
  have hf : f = (trunc N f : K⟦X⟧) + X ^ N * g := by rw [← hg]; ring
  rw [hf, map_add, map_add, hpoly, map_mul, map_mul, map_pow, map_pow, ← hX, hs, add_sub_add_left_eq_sub,
    ← mul_sub, ← pow_mul]
  exact small_mono (small_pow_mul _ _) (Nat.le_mul_of_pos_left N hm)

end Unique

/- English proof (translation)
Introduce `l _ K _ _`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective`. Establish `hl : 1 ≤ l` using `(Fact.out : l.Prime).one_lt.le`. Use `⟨shift, frob2 l, fun f i => ?_, frobeniusTwoVariablePowerSeries_C l, fun f => ?_⟩` and prove the remaining obligations. Establish `h0 : (i.factorial : K) ≠ 0` using `Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)`.

Rewrite using `[coeff_shift, smul_eq_C_mul, ← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]`. Establish `key : (frob2 l).comp shift = shift.comp (frob K l).toRingHom`. Use `ringHom_eq_of _ _ (fun c => ?_) ?_ l hl ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, shift_C, frobeniusTwoVariablePowerSeries_C, frob_C]`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, shift_X, frob_X, map_pow, map_add, frobeniusTwoVariablePowerSeries_C, frobeniusTwoVariablePowerSeries_X, frobW, frob_X]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [RingHom.comp_apply, shift_X, map_add, frobeniusTwoVariablePowerSeries_C, frobeniusTwoVariablePowerSeries_X, frobW, frob_X]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `RingHom.congr_fun key f`.
-/
theorem shift_frob_exists : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K],
    ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧),
      (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) ∧
      (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧
      (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  intro l _ K _ _
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  refine ⟨shift, frob2 l, fun f i => ?_, frobeniusTwoVariablePowerSeries_C l, fun f => ?_⟩
  · have h0 : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [coeff_shift, smul_eq_C_mul, ← map_natCast (C : K →+* K⟦X⟧), ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ h0, map_one, one_mul]
  · have key : (frob2 l).comp shift = shift.comp (frob K l).toRingHom := by
      refine ringHom_eq_of _ _ (fun c => ?_) ?_ l hl ?_
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, shift_C, frobeniusTwoVariablePowerSeries_C, frob_C]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, shift_X, frob_X, map_pow,
          map_add, frobeniusTwoVariablePowerSeries_C, frobeniusTwoVariablePowerSeries_X, frobW, frob_X]
        ring
      · simp only [RingHom.comp_apply, shift_X, map_add, frobeniusTwoVariablePowerSeries_C, frobeniusTwoVariablePowerSeries_X, frobW, frob_X]
        ring
    exact RingHom.congr_fun key f

end GlobalTheory.TaylorShift
