import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementT

open PowerSeries

universe u

noncomputable section

namespace Formalism.L2.Th1.A

variable {R : Type u} [CommRing R]

/- English proof (translation)
Use `show (LaurentSeries.hasseDeriv R 1 f).coeff n = _`. Rewrite using `[LaurentSeries.hasseDeriv_coeff]`. Simplify using `[Ring.choose_one_right, zsmul_eq_mul]`.
-/
theorem dL_coeff (f : LaurentSeries R) (n : ℤ) :
    (dL f).coeff n = ((n + 1 : ℤ) : R) * f.coeff (n + 1) := by
  show (LaurentSeries.hasseDeriv R 1 f).coeff n = _
  rw [LaurentSeries.hasseDeriv_coeff]
  simp [Ring.choose_one_right, zsmul_eq_mul]

/- English proof (translation)
Use `first`. Consider the case `(have h := HahnSeries.coeff_single_mul_add (r := (1 : R)) (x := f) (a := n - m) (b := m)`. Rewrite `h` using `[sub_add_cancel, one_mul]`. Conclude with `h)`. Consider the case `(have h := HahnSeries.single_mul_coeff_add (r := (1 : R)) (x := f) (a := n - m) (b := m)`.

Rewrite `h` using `[sub_add_cancel, one_mul]`. Conclude with `h)`.
-/
theorem uPow_mul_coeff (m n : ℤ) (f : LaurentSeries R) :
    (uPow m * f).coeff n = f.coeff (n - m) := by
  first
    | (have h := HahnSeries.coeff_single_mul_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)
    | (have h := HahnSeries.single_mul_coeff_add (r := (1 : R)) (x := f) (a := n - m) (b := m)
       rw [sub_add_cancel, one_mul] at h
       exact h)

/- English proof (translation)
Rewrite using `[HahnSeries.C_mul_eq_smul]`. Apply the tactic sequence `first | rw [HahnSeries.coeff_smul, smul_eq_mul] | rw [HahnSeries.smul_coeff, smul_eq_mul] | simp`.
-/
theorem C_mul_coeff (r : R) (f : LaurentSeries R) (n : ℤ) :
    (HahnSeries.C r * f).coeff n = r * f.coeff n := by
  rw [HahnSeries.C_mul_eq_smul]
  first | rw [HahnSeries.coeff_smul, smul_eq_mul] | rw [HahnSeries.smul_coeff, smul_eq_mul] | simp

/- English proof (translation)
Conclude with `HahnSeries.ofPowerSeries_apply_coeff f n`.
-/
theorem toL_coeff_nat (f : R⟦X⟧) (n : ℕ) : (toL f).coeff (n : ℤ) = coeff n f := by
  exact HahnSeries.ofPowerSeries_apply_coeff f n

/- English proof (translation)
Use `first`. Consider the case `(rw [PowerSeries.coeff_coe, if_pos hn])`. Consider the case `(simp only [toL, HahnSeries.ofPowerSeries_apply]`. Rewrite using `[HahnSeries.embDomain_notin_range]`. Introduce and unpack `⟨k, hk⟩`.

Simplify using `at hk`. Use the proof step `omega)`.
-/
theorem toL_coeff_neg (f : R⟦X⟧) {n : ℤ} (hn : n < 0) : (toL f).coeff n = 0 := by
  first
    | (rw [PowerSeries.coeff_coe, if_pos hn])
    | (simp only [toL, HahnSeries.ofPowerSeries_apply]
       rw [HahnSeries.embDomain_notin_range]
       rintro ⟨k, hk⟩
       simp at hk
       omega)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uPow_zero : (uPow 0 : LaurentSeries R) = 1 := rfl

/- English proof (translation)
Use `show HahnSeries.single (1 : ℤ) (1 : R) = _`. Rewrite using `[HahnSeries.ofPowerSeries_X]`.
-/
theorem uPow_one : (uPow 1 : LaurentSeries R) = toL X := by
  show HahnSeries.single (1 : ℤ) (1 : R) = _
  rw [HahnSeries.ofPowerSeries_X]

/- English proof (translation)
Use `show HahnSeries.single (m + n) (1 : R) = HahnSeries.single m 1 * HahnSeries.single n 1`. Rewrite using `[HahnSeries.single_mul_single, mul_one]`.
-/
theorem uPow_add (m n : ℤ) : (uPow (m + n) : LaurentSeries R) = uPow m * uPow n := by
  show HahnSeries.single (m + n) (1 : R) = HahnSeries.single m 1 * HahnSeries.single n 1
  rw [HahnSeries.single_mul_single, mul_one]

/- English proof (translation)
Rewrite using `[← uPow_add]`. Apply the tactic sequence `first | rw [neg_add_cancel] | rw [neg_add_self] | rw [add_left_neg]`. Conclude with `uPow_zero`.
-/
theorem uPow_neg_mul (n : ℤ) : (uPow (-n) : LaurentSeries R) * uPow n = 1 := by
  rw [← uPow_add]
  first | rw [neg_add_cancel] | rw [neg_add_self] | rw [add_left_neg]
  exact uPow_zero

/- English proof (translation)
Rewrite using `[← uPow_add]`. Apply the tactic sequence `first | rw [add_neg_cancel] | rw [add_neg_self] | rw [add_right_neg]`. Conclude with `uPow_zero`.
-/
theorem uPow_mul_neg (n : ℤ) : (uPow n : LaurentSeries R) * uPow (-n) = 1 := by
  rw [← uPow_add]
  first | rw [add_neg_cancel] | rw [add_neg_self] | rw [add_right_neg]
  exact uPow_zero

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem uPow_mul_cancel (n : ℤ) {f g : LaurentSeries R} (h : uPow n * f = uPow n * g) :
    f = g := by
  calc f = uPow (-n) * (uPow n * f) := by rw [← mul_assoc, uPow_neg_mul, one_mul]
    _ = uPow (-n) * (uPow n * g) := by rw [h]
    _ = g := by rw [← mul_assoc, uPow_neg_mul, one_mul]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [uPow_zero]`. Consider the case `succ k ih => rw [Nat.cast_succ, uPow_add, ih, uPow_one, ← map_mul, pow_succ]`.
-/
theorem uPow_natCast (n : ℕ) : (uPow (n : ℤ) : LaurentSeries R) = toL (X ^ n) := by
  induction n with
  | zero => simp [uPow_zero]
  | succ k ih => rw [Nat.cast_succ, uPow_add, ih, uPow_one, ← map_mul, pow_succ]

/- English proof (translation)
Use `first`. Consider the case `exact HahnSeries.ofPowerSeries_C r`. Consider the case `simp [toL]`.
-/
theorem toL_C (r : R) : toL (C r) = (HahnSeries.C r : LaurentSeries R) := by
  first
    | exact HahnSeries.ofPowerSeries_C r
    | simp [toL]

/- English proof (translation)
Conclude with `HahnSeries.ofPowerSeries_injective`.
-/
theorem toL_injective : Function.Injective (toL : R⟦X⟧ → LaurentSeries R) := by
  exact HahnSeries.ofPowerSeries_injective

/- English proof (translation)
Use `⟨f.order, f.powerSeriesPart, ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `exact (LaurentSeries.single_order_mul_powerSeriesPart f).symm`. Consider the case `(show f = uPow f.order * HahnSeries.ofPowerSeries ℤ R f.powerSeriesPart`. Rewrite using `[LaurentSeries.ofPowerSeries_powerSeriesPart]`.

Express the relevant statement in the definitionally equal form `f = uPow f.order * (uPow (-f.order) * f)`. Rewrite using `[← mul_assoc, uPow_mul_neg, one_mul])`.
-/
theorem exists_uPow_mul_toL (f : LaurentSeries R) :
    ∃ (m : ℤ) (F : R⟦X⟧), f = uPow m * toL F := by
  refine ⟨f.order, f.powerSeriesPart, ?_⟩
  first
    | exact (LaurentSeries.single_order_mul_powerSeriesPart f).symm
    | (show f = uPow f.order * HahnSeries.ofPowerSeries ℤ R f.powerSeriesPart
       rw [LaurentSeries.ofPowerSeries_powerSeriesPart]
       change f = uPow f.order * (uPow (-f.order) * f)
       rw [← mul_assoc, uPow_mul_neg, one_mul])

/- English proof (translation)
Rewrite using `[show HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f = HahnSeries.C ((m : ℤ) : R) * (uPow (m - 1) * f) from mul_assoc _ _ _]`. Use extensionality with `n`. Apply the tactic sequence `first | rw [HahnSeries.add_coeff] | rw [HahnSeries.coeff_add] | rw [HahnSeries.add_coeff']`. Rewrite using `[dL_coeff, uPow_mul_coeff, uPow_mul_coeff, dL_coeff, C_mul_coeff, uPow_mul_coeff]`. Establish `h1 : n + 1 - m = n - m + 1` using `by ring`.

Establish `h2 : n - (m - 1) = n - m + 1` using `by ring`. Rewrite using `[h1, h2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dL_uPow_mul (m : ℤ) (f : LaurentSeries R) :
    dL (uPow m * f) = uPow m * dL f + HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f := by
  rw [show HahnSeries.C ((m : ℤ) : R) * uPow (m - 1) * f
      = HahnSeries.C ((m : ℤ) : R) * (uPow (m - 1) * f) from mul_assoc _ _ _]
  ext n
  first | rw [HahnSeries.add_coeff] | rw [HahnSeries.coeff_add] | rw [HahnSeries.add_coeff']
  rw [dL_coeff, uPow_mul_coeff, uPow_mul_coeff, dL_coeff, C_mul_coeff, uPow_mul_coeff]
  have h1 : n + 1 - m = n - m + 1 := by ring
  have h2 : n - (m - 1) = n - m + 1 := by ring
  rw [h1, h2]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[dL_coeff]`. Break down `lt_or_ge n 0 with hn | hn` into its components or cases. Rewrite using `[toL_coeff_neg _ hn]`. Break down `lt_or_eq_of_le (show n + 1 ≤ 0 by omega) with h | h` into its components or cases.

Rewrite using `[toL_coeff_neg _ h, mul_zero]`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hn`. Establish `hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ)` using `by push_cast; ring`.

Rewrite using `[hk, toL_coeff_nat, toL_coeff_nat, PowerSeries.coeff_derivative]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dL_toL (f : R⟦X⟧) : dL (toL f) = toL (derivative R f) := by
  ext n
  rw [dL_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [toL_coeff_neg _ hn]
    rcases lt_or_eq_of_le (show n + 1 ≤ 0 by omega) with h | h
    · rw [toL_coeff_neg _ h, mul_zero]
    · rw [h]
      simp
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    have hk : ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hk, toL_coeff_nat, toL_coeff_nat, PowerSeries.coeff_derivative]
    push_cast
    ring

/- English proof (translation)
Take `⟨m, F, rfl⟩` from `exists_uPow_mul_toL f`. Take `⟨k, G, rfl⟩` from `exists_uPow_mul_toL g`. Establish `e : uPow m * toL F * (uPow k * toL G) = uPow (m + k) * toL (F * G)`. Rewrite using `[uPow_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0 : (uPow (m + k) : LaurentSeries R) = uPow m * uPow k` using `uPow_add m k`. Establish `h1 : (uPow (m + k - 1) : LaurentSeries R) = uPow (m - 1) * uPow k`. Rewrite using `[← uPow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : (uPow (m + k - 1) : LaurentSeries R) = uPow m * uPow (k - 1)`. Rewrite using `[← uPow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : (HahnSeries.C (((m + k : ℤ)) : R) : LaurentSeries R) = HahnSeries.C ((m : ℤ) : R) + HahnSeries.C ((k : ℤ) : R)`.

Rewrite using `[Int.cast_add, map_add]`. Rewrite using `[e, dL_uPow_mul, dL_toL, Derivation.leibniz]`. Simplify using `only [dL_uPow_mul, dL_toL, Derivation.leibniz, smul_eq_mul, map_add, map_mul]`. Take the linear combination `(toL F * toL (derivative R G) + toL G * toL (derivative R F)) * h0 + (toL F * toL G * uPow (m + k - 1)) * h3 + (HahnSeries.C ((m : ℤ) : R) * toL F * toL G) * h1 + (HahnSeries.C ((k : ℤ) : R) * toL F * toL G) * h2`.
-/
theorem dL_mul (f g : LaurentSeries R) : dL (f * g) = f * dL g + g * dL f := by
  obtain ⟨m, F, rfl⟩ := exists_uPow_mul_toL f
  obtain ⟨k, G, rfl⟩ := exists_uPow_mul_toL g
  have e : uPow m * toL F * (uPow k * toL G) = uPow (m + k) * toL (F * G) := by
    rw [uPow_add, map_mul]; ring
  have h0 : (uPow (m + k) : LaurentSeries R) = uPow m * uPow k := uPow_add m k
  have h1 : (uPow (m + k - 1) : LaurentSeries R) = uPow (m - 1) * uPow k := by
    rw [← uPow_add]; congr 1; ring
  have h2 : (uPow (m + k - 1) : LaurentSeries R) = uPow m * uPow (k - 1) := by
    rw [← uPow_add]; congr 1; ring
  have h3 : (HahnSeries.C (((m + k : ℤ)) : R) : LaurentSeries R)
      = HahnSeries.C ((m : ℤ) : R) + HahnSeries.C ((k : ℤ) : R) := by
    rw [Int.cast_add, map_add]
  rw [e, dL_uPow_mul, dL_toL, Derivation.leibniz]
  simp only [dL_uPow_mul, dL_toL, Derivation.leibniz, smul_eq_mul, map_add, map_mul]
  linear_combination (toL F * toL (derivative R G) + toL G * toL (derivative R F)) * h0
    + (toL F * toL G * uPow (m + k - 1)) * h3
    + (HahnSeries.C ((m : ℤ) : R) * toL F * toL G) * h1
    + (HahnSeries.C ((k : ℤ) : R) * toL F * toL G) * h2

/- English proof (translation)
Establish `h1 : dL (1 : LaurentSeries R) = 0`. Establish `h` using `dL_toL (R := R) 1`. Rewrite `h` using `[map_one, Derivation.map_one_eq_zero, map_zero]`. Then use the resulting hypothesis. Establish `h` using `dL_uPow_mul n (1 : LaurentSeries R)`. Rewrite `h` using `[mul_one, mul_one, h1, mul_zero, zero_add]`.

Conclude with `h`.
-/
theorem dL_uPow (n : ℤ) :
    dL (uPow n : LaurentSeries R) = HahnSeries.C ((n : ℤ) : R) * uPow (n - 1) := by
  have h1 : dL (1 : LaurentSeries R) = 0 := by
    have h := dL_toL (R := R) 1
    rwa [map_one, Derivation.map_one_eq_zero, map_zero] at h
  have h := dL_uPow_mul n (1 : LaurentSeries R)
  rw [mul_one, mul_one, h1, mul_zero, zero_add] at h
  exact h

/- English proof (translation)
Rewrite using `[← toL_C, dL_toL]`. Apply the tactic sequence `first | rw [PowerSeries.derivative_C, map_zero] | simp`.
-/
theorem dL_C (r : R) : dL (HahnSeries.C r : LaurentSeries R) = 0 := by
  rw [← toL_C, dL_toL]
  first | rw [PowerSeries.derivative_C, map_zero] | simp

/- English proof (translation)
Establish `h` using `dL_C (R := R) 1`. Rewrite `h` using `[map_one]`. Then use the resulting hypothesis.
-/
theorem dL_one : dL (1 : LaurentSeries R) = 0 := by
  have h := dL_C (R := R) 1
  rwa [map_one] at h

/- English proof (translation)
Introduce `R _ f n`. Conclude with `dL_coeff f n`.
-/
theorem derivation_coeff : DLCoeff.{u} := by
  intro R _ f n
  exact dL_coeff f n

/- English proof (translation)
Introduce `R _ f g`. Conclude with `dL_mul f g`.
-/
theorem derivation_leibniz : DLLeibniz.{u} := by
  intro R _ f g
  exact dL_mul f g

/- English proof (translation)
Introduce `R _ f`. Conclude with `dL_toL f`.
-/
theorem derivation_coe : DLCoe.{u} := by
  intro R _ f
  exact dL_toL f

/- English proof (translation)
Introduce `R _`. Conclude with `⟨uPow_zero, uPow_one, uPow_add, dL_uPow, dL_C, toL_C⟩`.
-/
theorem laurent_power_rules : UPowRules.{u} := by
  intro R _
  exact ⟨uPow_zero, uPow_one, uPow_add, dL_uPow, dL_C, toL_C⟩

/- English proof (translation)
Introduce `R _`. Conclude with `⟨toL_injective, fun n f g h => uPow_mul_cancel n h⟩`.
-/
theorem laurent_embedding_injective : ToLInjective.{u} := by
  intro R _
  exact ⟨toL_injective, fun n f g h => uPow_mul_cancel n h⟩

def derivationOfLeibniz {k A M : Type*} [CommSemiring k] [CommSemiring A] [AddCommGroup M]
    [Algebra k A] [Module A M] [Module k M] (D : A → M)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hsmul : ∀ (r : k) (a : A), D (r • a) = r • D a)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a) : Derivation k A M :=
  Derivation.mk' { toFun := D, map_add' := hadd, map_smul' := hsmul } hmul

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derivationOfLeibniz_apply {k A M : Type*} [CommSemiring k] [CommSemiring A]
    [AddCommGroup M] [Algebra k A] [Module A M] [Module k M] (D : A → M)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hsmul : ∀ (r : k) (a : A), D (r • a) = r • D a)
    (hmul : ∀ a b, D (a * b) = a • D b + b • D a) (a : A) :
    derivationOfLeibniz D hadd hsmul hmul a = D a := rfl

def dLDR (R : Type u) [CommRing R] : Derivation R (LaurentSeries R) (LaurentSeries R) :=
  derivationOfLeibniz (fun f => dL f) (fun a b => map_add dL a b)
    (fun r f => by
      rw [Algebra.smul_def, HahnSeries.algebraMap_apply', ← HahnSeries.C_mul_eq_smul]
      change dL (toL (C r) * f) = _
      rw [toL_C, dL_mul, dL_C, mul_zero, add_zero])
    (fun f g => by rw [smul_eq_mul, smul_eq_mul, dL_mul])

def dLD (R : Type u) [CommRing R] : Derivation ℤ (LaurentSeries R) (LaurentSeries R) :=
  derivationOfLeibniz (fun f => dL f) (fun a b => map_add dL a b)
    (fun r f => by
      rw [Algebra.smul_def, eq_intCast, zsmul_eq_mul, dL_mul,
        ← map_intCast (HahnSeries.C : R →+* LaurentSeries R), dL_C, mul_zero, add_zero])
    (fun f g => by rw [smul_eq_mul, smul_eq_mul, dL_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem dLDR_apply (f : LaurentSeries R) : dLDR R f = dL f := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem dLD_apply (f : LaurentSeries R) : dLD R f = dL f := rfl

/- English proof (translation)
Conclude with `⟨fun a b => map_add dL a b, dL_mul⟩`.
-/
theorem isDer_dL : (∀ a b : LaurentSeries R, dL (a + b) = dL a + dL b) ∧
    (∀ a b : LaurentSeries R, dL (a * b) = a * dL b + b * dL a) := by
  exact ⟨fun a b => map_add dL a b, dL_mul⟩

/- English proof (translation)
Establish `h0` using `dL_mul f g`. Rewrite `h0` using `[h, dL_one]`. Take the linear combination `(-g) * h0 - (dL g) * h`.
-/
theorem dL_inv_of_mul_eq_one {f g : LaurentSeries R} (h : f * g = 1) :
    dL g = - g ^ 2 * dL f := by
  have h0 := dL_mul f g
  rw [h, dL_one] at h0
  linear_combination (-g) * h0 - (dL g) * h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [dL_one]`. Consider the case `succ k ih`. Rewrite using `[pow_succ, dL_mul, ih]`. Break down `k with _ | j` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dL_pow (f : LaurentSeries R) (n : ℕ) :
    dL (f ^ n) = (n : LaurentSeries R) * f ^ (n - 1) * dL f := by
  induction n with
  | zero => simp [dL_one]
  | succ k ih =>
    rw [pow_succ, dL_mul, ih]
    rcases k with _ | j
    · simp
    · simp only [Nat.add_sub_cancel]
      push_cast
      ring

/- English proof (translation)
Conclude with `map_neg dL f`.
-/
theorem dL_neg (f : LaurentSeries R) : dL (-f) = - dL f := by
  exact map_neg dL f

/- English proof (translation)
Conclude with `map_sub dL f g`.
-/
theorem dL_sub (f g : LaurentSeries R) : dL (f - g) = dL f - dL g := by
  exact map_sub dL f g

/- English proof (translation)
Rewrite using `[dL_mul, dL_C, mul_zero, add_zero]`.
-/
theorem dL_C_mul (r : R) (f : LaurentSeries R) :
    dL (HahnSeries.C r * f) = HahnSeries.C r * dL f := by
  rw [dL_mul, dL_C, mul_zero, add_zero]

end Formalism.L2.Th1.A
