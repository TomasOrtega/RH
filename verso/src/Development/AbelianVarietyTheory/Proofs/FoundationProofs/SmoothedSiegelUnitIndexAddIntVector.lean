import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Foundations.MultipliableAndSgNeZero

noncomputable section

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam GlobalTheory.Sieg.Model

namespace GlobalTheory.Sieg.Per

def qp (q u : ℂ) : ℂ := ∏' m : ℕ, (1 - q ^ (m + 1) * u)

/- English proof (translation)
Establish `hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * u)‖`. Simplify using `only [norm_neg, norm_mul, norm_pow, pow_succ]`. Conclude with `((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _`. Simplify `multipliable_one_add_of_summable hs` using `[sub_eq_add_neg]`.
-/
theorem multipliable_qp {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun m : ℕ => 1 - q ^ (m + 1) * u := by
  have hs : Summable fun m : ℕ => ‖-(q ^ (m + 1) * u)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_succ]
    exact ((summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _).mul_right _
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

/- English proof (translation)
Establish `e : (fun m : ℕ => 1 - q ^ (m + 1 + 1) * u) = fun m : ℕ => 1 - q ^ (m + 1) * (q * u)`. Use function extensionality and compare the values at `m`. Expand and normalize the polynomial expressions, which then agree. Establish `h : Multipliable fun m : ℕ => (fun m : ℕ => 1 - q ^ (m + 1) * u) (m + 1)` using `by show Multipliable fun m : ℕ => 1 - q ^ (m + 1 + 1) * u`. Rewrite using `[e]`.

Conclude with `multipliable_qp hq _`. Use `tprod_eq_zero_mul' (f := fun m : ℕ => 1 - q ^ (m + 1) * u) h` as an intermediate fact. Simplify using `only [e, zero_add, pow_one] at this`. Conclude with `this`.
-/
theorem qp_shift {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : qp q u = (1 - q * u) * qp q (q * u) := by
  have e : (fun m : ℕ => 1 - q ^ (m + 1 + 1) * u) = fun m : ℕ => 1 - q ^ (m + 1) * (q * u) := by
    funext m; ring
  have h : Multipliable fun m : ℕ => (fun m : ℕ => 1 - q ^ (m + 1) * u) (m + 1) := by
    show Multipliable fun m : ℕ => 1 - q ^ (m + 1 + 1) * u
    rw [e]; exact multipliable_qp hq _
  have := tprod_eq_zero_mul' (f := fun m : ℕ => 1 - q ^ (m + 1) * u) h
  simp only [e, zero_add, pow_one] at this
  exact this

def tp (q u : ℂ) : ℂ := (1 - u) * qp q u * qp q u⁻¹

/- English proof (translation)
Establish `e : q * (q * u)⁻¹ = u⁻¹` using `by field_simp`. Unfold `tp`. Rewrite using `[← qp_shift hq u, qp_shift hq (q * u)⁻¹, e]`. Establish `: 1 - u⁻¹ = -u⁻¹ * (1 - u)` using `by field_simp; ring`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem tp_shift {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) : tp q (q * u) = -u⁻¹ * tp q u := by
  have e : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  unfold tp
  rw [← qp_shift hq u, qp_shift hq (q * u)⁻¹, e]
  have : 1 - u⁻¹ = -u⁻¹ * (1 - u) := by field_simp; ring
  rw [this]; ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : q ^ (k + 1) * u = q * (q ^ k * u)` using `by ring`. Establish `e2 : (k + 1).choose 2 = k + k.choose 2`.

Rewrite using `[Nat.choose_succ_succ' k 1, Nat.choose_one_right]`. Rewrite using `[e, tp_shift hq hq0 (mul_ne_zero (pow_ne_zero _ hq0) hu), ih, e2, pow_add q, pow_succ (-u⁻¹)]`. Generalize the expression as in `(-u⁻¹) ^ k = A`. Clear the denominators using the available nonvanishing facts.
-/
theorem tp_shift_pow {q u : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hu : u ≠ 0) (k : ℕ) :
    tp q (q ^ k * u) = (-u⁻¹) ^ k * (q ^ (k.choose 2))⁻¹ * tp q u := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : q ^ (k + 1) * u = q * (q ^ k * u) := by ring
    have e2 : (k + 1).choose 2 = k + k.choose 2 := by
      rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [e, tp_shift hq hq0 (mul_ne_zero (pow_ne_zero _ hq0) hu), ih, e2, pow_add q, pow_succ (-u⁻¹)]
    generalize (-u⁻¹) ^ k = A
    field_simp

/- English proof (translation)
Establish `pA` using `(multipliable_qp hq t).hasProd`. Establish `pB` using `(multipliable_qp hq t⁻¹).hasProd`. Take `⟨C, hC, pC⟩` from `hasProd_geom hq _ h1`. Take `⟨D, hD, pD⟩` from `hasProd_geom hq _ h2`. Establish `hP : HasProd (fun m : ℕ => cthFac c q t (m + 1)) (qp q t ^ (c ^ 2) * qp q t⁻¹ ^ (c ^ 2) * (C * D)⁻¹)`.

Use `((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))` as an intermediate fact. Simplify `this` using `only [cthFac, div_eq_mul_inv, qp]`. Establish `eC : qp q (t ^ c) = C` using `pC.tprod_eq`. Establish `eD : qp q (t ^ c)⁻¹ = D` using `pD.tprod_eq`. Unfold `cth tp`.

Rewrite using `[hP.tprod_eq, eC, eD]`. Simplify using `only [div_eq_mul_inv, mul_inv, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cth_eq {q t : ℂ} (hq : ‖q‖ < 1) (c : ℕ) (h1 : ∀ m : ℕ, 1 - q ^ (m + 1) * t ^ c ≠ 0)
    (h2 : ∀ m : ℕ, 1 - q ^ (m + 1) * (t ^ c)⁻¹ ≠ 0) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have pA := (multipliable_qp hq t).hasProd
  have pB := (multipliable_qp hq t⁻¹).hasProd
  obtain ⟨C, hC, pC⟩ := hasProd_geom hq _ h1
  obtain ⟨D, hD, pD⟩ := hasProd_geom hq _ h2
  have hP : HasProd (fun m : ℕ => cthFac c q t (m + 1)) (qp q t ^ (c ^ 2) * qp q t⁻¹ ^ (c ^ 2) * (C * D)⁻¹) := by
    have := ((hasProd_pow pA (c ^ 2)).mul (hasProd_pow pB (c ^ 2))).mul (hasProd_inv (pC.mul pD) (mul_ne_zero hC hD))
    simpa only [cthFac, div_eq_mul_inv, qp] using this
  have eC : qp q (t ^ c) = C := pC.tprod_eq
  have eD : qp q (t ^ c)⁻¹ = D := pD.tprod_eq
  unfold cth tp
  rw [hP.tprod_eq, eC, eD]
  simp only [div_eq_mul_inv, mul_inv, mul_pow]
  ring

/- English proof (translation)
Establish `h : (c : ℤ) - (c : ℤ) ^ 2 = 2 * -((c.choose 2 : ℕ) : ℤ)`. Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e2 : (k + 1).choose 2 = k + k.choose 2`.

Rewrite using `[Nat.choose_succ_succ' k 1, Nat.choose_one_right]`. Rewrite using `[e2]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[h]; exact Int.mul_ediv_cancel_left _ (by norm_num)`.
-/
theorem expo (c : ℕ) : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = -((c.choose 2 : ℕ) : ℤ) := by
  have h : (c : ℤ) - (c : ℤ) ^ 2 = 2 * -((c.choose 2 : ℕ) : ℤ) := by
    induction c with
    | zero => simp
    | succ k ih =>
      have e2 : (k + 1).choose 2 = k + k.choose 2 := by
        rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
      rw [e2]; push_cast; linarith
  rw [h]; exact Int.mul_ediv_cancel_left _ (by norm_num)

/- English proof (translation)
Establish `hs : (-t⁻¹) ^ (c ^ 2) = (-(t ^ c)⁻¹) ^ c`. Establish `hpar : (-1 : ℂ) ^ (c ^ 2) = (-1) ^ c`. Break down `Nat.even_or_odd c with h | h` into its components or cases. Rewrite using `[h.neg_one_pow, (h.pow_of_ne_zero two_ne_zero).neg_one_pow]`. Rewrite using `[h.neg_one_pow, h.pow.neg_one_pow]`.

Rewrite using `[neg_pow, neg_pow (t ^ c)⁻¹, hpar, ← inv_pow, ← pow_mul, sq]`. Establish `hn : (-(t ^ c)⁻¹) ^ c ≠ 0` using `pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))`. Establish `hqk : q ^ (c.choose 2) ≠ 0` using `pow_ne_zero _ hq0`. Establish `e : -(q * t) = q * -t` using `by ring`. Rewrite using `[tp_shift hq hq0 ht, mul_pow q t c, tp_shift_pow hq hq0 (pow_ne_zero c ht), mul_pow, hs, e, mul_zpow, expo, zpow_neg q, zpow_natCast]`.

Generalize the expression as in `(-(t ^ c)⁻¹) ^ c = A at hn`. Generalize the expression as in `q ^ (c.choose 2) = B at hqk`. Simplify using `only [div_eq_mul_inv, mul_inv, inv_inv]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mono_shift {q t : ℂ} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ht : t ≠ 0) (c : ℕ) :
    (-(q * t)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q (q * t) ^ (c ^ 2) / tp q ((q * t) ^ c)) =
      (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (tp q t ^ (c ^ 2) / tp q (t ^ c)) := by
  have hs : (-t⁻¹) ^ (c ^ 2) = (-(t ^ c)⁻¹) ^ c := by
    have hpar : (-1 : ℂ) ^ (c ^ 2) = (-1) ^ c := by
      rcases Nat.even_or_odd c with h | h
      · rw [h.neg_one_pow, (h.pow_of_ne_zero two_ne_zero).neg_one_pow]
      · rw [h.neg_one_pow, h.pow.neg_one_pow]
    rw [neg_pow, neg_pow (t ^ c)⁻¹, hpar, ← inv_pow, ← pow_mul, sq]
  have hn : (-(t ^ c)⁻¹) ^ c ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero (pow_ne_zero _ ht)))
  have hqk : q ^ (c.choose 2) ≠ 0 := pow_ne_zero _ hq0
  have e : -(q * t) = q * -t := by ring
  rw [tp_shift hq hq0 ht, mul_pow q t c, tp_shift_pow hq hq0 (pow_ne_zero c ht), mul_pow, hs, e, mul_zpow, expo,
    zpow_neg q, zpow_natCast]
  generalize (-(t ^ c)⁻¹) ^ c = A at hn
  generalize q ^ (c.choose 2) = B at hqk
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  field_simp

/- English proof (translation)
Establish `hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ))`. Simplify using `using h.2.2`. Unfold `sg`. Rewrite using `[cth_eq (norm_ee_lt_one τ) c (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).1) (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).2), mul_assoc]`.
-/
theorem sg_eq {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (τ : ℍ) :
    sg c x τ = ee τ ^ ((c ^ 2 - 1) / 12) * ((-ee (pt x τ)) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) *
      (tp (ee τ) (ee (pt x τ)) ^ (c ^ 2) / tp (ee τ) (ee (pt x τ) ^ c))) := by
  have hc : ¬ ((c • x) 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c • x) 1 ∈ Set.range ((↑) : ℤ → ℚ)) := by
    simpa using h.2.2
  unfold sg
  rw [cth_eq (norm_ee_lt_one τ) c (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).1)
    (fun m => by rw [ee_pt_pow]; exact (ne_one_of_not_int hc τ (m + 1)).2), mul_assoc]

/- English proof (translation)
Use `⟨h.1, h.2.1, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨a, ha⟩, ⟨b, hb⟩⟩`. Conclude with `h.2.2 ⟨⟨a - c * n 0, by push_cast; rw [ha]; ring⟩, ⟨b - c * n 1, by push_cast; rw [hb]; ring⟩⟩`.
-/
theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x : Fin 2 → ℚ} (h : admitted c x) (n : Fin 2 → ℤ) : admitted c fun i => x i + n i := by
  refine ⟨h.1, h.2.1, ?_⟩
  rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
  exact h.2.2 ⟨⟨a - c * n 0, by push_cast; rw [ha]; ring⟩, ⟨b - c * n 1, by push_cast; rw [hb]; ring⟩⟩

/- English proof (translation)
Establish `e : ee (pt y τ) = ee τ * ee (pt x τ)`. Rewrite using `[← ee_add]`. Use `congr 1`. Simplify using `only [pt, h0, h1]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sg_eq hx, sg_eq hy, e, mono_shift (norm_ee_lt_one τ) (ee_ne_zero _) (ee_ne_zero _)]`.
-/
theorem sg_step {c : ℕ} {x y : Fin 2 → ℚ} (hx : admitted c x) (hy : admitted c y) (τ : ℍ) (h0 : y 0 = x 0 + 1) (h1 : y 1 = x 1) :
    sg c y τ = sg c x τ := by
  have e : ee (pt y τ) = ee τ * ee (pt x τ) := by
    rw [← ee_add]; congr 1; simp only [pt, h0, h1]; push_cast; ring
  rw [sg_eq hx, sg_eq hy, e, mono_shift (norm_ee_lt_one τ) (ee_ne_zero _) (ee_ne_zero _)]

/- English proof (translation)
Proceed by induction on `k using Int.induction_on with`. Consider the case `zero`. Apply the tactic sequence `congr 1; funext i; fin_cases i <;> simp`. Consider the case `succ k ih`. Rewrite using `[← ih]`.

Conclude with `sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)`. Consider the case `pred k ih`. Rewrite using `[← ih]`. Conclude with `(sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)).symm`.
-/
theorem sg_fst {c : ℕ} {x : Fin 2 → ℚ} (hx : admitted c x) (τ : ℍ) (k : ℤ) :
    sg c (fun i => x i + (![k, 0] : Fin 2 → ℤ) i) τ = sg c x τ := by
  induction k using Int.induction_on with
  | zero =>
    congr 1; funext i; fin_cases i <;> simp
  | succ k ih =>
    rw [← ih]
    exact sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)
  | pred k ih =>
    rw [← ih]
    exact (sg_step (isAdmissibleSmoothingFactor_add_intVector hx _) (isAdmissibleSmoothingFactor_add_intVector hx _) τ (by simp; ring) (by simp)).symm

/- English proof (translation)
Introduce `c x n τ hx`. Rewrite using `[← sg_fst hx τ (n 0)]`. Establish `e1 : ee (n 1 : ℂ) = 1`. Unfold `ee`. Rewrite using `[mul_comm]`.

Conclude with `Complex.exp_int_mul_two_pi_mul_I _`. Unfold `sg`. Use `congr 1`. Rewrite using `[← mul_one (ee (pt (fun i => x i + (![n 0, 0] : Fin 2 → ℤ) i) τ)), ← e1, ← ee_add]`. Use `congr 1`.

Simplify using `[pt]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sg_add_int : ∀ (c : ℕ) (x : Fin 2 → ℚ) (n : Fin 2 → ℤ) (τ : ℍ), admitted c x →
    sg c (fun i => x i + n i) τ = sg c x τ := by
  intro c x n τ hx
  rw [← sg_fst hx τ (n 0)]
  have e1 : ee (n 1 : ℂ) = 1 := by
    unfold ee
    rw [mul_comm]; exact Complex.exp_int_mul_two_pi_mul_I _
  unfold sg
  congr 1
  rw [← mul_one (ee (pt (fun i => x i + (![n 0, 0] : Fin 2 → ℤ) i) τ)), ← e1, ← ee_add]
  congr 1
  simp [pt]; ring

end GlobalTheory.Sieg.Per
