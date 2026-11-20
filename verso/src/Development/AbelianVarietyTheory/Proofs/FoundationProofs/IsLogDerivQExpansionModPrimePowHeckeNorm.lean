import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaBasisLinearCombination

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue GlobalTheory.ThAdd
open scoped MatrixGroups

namespace GlobalTheory.NormDl

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp only [Nat.cast_zero, mul_zero, pow_zero]`. Conclude with `eOm_zero ε`. Consider the case `succ k ih => rw [Nat.cast_succ, mul_add, mul_one, eOm_add, ih, pow_succ]`.
-/
theorem eOm_mul_nat (x : ℚ) (k : ℕ) : eOm ε (x * k) = eOm ε x ^ k := by
  induction k with
  | zero => simp only [Nat.cast_zero, mul_zero, pow_zero]; exact eOm_zero ε
  | succ k ih => rw [Nat.cast_succ, mul_add, mul_one, eOm_add, ih, pow_succ]

/- English proof (translation)
Apply `ε.injective` to reduce the goal to its premises. Rewrite using `[eOm_spec, map_one, ← Rat.coe_int_num_of_den_eq_one h]`. Use `Complex.exp_int_mul_two_pi_mul_I x.num` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eOm_of_den {x : ℚ} (h : x.den = 1) : eOm ε x = 1 := by
  apply ε.injective
  rw [eOm_spec, map_one, ← Rat.coe_int_num_of_den_eq_one h]
  have := Complex.exp_int_mul_two_pi_mul_I x.num
  rw [← this]; congr 1; push_cast; ring

/- English proof (translation)
Establish `h : eOm ε x ^ x.den = 1`. Rewrite using `[← eOm_mul_nat, eOm_of_den]`. Rewrite using `[Rat.mul_den_eq_num]`. Simplify using the standard rewrite rules. Break down `A.mem_or_inv_mem (eOm ε x) with hz | hz` into its components or cases.

Conclude with `hz`. Establish `h1 : eOm ε x * eOm ε x ^ (x.den - 1) = 1` using `by rw [← pow_succ', Nat.sub_add_cancel x.den_pos, h]`. Rewrite using `[eq_inv_of_mul_eq_one_left h1, ← _root_.inv_pow]`. Conclude with `pow_mem hz _`.
-/
theorem eOm_mem (A : ValuationSubring Ω) (x : ℚ) : eOm ε x ∈ A := by
  have h : eOm ε x ^ x.den = 1 := by
    rw [← eOm_mul_nat, eOm_of_den]; rw [Rat.mul_den_eq_num]; simp
  rcases A.mem_or_inv_mem (eOm ε x) with hz | hz
  · exact hz
  · have h1 : eOm ε x * eOm ε x ^ (x.den - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel x.den_pos, h]
    rw [eq_inv_of_mul_eq_one_left h1, ← _root_.inv_pow]
    exact pow_mem hz _

/- English proof (translation)
Rewrite using `[← eOm_add, neg_add_cancel, eOm_zero]`.
-/
theorem eOm_neg_mul (x : ℚ) : eOm ε (-x) * eOm ε x = 1 := by rw [← eOm_add, neg_add_cancel, eOm_zero]

/- English proof (translation)
The claim follows from `right_ne_zero_of_mul_eq_one (eOm_neg_mul ε x)`.
-/
theorem eOm_ne_zero (x : ℚ) : eOm ε x ≠ 0 := right_ne_zero_of_mul_eq_one (eOm_neg_mul ε x)

/- English proof (translation)
Rewrite using `[← eq_inv_of_mul_eq_one_left (eOm_neg_mul ε x)]`. Conclude with `eOm_mem ε A _`.
-/
theorem eOm_inv_mem (A : ValuationSubring Ω) (x : ℚ) : (eOm ε x)⁻¹ ∈ A := by
  rw [← eq_inv_of_mul_eq_one_left (eOm_neg_mul ε x)]
  exact eOm_mem ε A _

def subHom (j : ℚ) (d : ℕ) [NeZero d] : HahnSeries ℚ Ω →+* HahnSeries ℚ Ω where
  toFun := sub ε 1 j d
  map_one' := (sub_mul_and_one Ω ε 1 j d (one_div_pos.2 (Nat.cast_pos.2 (NeZero.pos d))) 1 1).2
  map_mul' x y := (sub_mul_and_one Ω ε 1 j d (one_div_pos.2 (Nat.cast_pos.2 (NeZero.pos d))) x y).1
  map_add' := Api.sub_map_add 1 j d
  map_zero' := by simpa using Api.sub_map_smul (ε := ε) 1 j d 0 0

/- English proof (translation)
Establish `h0 : (0 : ℚ) < d` using `Nat.cast_pos.2 (NeZero.pos d)`. Use `Api.coeff_sub_upper (ε := ε) (a := 1) (d := d) (by positivity) j φ (d * r)` as an intermediate fact. Rewrite `this` using `[show (d : ℚ) * r * 1 / d = r by field_simp, show (d : ℚ) * r * j / d = r * j by field_simp]`. Conclude with `this`.
-/
theorem coeff_subHom (j : ℚ) (d : ℕ) [NeZero d] (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (subHom ε j d φ).coeff r = eOm ε (r * j) * φ.coeff (d * r) := by
  have h0 : (0 : ℚ) < d := Nat.cast_pos.2 (NeZero.pos d)
  have := Api.coeff_sub_upper (ε := ε) (a := 1) (d := d) (by positivity) j φ (d * r)
  rw [show (d : ℚ) * r * 1 / d = r by field_simp, show (d : ℚ) * r * j / d = r * j by field_simp] at this
  exact this

/- English proof (translation)
Rewrite using `[coeff_subHom, Nat.cast_one, one_mul]`.
-/
theorem coeff_tr (j : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (subHom ε j 1 φ).coeff r = eOm ε (r * j) * φ.coeff r := by
  rw [coeff_subHom, Nat.cast_one, one_mul]

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[coeff_tr, coeff_subHom, coeff_subHom, mul_add, eOm_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tr_subHom (i j : ℚ) (d : ℕ) [NeZero d] (φ : HahnSeries ℚ Ω) :
    subHom ε j 1 (subHom ε i d φ) = subHom ε (i + j) d φ := by
  ext r
  rw [coeff_tr, coeff_subHom, coeff_subHom, mul_add, eOm_add]; ring

/- English proof (translation)
Use extensionality with `r`. Use `conv_rhs => rw [← h]`. Rewrite using `[coeff_subHom, coeff_subHom, coeff_tr, mul_add, eOm_add, mul_one, mul_comm r d]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem subHom_period (i : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : subHom ε 1 1 φ = φ) :
    subHom ε (i + d) d φ = subHom ε i d φ := by
  ext r
  conv_rhs => rw [← h]
  rw [coeff_subHom, coeff_subHom, coeff_tr, mul_add, eOm_add, mul_one, mul_comm r d]; ring

/- English proof (translation)
Use `haveI : CharZero Ω := ε.charZero`. Establish `h0 : (d : Ω) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne d)`. Use extensionality with `r`. Rewrite using `[HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, coeff_subHom]`. Use `show algebraMap ℚ Ω (1 * r) * (subHom ε j d φ).coeff r = (d : Ω)⁻¹ * (eOm ε (r * j) * (algebraMap ℚ Ω (1 * (d * r)) * φ.coeff (d * r)))`.

Rewrite using `[coeff_subHom, one_mul, one_mul, map_mul, map_natCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem theta_subHom (j : ℚ) (d : ℕ) [NeZero d] (φ : HahnSeries ℚ Ω) :
    theta 1 (subHom ε j d φ) = HahnSeries.C ((d : Ω)⁻¹) * subHom ε j d (theta 1 φ) := by
  haveI : CharZero Ω := ε.charZero
  have h0 : (d : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  ext r
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, coeff_subHom]
  show algebraMap ℚ Ω (1 * r) * (subHom ε j d φ).coeff r =
    (d : Ω)⁻¹ * (eOm ε (r * j) * (algebraMap ℚ Ω (1 * (d * r)) * φ.coeff (d * r)))
  rw [coeff_subHom, one_mul, one_mul, map_mul, map_natCast]
  field_simp

/- English proof (translation)
Introduce `r` and use `by rw [coeff_subHom]; exact mul_mem (eOm_mem ε A _) (h _)`.
-/
theorem ig_subHom {A : ValuationSubring Ω} (j : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : Ig A φ) :
    Ig A (subHom ε j d φ) := fun r => by
  rw [coeff_subHom]; exact mul_mem (eOm_mem ε A _) (h _)

/- English proof (translation)
Introduce `r` and use `by obtain ⟨z, hz, e⟩ := h (d * r) exact ⟨eOm ε (r * j) * z, mul_mem (eOm_mem ε A _) hz, by rw [coeff_subHom, e]; ring⟩`.
-/
theorem dv_subHom {A : ValuationSubring Ω} {l n : ℕ} (j : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : Dv A l n φ) :
    Dv A l n (subHom ε j d φ) := fun r => by
  obtain ⟨z, hz, e⟩ := h (d * r)
  exact ⟨eOm ε (r * j) * z, mul_mem (eOm_mem ε A _) hz, by rw [coeff_subHom, e]; ring⟩

/- English proof (translation)
Establish `h0 : (d : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne d)`. Take `⟨h1, r, hr0, hr⟩` from `h`. Use `⟨ig_subHom ε j d h1, r / d, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_subHom, mul_div_cancel₀ _ h0]`. Conclude with `mul_ne_zero (eOm_ne_zero ε _) hr0`.

Rewrite using `[coeff_subHom, mul_div_cancel₀ _ h0, mul_inv]`. Conclude with `mul_mem (eOm_inv_mem ε A _) hr`.
-/
theorem prim_subHom {A : ValuationSubring Ω} (j : ℚ) (d : ℕ) [NeZero d] {φ : HahnSeries ℚ Ω} (h : Prim A φ) :
    Prim A (subHom ε j d φ) := by
  have h0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne d)
  obtain ⟨h1, r, hr0, hr⟩ := h
  refine ⟨ig_subHom ε j d h1, r / d, ?_, ?_⟩
  · rw [coeff_subHom, mul_div_cancel₀ _ h0]; exact mul_ne_zero (eOm_ne_zero ε _) hr0
  · rw [coeff_subHom, mul_div_cancel₀ _ h0, mul_inv]; exact mul_mem (eOm_inv_mem ε A _) hr

omit [IsAlgClosed Ω] in
/- English proof (translation)
The claim follows from `Finset.prod_induction U (Prim A) (fun _ _ => prim_mul) ⟨fun r => by rw [HahnSeries.coeff_one]; split_ifs <;> simp, 0, by simp⟩ (fun i _ => h i)`.
-/
theorem prim_prod {A : ValuationSubring Ω} {ι : Type} (s : Finset ι) {U : ι → HahnSeries ℚ Ω} (h : ∀ i, Prim A (U i)) :
    Prim A (∏ i ∈ s, U i) :=
  Finset.prod_induction U (Prim A) (fun _ _ => prim_mul)
    ⟨fun r => by rw [HahnSeries.coeff_one]; split_ifs <;> simp, 0, by simp⟩ (fun i _ => h i)

omit [IsAlgClosed Ω] [Algebra ℚ Ω] in
/- English proof (translation)
Take `⟨-, r, hr, -⟩` from `h`. Introduce and unpack `rfl`. Simplify using `at hr`.
-/
theorem prim_ne_zero {A : ValuationSubring Ω} {φ : HahnSeries ℚ Ω} (h : Prim A φ) : φ ≠ 0 := by
  obtain ⟨-, r, hr, -⟩ := h
  rintro rfl; simp at hr

omit [IsAlgClosed Ω] in

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Simplify using `only [Finset.prod_range_succ, Finset.sum_range_succ, theta_mul, mul_add]`. Establish `h1` using `hU k`.

Establish `h2` using `hV k`. Establish `e : (∏ i ∈ Finset.range k, U i) * U k * ((∏ i ∈ Finset.range k, V i) * V k) * ((theta 1 (U k) * V k - U k * theta 1 (V k)) / (U k * V k)) = (∏ i ∈ Finset.range k, U i) * (∏ i ∈ Finset.range k, V i) * (theta 1 (U k) * V k - U k * theta 1 (V k))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Take the linear combination `(U k * V k) * ih`.
-/
theorem wron_prod (k : ℕ) {U V : ℕ → HahnSeries ℚ Ω} (hU : ∀ i, U i ≠ 0) (hV : ∀ i, V i ≠ 0) :
    theta 1 (∏ i ∈ Finset.range k, U i) * ∏ i ∈ Finset.range k, V i -
      (∏ i ∈ Finset.range k, U i) * theta 1 (∏ i ∈ Finset.range k, V i) =
    (∏ i ∈ Finset.range k, U i) * (∏ i ∈ Finset.range k, V i) *
      ∑ i ∈ Finset.range k, (theta 1 (U i) * V i - U i * theta 1 (V i)) / (U i * V i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Finset.prod_range_succ, Finset.sum_range_succ, theta_mul, mul_add]
    have h1 := hU k
    have h2 := hV k
    have e : (∏ i ∈ Finset.range k, U i) * U k * ((∏ i ∈ Finset.range k, V i) * V k) *
        ((theta 1 (U k) * V k - U k * theta 1 (V k)) / (U k * V k)) =
        (∏ i ∈ Finset.range k, U i) * (∏ i ∈ Finset.range k, V i) * (theta 1 (U k) * V k - U k * theta 1 (V k)) := by
      field_simp
    rw [e]
    linear_combination (U k * V k) * ih

/- English proof (translation)
Rewrite using `[map_prod]`. Simplify using `only [tr_subHom]`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`.

Rewrite using `[← ih]`. Establish `h1` using `Finset.prod_range_succ (fun i : ℕ => subHom ε ((i : ℚ) + j) l c) l`. Rewrite `h1` using `[Finset.prod_range_succ']`. Rewrite `h1` using `[add_comm (l : ℚ), subHom_period ε _ l h, Nat.cast_zero, zero_add]`. Rewrite using `[← mul_right_cancel₀ ((map_ne_zero _).2 h0) h1]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tr_norm (l : ℕ) [NeZero l] {c : HahnSeries ℚ Ω} (h0 : c ≠ 0) (h : subHom ε 1 1 c = c) (j : ℕ) :
    subHom ε j 1 (∏ i ∈ Finset.range l, subHom ε (i : ℕ) l c) = ∏ i ∈ Finset.range l, subHom ε (i : ℕ) l c := by
  rw [map_prod]
  simp only [tr_subHom]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih]
    have h1 := Finset.prod_range_succ (fun i : ℕ => subHom ε ((i : ℚ) + j) l c) l
    rw [Finset.prod_range_succ'] at h1
    rw [add_comm (l : ℚ), subHom_period ε _ l h, Nat.cast_zero, zero_add] at h1
    rw [← mul_right_cancel₀ ((map_ne_zero _).2 h0) h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 2; push_cast; ring

/- English proof (translation)
Use `haveI : CharZero Ω := ε.charZero`. Establish `h0 : (l : Ω) ≠ 0` using `Nat.cast_ne_zero.2 (NeZero.ne l)`. Introduce `r`. Rewrite using `[HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_sum]`. Simplify using `only [coeff_tr, eOm_mul_nat]`.

Rewrite using `[← Finset.sum_mul]`. Distinguish the cases in `h1 : eOm ε r = 1`. Take `⟨z, hz, e⟩` from `hw r`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Rewrite using `[← e, h1]`.

Simplify using `[h0]`. Use `⟨0, zero_mem A, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h2 : w.coeff r = 0`. Simplify using `[h2]`. Establish `h3 : eOm ε r ^ l = 1`.

Use `congrArg (fun x => x.coeff r) h` as an intermediate fact. Simplify using `only [coeff_tr, eOm_mul_nat] at this`. Conclude with `(mul_left_eq_self₀.1 this).resolve_right h2`. Rewrite using `[geom_sum_eq h1, h3]`. Simplify using the standard rewrite rules.
-/
theorem dv_mean {A : ValuationSubring Ω} {n : ℕ} (l : ℕ) [NeZero l] {w : HahnSeries ℚ Ω} (hw : Dv A l n w)
    (h : subHom ε l 1 w = w) :
    Dv A l n (HahnSeries.C ((l : Ω)⁻¹) * ∑ j ∈ Finset.range l, subHom ε (j : ℕ) 1 w) := by
  haveI : CharZero Ω := ε.charZero
  have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  intro r
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul, HahnSeries.coeff_sum]
  simp only [coeff_tr, eOm_mul_nat]
  rw [← Finset.sum_mul]
  by_cases h1 : eOm ε r = 1
  · obtain ⟨z, hz, e⟩ := hw r
    refine ⟨z, hz, ?_⟩
    rw [← e, h1]; simp [h0]
  · refine ⟨0, zero_mem A, ?_⟩
    by_cases h2 : w.coeff r = 0
    · simp [h2]
    have h3 : eOm ε r ^ l = 1 := by
      have := congrArg (fun x => x.coeff r) h
      simp only [coeff_tr, eOm_mul_nat] at this
      exact (mul_left_eq_self₀.1 this).resolve_right h2
    rw [geom_sum_eq h1, h3]; simp

/- English proof (translation)
Establish `a0` using `prim_ne_zero ha`. Establish `b0` using `prim_ne_zero hb`. Establish `tc : subHom ε 1 1 (a * b) = a * b` using `by rw [map_mul, ta, tb]`. Establish `tθ : ∀ x : HahnSeries ℚ Ω, subHom ε 1 1 x = x → subHom ε 1 1 (theta 1 x) = theta 1 x` using `fun x hx => by`. Use `theta_subHom ε 1 1 x` as an intermediate fact.

Rewrite `this` using `[hx]`. Simplify using `using this.symm`. Use `set E := φ * a * b - (theta 1 a * b - a * theta 1 b) with hEdef`. Establish `tE : subHom ε 1 1 E = E`. Simplify using `only [hEdef, map_sub, map_mul, tφ, ta, tb, tθ a ta, tθ b tb]`.

Take `⟨m, hm⟩ : ∃ m, l = m + 1` from `Nat.exists_eq_succ_of_ne_zero (NeZero.ne l)`. Use `set R := ∏ i ∈ Finset.range m, subHom ε ((i + 1 : ℕ) : ℚ) l (a * b) with hR`. Establish `hN : ∏ i ∈ Finset.range l, subHom ε (i : ℕ) l (a * b) = R * subHom ε 0 l (a * b)`. Establish `: Finset.range l = Finset.range (m + 1)` using `by rw [hm]`. Rewrite using `[this, Finset.prod_range_succ', Nat.cast_zero]`.

Establish `iR : Ig A R` using `(prim_prod _ fun i => prim_subHom ε _ l (prim_mul ha hb)).1`. Establish `tR : subHom ε l 1 R = R`. Rewrite using `[hR, map_prod]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [tr_subHom, subHom_period ε _ l tc]`. Establish `hw` using `dv_mean ε l ((dv_subHom ε 0 l hE).mul iR) (by rw [map_mul, tR, tr_subHom, subHom_period ε _ l tE])`.

Use `hw using 1` and compare the differences between its conclusion and the goal. Rewrite using `[wron_prod l (U := fun j : ℕ => subHom ε (j : ℕ) l a) (V := fun j : ℕ => subHom ε (j : ℕ) l b) (fun i => (map_ne_zero _).2 a0) (fun i => (map_ne_zero _).2 b0), mul_assoc (hq ε l φ), ← Finset.prod_mul_distrib]`. Simplify using `only [← map_mul]`. Establish `hhq : hq ε l φ = ∑ j ∈ Finset.range l, HahnSeries.C ((l : Ω)⁻¹) * subHom ε (j : ℕ) l φ`. Rewrite using `[← Finset.mul_sum, HahnSeries.C_mul_eq_smul]`.

Both sides reduce to the same expression. Rewrite using `[hhq, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← tr_norm ε l (mul_ne_zero a0 b0) tc j, hN, theta_subHom, theta_subHom]`. Simplify using `only [map_mul, tr_subHom, zero_add, hEdef, map_sub]`.

Establish `h1 : subHom ε (j : ℕ) l a ≠ 0` using `(map_ne_zero _).2 a0`. Establish `h2 : subHom ε (j : ℕ) l b ≠ 0` using `(map_ne_zero _).2 b0`. Clear the denominators using the available nonvanishing facts.
-/
theorem dv_norm {A : ValuationSubring Ω} {n : ℕ} (l : ℕ) [NeZero l] {φ a b : HahnSeries ℚ Ω}
    (ha : Prim A a) (hb : Prim A b) (tφ : subHom ε 1 1 φ = φ) (ta : subHom ε 1 1 a = a) (tb : subHom ε 1 1 b = b)
    (hE : Dv A l n (φ * a * b - (theta 1 a * b - a * theta 1 b))) :
    Dv A l n (hq ε l φ * (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l a) * (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l b) -
      (theta 1 (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l a) * (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l b) -
        (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l a) * theta 1 (∏ j ∈ Finset.range l, subHom ε (j : ℕ) l b))) := by
  have a0 := prim_ne_zero ha
  have b0 := prim_ne_zero hb
  have tc : subHom ε 1 1 (a * b) = a * b := by rw [map_mul, ta, tb]
  have tθ : ∀ x : HahnSeries ℚ Ω, subHom ε 1 1 x = x → subHom ε 1 1 (theta 1 x) = theta 1 x := fun x hx => by
    have := theta_subHom ε 1 1 x
    rw [hx] at this
    simpa using this.symm
  set E := φ * a * b - (theta 1 a * b - a * theta 1 b) with hEdef
  have tE : subHom ε 1 1 E = E := by
    simp only [hEdef, map_sub, map_mul, tφ, ta, tb, tθ a ta, tθ b tb]
  obtain ⟨m, hm⟩ : ∃ m, l = m + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne l)
  set R := ∏ i ∈ Finset.range m, subHom ε ((i + 1 : ℕ) : ℚ) l (a * b) with hR
  have hN : ∏ i ∈ Finset.range l, subHom ε (i : ℕ) l (a * b) = R * subHom ε 0 l (a * b) := by
    have : Finset.range l = Finset.range (m + 1) := by rw [hm]
    rw [this, Finset.prod_range_succ', Nat.cast_zero]
  have iR : Ig A R := (prim_prod _ fun i => prim_subHom ε _ l (prim_mul ha hb)).1
  have tR : subHom ε l 1 R = R := by
    rw [hR, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [tr_subHom, subHom_period ε _ l tc]
  have hw := dv_mean ε l ((dv_subHom ε 0 l hE).mul iR)
    (by rw [map_mul, tR, tr_subHom, subHom_period ε _ l tE])
  convert hw using 1
  rw [wron_prod l (U := fun j : ℕ => subHom ε (j : ℕ) l a) (V := fun j : ℕ => subHom ε (j : ℕ) l b)
    (fun i => (map_ne_zero _).2 a0) (fun i => (map_ne_zero _).2 b0), mul_assoc (hq ε l φ), ← Finset.prod_mul_distrib]
  simp only [← map_mul]
  have hhq : hq ε l φ = ∑ j ∈ Finset.range l, HahnSeries.C ((l : Ω)⁻¹) * subHom ε (j : ℕ) l φ := by
    rw [← Finset.mul_sum, HahnSeries.C_mul_eq_smul]; rfl
  rw [hhq, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tr_norm ε l (mul_ne_zero a0 b0) tc j, hN, theta_subHom, theta_subHom]
  simp only [map_mul, tr_subHom, zero_add, hEdef, map_sub]
  have h1 : subHom ε (j : ℕ) l a ≠ 0 := (map_ne_zero _).2 a0
  have h2 : subHom ε (j : ℕ) l b ≠ 0 := (map_ne_zero _).2 b0
  field_simp

/- English proof (translation)
Establish `he : ∀ i j, ent (ofSL (ModularGroup.T ^ k)) i j = ((!![1, (k : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ)`. Introduce `i j`. Rewrite using `[← ModularGroup.coe_T_zpow, zpow_natCast]`. Both sides reduce to the same expression. Rewrite using `[Api.exp_sl_upper X _ (by rw [he]; simp), he, he, he]`.

Simplify using `[subHom]`.
-/
theorem modularTowerExp_slAction_T_pow (X : Tower Ω ε) (k : ℕ) (g : X.K) :
    X.exp (X.sl (ofSL (ModularGroup.T ^ k)) g) = subHom ε k 1 (X.exp g) := by
  have he : ∀ i j, ent (ofSL (ModularGroup.T ^ k)) i j = ((!![1, (k : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
    intro i j
    rw [← ModularGroup.coe_T_zpow, zpow_natCast]; rfl
  rw [Api.exp_sl_upper X _ (by rw [he]; simp), he, he, he]
  simp [subHom]

/- English proof (translation)
Establish `hd : (0 : ℤ) < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det`. Simplify using `[Matrix.det_fin_two, NeZero.pos l]`. Establish `he : ∀ a b, ent (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) a b = ((!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) a b : ℚ)`. Introduce `a b`. Unfold `ent toGQ`.

Rewrite using `[dif_pos hd]`. Both sides reduce to the same expression. Rewrite using `[Api.exp_sl_upper X _ (by rw [he]; simp), he, he, he]`. Simplify using `[subHom]`.
-/
theorem exp_sl_m (X : Tower Ω ε) (j l : ℕ) [NeZero l] (g : X.K) :
    X.exp (X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) g) = subHom ε j l (X.exp g) := by
  have hd : (0 : ℤ) < (!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two, NeZero.pos l]
  have he : ∀ a b, ent (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) a b =
      ((!![1, (j : ℤ); 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) a b : ℚ) := by
    intro a b
    unfold ent toGQ
    rw [dif_pos hd]; rfl
  rw [Api.exp_sl_upper X _ (by rw [he]; simp), he, he, he]
  simp [subHom]

/- English proof (translation)
Take `⟨-, a, b, κ, hκ, e, pa, pb, c⟩` from `h`. Rewrite `c` using `[dv_iff]`. Take `⟨M, hM, hb⟩` from `X.level b`. Take `⟨m, rfl⟩ : ∃ m, M = m + 1` from `Nat.exists_eq_succ_of_ne_zero hM.ne'`. Establish `hT : X.sl (ofSL (ModularGroup.T ^ (m + 1))) b = b`.

Apply `hb` to reduce the goal to its premises. Rewrite using `[CongruenceSubgroup.Gamma_mem]`. Use `ModularGroup.coe_T_zpow ((m + 1 : ℕ) : ℤ)` as an intermediate fact. Rewrite `this` using `[zpow_natCast]`. Establish `h' : ∀ i j, (ModularGroup.T ^ (m + 1)) i j = (!![1, ((m + 1 : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j` using `fun i j => by rw [← this]`.

Simplify using `only [h']`. Simplify using `[-Nat.cast_add, -Nat.cast_succ]`. Use `set Q := ∏ k ∈ Finset.range m, X.sl (ofSL (ModularGroup.T ^ (k + 1))) b with hQ`. Establish `pQ : Prim A (X.exp Q)`. Rewrite using `[hQ, map_prod]`.

Conclude with `prim_prod _ fun k => by rw [modularTowerExp_slAction_T_pow]; exact prim_subHom ε _ 1 pb`. Establish `tb : X.sl (ofSL ModularGroup.T) (b * Q) = b * Q`. Establish `h1 : b * Q = ∏ k ∈ Finset.range (m + 1), X.sl (ofSL (ModularGroup.T ^ k)) b`. Rewrite using `[Finset.prod_range_succ', pow_zero, map_one, X.sl_one, mul_comm]`. Use `conv_lhs => rw [h1, map_prod]`.

Simplify using `only [← X.sl_mul, ← map_mul, ← pow_succ]`. Rewrite using `[Finset.prod_range_succ, hT, mul_comm]`. Establish `e' : f * (b * Q) = algebraMap Ω X.K κ * (a * Q)` using `by rw [← mul_assoc, e, mul_assoc]`. Use `⟨a * Q, b * Q, κ, hκ, e', by rw [map_mul]; exact prim_mul pa pQ, by rw [map_mul]; exact prim_mul pb pQ, ?_, tb, ?_⟩` and prove the remaining obligations. Use `congrArg (X.sl (ofSL ModularGroup.T)) e'` as an intermediate fact.

Rewrite `this` using `[map_mul, hf, tb, e', map_mul (X.sl _) (algebraMap Ω X.K κ), AlgEquiv.commutes]`. Conclude with `(mul_left_cancel₀ ((map_ne_zero _).2 hκ) this).symm`. Use `c.mul (Ig.mul pQ.1 pQ.1) using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_mul, theta_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_inv_pres (X : Tower Ω ε) (A : ValuationSubring Ω) (l n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω)
    (hf : X.sl (ofSL ModularGroup.T) f = f) (h : IsDl X A l n 1 f φ) :
    ∃ (a b : X.K) (κ : Ω), κ ≠ 0 ∧ f * b = algebraMap Ω X.K κ * a ∧ Prim A (X.exp a) ∧ Prim A (X.exp b) ∧
      X.sl (ofSL ModularGroup.T) a = a ∧ X.sl (ofSL ModularGroup.T) b = b ∧
      Dv A l n (φ * X.exp a * X.exp b - (theta 1 (X.exp a) * X.exp b - X.exp a * theta 1 (X.exp b))) := by
  obtain ⟨-, a, b, κ, hκ, e, pa, pb, c⟩ := h
  rw [dv_iff] at c
  obtain ⟨M, hM, hb⟩ := X.level b
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have hT : X.sl (ofSL (ModularGroup.T ^ (m + 1))) b = b := by
    apply hb
    rw [CongruenceSubgroup.Gamma_mem]
    have := ModularGroup.coe_T_zpow ((m + 1 : ℕ) : ℤ)
    rw [zpow_natCast] at this
    have h' : ∀ i j, (ModularGroup.T ^ (m + 1)) i j =
      (!![1, ((m + 1 : ℕ) : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j := fun i j => by rw [← this]
    simp only [h']
    simp [-Nat.cast_add, -Nat.cast_succ]
  set Q := ∏ k ∈ Finset.range m, X.sl (ofSL (ModularGroup.T ^ (k + 1))) b with hQ
  have pQ : Prim A (X.exp Q) := by
    rw [hQ, map_prod]
    exact prim_prod _ fun k => by rw [modularTowerExp_slAction_T_pow]; exact prim_subHom ε _ 1 pb
  have tb : X.sl (ofSL ModularGroup.T) (b * Q) = b * Q := by
    have h1 : b * Q = ∏ k ∈ Finset.range (m + 1), X.sl (ofSL (ModularGroup.T ^ k)) b := by
      rw [Finset.prod_range_succ', pow_zero, map_one, X.sl_one, mul_comm]
    conv_lhs => rw [h1, map_prod]
    simp only [← X.sl_mul, ← map_mul, ← pow_succ]
    rw [Finset.prod_range_succ, hT, mul_comm]
  have e' : f * (b * Q) = algebraMap Ω X.K κ * (a * Q) := by rw [← mul_assoc, e, mul_assoc]
  refine ⟨a * Q, b * Q, κ, hκ, e', by rw [map_mul]; exact prim_mul pa pQ, by rw [map_mul]; exact prim_mul pb pQ,
    ?_, tb, ?_⟩
  · have := congrArg (X.sl (ofSL ModularGroup.T)) e'
    rw [map_mul, hf, tb, e', map_mul (X.sl _) (algebraMap Ω X.K κ), AlgEquiv.commutes] at this
    exact (mul_left_cancel₀ ((map_ne_zero _).2 hκ) this).symm
  · convert c.mul (Ig.mul pQ.1 pQ.1) using 1
    simp only [map_mul, theta_mul]; ring

/- English proof (translation)
Introduce `Ω _ _ _ ε X A l hl n f φ hf hφ h`. Use `haveI : NeZero l := ⟨hl.out.ne_zero⟩`. Take `⟨a, b, κ, hκ, e, pa, pb, ta, tb, c⟩` from `exists_inv_pres ε X A l n f φ hf h`. Establish `tx : ∀ x : X.K, X.sl (ofSL ModularGroup.T) x = x → subHom ε 1 1 (X.exp x) = X.exp x` using `fun x hx => by`. Use `modularTowerExp_slAction_T_pow ε X 1 x` as an intermediate fact.

Rewrite `this` using `[pow_one, hx, Nat.cast_one]`. Conclude with `this.symm`. Establish `tφ : subHom ε 1 1 φ = φ`. Use extensionality with `r`. Rewrite using `[coeff_tr, mul_one]`.

Distinguish the cases in `h0 : φ.coeff r = 0`. Simplify using `[h0]`. Rewrite using `[eOm_of_den ε (hφ r h0), one_mul]`. Establish `hx : ∀ x : X.K, X.exp (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) x) = ∏ j ∈ Finset.range l, subHom ε (j : ℕ) l (X.exp x)` using `fun x => by`. Rewrite using `[map_prod]`.

Conclude with `Finset.prod_congr rfl fun j _ => exp_sl_m ε X j l x`. Use `⟨fun r => ?_, ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) a, ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) b, κ ^ l, pow_ne_zero _ hκ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Api.hq_eq_uq_of_isAlgClosed (NeZero.pos l) (fun r hr => by simpa using hφ r hr), Api.coeff_uq (NeZero.pos l)] split_ifs`. Conclude with `h.1 _`. Conclude with `zero_mem A`.

Rewrite using `[← Finset.prod_mul_distrib]`. Simplify using `only [← map_mul, e]`. Simplify using `only [map_mul, AlgEquiv.commutes]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, map_pow]`. Rewrite using `[hx]`.

Conclude with `prim_prod _ fun j => prim_subHom ε _ l pa`. Rewrite using `[hx]`. Conclude with `prim_prod _ fun j => prim_subHom ε _ l pb`. Rewrite using `[dv_iff, hx, hx]`. Conclude with `dv_norm ε l pa pb tφ (tx a ta) (tx b tb) c`.
-/
theorem isDl_norm : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ) (f : X.K) (φ : HahnSeries ℚ Ω),
  X.sl (ofSL ModularGroup.T) f = f → (∀ r : ℚ, φ.coeff r ≠ 0 → r.den = 1) → IsDl X A l n 1 f φ →
  IsDl X A l n 1 (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) f) (hq ε l φ) := by
  intro Ω _ _ _ ε X A l hl n f φ hf hφ h
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨a, b, κ, hκ, e, pa, pb, ta, tb, c⟩ := exists_inv_pres ε X A l n f φ hf h
  have tx : ∀ x : X.K, X.sl (ofSL ModularGroup.T) x = x → subHom ε 1 1 (X.exp x) = X.exp x := fun x hx => by
    have := modularTowerExp_slAction_T_pow ε X 1 x
    rw [pow_one, hx, Nat.cast_one] at this
    exact this.symm
  have tφ : subHom ε 1 1 φ = φ := by
    ext r
    rw [coeff_tr, mul_one]
    by_cases h0 : φ.coeff r = 0
    · simp [h0]
    · rw [eOm_of_den ε (hφ r h0), one_mul]
  have hx : ∀ x : X.K, X.exp (∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) x) =
      ∏ j ∈ Finset.range l, subHom ε (j : ℕ) l (X.exp x) := fun x => by
    rw [map_prod]; exact Finset.prod_congr rfl fun j _ => exp_sl_m ε X j l x
  refine ⟨fun r => ?_, ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) a,
    ∏ j ∈ Finset.range l, X.sl (toGQ !![1, (j : ℤ); 0, (l : ℤ)]) b, κ ^ l, pow_ne_zero _ hκ, ?_, ?_, ?_, ?_⟩
  · rw [Api.hq_eq_uq_of_isAlgClosed (NeZero.pos l) (fun r hr => by simpa using hφ r hr), Api.coeff_uq (NeZero.pos l)]
    split_ifs
    · exact h.1 _
    · exact zero_mem A
  · rw [← Finset.prod_mul_distrib]
    simp only [← map_mul, e]
    simp only [map_mul, AlgEquiv.commutes]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, map_pow]
  · rw [hx]; exact prim_prod _ fun j => prim_subHom ε _ l pa
  · rw [hx]; exact prim_prod _ fun j => prim_subHom ε _ l pb
  · rw [dv_iff, hx, hx]
    exact dv_norm ε l pa pb tφ (tx a ta) (tx b tb) c

end GlobalTheory.NormDl
