import Formalism.WachModuleLifts.Statement

open Finset PowerSeries

noncomputable section

namespace Formalism.CL

namespace CSharpG

def Bd (p : ℕ) [Fact p.Prime] (α c : ℝ) (f : PowerSeries ℚ_[p]) : Prop :=
  ∀ b : ℕ, ‖coeff b f‖ ≤ (p : ℝ) ^ (α * b + c)

def Dg (p : ℕ) [Fact p.Prime] (D : ℕ) (f : PowerSeries ℚ_[p]) : Prop := ∀ b, D < b → coeff b f = 0

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Conclude with `hp.out.pos` after adjusting the coercions.
-/
lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
/- English proof (translation)
Conclude with `hp.out.one_lt` after adjusting the coercions.
-/
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
/- English proof (translation)
The claim follows from `Real.rpow_pos_of_pos p_pos x`.
-/
lemma rp_pos (x : ℝ) : (0 : ℝ) < (p : ℝ) ^ x := Real.rpow_pos_of_pos p_pos x

/- English proof (translation)
Introduce `b`. Rewrite using `[coeff_mul]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (rp_pos _).le` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[HasAntidiagonal.mem_antidiagonal]`.

Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_add p_pos, ← hx]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma bd_mul {α c d : ℝ} {f g : PowerSeries ℚ_[p]} (hf : Bd p α c f) (hg : Bd p α d g) :
    Bd p α (c + d) (f * g) := by
  intro b
  rw [coeff_mul]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (rp_pos _).le
  intro x hx
  rw [HasAntidiagonal.mem_antidiagonal] at hx
  rw [norm_mul]
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ ≤ (p:ℝ) ^ (α * x.1 + c) * (p:ℝ) ^ (α * x.2 + d) :=
        mul_le_mul (hf _) (hg _) (norm_nonneg _) (rp_pos _).le
    _ = (p:ℝ) ^ (α * b + (c + d)) := by
        rw [← Real.rpow_add p_pos, ← hx]; congr 1; push_cast; ring

/- English proof (translation)
Introduce `b`. Rewrite using `[coeff_one]`. Use `split_ifs`. Rewrite using `[norm_one]`. Conclude with `Real.one_le_rpow one_lt_p.le (add_nonneg (mul_nonneg hα (Nat.cast_nonneg _)) le_rfl)`.

Rewrite using `[norm_zero]`. Conclude with `(rp_pos _).le`.
-/
lemma bd_one {α : ℝ} (hα : 0 ≤ α) : Bd p α 0 1 := by
  intro b
  rw [coeff_one]
  split_ifs
  · rw [norm_one]
    exact Real.one_le_rpow one_lt_p.le (add_nonneg (mul_nonneg hα (Nat.cast_nonneg _)) le_rfl)
  · rw [norm_zero]; exact (rp_pos _).le

/- English proof (translation)
The claim follows from `| 0 => by have e : ((0 : ℕ) : ℝ) * c = 0 := by simp rw [e, pow_zero]; exact bd_one hα | n + 1 => by have e : ((n + 1 : ℕ) : ℝ) * c = n * c + c := by push_cast; ring rw [e, pow_succ]; exact bd_mul (bd_pow hα hf n) hf`.
-/
lemma bd_pow {α c : ℝ} (hα : 0 ≤ α) {f : PowerSeries ℚ_[p]} (hf : Bd p α c f) :
    ∀ n : ℕ, Bd p α (n * c) (f ^ n)
  | 0 => by
    have e : ((0 : ℕ) : ℝ) * c = 0 := by simp
    rw [e, pow_zero]; exact bd_one hα
  | n + 1 => by
    have e : ((n + 1 : ℕ) : ℝ) * c = n * c + c := by push_cast; ring
    rw [e, pow_succ]; exact bd_mul (bd_pow hα hf n) hf

/- English proof (translation)
Introduce `b`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf b) (hg b))`.
-/
lemma bd_add {α c : ℝ} {f g : PowerSeries ℚ_[p]} (hf : Bd p α c f) (hg : Bd p α c g) :
    Bd p α c (f + g) := by
  intro b; rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf b) (hg b))

/- English proof (translation)
Introduce `b`. Rewrite using `[map_neg, norm_neg]`. Conclude with `hf b`.
-/
lemma bd_neg {α c : ℝ} {f : PowerSeries ℚ_[p]} (hf : Bd p α c f) : Bd p α c (-f) := by
  intro b; rw [map_neg, norm_neg]; exact hf b

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `bd_add hf (bd_neg hg)`.
-/
lemma bd_sub {α c : ℝ} {f g : PowerSeries ℚ_[p]} (hf : Bd p α c f) (hg : Bd p α c g) :
    Bd p α c (f - g) := by
  rw [sub_eq_add_neg]; exact bd_add hf (bd_neg hg)

/- English proof (translation)
Introduce `b`. Rewrite using `[coeff_C_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma bd_C_mul {α c e : ℝ} {a : ℚ_[p]} {f : PowerSeries ℚ_[p]} (ha : ‖a‖ ≤ (p:ℝ) ^ e)
    (hf : Bd p α c f) : Bd p α (c + e) (C a * f) := by
  intro b; rw [coeff_C_mul, norm_mul]
  calc ‖a‖ * ‖coeff b f‖ ≤ (p:ℝ) ^ e * (p:ℝ) ^ (α * b + c) :=
        mul_le_mul ha (hf b) (norm_nonneg _) (rp_pos _).le
    _ = _ := by rw [← Real.rpow_add p_pos]; congr 1; ring

/- English proof (translation)
Introduce `b hb`. Rewrite using `[coeff_mul]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `x hx`. Rewrite `hx` using `[HasAntidiagonal.mem_antidiagonal]`.

Distinguish the cases in `h1 : D < x.1`. Rewrite using `[hf _ h1, zero_mul]`. Rewrite using `[hg _ (by omega), mul_zero]`.
-/
lemma dg_mul {D E : ℕ} {f g : PowerSeries ℚ_[p]} (hf : Dg p D f) (hg : Dg p E g) :
    Dg p (D + E) (f * g) := by
  intro b hb; rw [coeff_mul]
  apply Finset.sum_eq_zero; intro x hx; rw [HasAntidiagonal.mem_antidiagonal] at hx
  by_cases h1 : D < x.1
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

/- English proof (translation)
Introduce `b hb; rw [coeff_one, if_neg (by omega)]`.
-/
lemma dg_one : Dg p 0 (1 : PowerSeries ℚ_[p]) := by
  intro b hb; rw [coeff_one, if_neg (by omega)]

/- English proof (translation)
The claim follows from `| 0 => by rw [zero_mul, pow_zero]; exact dg_one | n + 1 => by rw [pow_succ, Nat.succ_mul]; exact dg_mul (dg_pow hf n) hf`.
-/
lemma dg_pow {D : ℕ} {f : PowerSeries ℚ_[p]} (hf : Dg p D f) : ∀ n : ℕ, Dg p (n * D) (f ^ n)
  | 0 => by rw [zero_mul, pow_zero]; exact dg_one
  | n + 1 => by rw [pow_succ, Nat.succ_mul]; exact dg_mul (dg_pow hf n) hf

/- English proof (translation)
Introduce `b hb` and use `hf b (by omega)`.
-/
lemma dg_mono {D D' : ℕ} {f : PowerSeries ℚ_[p]} (h : D ≤ D') (hf : Dg p D f) : Dg p D' f :=
  fun b hb => hf b (by omega)

/- English proof (translation)
Introduce `b hb`. Rewrite using `[map_add, hf b hb, hg b hb, add_zero]`.
-/
lemma dg_add {D : ℕ} {f g : PowerSeries ℚ_[p]} (hf : Dg p D f) (hg : Dg p D g) :
    Dg p D (f + g) := by
  intro b hb; rw [map_add, hf b hb, hg b hb, add_zero]

/- English proof (translation)
Introduce `b hb`. Rewrite using `[map_sub, hf b hb, hg b hb, sub_zero]`.
-/
lemma dg_sub {D : ℕ} {f g : PowerSeries ℚ_[p]} (hf : Dg p D f) (hg : Dg p D g) :
    Dg p D (f - g) := by
  intro b hb; rw [map_sub, hf b hb, hg b hb, sub_zero]

/- English proof (translation)
Introduce `b hb`. Rewrite using `[coeff_C_mul, hf b hb, mul_zero]`.
-/
lemma dg_C_mul {D : ℕ} {a : ℚ_[p]} {f : PowerSeries ℚ_[p]} (hf : Dg p D f) :
    Dg p D (C a * f) := by
  intro b hb; rw [coeff_C_mul, hf b hb, mul_zero]

/- English proof (translation)
Rewrite using `[coeff_mul, Finset.sum_eq_single (D, E)]`. Introduce `x hx hne`. Rewrite `hx` using `[HasAntidiagonal.mem_antidiagonal]`. Distinguish the cases in `h1 : D < x.1`. Rewrite using `[hf _ h1, zero_mul]`.

Distinguish the cases in `h2 : E < x.2`. Rewrite using `[hg _ h2, mul_zero]`. Conclude with `absurd (Prod.ext (by simp only; omega) (by simp only; omega)) hne`. Introduce `h`. Conclude with `absurd (HasAntidiagonal.mem_antidiagonal.mpr (rfl : D + E = D + E)) h`.
-/
lemma top_mul {D E : ℕ} {f g : PowerSeries ℚ_[p]} (hf : Dg p D f) (hg : Dg p E g) :
    coeff (D + E) (f * g) = coeff D f * coeff E g := by
  rw [coeff_mul, Finset.sum_eq_single (D, E)]
  · intro x hx hne; rw [HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h1 : D < x.1
    · rw [hf _ h1, zero_mul]
    · by_cases h2 : E < x.2
      · rw [hg _ h2, mul_zero]
      · exact absurd (Prod.ext (by simp only; omega) (by simp only; omega)) hne
  · intro h; exact absurd (HasAntidiagonal.mem_antidiagonal.mpr (rfl : D + E = D + E)) h

/- English proof (translation)
The claim follows from `| 0 => by rw [zero_mul, pow_zero, pow_zero, coeff_one, if_pos rfl] | n + 1 => by rw [pow_succ, Nat.succ_mul, top_mul (dg_pow hf n) hf, top_pow hf n, pow_succ]`.
-/
lemma top_pow {D : ℕ} {f : PowerSeries ℚ_[p]} (hf : Dg p D f) :
    ∀ n : ℕ, coeff (n * D) (f ^ n) = (coeff D f) ^ n
  | 0 => by rw [zero_mul, pow_zero, pow_zero, coeff_one, if_pos rfl]
  | n + 1 => by
    rw [pow_succ, Nat.succ_mul, top_mul (dg_pow hf n) hf, top_pow hf n, pow_succ]

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero => omega`. Consider the case `succ n => simp [Nat.succ_mul]`.
-/
lemma aux_mul (n Q : ℕ) (hn : 1 ≤ n) : n * Q = (n - 1) * Q + Q := by
  cases n with
  | zero => omega
  | succ n => simp [Nat.succ_mul]

/- English proof (translation)
Rewrite using `[inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), one_mul]`.
-/
lemma sub_one_add_inv_sub_one_add_mul_eq_zero {K : Type*} [Field K] (x : K) (hx : x ≠ 0) (k : ℕ) :
    x ^ k * (x⁻¹) ^ (k + 1) = x⁻¹ := by
  rw [inv_pow, pow_succ, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hx), one_mul]

/- English proof (translation)
Rewrite using `[norm_inv, Padic.norm_p, inv_inv]`.
-/
lemma norm_p_inv : ‖(p : ℚ_[p])⁻¹‖ = (p : ℝ) := by
  rw [norm_inv, Padic.norm_p, inv_inv]

/- English proof (translation)
Rewrite using `[Padic.norm_p_pow, ← Real.rpow_intCast]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_p_pow_r (n : ℕ) : ‖(p : ℚ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℝ)) := by
  rw [Padic.norm_p_pow, ← Real.rpow_intCast]; congr 1; push_cast; ring

/- English proof (translation)
Rewrite using `[Nat.cast_sub hp.out.one_le, Nat.cast_one]`.
-/
lemma km1 : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]

/- English proof (translation)
Simplify using `[uu, phiIter, PowerSeries.smul_eq_C_mul, Polynomial.coe_X]`.
-/
lemma uu_zero : uu p 0 = C ((p : ℚ_[p])⁻¹) * X ^ 1 := by
  simp [uu, phiIter, PowerSeries.smul_eq_C_mul, Polynomial.coe_X]

/- English proof (translation)
Simplify using `only [phiIter]`. Rewrite using `[Function.iterate_succ_apply']`.
-/
lemma phiIter_succ (g : ℕ) : phiIter p (g + 1) = (phiPoly p).comp (phiIter p g) := by
  simp only [phiIter]; rw [Function.iterate_succ_apply']

def hh (p : ℕ) [Fact p.Prime] (g : ℕ) : PowerSeries ℚ_[p] :=
  C ((p : ℚ_[p]) ^ (p - 1)) * (uu p g ^ p - uu p g ^ (p - 1))

/- English proof (translation)
Establish `hp0 : (p : ℚ_[p]) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Use `set F : PowerSeries ℚ_[p] := ((phiIter p g : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) with hF`. Establish `hu : uu p g = C ((p:ℚ_[p])⁻¹) * F` using `by simp [uu, F, PowerSeries.smul_eq_C_mul]`. Establish `hu1 : uu p (g + 1) = C ((p:ℚ_[p])⁻¹) * (F ^ p - C (p:ℚ_[p]) * F ^ (p - 1) + C (p:ℚ_[p]))`. Simplify using `only [uu, phiIter_succ, phiPoly, PowerSeries.smul_eq_C_mul, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_C, …`.

Establish `hc : C ((p:ℚ_[p])⁻¹) * C (p:ℚ_[p]) = 1`. Rewrite using `[← map_mul, inv_mul_cancel₀ hp0, map_one]`. Rewrite using `[hu1, hh, hu, map_pow]`. Use `set a := C ((p:ℚ_[p])⁻¹)`. Use `set c := C (p:ℚ_[p])`.

Establish `hk : p = (p - 1) + 1` using `(Nat.sub_add_cancel hp.out.one_le).symm`. Use `set k := p - 1`. Establish `hck : (a * c) ^ k = 1` using `by rw [hc, one_pow]`. Establish `hpow : ∀ x : PowerSeries ℚ_[p], x ^ p = x ^ k * x` using `fun x => by`. Rewrite using `[← pow_succ, ← hk]`.

Simplify using `only [hpow]`. Take the linear combination `(1 - F ^ k) * hc - (a * F ^ (k + 1) - F ^ k) * hck`.
-/
lemma uu_succ (g : ℕ) : uu p (g + 1) = 1 + hh p g := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set F : PowerSeries ℚ_[p] := ((phiIter p g : Polynomial ℚ_[p]) : PowerSeries ℚ_[p]) with hF
  have hu : uu p g = C ((p:ℚ_[p])⁻¹) * F := by simp [uu, F, PowerSeries.smul_eq_C_mul]
  have hu1 : uu p (g + 1) =
      C ((p:ℚ_[p])⁻¹) * (F ^ p - C (p:ℚ_[p]) * F ^ (p - 1) + C (p:ℚ_[p])) := by
    simp only [uu, phiIter_succ, phiPoly, PowerSeries.smul_eq_C_mul, Polynomial.add_comp,
      Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp,
      Polynomial.C_comp, Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_C, F]
  have hc : C ((p:ℚ_[p])⁻¹) * C (p:ℚ_[p]) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  rw [hu1, hh, hu, map_pow]
  set a := C ((p:ℚ_[p])⁻¹)
  set c := C (p:ℚ_[p])
  have hk : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.out.one_le).symm
  set k := p - 1
  have hck : (a * c) ^ k = 1 := by rw [hc, one_pow]
  have hpow : ∀ x : PowerSeries ℚ_[p], x ^ p = x ^ k * x := fun x => by
    rw [← pow_succ, ← hk]
  simp only [hpow]
  linear_combination (1 - F ^ k) * hc - (a * F ^ (k + 1) - F ^ k) * hck

/- English proof (translation)
Establish `hp2 : 2 ≤ p` using `hp.out.two_le`. Rewrite using `[hh, coeff_C_mul, coeff_zero_eq_constantCoeff_apply, map_sub, map_pow, map_pow, ← coeff_zero_eq_constantCoeff_apply]`. Apply the tactic sequence `rcases h0 with h | h <;> rw [h]`. Rewrite using `[zero_pow (by omega), zero_pow (by omega), sub_zero, mul_zero]`. Rewrite using `[one_pow, one_pow, sub_self, mul_zero]`.
-/
lemma hh_coeff0_of {g : ℕ} (h0 : coeff 0 (uu p g) = 0 ∨ coeff 0 (uu p g) = 1) :
    coeff 0 (hh p g) = 0 := by
  have hp2 : 2 ≤ p := hp.out.two_le
  rw [hh, coeff_C_mul, coeff_zero_eq_constantCoeff_apply, map_sub, map_pow, map_pow,
    ← coeff_zero_eq_constantCoeff_apply]
  rcases h0 with h | h <;> rw [h]
  · rw [zero_pow (by omega), zero_pow (by omega), sub_zero, mul_zero]
  · rw [one_pow, one_pow, sub_self, mul_zero]

structure Level (p : ℕ) [Fact p.Prime] (g : ℕ) : Prop where
  bd : Bd p (1 / (p : ℝ) ^ g) 0 (uu p g)
  dg : Dg p (p ^ g) (uu p g)
  top : coeff (p ^ g) (uu p g) = (p : ℚ_[p])⁻¹
  c0 : coeff 0 (uu p g) = 0 ∨ coeff 0 (uu p g) = 1

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b`. Rewrite using `[uu_zero, coeff_C_mul_X_pow]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Rewrite using `[norm_p_inv]`. Simplify using the standard rewrite rules. Rewrite using `[norm_zero]`. Conclude with `(rp_pos _).le`. Introduce `b hb`.

Rewrite using `[uu_zero, coeff_C_mul_X_pow, if_neg (by simp at hb; omega)]`. Rewrite using `[uu_zero, coeff_C_mul_X_pow, if_pos (by simp)]`. Use the proof step `left; rw [uu_zero, coeff_C_mul_X_pow, if_neg (by omega)]`.
-/
lemma level_zero : Level p 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    rw [uu_zero, coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; rw [norm_p_inv]; simp
    · rw [norm_zero]; exact (rp_pos _).le
  · intro b hb
    rw [uu_zero, coeff_C_mul_X_pow, if_neg (by simp at hb; omega)]
  · rw [uu_zero, coeff_C_mul_X_pow, if_pos (by simp)]
  · left; rw [uu_zero, coeff_C_mul_X_pow, if_neg (by omega)]

structure HFacts (p : ℕ) [Fact p.Prime] (g : ℕ) : Prop where
  bd : Bd p (1 / (p : ℝ) ^ g) (-((p - 1 : ℕ) : ℝ)) (hh p g)
  dg : Dg p (p ^ (g + 1)) (hh p g)
  top : coeff (p ^ (g + 1)) (hh p g) = (p : ℚ_[p])⁻¹
  c0 : coeff 0 (hh p g) = 0

/- English proof (translation)
Establish `hα : 0 ≤ 1 / (p : ℝ) ^ g` using `by positivity`. Establish `hp1 : 1 ≤ p` using `hp.out.one_le`. Establish `hp0 : (p : ℚ_[p]) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Use `⟨?_, ?_, ?_, hh_coeff0_of L.c0⟩` and prove the remaining obligations. Establish `h1 : Bd p (1 / (p : ℝ) ^ g) 0 (uu p g ^ p)`.

Use `bd_pow hα L.bd p` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis. Establish `h2 : Bd p (1 / (p : ℝ) ^ g) 0 (uu p g ^ (p - 1))`. Use `bd_pow hα L.bd (p - 1)` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Then use the resulting hypothesis.

Use `bd_C_mul (le_of_eq (norm_p_pow_r (p := p) (p - 1))) (bd_sub h1 h2)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Conclude with `this`. Establish `e : p ^ (g + 1) = p * p ^ g` using `pow_succ' p g`. Rewrite using `[e]`.

Apply `dg_C_mul` to reduce the goal to its premises. Apply `dg_sub (dg_pow L.dg p)` to reduce the goal to its premises. Conclude with `dg_mono (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (dg_pow L.dg (p - 1))`. Establish `e : p ^ (g + 1) = p * p ^ g` using `pow_succ' p g`. Establish `hQ : 0 < p ^ g` using `pow_pos hp.out.pos g`.

Establish `hlt : (p - 1) * p ^ g < p ^ (g + 1)`. Rewrite using `[e]`. Establish `e2 : p * p ^ g = (p - 1) * p ^ g + p ^ g` using `aux_mul p _ hp1`. Rewrite using `[e2]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hh, coeff_C_mul, map_sub, dg_pow L.dg (p - 1) _ hlt, sub_zero, e, top_pow L.dg p, L.top]`. Use `sub_one_add_inv_sub_one_add_mul_eq_zero (p : ℚ_[p]) hp0 (p - 1)` as an intermediate fact. Rewrite `this` using `[Nat.sub_add_cancel hp1]`. Then use the resulting hypothesis.
-/
lemma hfacts {g : ℕ} (L : Level p g) : HFacts p g := by
  have hα : 0 ≤ 1 / (p : ℝ) ^ g := by positivity
  have hp1 : 1 ≤ p := hp.out.one_le
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  refine ⟨?_, ?_, ?_, hh_coeff0_of L.c0⟩
  · have h1 : Bd p (1 / (p : ℝ) ^ g) 0 (uu p g ^ p) := by
      have := bd_pow hα L.bd p; rwa [mul_zero] at this
    have h2 : Bd p (1 / (p : ℝ) ^ g) 0 (uu p g ^ (p - 1)) := by
      have := bd_pow hα L.bd (p - 1); rwa [mul_zero] at this
    have := bd_C_mul (le_of_eq (norm_p_pow_r (p := p) (p - 1))) (bd_sub h1 h2)
    rw [zero_add] at this
    exact this
  · have e : p ^ (g + 1) = p * p ^ g := pow_succ' p g
    rw [e]
    apply dg_C_mul
    apply dg_sub (dg_pow L.dg p)
    exact dg_mono (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) (dg_pow L.dg (p - 1))
  · have e : p ^ (g + 1) = p * p ^ g := pow_succ' p g
    have hQ : 0 < p ^ g := pow_pos hp.out.pos g
    have hlt : (p - 1) * p ^ g < p ^ (g + 1) := by
      rw [e]
      have e2 : p * p ^ g = (p - 1) * p ^ g + p ^ g := aux_mul p _ hp1
      rw [e2]; omega
    rw [hh, coeff_C_mul, map_sub, dg_pow L.dg (p - 1) _ hlt, sub_zero, e, top_pow L.dg p, L.top]
    have := sub_one_add_inv_sub_one_add_mul_eq_zero (p : ℚ_[p]) hp0 (p - 1)
    rwa [Nat.sub_add_cancel hp1] at this

/- English proof (translation)
Establish `H` using `hfacts L`. Establish `hQ : (0 : ℝ) < (p : ℝ) ^ g` using `pow_pos p_pos g`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `b`. Rewrite using `[uu_succ, map_add]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `bd_one (by positivity) b`. Distinguish the cases in `hb : p ^ (g + 1) < b`. Rewrite using `[H.dg b hb, norm_zero]`. Conclude with `(rp_pos _).le`.

Use `(H.bd b).trans (Real.rpow_le_rpow_of_exponent_le one_lt_p.le ?_)` and prove the remaining obligations. Establish `hb' : (b : ℝ) ≤ (p : ℝ) ^ (g + 1)` using `by exact_mod_cast (not_lt.mp hb)`. Rewrite `*` using `[km1, pow_succ]`. Establish `hP : (1 : ℝ) < p` using `one_lt_p`. Use `set t := (b : ℝ) / ((p : ℝ) ^ g * p) with ht`.

Establish `ht1 : t ≤ 1` using `by rw [ht, div_le_one (by positivity)]; exact hb'`. Establish `e1 : 1 / (p : ℝ) ^ g * b = p * t` using `by rw [ht]; field_simp`. Establish `e2 : 1 / ((p : ℝ) ^ g * p) * b = t` using `by rw [ht]; field_simp`. Rewrite using `[e1, e2]`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[uu_succ]`. Conclude with `dg_add (dg_mono (Nat.zero_le _) dg_one) H.dg`. Rewrite using `[uu_succ, map_add, coeff_one, if_neg (pow_pos hp.out.pos _).ne', zero_add, H.top]`. Use `right`. Rewrite using `[uu_succ, map_add, coeff_one, if_pos rfl, H.c0, add_zero]`.
-/
lemma level_succ {g : ℕ} (L : Level p g) : Level p (g + 1) := by
  have H := hfacts L
  have hQ : (0 : ℝ) < (p : ℝ) ^ g := pow_pos p_pos g
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    rw [uu_succ, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact bd_one (by positivity) b
    · by_cases hb : p ^ (g + 1) < b
      · rw [H.dg b hb, norm_zero]; exact (rp_pos _).le
      · refine (H.bd b).trans (Real.rpow_le_rpow_of_exponent_le one_lt_p.le ?_)
        have hb' : (b : ℝ) ≤ (p : ℝ) ^ (g + 1) := by exact_mod_cast (not_lt.mp hb)
        rw [km1, pow_succ] at *
        have hP : (1 : ℝ) < p := one_lt_p
        set t := (b : ℝ) / ((p : ℝ) ^ g * p) with ht
        have ht1 : t ≤ 1 := by rw [ht, div_le_one (by positivity)]; exact hb'
        have e1 : 1 / (p : ℝ) ^ g * b = p * t := by rw [ht]; field_simp
        have e2 : 1 / ((p : ℝ) ^ g * p) * b = t := by rw [ht]; field_simp
        rw [e1, e2]
        nlinarith
  · rw [uu_succ]
    exact dg_add (dg_mono (Nat.zero_le _) dg_one) H.dg
  · rw [uu_succ, map_add, coeff_one, if_neg (pow_pos hp.out.pos _).ne', zero_add, H.top]
  · right; rw [uu_succ, map_add, coeff_one, if_pos rfl, H.c0, add_zero]

/- English proof (translation)
The claim follows from `| 0 => level_zero | g + 1 => level_succ (level g)`.
-/
lemma level : ∀ g : ℕ, Level p g
  | 0 => level_zero
  | g + 1 => level_succ (level g)

def TT (p : ℕ) [Fact p.Prime] (g : ℕ) : PowerSeries ℚ_[p] := C ((p:ℚ_[p])⁻¹) * X ^ (p ^ (g + 1))

/- English proof (translation)
Establish `: (0:ℝ) < (p:ℝ) ^ g` using `pow_pos p_pos g`. Use `push_cast`. Rewrite using `[pow_succ]`. Clear the denominators using the available nonvanishing facts.
-/
lemma alphaN (g : ℕ) : 1 / (p:ℝ) ^ g * ((p ^ (g + 1) : ℕ) : ℝ) = p := by
  have : (0:ℝ) < (p:ℝ) ^ g := pow_pos p_pos g
  push_cast; rw [pow_succ]; field_simp

/- English proof (translation)
The claim follows from `coeff_C_mul_X_pow _ _ _`.
-/
lemma TT_coeff (g b : ℕ) :
    coeff b (TT p g) = if b = p ^ (g + 1) then (p:ℚ_[p])⁻¹ else 0 := coeff_C_mul_X_pow _ _ _

/- English proof (translation)
Introduce `b`. Rewrite using `[TT_coeff]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[norm_p_inv, alphaN, km1]`.

Rewrite using `[show (p:ℝ) + -((p:ℝ) - 1) = 1 by ring, Real.rpow_one]`. Rewrite using `[norm_zero]`. Conclude with `(rp_pos _).le`.
-/
lemma TT_bd (g : ℕ) : Bd p (1 / (p:ℝ) ^ g) (-((p - 1 : ℕ) : ℝ)) (TT p g) := by
  intro b; rw [TT_coeff]; split_ifs with h
  · subst h; rw [norm_p_inv, alphaN, km1]
    rw [show (p:ℝ) + -((p:ℝ) - 1) = 1 by ring, Real.rpow_one]
  · rw [norm_zero]; exact (rp_pos _).le

/- English proof (translation)
Introduce `b hb; rw [TT_coeff, if_neg (by omega)]`.
-/
lemma TT_dg (g : ℕ) : Dg p (p ^ (g + 1)) (TT p g) := by
  intro b hb; rw [TT_coeff, if_neg (by omega)]

/- English proof (translation)
Establish `H` using `hfacts (level (p := p) g)`. Introduce `b hb`. Rewrite using `[map_sub, TT_coeff]`. Distinguish the cases in `h : b = p ^ (g + 1)`. Rewrite using `[h, H.top, if_pos rfl, sub_self]`.

Establish `hN0 : 0 < p ^ (g + 1)` using `pow_pos hp.out.pos _`. Rewrite using `[H.dg b (by omega), if_neg h, sub_zero]`.
-/
lemma LL_dg (g : ℕ) : Dg p (p ^ (g + 1) - 1) (hh p g - TT p g) := by
  have H := hfacts (level (p := p) g)
  intro b hb
  rw [map_sub, TT_coeff]
  by_cases h : b = p ^ (g + 1)
  · rw [h, H.top, if_pos rfl, sub_self]
  · have hN0 : 0 < p ^ (g + 1) := pow_pos hp.out.pos _
    rw [H.dg b (by omega), if_neg h, sub_zero]

/- English proof (translation)
Use linear arithmetic over natural numbers and integers.
-/
lemma ineq1 (N A : ℕ) (hA : 1 ≤ A) : N + (A - 1) ≤ (A + N) - 1 := by omega
/- English proof (translation)
Use linear arithmetic over natural numbers and integers.
-/
lemma ineq2 (N A : ℕ) (hN : 1 ≤ N) : (N - 1) + A ≤ (A + N) - 1 := by omega

/- English proof (translation)
Establish `H` using `hfacts (level (p := p) g)`. Establish `hN0 : 0 < p ^ (g + 1)` using `pow_pos hp.out.pos _`. Introduce `n hn`. Proceed by induction on `n, hn using Nat.le_induction with`. Consider the case `base => rw [pow_one, pow_one, mul_one]`.

Conclude with `LL_dg g`. Consider the case `succ n hn ih`. Establish `e : hh p g ^ (n + 1) - TT p g ^ (n + 1) = hh p g * (hh p g ^ n - TT p g ^ n) + (hh p g - TT p g) * TT p g ^ n` using `by ring`. Rewrite using `[e, Nat.mul_succ]`. Apply `dg_add` to reduce the goal to its premises.

Conclude with `dg_mono (ineq1 _ _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hN0 hn).ne')) (dg_mul H.dg ih)`. Use `dg_mul (LL_dg g) (dg_pow (TT_dg (p := p) g) n)` as an intermediate fact. Rewrite `this` using `[mul_comm n]`. Conclude with `dg_mono (ineq2 _ _ hN0) this`.
-/
lemma E_dg (g : ℕ) : ∀ n : ℕ, 1 ≤ n →
    Dg p (p ^ (g + 1) * n - 1) (hh p g ^ n - TT p g ^ n) := by
  have H := hfacts (level (p := p) g)
  have hN0 : 0 < p ^ (g + 1) := pow_pos hp.out.pos _
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rw [pow_one, pow_one, mul_one]; exact LL_dg g
  | succ n hn ih =>
    have e : hh p g ^ (n + 1) - TT p g ^ (n + 1) =
        hh p g * (hh p g ^ n - TT p g ^ n) + (hh p g - TT p g) * TT p g ^ n := by ring
    rw [e, Nat.mul_succ]
    apply dg_add
    · exact dg_mono (ineq1 _ _ (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hN0 hn).ne'))
        (dg_mul H.dg ih)
    · have := dg_mul (LL_dg g) (dg_pow (TT_dg (p := p) g) n)
      rw [mul_comm n] at this
      exact dg_mono (ineq2 _ _ hN0) this

/- English proof (translation)
Establish `H` using `hfacts (level (p := p) g)`. Establish `hα : 0 ≤ 1 / (p : ℝ) ^ g` using `by have := pow_pos (p_pos (p := p)) g; positivity`. Conclude with `bd_sub (bd_pow hα H.bd n) (bd_pow hα (TT_bd g) n)`.
-/
lemma E_bd (g n : ℕ) :
    Bd p (1 / (p:ℝ) ^ g) (n * -((p - 1 : ℕ) : ℝ)) (hh p g ^ n - TT p g ^ n) := by
  have H := hfacts (level (p := p) g)
  have hα : 0 ≤ 1 / (p : ℝ) ^ g := by have := pow_pos (p_pos (p := p)) g; positivity
  exact bd_sub (bd_pow hα H.bd n) (bd_pow hα (TT_bd g) n)

/- English proof (translation)
Establish `hN0 : 0 < p ^ (g + 1)` using `pow_pos hp.out.pos _`. Establish `hT : TT p g ^ n = C ((p:ℚ_[p])⁻¹ ^ n) * X ^ (p ^ (g + 1) * n)`. Rewrite using `[TT, mul_pow, ← map_pow, ← pow_mul]`. Establish `hsplit : coeff (p ^ (g + 1) * r) (hh p g ^ n) = coeff (p ^ (g + 1) * r) (TT p g ^ n) + coeff (p ^ (g + 1) * r) (hh p g ^ n - TT p g ^ n)` using `by rw [map_sub]; ring`. Establish `hmain : coeff (p ^ (g + 1) * r) (TT p g ^ n) = if n = r then (p:ℚ_[p])⁻¹ ^ r else 0`.

Rewrite using `[hT, coeff_C_mul_X_pow]`. Distinguish the cases in `h : n = r`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun h' => h (Nat.eq_of_mul_eq_mul_left hN0 h').symm)]`.

Rewrite using `[hsplit, hmain, add_sub_cancel_left]`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Rewrite using `[pow_zero, pow_zero, sub_self, map_zero, norm_zero]`. Conclude with `(rp_pos _).le`.

Distinguish the cases in `hrn : n ≤ r`. Establish `hlt : p ^ (g + 1) * n - 1 < p ^ (g + 1) * r`. Establish `h1` using `Nat.mul_le_mul_left (p ^ (g + 1)) hrn`. Establish `h2` using `Nat.mul_pos hN0 hn`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[E_dg g n hn _ hlt, norm_zero]`. Conclude with `(rp_pos _).le`. Use `push Not at hrn`. Use `(E_bd g n _).trans (Real.rpow_le_rpow_of_exponent_le one_lt_p.le ?_)` and prove the remaining obligations. Establish `e : 1 / (p:ℝ) ^ g * ((p ^ (g + 1) * r : ℕ) : ℝ) = p * r`.

Rewrite using `[Nat.cast_mul, ← mul_assoc, alphaN]`. Rewrite using `[e, km1]`. Establish `hr : (r:ℝ) + 1 ≤ n` using `by exact_mod_cast hrn`. Establish `hP : (1:ℝ) ≤ p` using `one_lt_p.le`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hr)]`.
-/
lemma key (g n r : ℕ) :
    ‖coeff (p ^ (g + 1) * r) (hh p g ^ n) - (if n = r then (p:ℚ_[p])⁻¹ ^ r else 0)‖ ≤
      (p:ℝ) ^ ((r:ℝ) - ((p - 1 : ℕ) : ℝ)) := by
  have hN0 : 0 < p ^ (g + 1) := pow_pos hp.out.pos _
  have hT : TT p g ^ n = C ((p:ℚ_[p])⁻¹ ^ n) * X ^ (p ^ (g + 1) * n) := by
    rw [TT, mul_pow, ← map_pow, ← pow_mul]
  have hsplit : coeff (p ^ (g + 1) * r) (hh p g ^ n) = coeff (p ^ (g + 1) * r) (TT p g ^ n) +
      coeff (p ^ (g + 1) * r) (hh p g ^ n - TT p g ^ n) := by rw [map_sub]; ring
  have hmain : coeff (p ^ (g + 1) * r) (TT p g ^ n) =
      if n = r then (p:ℚ_[p])⁻¹ ^ r else 0 := by
    rw [hT, coeff_C_mul_X_pow]
    by_cases h : n = r
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Nat.eq_of_mul_eq_mul_left hN0 h').symm)]
  rw [hsplit, hmain, add_sub_cancel_left]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; rw [pow_zero, pow_zero, sub_self, map_zero, norm_zero]; exact (rp_pos _).le
  by_cases hrn : n ≤ r
  · have hlt : p ^ (g + 1) * n - 1 < p ^ (g + 1) * r := by
      have h1 := Nat.mul_le_mul_left (p ^ (g + 1)) hrn
      have h2 := Nat.mul_pos hN0 hn
      omega
    rw [E_dg g n hn _ hlt, norm_zero]; exact (rp_pos _).le
  · push Not at hrn
    refine (E_bd g n _).trans (Real.rpow_le_rpow_of_exponent_le one_lt_p.le ?_)
    have e : 1 / (p:ℝ) ^ g * ((p ^ (g + 1) * r : ℕ) : ℝ) = p * r := by
      rw [Nat.cast_mul, ← mul_assoc, alphaN]
    rw [e, km1]
    have hr : (r:ℝ) + 1 ≤ n := by exact_mod_cast hrn
    have hP : (1:ℝ) ≤ p := one_lt_p.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hr)]

/- English proof (translation)
Rewrite using `[Polynomial.aeval_eq_sum_range, map_sum]`. Establish `hm : P.coeff r * (p:ℚ_[p])⁻¹ ^ r = ∑ i ∈ range (P.natDegree + 1), P.coeff i * (if i = r then (p:ℚ_[p])⁻¹ ^ r else 0)`. Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]`. Rewrite using `[hm, ← Finset.sum_sub_distrib]`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (rp_pos _).le` to reduce the goal to its premises. Introduce `i _`. Simplify using `only [coeff_smul, smul_eq_mul]`.

Rewrite using `[← mul_sub, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gen (g r : ℕ) (P : Polynomial ℚ_[p]) (hP : ∀ n, ‖P.coeff n‖ ≤ 1) :
    ‖coeff (p ^ (g + 1) * r) (Polynomial.aeval (hh p g) P) - P.coeff r * (p:ℚ_[p])⁻¹ ^ r‖ ≤
      (p:ℝ) ^ ((r:ℝ) - ((p - 1 : ℕ) : ℝ)) := by
  rw [Polynomial.aeval_eq_sum_range, map_sum]
  have hm : P.coeff r * (p:ℚ_[p])⁻¹ ^ r = ∑ i ∈ range (P.natDegree + 1),
      P.coeff i * (if i = r then (p:ℚ_[p])⁻¹ ^ r else 0) := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with h
    · rfl
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  rw [hm, ← Finset.sum_sub_distrib]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (rp_pos _).le
  intro i _
  simp only [coeff_smul, smul_eq_mul]
  rw [← mul_sub, norm_mul]
  calc _ ≤ 1 * (p:ℝ) ^ ((r:ℝ) - ((p - 1 : ℕ) : ℝ)) :=
        mul_le_mul (hP i) (key g i r) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end CSharpG

end Formalism.CL
