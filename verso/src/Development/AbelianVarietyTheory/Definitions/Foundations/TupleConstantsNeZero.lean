import Mathlib
import Formalism.PairingDivisors.StatementH
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

noncomputable section

namespace GlobalTheory.Square

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def IsAwayUnit (m : ℕ) (x : K) : Prop :=
  ∃ (a : 𝓞 K) (k k' : ℕ), a ∣ (m : 𝓞 K) ^ k' ∧ x * (m : K) ^ k = (a : K)

structure An (y : ℕ) where

  c : ℂ

  c0 : ℂ

  u : Fin y → ℂ

  Lv : ℤ → ℂ

structure Co (K κ : Type) where

  X : Type
  [finX : Fintype X]

  gam : X → ℕ

  z : X → κ → K

  z' : X → κ → K

attribute [instance] Co.finX

def normAlg {κ X : Type} [Fintype κ] [Fintype X] (G : κ → κ → K) (gam : X → ℕ) (z : X → κ → K) : K :=
  ∑ x, (gam x : K)⁻¹ * ∑ k, ∑ l, z x k * star (z x l) * G k l

structure Sq (K : Type) where

  κ : Type
  [finκ : Fintype κ]

  G : κ → κ → K

  Om : ℂ

  Om' : ℂ

  A : ℂ

  e : ℕ

  p : ℕ

  q : ℕ

  e0 : ℕ

  h0 : ℕ

  base : An (p + q)

attribute [instance] Sq.finκ

structure Sq.OK (S : Sq K) (hd y : ℕ) : Prop where

  e0_eq : S.e0 + S.p = S.e + S.q

  sqrt_error_le_half : S.e0 ≤ S.h0

  hd_eq : hd = S.h0 + S.p + S.q

  y_eq : y = S.p + S.q

  Om_ne : S.Om ≠ 0

  Om'_ne : S.Om' ≠ 0

  A_ne : S.A ≠ 0

  c_ne : S.base.c ≠ 0

structure Sq.Tuple (S : Sq K) (σ₀ : K →+* ℂ) (a : An (S.p + S.q)) (Z : Co K S.κ) (w : Pl K) (dl : ℝ) : Prop where

  tower : a.c * ∏ k ∈ range S.q, a.Lv ((S.e : ℤ) + k + 1) =
    (∏ i, a.u i) * a.c0 * ∏ k ∈ range S.p, a.Lv ((S.e : ℤ) + S.q - k)

  bottom : ∀ x k, σ₀ (Z.z x k) * S.Om = a.c0 * (σ₀ (Z.z' x k) * S.Om')

  norm_eq : σ₀ (normAlg S.G Z.gam Z.z) * ((‖S.Om‖ ^ 2 : ℝ) : ℂ) =
    S.A * ∏ s ∈ Icc (1 - (S.e0 : ℤ)) (S.h0 : ℤ), a.Lv s

  norm'_ne : normAlg S.G Z.gam Z.z' ≠ 0

  L_ne : ∀ s : ℤ, 1 - (S.e0 : ℤ) ≤ s → s ≤ (S.h0 : ℤ) + S.p + S.q → a.Lv s ≠ 0

  u_ne : ∀ i, a.u i ≠ 0

  gam_pos : ∀ x, 0 < Z.gam x

  z_int : ∀ x k, -dl ≤ (vw w (Z.z x k) : ℝ) ∧ -dl ≤ (vw (conjPl w) (Z.z x k) : ℝ)

  z'_int : ∀ x k, -dl ≤ (vw w (Z.z' x k) : ℝ) ∧ -dl ≤ (vw (conjPl w) (Z.z' x k) : ℝ)

  G_int : ∀ x k l, -dl ≤ (vw w (S.G k l / (Z.gam x : K)) : ℝ)

def StepRatio {T : Type} (σ₀ : K →+* ℂ) (Qn : ℕ) (S0 : Finset T) (cc qq : T → ℕ) (u1 u0 : ℂ) : Prop :=
  ∃ (b : K) (g g' : T → 𝓞 K), IsAwayUnit Qn b ∧
    (∀ v ∈ S0, g v ∣ (qq v : 𝓞 K) ^ cc v ∧ g' v ∣ (qq v : 𝓞 K) ^ cc v) ∧
    u1 = σ₀ (b * ∏ v ∈ S0, (g v : K) / (g' v : K)) * u0

def Sq.Twisted (S : Sq K) (σ₀ : K →+* ℂ) (w : Pl K) (cw : ℂ) (zA zA' : K) (zT zTd : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ)
    (er dl : ℝ) {T : Type} (S0 : Finset T) (cc qq : T → ℕ) : Prop :=
  ∃ (a : An (S.p + S.q)) (Z0 Z1 : Co K S.κ) (zψ Ep : ℤ → K) (Qn : ℕ),
    a.c = cw ∧ S.Tuple σ₀ S.base Z0 w dl ∧ S.Tuple σ₀ a Z1 w dl ∧
    normAlg S.G Z0.gam Z0.z = zA ∧ normAlg S.G Z0.gam Z0.z' = zA' ∧ (Qn : 𝓞 K) ∉ w.asIdeal ∧
    (∀ s : ℤ, 1 ≤ s → s ≤ (S.h0 : ℤ) + S.p + S.q →
      zT s ≠ 0 ∧ zTd s ≠ 0 ∧ σ₀ (zψ s) * S.base.Lv s = σ₀ (zT s) * a.Lv s ∧
      -(n0 s) ≤ ((vw w (zψ s) + gT s : ℤ) : ℝ) ∧ (vw w (zψ s) : ℝ) ≤ (vw w (zTd s) : ℝ) + er) ∧
    (∀ s : ℤ, 1 - (S.e0 : ℤ) ≤ s → s ≤ 0 → IsAwayUnit Qn (Ep s) ∧
      a.Lv s * S.base.Lv (1 - s) = σ₀ (Ep s) * (a.Lv (1 - s) * S.base.Lv s)) ∧
    (∀ i, StepRatio σ₀ Qn S0 cc qq (a.u i) (S.base.u i))

omit [NumberField K] [StarRing K] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨a, 0, k, h, by simp⟩`.
-/
theorem IsAwayUnit.of_dvd {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) : IsAwayUnit m (a : K) :=
  ⟨a, 0, k, h, by simp⟩

omit [NumberField K] [StarRing K] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 0, 0, by simp, by simp⟩`.
-/
theorem IsAwayUnit.one (m : ℕ) : IsAwayUnit m (1 : K) :=
  ⟨1, 0, 0, by simp, by simp⟩

omit [NumberField K] [StarRing K] in

/- English proof (translation)
Take `⟨a, k, j, ha, hx⟩` from `h`. Take `⟨a', k', j', ha', hx'⟩` from `h'`. Use `⟨a * a', k + k', j + j', by rw [pow_add]; exact mul_dvd_mul ha ha', ?_⟩` and prove the remaining obligations. Establish `: ((a * a' : 𝓞 K) : K) = (a : K) * (a' : K)` using `by simp`. Rewrite using `[this, ← hx, ← hx']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem IsAwayUnit.mul {m : ℕ} {x x' : K} (h : IsAwayUnit m x) (h' : IsAwayUnit m x') : IsAwayUnit m (x * x') := by
  obtain ⟨a, k, j, ha, hx⟩ := h
  obtain ⟨a', k', j', ha', hx'⟩ := h'
  refine ⟨a * a', k + k', j + j', by rw [pow_add]; exact mul_dvd_mul ha ha', ?_⟩
  have : ((a * a' : 𝓞 K) : K) = (a : K) * (a' : K) := by simp
  rw [this, ← hx, ← hx']
  ring

omit [StarRing K] in

/- English proof (translation)
Establish `ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0`. Rewrite using `[ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Introduce and unpack `rfl`. Conclude with `ha w.asIdeal.zero_mem`. Unfold `vw`.

Rewrite using `[← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]`. Assume the negation of the conclusion as `h`. Establish `h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0`. Introduce `h0`. Conclude with `h (by rw [h0]; rfl)`.

Conclude with `ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))`.
-/
theorem vw_eq_zero_of_notMem (w : Pl K) {a : 𝓞 K} (ha : a ∉ w.asIdeal) : vw w (a : K) = 0 := by
  classical
  have ha0 : (Ideal.span {a} : Ideal (𝓞 K)) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    rintro rfl
    exact ha w.asIdeal.zero_mem
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ ha0]
  by_contra h
  have h' : (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors ≠ 0 := by
    intro h0
    exact h (by rw [h0]; rfl)
  exact ha (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd ha0 w.irreducible).1 h'))

/- English proof (translation)
Take `⟨a, k, k', ⟨b, hb⟩, hx⟩` from `h`. Establish `hpow : ∀ j : ℕ, (m : 𝓞 K) ^ j ∉ w.asIdeal` using `fun j hj => hm (w.isPrime.mem_of_pow_mem j hj)`. Establish `ha : a ∉ w.asIdeal` using `fun h => hpow k' (hb ▸ w.asIdeal.mul_mem_right b h)`. Establish `ha0 : (a : K) ≠ 0`. Introduce `h`.

Establish `: a = 0` using `by exact_mod_cast h`. Conclude with `ha (this ▸ w.asIdeal.zero_mem)`. Establish `hx0 : x ≠ 0` using `by rintro rfl; rw [zero_mul] at hx; exact ha0 hx.symm`. Establish `hk0 : (m : K) ^ k ≠ 0` using `by intro h; rw [h, mul_zero] at hx; exact ha0 hx.symm`. Use `⟨hx0, ?_⟩` and prove the remaining obligations.

Establish `h1` using `Formalism.DivisionValues.ValuationRepresentative.vw_mul w x _ hx0 hk0`. Establish `h2` using `vw_eq_zero_of_notMem w ha`. Establish `h3` using `vw_eq_zero_of_notMem w (hpow k)`. Establish `h4 : ((((m : 𝓞 K) ^ k : 𝓞 K)) : K) = (m : K) ^ k` using `by simp`. Rewrite `h3` using `[h4]`.

Rewrite `h1` using `[hx, h2, h3]`. Use linear arithmetic over natural numbers and integers.
-/
theorem IsAwayUnit.ne_zero_and_vw {m : ℕ} {x : K} (h : IsAwayUnit m x) (w : Pl K) (hm : (m : 𝓞 K) ∉ w.asIdeal) :
    x ≠ 0 ∧ vw w x = 0 := by
  obtain ⟨a, k, k', ⟨b, hb⟩, hx⟩ := h
  have hpow : ∀ j : ℕ, (m : 𝓞 K) ^ j ∉ w.asIdeal := fun j hj => hm (w.isPrime.mem_of_pow_mem j hj)
  have ha : a ∉ w.asIdeal := fun h => hpow k' (hb ▸ w.asIdeal.mul_mem_right b h)
  have ha0 : (a : K) ≠ 0 := by
    intro h
    have : a = 0 := by exact_mod_cast h
    exact ha (this ▸ w.asIdeal.zero_mem)
  have hx0 : x ≠ 0 := by rintro rfl; rw [zero_mul] at hx; exact ha0 hx.symm
  have hk0 : (m : K) ^ k ≠ 0 := by intro h; rw [h, mul_zero] at hx; exact ha0 hx.symm
  refine ⟨hx0, ?_⟩
  have h1 := Formalism.DivisionValues.ValuationRepresentative.vw_mul w x _ hx0 hk0
  have h2 := vw_eq_zero_of_notMem w ha
  have h3 := vw_eq_zero_of_notMem w (hpow k)
  have h4 : ((((m : 𝓞 K) ^ k : 𝓞 K)) : K) = (m : K) ^ k := by simp
  rw [h4] at h3
  rw [hx, h2, h3] at h1
  omega

omit [NumberField K] in

/- English proof (translation)
Simplify using `only [normAlg, Finset.mul_sum, star_mul']`. Use `Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normAlg_mul {κ X : Type} [Fintype κ] [Fintype X] (G : κ → κ → K) (gam : X → ℕ) (z : X → κ → K) (t : K) :
    normAlg G gam (fun x k => t * z x k) = t * star t * normAlg G gam z := by
  simp only [normAlg, Finset.mul_sum, star_mul']
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/- English proof (translation)
Establish `he` using `hS.e0_eq`. Establish `hle` using `hS.sqrt_error_le_half`. Establish `hc0 : a.c0 ≠ 0`. Introduce `h0`. Establish `hz : ∀ x k, Z.z x k = 0`.

Introduce `x k`. Use `h.bottom x k` as an intermediate fact. Rewrite `this` using `[h0, zero_mul, mul_eq_zero]`. Break down `this with h1 | h1` into its components or cases. Conclude with `(map_eq_zero σ₀).1 h1`.

Conclude with `absurd h1 hS.Om_ne`. Establish `hn` using `h.norm_eq`. Establish `: normAlg S.G Z.gam Z.z = 0` using `by simp [normAlg, hz]`. Rewrite `hn` using `[this, map_zero, zero_mul]`. Use `mul_ne_zero hS.A_ne (Finset.prod_ne_zero_iff.2 fun s hs => ?_) hn.symm` and prove the remaining obligations.

Rewrite `hs` using `[Finset.mem_Icc]`. Conclude with `h.L_ne s hs.1 (by omega)`. Use `⟨hc0, fun h0 => ?_⟩` and prove the remaining obligations. Establish `ht` using `h.tower`. Rewrite `ht` using `[h0, zero_mul]`.

Use `mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => h.u_ne i) hc0) (Finset.prod_ne_zero_iff.2 fun k hk => ?_) ht.symm` and prove the remaining obligations. Rewrite `hk` using `[Finset.mem_range]`. Conclude with `h.L_ne _ (by omega) (by omega)`.
-/
theorem Sq.Tuple.tuple_constants_ne_zero {S : Sq K} {hd y : ℕ} {σ₀ : K →+* ℂ} {a : An (S.p + S.q)} {Z : Co K S.κ} {w : Pl K}
    {dl : ℝ} (h : S.Tuple σ₀ a Z w dl) (hS : S.OK hd y) : a.c0 ≠ 0 ∧ a.c ≠ 0 := by
  have he := hS.e0_eq
  have hle := hS.sqrt_error_le_half
  have hc0 : a.c0 ≠ 0 := by
    intro h0
    have hz : ∀ x k, Z.z x k = 0 := by
      intro x k
      have := h.bottom x k
      rw [h0, zero_mul, mul_eq_zero] at this
      rcases this with h1 | h1
      · exact (map_eq_zero σ₀).1 h1
      · exact absurd h1 hS.Om_ne
    have hn := h.norm_eq
    have : normAlg S.G Z.gam Z.z = 0 := by simp [normAlg, hz]
    rw [this, map_zero, zero_mul] at hn
    refine mul_ne_zero hS.A_ne (Finset.prod_ne_zero_iff.2 fun s hs => ?_) hn.symm
    rw [Finset.mem_Icc] at hs
    exact h.L_ne s hs.1 (by omega)
  refine ⟨hc0, fun h0 => ?_⟩
  have ht := h.tower
  rw [h0, zero_mul] at ht
  refine mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => h.u_ne i) hc0)
    (Finset.prod_ne_zero_iff.2 fun k hk => ?_) ht.symm
  rw [Finset.mem_range] at hk
  exact h.L_ne _ (by omega) (by omega)

/- English proof (translation)
Take `⟨a, _, _, _, _, _, rfl, _, h1, _⟩` from `h`. Conclude with `(h1.tuple_constants_ne_zero hS).2`.
-/
theorem Sq.Twisted.ne_zero {S : Sq K} {hd y : ℕ} {σ₀ : K →+* ℂ} {w : Pl K} {cw : ℂ} {zA zA' : K}
    {zT zTd : ℤ → K} {gT : ℤ → ℤ} {n0 : ℤ → ℝ} {er dl : ℝ} {T : Type} {S0 : Finset T} {cc qq : T → ℕ}
    (h : S.Twisted σ₀ w cw zA zA' zT zTd gT n0 er dl S0 cc qq) (hS : S.OK hd y) : cw ≠ 0 := by
  obtain ⟨a, _, _, _, _, _, rfl, _, h1, _⟩ := h
  exact (h1.tuple_constants_ne_zero hS).2

namespace TwoStep

/- English proof (translation)
Establish `: 0 ≤ vw w (n : K)` using `by simpa using Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)`. Conclude with `this` after adjusting the coercions.
-/
theorem vw_natCast_nonneg (w : Pl K) (n : ℕ) : (0 : ℝ) ≤ (vw w (n : K) : ℝ) := by
  have : 0 ≤ vw w (n : K) := by simpa using Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w (n : 𝓞 K)
  exact_mod_cast this

def square (K : Type) [Field K] : Sq K where
  κ := Unit
  G := fun _ _ => 1
  Om := Complex.I
  Om' := 1
  A := 1
  e := 1
  p := 1
  q := 1
  e0 := 1
  h0 := 1
  base := ⟨Complex.I, Complex.I, fun _ => 1, fun _ => 1⟩

omit [NumberField K] [StarRing K] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, le_rfl, rfl, rfl, Complex.I_ne_zero, one_ne_zero, one_ne_zero, Complex.I_ne_zero⟩`.
-/
theorem square_ok : (square K).OK 3 2 :=
  ⟨rfl, le_rfl, rfl, rfl, Complex.I_ne_zero, one_ne_zero, one_ne_zero, Complex.I_ne_zero⟩

def coords (K : Type) [Field K] (t : ℕ) : Co K Unit where
  X := Fin 2
  gam := fun _ => 2
  z := fun _ _ => t
  z' := fun _ _ => 1

def numbers (n m Q : ℕ) : An 2 :=
  ⟨(n ^ 2 * m * Q : ℕ) * Complex.I, (m * Q : ℕ) * Complex.I, fun _ => n, fun s => if s = 0 then (Q ^ 2 * m : ℕ) else m⟩

/- English proof (translation)
Use `show (∑ _x : Fin 2, ((2 : ℕ) : K)⁻¹ * ∑ _k : Unit, ∑ _l : Unit, (t : K) * star (t : K) * 1) = _`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normAlg_coords (t : ℕ) : normAlg (square K).G (coords K t).gam (coords K t).z = (t : K) ^ 2 := by
  show (∑ _x : Fin 2, ((2 : ℕ) : K)⁻¹ * ∑ _k : Unit, ∑ _l : Unit, (t : K) * star (t : K) * 1) = _
  simp; ring

/- English proof (translation)
Use `show (∑ _x : Fin 2, ((2 : ℕ) : K)⁻¹ * ∑ _k : Unit, ∑ _l : Unit, (1 : K) * star (1 : K) * 1) = _`. Simplify using the standard rewrite rules.
-/
theorem normAlg_coords' (t : ℕ) : normAlg (square K).G (coords K t).gam (coords K t).z' = 1 := by
  show (∑ _x : Fin 2, ((2 : ℕ) : K)⁻¹ * ∑ _k : Unit, ∑ _l : Unit, (1 : K) * star (1 : K) * 1) = _
  simp

/- English proof (translation)
Establish `h2` using `vw_natCast_nonneg w 2`. Establish `hnat : ∀ (v : Pl K) (t : ℕ), -(vw w ((2 : ℕ) : K) : ℝ) ≤ (vw v (t : K) : ℝ)` using `fun v t => by`. Use `vw_natCast_nonneg v t` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show _ = (∏ _i : Fin 2, (n : ℂ)) * _ * _`. Rewrite using `[Fin.prod_univ_two]`. Simplify using `[square, numbers]`. Use `left`. Expand and normalize the polynomial expressions, which then agree.

Introduce `x k`. Simplify using `[square, numbers, coords]`. Rewrite using `[normAlg_coords]`. Establish `: Icc (1 - ((square K).e0 : ℤ)) ((square K).h0 : ℤ) = {0, 1}` using `by simp only [square]; decide`. Rewrite using `[this]`.

Simplify using `[square, numbers]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[normAlg_coords']`. Conclude with `one_ne_zero`. Introduce `s _ _`.

Simplify using `only [numbers]`. Apply the tactic sequence `split_ifs <;> simp [hm, hQ]`. Introduce `i`. Simplify using `[numbers, hn]`. Introduce `x`.

Simplify using `[coords]`. Introduce `x k`. Conclude with `⟨hnat _ _, hnat _ _⟩`. Introduce `x k; exact ⟨by simpa [coords] using hnat w 1, by simpa [coords] using hnat (conjPl w) 1⟩`. Introduce `x k l show _ ≤ (vw w ((1 : K) / ((2 : ℕ) : K)) : ℝ)`.

Rewrite using `[one_div, Formalism.DivisionValues.ValuationRepresentative.vw_inv]`. Simplify using the standard rewrite rules.
-/
theorem tuple (σ₀ : K →+* ℂ) (w : Pl K) {n m Q : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hQ : Q ≠ 0) :
    (square K).Tuple σ₀ (numbers n m Q) (coords K (m * Q)) w (vw w ((2 : ℕ) : K) : ℝ) := by
  have h2 := vw_natCast_nonneg w 2
  have hnat : ∀ (v : Pl K) (t : ℕ), -(vw w ((2 : ℕ) : K) : ℝ) ≤ (vw v (t : K) : ℝ) := fun v t => by
    have := vw_natCast_nonneg v t
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show _ = (∏ _i : Fin 2, (n : ℂ)) * _ * _
    rw [Fin.prod_univ_two]
    simp [square, numbers]; left; ring
  · intro x k; simp [square, numbers, coords]
  · rw [normAlg_coords]
    have : Icc (1 - ((square K).e0 : ℤ)) ((square K).h0 : ℤ) = {0, 1} := by simp only [square]; decide
    rw [this]
    simp [square, numbers]; ring
  · rw [normAlg_coords']; exact one_ne_zero
  · intro s _ _
    simp only [numbers]
    split_ifs <;> simp [hm, hQ]
  · intro i; simp [numbers, hn]
  · intro x; simp [coords]
  · intro x k; exact ⟨hnat _ _, hnat _ _⟩
  · intro x k; exact ⟨by simpa [coords] using hnat w 1, by simpa [coords] using hnat (conjPl w) 1⟩
  · intro x k l
    show _ ≤ (vw w ((1 : K) / ((2 : ℕ) : K)) : ℝ)
    rw [one_div, Formalism.DivisionValues.ValuationRepresentative.vw_inv]; simp

omit [NumberField K] [StarRing K] in

/- English proof (translation)
Simplify using `[numbers, square]`.
-/
theorem numbers_one : numbers 1 1 1 = (square K).base := by
  simp [numbers, square]

/- English proof (translation)
Establish `hQ0 : Q ≠ 0` using `by rintro rfl; exact hQ (by simp)`. Use `⟨numbers n m Q, coords K (1 * 1), coords K (m * Q), fun _ => m, fun _ => (Q : K) ^ 2, Q, ?_, ?_, tuple σ₀ w hn hm hQ0, ?_, normAlg_coords' _, hQ, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[numbers, square]`. Use `tuple σ₀ w one_ne_zero one_ne_zero one_ne_zero` as an intermediate fact. Rewrite `this` using `[numbers_one (K := K)]`. Then use the resulting hypothesis.

Rewrite using `[normAlg_coords]`. Simplify using the standard rewrite rules. Introduce `s h1 _`. Establish `hs : s ≠ 0` using `by omega`. Use `⟨one_ne_zero, Nat.cast_ne_zero.2 hd, by simp [numbers, square, hs], ?_, her⟩` and prove the remaining obligations.

Simplify using `using vw_natCast_nonneg w m`. Introduce `s h1 h2`. Establish `hs : s = 0` using `by simp only [square] at h1; omega`. Substitute `hs` using the available equality. Conclude with `⟨⟨(Q : 𝓞 K) ^ 2, 0, 2, dvd_rfl, by simp⟩, by simp [numbers, square]⟩`.

Introduce `i`. Conclude with `⟨1, fun _ => n, fun _ => 1, IsAwayUnit.one Q, by simp, by simp [numbers, square]⟩`.
-/
theorem twisted (σ₀ : K →+* ℂ) (w : Pl K) {n m d Q : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hd : d ≠ 0)
    (hQ : (Q : 𝓞 K) ∉ w.asIdeal) {er : ℝ} (her : (vw w (m : K) : ℝ) ≤ (vw w (d : K) : ℝ) + er) :
    (square K).Twisted σ₀ w (σ₀ ((n ^ 2 * m * Q : ℕ) : K) * (square K).base.c) 1 1 (fun _ => 1) (fun _ => d) (fun _ => 0)
      (fun _ => 0) er (vw w ((2 : ℕ) : K) : ℝ) (univ : Finset Unit) (fun _ => 1) (fun _ => n) := by
  have hQ0 : Q ≠ 0 := by rintro rfl; exact hQ (by simp)
  refine ⟨numbers n m Q, coords K (1 * 1), coords K (m * Q), fun _ => m, fun _ => (Q : K) ^ 2, Q, ?_, ?_,
    tuple σ₀ w hn hm hQ0, ?_, normAlg_coords' _, hQ, ?_, ?_, ?_⟩
  · simp [numbers, square]
  · have := tuple σ₀ w one_ne_zero one_ne_zero one_ne_zero
    rwa [numbers_one (K := K)] at this
  · rw [normAlg_coords]; simp
  · intro s h1 _
    have hs : s ≠ 0 := by omega
    refine ⟨one_ne_zero, Nat.cast_ne_zero.2 hd, by simp [numbers, square, hs], ?_, her⟩
    simpa using vw_natCast_nonneg w m
  · intro s h1 h2
    have hs : s = 0 := by simp only [square] at h1; omega
    subst hs
    exact ⟨⟨(Q : 𝓞 K) ^ 2, 0, 2, dvd_rfl, by simp⟩, by simp [numbers, square]⟩
  · intro i
    exact ⟨1, fun _ => n, fun _ => 1, IsAwayUnit.one Q, by simp, by simp [numbers, square]⟩

/- English proof (translation)
Establish `h1 : ((1 : ℕ) : 𝓞 K) ∉ w.asIdeal` using `by simpa using (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top`. Establish `h` using `twisted σ₀ w (n := 2) (m := 3) (d := 3) (Q := 1) (er := 0) (by norm_num) (by norm_num) (by norm_num) h1 (by simp)`. Establish `h12 : σ₀ ((2 ^ 2 * 3 * 1 : ℕ) : K) = 12` using `by rw [map_natCast]; norm_num`. Rewrite `h` using `[h12]`. Use `⟨square K, _, _, square_ok, vw_natCast_nonneg w 2, rfl, ?_, by simpa using h⟩` and prove the remaining obligations.

Introduce `h'`. Establish `h0 : (11 : ℂ) * (square K).base.c = 0` using `by linear_combination h'`. Conclude with `mul_ne_zero (by norm_num) (square_ok (K := K)).c_ne h0`.
-/
theorem exists_twisted_ne_base (σ₀ : K →+* ℂ) (w : Pl K) :
    ∃ (S : Sq K) (cw : ℂ) (dl : ℝ), S.OK 3 2 ∧ 0 ≤ dl ∧ cw = 12 * S.base.c ∧ cw ≠ S.base.c ∧
      S.Twisted σ₀ w cw 1 1 (fun _ => 1) (fun _ => 3) (fun _ => 0) (fun _ => 0) 0 dl (univ : Finset Unit) (fun _ => 1)
        (fun _ => 2) := by
  have h1 : ((1 : ℕ) : 𝓞 K) ∉ w.asIdeal := by simpa using (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  have h := twisted σ₀ w (n := 2) (m := 3) (d := 3) (Q := 1) (er := 0) (by norm_num) (by norm_num) (by norm_num) h1 (by simp)
  have h12 : σ₀ ((2 ^ 2 * 3 * 1 : ℕ) : K) = 12 := by rw [map_natCast]; norm_num
  rw [h12] at h
  refine ⟨square K, _, _, square_ok, vw_natCast_nonneg w 2, rfl, ?_, by simpa using h⟩
  intro h'
  have h0 : (11 : ℂ) * (square K).base.c = 0 := by linear_combination h'
  exact mul_ne_zero (by norm_num) (square_ok (K := K)).c_ne h0

end TwoStep

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 1, 0, by simp, by norm_num⟩`.
-/
example : IsAwayUnit 2 (1 / 2 : ℚ) := ⟨1, 1, 0, by simp, by norm_num⟩

/- English proof (translation)
Simplify using `[normAlg, Fin.sum_univ_two]`.
-/
example (s t : K) : normAlg (κ := Fin 2) (X := Unit) ![![0, 1], ![0, 0]] (fun _ => 1) (fun _ => ![s, t]) = s * star t := by
  simp [normAlg, Fin.sum_univ_two]

end GlobalTheory.Square
