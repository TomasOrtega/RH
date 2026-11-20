import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZeroStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.PrimInv

variable {Ω : Type} [Field Ω]

def IntS (A : ValuationSubring Ω) (Y : HahnSeries ℚ Ω) : Prop := ∀ r, Y.coeff r ∈ A

def LatS (L : ℕ) (Y : HahnSeries ℚ Ω) : Prop := ∀ r, Y.coeff r ≠ 0 → ∃ k : ℤ, r * L = k

def DivS (A : ValuationSubring Ω) (c : Ω) (Y : HahnSeries ℚ Ω) : Prop := ∀ r, ∃ z ∈ A, Y.coeff r = c * z

/- English proof (translation)
Rewrite using `[HahnSeries.coeff_mul]`. Conclude with `Finset.sum_induction _ s hadd h0 (fun ij _ => hm _ _ (hY _) (hZ _))`.
-/
theorem coeff_mul_of (Y Z : HahnSeries ℚ Ω) (p q s : Ω → Prop) (h0 : s 0)
    (hadd : ∀ a b, s a → s b → s (a + b)) (hY : ∀ r, p (Y.coeff r)) (hZ : ∀ r, q (Z.coeff r))
    (hm : ∀ a b, p a → q b → s (a * b)) (r : ℚ) : s ((Y * Z).coeff r) := by
  rw [HahnSeries.coeff_mul]
  exact Finset.sum_induction _ s hadd h0 (fun ij _ => hm _ _ (hY _) (hZ _))

section Int
variable {A : ValuationSubring Ω}

/- English proof (translation)
The claim follows from `coeff_mul_of Y Z (· ∈ A) (· ∈ A) (· ∈ A) (zero_mem A) (fun _ _ => add_mem) hY hZ (fun _ _ => mul_mem)`.
-/
theorem intS_mul {Y Z : HahnSeries ℚ Ω} (hY : IntS A Y) (hZ : IntS A Z) : IntS A (Y * Z) :=
  coeff_mul_of Y Z (· ∈ A) (· ∈ A) (· ∈ A) (zero_mem A) (fun _ _ => add_mem) hY hZ (fun _ _ => mul_mem)

/- English proof (translation)
Introduce `r`. Simplify using `using add_mem (hY r) (hZ r)`.
-/
theorem intS_add {Y Z : HahnSeries ℚ Ω} (hY : IntS A Y) (hZ : IntS A Z) : IntS A (Y + Z) := by
  intro r; simpa using add_mem (hY r) (hZ r)

/- English proof (translation)
Introduce `r`. Simplify using `using neg_mem (hY r)`.
-/
theorem intS_neg {Y : HahnSeries ℚ Ω} (hY : IntS A Y) : IntS A (-Y) := by
  intro r; simpa using neg_mem (hY r)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `intS_add hY (intS_neg hZ)`.
-/
theorem intS_sub {Y Z : HahnSeries ℚ Ω} (hY : IntS A Y) (hZ : IntS A Z) : IntS A (Y - Z) := by
  rw [sub_eq_add_neg]; exact intS_add hY (intS_neg hZ)

/- English proof (translation)
Introduce `r`. Rewrite using `[HahnSeries.coeff_one]`. Use `split_ifs`. Conclude with `one_mem A`. Conclude with `zero_mem A`.
-/
theorem intS_one : IntS A (1 : HahnSeries ℚ Ω) := by
  intro r; rw [HahnSeries.coeff_one]; split_ifs
  · exact one_mem A
  · exact zero_mem A

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `intS_one`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `intS_mul ih hY`.
-/
theorem intS_pow {Y : HahnSeries ℚ Ω} (hY : IntS A Y) (k : ℕ) : IntS A (Y ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact intS_one
  | succ k ih => rw [pow_succ]; exact intS_mul ih hY

/- English proof (translation)
Introduce `r`. Distinguish the cases in `h : r = a`. Substitute `h` using the available equality. Simplify using `using hc`. Rewrite using `[HahnSeries.coeff_single_of_ne h]`.

Conclude with `zero_mem A`.
-/
theorem intS_single {a : ℚ} {c : Ω} (hc : c ∈ A) : IntS A (HahnSeries.single a c) := by
  intro r
  by_cases h : r = a
  · subst h; simpa using hc
  · rw [HahnSeries.coeff_single_of_ne h]; exact zero_mem A

/- English proof (translation)
Introduce `r`. Rewrite using `[HahnSeries.coeff_sum]`. Conclude with `Finset.sum_induction _ (· ∈ A) (fun _ _ => add_mem) (zero_mem A) (fun i _ => h i r)`.
-/
theorem intS_sum {s : Finset ℕ} {f : ℕ → HahnSeries ℚ Ω} (h : ∀ i, IntS A (f i)) : IntS A (∑ i ∈ s, f i) := by
  intro r
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_induction _ (· ∈ A) (fun _ _ => add_mem) (zero_mem A) (fun i _ => h i r)

/- English proof (translation)
Introduce `r`. Rewrite using `[HahnSeries.SummableFamily.coeff_hsum_eq_sum]`. Conclude with `Finset.sum_induction _ (· ∈ A) (fun _ _ => add_mem) (zero_mem A) (fun k _ => by`. Rewrite using `[HahnSeries.SummableFamily.powers_of_orderTop_pos hX]`. Conclude with `intS_pow h k r)`.
-/
theorem intS_hsum {X : HahnSeries ℚ Ω} (hX : 0 < X.orderTop) (h : IntS A X) :
    IntS A (HahnSeries.SummableFamily.powers X).hsum := by
  intro r
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum]
  exact Finset.sum_induction _ (· ∈ A) (fun _ _ => add_mem) (zero_mem A) (fun k _ => by
    rw [HahnSeries.SummableFamily.powers_of_orderTop_pos hX]; exact intS_pow h k r)

end Int

section Lat
variable {L : ℕ}

/- English proof (translation)
Introduce `r hr`. Rewrite `hr` using `[HahnSeries.coeff_mul]`. Take `⟨ij, hij, -⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hr`. Rewrite `hij` using `[Finset.mem_addAntidiagonal]`. Take `⟨h1, h2, h3⟩` from `hij`.

Take `⟨a, ha⟩` from `hY _ ((HahnSeries.mem_support _ _).1 h1)`. Take `⟨b, hb⟩` from `hZ _ ((HahnSeries.mem_support _ _).1 h2)`. Conclude with `⟨a + b, by rw [← h3, add_mul, ha, hb]; push_cast; ring⟩`.
-/
theorem latS_mul {Y Z : HahnSeries ℚ Ω} (hY : LatS L Y) (hZ : LatS L Z) : LatS L (Y * Z) := by
  intro r hr
  rw [HahnSeries.coeff_mul] at hr
  obtain ⟨ij, hij, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  rw [Finset.mem_addAntidiagonal] at hij
  obtain ⟨h1, h2, h3⟩ := hij
  obtain ⟨a, ha⟩ := hY _ ((HahnSeries.mem_support _ _).1 h1)
  obtain ⟨b, hb⟩ := hZ _ ((HahnSeries.mem_support _ _).1 h2)
  exact ⟨a + b, by rw [← h3, add_mul, ha, hb]; push_cast; ring⟩

/- English proof (translation)
Introduce `r hr`. Distinguish the cases in `h : Y.coeff r = 0`. Conclude with `hZ r (by simpa [h] using hr)`. Conclude with `hY r h`.
-/
theorem latS_add {Y Z : HahnSeries ℚ Ω} (hY : LatS L Y) (hZ : LatS L Z) : LatS L (Y + Z) := by
  intro r hr
  by_cases h : Y.coeff r = 0
  · exact hZ r (by simpa [h] using hr)
  · exact hY r h

/- English proof (translation)
Introduce `r hr; exact hY r (by simpa using hr)`.
-/
theorem latS_neg {Y : HahnSeries ℚ Ω} (hY : LatS L Y) : LatS L (-Y) := by
  intro r hr; exact hY r (by simpa using hr)

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `latS_add hY (latS_neg hZ)`.
-/
theorem latS_sub {Y Z : HahnSeries ℚ Ω} (hY : LatS L Y) (hZ : LatS L Z) : LatS L (Y - Z) := by
  rw [sub_eq_add_neg]; exact latS_add hY (latS_neg hZ)

/- English proof (translation)
Introduce `r hr`. Simplify using `at hr`.
-/
theorem latS_zero : LatS L (0 : HahnSeries ℚ Ω) := by
  intro r hr; simp at hr

/- English proof (translation)
Introduce `r hr`. Rewrite `hr` using `[HahnSeries.coeff_one]`. Use `split_ifs at hr with h`. Conclude with `⟨0, by simp [h]⟩`. Conclude with `absurd rfl hr`.
-/
theorem latS_one : LatS L (1 : HahnSeries ℚ Ω) := by
  intro r hr
  rw [HahnSeries.coeff_one] at hr
  split_ifs at hr with h
  · exact ⟨0, by simp [h]⟩
  · exact absurd rfl hr

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [pow_zero]`. Conclude with `latS_one`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `latS_mul ih hY`.
-/
theorem latS_pow {Y : HahnSeries ℚ Ω} (hY : LatS L Y) (k : ℕ) : LatS L (Y ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact latS_one
  | succ k ih => rw [pow_succ]; exact latS_mul ih hY

/- English proof (translation)
Introduce `r hr`. Distinguish the cases in `h : r = a`. Substitute `h` using the available equality. Conclude with `ha`. Rewrite `hr` using `[HahnSeries.coeff_single_of_ne h]`.

Conclude with `absurd rfl hr`.
-/
theorem latS_single {a : ℚ} {c : Ω} (ha : ∃ k : ℤ, a * L = k) : LatS L (HahnSeries.single a c) := by
  intro r hr
  by_cases h : r = a
  · subst h; exact ha
  · rw [HahnSeries.coeff_single_of_ne h] at hr; exact absurd rfl hr

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (LatS L) (fun _ _ => latS_add) latS_zero (fun i _ => h i)`.
-/
theorem latS_sum {s : Finset ℕ} {f : ℕ → HahnSeries ℚ Ω} (h : ∀ i, LatS L (f i)) : LatS L (∑ i ∈ s, f i) :=
  Finset.sum_induction _ (LatS L) (fun _ _ => latS_add) latS_zero (fun i _ => h i)

/- English proof (translation)
Introduce `r hr`. Rewrite `hr` using `[HahnSeries.SummableFamily.coeff_hsum_eq_sum]`. Take `⟨k, -, hk⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hr`. Rewrite `hk` using `[HahnSeries.SummableFamily.powers_of_orderTop_pos hX]`. Conclude with `latS_pow h k r hk`.
-/
theorem latS_hsum {X : HahnSeries ℚ Ω} (hX : 0 < X.orderTop) (h : LatS L X) :
    LatS L (HahnSeries.SummableFamily.powers X).hsum := by
  intro r hr
  rw [HahnSeries.SummableFamily.coeff_hsum_eq_sum] at hr
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  rw [HahnSeries.SummableFamily.powers_of_orderTop_pos hX] at hk
  exact latS_pow h k r hk

end Lat

section Div
variable {A : ValuationSubring Ω}

/- English proof (translation)
The claim follows from `coeff_mul_of Y Z (fun a => ∃ z ∈ A, a = c * z) (· ∈ A) (fun a => ∃ z ∈ A, a = c * z) ⟨0, zero_mem A, by simp⟩ (fun _ _ ⟨z, hz, e⟩ ⟨w, hw, f⟩ => ⟨z + w, add_mem hz hw, by rw [e, f]; ring⟩) hY hZ (fun _ b ⟨z, hz, e⟩ hb => ⟨z * b, mul_mem hz hb, by rw [e]; ring⟩)`.
-/
theorem divS_mul_int {c : Ω} {Y Z : HahnSeries ℚ Ω} (hY : DivS A c Y) (hZ : IntS A Z) : DivS A c (Y * Z) :=
  coeff_mul_of Y Z (fun a => ∃ z ∈ A, a = c * z) (· ∈ A) (fun a => ∃ z ∈ A, a = c * z)
    ⟨0, zero_mem A, by simp⟩ (fun _ _ ⟨z, hz, e⟩ ⟨w, hw, f⟩ => ⟨z + w, add_mem hz hw, by rw [e, f]; ring⟩)
    hY hZ (fun _ b ⟨z, hz, e⟩ hb => ⟨z * b, mul_mem hz hb, by rw [e]; ring⟩)

/- English proof (translation)
The claim follows from `coeff_mul_of Y Z (fun a => ∃ z ∈ A, a = c * z) (fun a => ∃ z ∈ A, a = d * z) (fun a => ∃ z ∈ A, a = c * d * z) ⟨0, zero_mem A, by simp⟩ (fun _ _ ⟨z, hz, e⟩ ⟨w, hw, f⟩ => ⟨z + w, add_mem hz hw, by rw [e, f]; ring⟩) hY hZ (fun _ _ ⟨z, hz, e⟩ ⟨w, hw, f⟩ => ⟨z * w, mul_mem hz hw, by …`.
-/
theorem divS_mul {c d : Ω} {Y Z : HahnSeries ℚ Ω} (hY : DivS A c Y) (hZ : DivS A d Z) : DivS A (c * d) (Y * Z) :=
  coeff_mul_of Y Z (fun a => ∃ z ∈ A, a = c * z) (fun a => ∃ z ∈ A, a = d * z) (fun a => ∃ z ∈ A, a = c * d * z)
    ⟨0, zero_mem A, by simp⟩ (fun _ _ ⟨z, hz, e⟩ ⟨w, hw, f⟩ => ⟨z + w, add_mem hz hw, by rw [e, f]; ring⟩)
    hY hZ (fun _ _ ⟨z, hz, e⟩ ⟨w, hw, f⟩ => ⟨z * w, mul_mem hz hw, by rw [e, f]; ring⟩)

/- English proof (translation)
Introduce `r`. Take `⟨z, hz, e⟩` from `hY r`. Conclude with `⟨-z, neg_mem hz, by simp [e]⟩`.
-/
theorem divS_neg {c : Ω} {Y : HahnSeries ℚ Ω} (hY : DivS A c Y) : DivS A c (-Y) := by
  intro r
  obtain ⟨z, hz, e⟩ := hY r
  exact ⟨-z, neg_mem hz, by simp [e]⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `r`. Conclude with `⟨(1 : HahnSeries ℚ Ω).coeff r, intS_one r, by simp⟩`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`.

Conclude with `divS_mul ih hY`.
-/
theorem divS_pow {c : Ω} {Y : HahnSeries ℚ Ω} (hY : DivS A c Y) (k : ℕ) : DivS A (c ^ k) (Y ^ k) := by
  induction k with
  | zero =>
    intro r
    exact ⟨(1 : HahnSeries ℚ Ω).coeff r, intS_one r, by simp⟩
  | succ k ih => rw [pow_succ, pow_succ]; exact divS_mul ih hY

end Div

/- English proof (translation)
Distinguish the cases in `hX : X = 0`. Simplify using `[hX]`. Take `⟨g, hg⟩` from `WithTop.ne_top_iff_exists.mp (HahnSeries.orderTop_ne_top.2 hX)`. Use `HahnSeries.coeff_orderTop_ne hg.symm` as an intermediate fact. Rewrite using `[← hg]`.

Conclude with `WithTop.coe_lt_coe.2 (lt_of_not_ge fun hle => this (h g hle))`.
-/
theorem pos_orderTop (X : HahnSeries ℚ Ω) (h : ∀ r ≤ 0, X.coeff r = 0) : 0 < X.orderTop := by
  by_cases hX : X = 0
  · simp [hX]
  · obtain ⟨g, hg⟩ := WithTop.ne_top_iff_exists.mp (HahnSeries.orderTop_ne_top.2 hX)
    have := HahnSeries.coeff_orderTop_ne hg.symm
    rw [← hg]
    exact WithTop.coe_lt_coe.2 (lt_of_not_ge fun hle => this (h g hle))

end GlobalTheory.PrimInv

namespace GlobalTheory.PrimInv

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `hLq : (L : ℚ) ≠ 0` using `Nat.cast_ne_zero.2 hL.ne'`. Use `set S : Set ℚ := {r | P.coeff r ≠ 0 ∧ (P.coeff r)⁻¹ ∈ A} with hSdef`. Establish `hSne : S.Nonempty` using `by obtain ⟨r, h1, h2⟩ := hP.2; exact ⟨r, h1, h2⟩`. Establish `hSwf : S.IsWF` using `P.isWF_support.mono (fun r hr => (HahnSeries.mem_support _ _).2 hr.1)`. Take `⟨i0, hi0, hmin⟩ : ∃ i0 ∈ S, ∀ r ∈ S, i0 ≤ r` from `⟨hSwf.min hSne, hSwf.min_mem hSne, fun r hr => hSwf.min_le hSne hr⟩`.

Take `⟨hu0, huinv⟩` from `hi0`. Use `set u := P.coeff i0 with hudef`. Establish `huA : u ∈ A` using `hP.1 i0`. Establish `hi0L : ∃ k : ℤ, -i0 * L = k`. Take `⟨k, hk⟩` from `hPL i0 hu0; exact ⟨-k, by rw [neg_mul, hk]; push_cast; ring⟩`.

Take `⟨P1, hP1e⟩ : ∃ P1 : HahnSeries ℚ Ω, P1 = HahnSeries.single (-i0) u⁻¹ * P` from `⟨_, rfl⟩`. Establish `hP1 : ∀ r, P1.coeff r = u⁻¹ * P.coeff (r + i0)`. Introduce `r`. Use `HahnSeries.coeff_single_mul_add (r := u⁻¹) (x := P) (a := r + i0) (b := -i0)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_right]`.

Rewrite using `[hP1e, this]`. Establish `hP1I : IntS A P1` using `by rw [hP1e]; exact intS_mul (intS_single huinv) hP.1`. Establish `hP1L : LatS L P1` using `by rw [hP1e]; exact latS_mul (latS_single hi0L) hPL`. Take `⟨N, hN⟩ : ∃ N : HahnSeries ℚ Ω, ∀ r, N.coeff r = if r < 0 then P1.coeff r else 0` from `⟨⟨fun r => if r < 0 then P1.coeff r else 0, P1.isPWO_support.mono (fun r hr => by`. Simplify using `only [Function.mem_support] at hr`.

Use `split_ifs at hr`. Conclude with `(HahnSeries.mem_support _ _).2 hr`. Conclude with `absurd rfl hr)⟩, fun r => rfl⟩`. Establish `hNI : IntS A N`. Introduce `r`.

Rewrite using `[hN]`. Use `split_ifs`. Conclude with `hP1I r`. Conclude with `zero_mem A`. Establish `hNL : LatS L N`.

Introduce `r hr`. Rewrite `hr` using `[hN]`. Use `split_ifs at hr`. Conclude with `hP1L r hr`. Conclude with `absurd rfl hr`.

Establish `hNneg : ∀ r, N.coeff r ≠ 0 → r < 0`. Introduce `r hr`. Rewrite `hr` using `[hN]`. Use `split_ifs at hr with h`. Conclude with `h`.

Conclude with `absurd rfl hr`. Establish `hNnon : ∀ r, N.coeff r ∈ A.nonunits`. Introduce `r`. Rewrite using `[hN]`. Use `split_ifs with h`.

Rewrite using `[hP1, ValuationSubring.mem_nonunits_iff_or]`. Distinguish the cases in `hc : P.coeff (r + i0) = 0`. Use `left`. Rewrite using `[hc, mul_zero]`. Use `right`.

Introduce `hinv`. Establish `: r + i0 ∈ S`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Establish `: (P.coeff (r + i0))⁻¹ = u⁻¹ * (u⁻¹ * P.coeff (r + i0))⁻¹`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `mul_mem huinv hinv`. Use `hmin _ this` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[ValuationSubring.mem_nonunits_iff_or]`.

Use `left`. Both sides reduce to the same expression. Establish `hF : N.support.Finite`. Break down `N.support.eq_empty_or_nonempty with h | h` into its components or cases. Rewrite using `[h]`.

Conclude with `Set.finite_empty`. Use `((Set.finite_Icc (⌊N.isWF_support.min h * L⌋) 0).image (fun k : ℤ => (k : ℚ) / L)).subset ?_` and prove the remaining obligations. Introduce `r hr`. Establish `hm` using `N.isWF_support.min_le h hr`. Establish `hr' : N.coeff r ≠ 0` using `(HahnSeries.mem_support _ _).1 hr`.

Establish `hrneg` using `hNneg r hr'`. Take `⟨k, hk⟩` from `hNL r hr'`. Use `⟨k, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `: ⌊N.isWF_support.min h * L⌋ ≤ ⌊r * L⌋` using `Int.floor_mono (mul_le_mul_of_nonneg_right hm (by positivity))`. Rewrite `this` using `[hk, Int.floor_intCast]`. Then use the resulting hypothesis.

Establish `: (k : ℚ) ≤ 0`. Rewrite using `[← hk]; exact mul_nonpos_of_nonpos_of_nonneg hrneg.le (by positivity)`. Conclude with `this` after adjusting the coercions. Use `show (k : ℚ) / L = r`. Rewrite using `[← hk]`.

Clear the denominators using the available nonvanishing facts. Establish `hx : ∃ x ∈ A.nonunits, DivS A x N`. Break down `hF.toFinset.eq_empty_or_nonempty with h | h` into its components or cases. Use `⟨0, by rw [ValuationSubring.mem_nonunits_iff_or]; left; rfl, fun r => ⟨0, zero_mem A, ?_⟩⟩` and prove the remaining obligations. Establish `: r ∉ N.support`.

Introduce `hr`. Use `(Set.Finite.mem_toFinset hF).2 hr` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`. Rewrite `this` using `[HahnSeries.mem_support, not_not]`.

Rewrite using `[this, mul_zero]`. Take `⟨r0, hr0, hmax⟩` from `Finset.exists_max_image _ (fun r => A.valuation (N.coeff r)) h`. Use `⟨N.coeff r0, hNnon r0, fun r => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hr : N.coeff r = 0`. Conclude with `⟨0, zero_mem A, by rw [hr, mul_zero]⟩`.

Establish `hr0' : N.coeff r0 ≠ 0` using `(HahnSeries.mem_support _ _).1 ((Set.Finite.mem_toFinset hF).1 hr0)`. Use `⟨N.coeff r / N.coeff r0, ?_, by field_simp⟩` and prove the remaining obligations. Rewrite using `[← ValuationSubring.valuation_le_one_iff, map_div₀]`. Establish `hle` using `hmax r ((Set.Finite.mem_toFinset hF).2 ((HahnSeries.mem_support _ _).2 hr))`. Establish `hpos : 0 < A.valuation (N.coeff r0)`.

Rewrite using `[zero_lt_iff]`. Conclude with `(map_ne_zero _).2 hr0'`. Conclude with `(div_le_one₀ hpos).2 hle`. Take `⟨x, hxn, hxN⟩` from `hx`. Take `⟨k, z, hz, hxk⟩` from `hnil x hxn`.

Take `⟨E, hEe⟩ : ∃ E : HahnSeries ℚ Ω, E = P1 - 1 - N` from `⟨_, rfl⟩`. Establish `hE0 : ∀ r ≤ 0, E.coeff r = 0`. Introduce `r hr`. Rewrite using `[hEe, HahnSeries.coeff_sub, HahnSeries.coeff_sub, hN, HahnSeries.coeff_one]`. Break down `hr.lt_or_eq with h | h` into its components or cases.

Rewrite using `[if_pos h, if_neg h.ne]`. Expand and normalize the polynomial expressions, which then agree. Substitute `h` using the available equality. Rewrite using `[if_neg (lt_irrefl _), if_pos rfl, hP1, zero_add, inv_mul_cancel₀ hu0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hEpos : 0 < (-E).orderTop` using `pos_orderTop _ (fun r hr => by simp [hE0 r hr])`. Establish `hEI : IntS A E` using `by rw [hEe]; exact intS_sub (intS_sub hP1I intS_one) hNI`. Establish `hEL : LatS L E` using `by rw [hEe]; exact latS_sub (latS_sub hP1L latS_one) hNL`. Take `⟨R, hRe⟩ : ∃ R : HahnSeries ℚ Ω, R = (HahnSeries.SummableFamily.powers (-E)).hsum` from `⟨_, rfl⟩`. Establish `hR : (1 + E) * R = 1`.

Use `HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers hEpos` as an intermediate fact. Rewrite `this` using `[sub_neg_eq_add, ← hRe]`. Then use the resulting hypothesis. Establish `hRI : IntS A R` using `by rw [hRe]; exact intS_hsum hEpos (intS_neg hEI)`. Establish `hRL : LatS L R` using `by rw [hRe]; exact latS_hsum hEpos (latS_neg hEL)`. Take `⟨G, hGe⟩ : ∃ G : HahnSeries ℚ Ω, G = ∑ j ∈ Finset.range (k * n), (-(N * R)) ^ j` from `⟨_, rfl⟩`.

Establish `hg : (1 - -(N * R)) * G = 1 - (-(N * R)) ^ (k * n)` using `by rw [hGe]; exact mul_neg_geom_sum _ _`. Establish `hGI : IntS A G` using `by rw [hGe]; exact intS_sum (fun j => intS_pow (intS_neg (intS_mul hNI hRI)) j)`. Establish `hGL : LatS L G` using `by rw [hGe]; exact latS_sum (fun j => latS_pow (latS_neg (latS_mul hNL hRL)) j)`. Use `⟨R * G * HahnSeries.single (-i0) u⁻¹, intS_mul (intS_mul hRI hGI) (intS_single huinv), latS_mul (latS_mul hRL hGL) (latS_single hi0L), ?_⟩` and prove the remaining obligations. Establish `hQP : R * G * HahnSeries.single (-i0) u⁻¹ * P - 1 = -(-(N * R)) ^ (k * n)`.

Establish `hP1' : P1 = 1 + E + N` using `by rw [hEe]; ring`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQP]`. Establish `hD : DivS A (x ^ (k * n)) (-(-(N * R)) ^ (k * n))` using `divS_neg (divS_pow (divS_neg (divS_mul_int hxN hRI)) _)`. Introduce `r`.

Take `⟨w, hw, e⟩` from `hD r`. Use `⟨z ^ n * w, mul_mem (pow_mem hz n) hw, ?_⟩` and prove the remaining obligations. Rewrite using `[e, pow_mul, hxk, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem core (A : ValuationSubring Ω) (c : Ω) (hnil : ∀ x ∈ A.nonunits, ∃ k : ℕ, ∃ z ∈ A, x ^ k = c * z)
    (L : ℕ) (hL : 0 < L) (P : HahnSeries ℚ Ω) (hP : Prim A P) (hPL : LatS L P) (n : ℕ) :
    ∃ Q : HahnSeries ℚ Ω, IntS A Q ∧ LatS L Q ∧ DivS A (c ^ n) (Q * P - 1) := by
  have hLq : (L : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hL.ne'

  set S : Set ℚ := {r | P.coeff r ≠ 0 ∧ (P.coeff r)⁻¹ ∈ A} with hSdef
  have hSne : S.Nonempty := by obtain ⟨r, h1, h2⟩ := hP.2; exact ⟨r, h1, h2⟩
  have hSwf : S.IsWF := P.isWF_support.mono (fun r hr => (HahnSeries.mem_support _ _).2 hr.1)
  obtain ⟨i0, hi0, hmin⟩ : ∃ i0 ∈ S, ∀ r ∈ S, i0 ≤ r :=
    ⟨hSwf.min hSne, hSwf.min_mem hSne, fun r hr => hSwf.min_le hSne hr⟩
  obtain ⟨hu0, huinv⟩ := hi0
  set u := P.coeff i0 with hudef
  have huA : u ∈ A := hP.1 i0
  have hi0L : ∃ k : ℤ, -i0 * L = k := by
    obtain ⟨k, hk⟩ := hPL i0 hu0; exact ⟨-k, by rw [neg_mul, hk]; push_cast; ring⟩

  obtain ⟨P1, hP1e⟩ : ∃ P1 : HahnSeries ℚ Ω, P1 = HahnSeries.single (-i0) u⁻¹ * P := ⟨_, rfl⟩
  have hP1 : ∀ r, P1.coeff r = u⁻¹ * P.coeff (r + i0) := by
    intro r
    have := HahnSeries.coeff_single_mul_add (r := u⁻¹) (x := P) (a := r + i0) (b := -i0)
    rw [add_neg_cancel_right] at this
    rw [hP1e, this]
  have hP1I : IntS A P1 := by rw [hP1e]; exact intS_mul (intS_single huinv) hP.1
  have hP1L : LatS L P1 := by rw [hP1e]; exact latS_mul (latS_single hi0L) hPL

  obtain ⟨N, hN⟩ : ∃ N : HahnSeries ℚ Ω, ∀ r, N.coeff r = if r < 0 then P1.coeff r else 0 :=
    ⟨⟨fun r => if r < 0 then P1.coeff r else 0, P1.isPWO_support.mono (fun r hr => by
      simp only [Function.mem_support] at hr
      split_ifs at hr
      · exact (HahnSeries.mem_support _ _).2 hr
      · exact absurd rfl hr)⟩, fun r => rfl⟩
  have hNI : IntS A N := by
    intro r; rw [hN]; split_ifs
    · exact hP1I r
    · exact zero_mem A
  have hNL : LatS L N := by
    intro r hr; rw [hN] at hr; split_ifs at hr
    · exact hP1L r hr
    · exact absurd rfl hr
  have hNneg : ∀ r, N.coeff r ≠ 0 → r < 0 := by
    intro r hr; rw [hN] at hr; split_ifs at hr with h
    · exact h
    · exact absurd rfl hr
  have hNnon : ∀ r, N.coeff r ∈ A.nonunits := by
    intro r
    rw [hN]; split_ifs with h
    · rw [hP1, ValuationSubring.mem_nonunits_iff_or]
      by_cases hc : P.coeff (r + i0) = 0
      · left; rw [hc, mul_zero]
      · right
        intro hinv
        have : r + i0 ∈ S := by
          refine ⟨hc, ?_⟩
          have : (P.coeff (r + i0))⁻¹ = u⁻¹ * (u⁻¹ * P.coeff (r + i0))⁻¹ := by
            field_simp
          rw [this]; exact mul_mem huinv hinv
        have := hmin _ this
        linarith
    · rw [ValuationSubring.mem_nonunits_iff_or]; left; rfl

  have hF : N.support.Finite := by
    rcases N.support.eq_empty_or_nonempty with h | h
    · rw [h]; exact Set.finite_empty
    · refine ((Set.finite_Icc (⌊N.isWF_support.min h * L⌋) 0).image (fun k : ℤ => (k : ℚ) / L)).subset ?_
      intro r hr
      have hm := N.isWF_support.min_le h hr
      have hr' : N.coeff r ≠ 0 := (HahnSeries.mem_support _ _).1 hr
      have hrneg := hNneg r hr'
      obtain ⟨k, hk⟩ := hNL r hr'
      refine ⟨k, ⟨?_, ?_⟩, ?_⟩
      · have : ⌊N.isWF_support.min h * L⌋ ≤ ⌊r * L⌋ :=
          Int.floor_mono (mul_le_mul_of_nonneg_right hm (by positivity))
        rwa [hk, Int.floor_intCast] at this
      · have : (k : ℚ) ≤ 0 := by
          rw [← hk]; exact mul_nonpos_of_nonpos_of_nonneg hrneg.le (by positivity)
        exact_mod_cast this
      · show (k : ℚ) / L = r
        rw [← hk]; field_simp
  have hx : ∃ x ∈ A.nonunits, DivS A x N := by
    rcases hF.toFinset.eq_empty_or_nonempty with h | h
    · refine ⟨0, by rw [ValuationSubring.mem_nonunits_iff_or]; left; rfl, fun r => ⟨0, zero_mem A, ?_⟩⟩
      have : r ∉ N.support := by
        intro hr; have := (Set.Finite.mem_toFinset hF).2 hr; rw [h] at this; simp at this
      rw [HahnSeries.mem_support, not_not] at this
      rw [this, mul_zero]
    · obtain ⟨r0, hr0, hmax⟩ := Finset.exists_max_image _ (fun r => A.valuation (N.coeff r)) h
      refine ⟨N.coeff r0, hNnon r0, fun r => ?_⟩
      by_cases hr : N.coeff r = 0
      · exact ⟨0, zero_mem A, by rw [hr, mul_zero]⟩
      · have hr0' : N.coeff r0 ≠ 0 := (HahnSeries.mem_support _ _).1 ((Set.Finite.mem_toFinset hF).1 hr0)
        refine ⟨N.coeff r / N.coeff r0, ?_, by field_simp⟩
        rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
        have hle := hmax r ((Set.Finite.mem_toFinset hF).2 ((HahnSeries.mem_support _ _).2 hr))
        have hpos : 0 < A.valuation (N.coeff r0) := by
          rw [zero_lt_iff]; exact (map_ne_zero _).2 hr0'
        exact (div_le_one₀ hpos).2 hle
  obtain ⟨x, hxn, hxN⟩ := hx
  obtain ⟨k, z, hz, hxk⟩ := hnil x hxn

  obtain ⟨E, hEe⟩ : ∃ E : HahnSeries ℚ Ω, E = P1 - 1 - N := ⟨_, rfl⟩
  have hE0 : ∀ r ≤ 0, E.coeff r = 0 := by
    intro r hr
    rw [hEe, HahnSeries.coeff_sub, HahnSeries.coeff_sub, hN, HahnSeries.coeff_one]
    rcases hr.lt_or_eq with h | h
    · rw [if_pos h, if_neg h.ne]; ring
    · subst h
      rw [if_neg (lt_irrefl _), if_pos rfl, hP1, zero_add, inv_mul_cancel₀ hu0]; ring
  have hEpos : 0 < (-E).orderTop := pos_orderTop _ (fun r hr => by simp [hE0 r hr])
  have hEI : IntS A E := by rw [hEe]; exact intS_sub (intS_sub hP1I intS_one) hNI
  have hEL : LatS L E := by rw [hEe]; exact latS_sub (latS_sub hP1L latS_one) hNL
  obtain ⟨R, hRe⟩ : ∃ R : HahnSeries ℚ Ω, R = (HahnSeries.SummableFamily.powers (-E)).hsum := ⟨_, rfl⟩
  have hR : (1 + E) * R = 1 := by
    have := HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers hEpos
    rwa [sub_neg_eq_add, ← hRe] at this
  have hRI : IntS A R := by rw [hRe]; exact intS_hsum hEpos (intS_neg hEI)
  have hRL : LatS L R := by rw [hRe]; exact latS_hsum hEpos (latS_neg hEL)
  obtain ⟨G, hGe⟩ : ∃ G : HahnSeries ℚ Ω, G = ∑ j ∈ Finset.range (k * n), (-(N * R)) ^ j := ⟨_, rfl⟩
  have hg : (1 - -(N * R)) * G = 1 - (-(N * R)) ^ (k * n) := by rw [hGe]; exact mul_neg_geom_sum _ _
  have hGI : IntS A G := by rw [hGe]; exact intS_sum (fun j => intS_pow (intS_neg (intS_mul hNI hRI)) j)
  have hGL : LatS L G := by rw [hGe]; exact latS_sum (fun j => latS_pow (latS_neg (latS_mul hNL hRL)) j)
  refine ⟨R * G * HahnSeries.single (-i0) u⁻¹, intS_mul (intS_mul hRI hGI) (intS_single huinv),
    latS_mul (latS_mul hRL hGL) (latS_single hi0L), ?_⟩
  have hQP : R * G * HahnSeries.single (-i0) u⁻¹ * P - 1 = -(-(N * R)) ^ (k * n) := by
    have hP1' : P1 = 1 + E + N := by rw [hEe]; ring
    calc R * G * HahnSeries.single (-i0) u⁻¹ * P - 1 = R * G * P1 - 1 := by rw [hP1e]; ring
      _ = -(-(N * R)) ^ (k * n) := by rw [hP1']; linear_combination G * hR + hg
  rw [hQP]
  have hD : DivS A (x ^ (k * n)) (-(-(N * R)) ^ (k * n)) :=
    divS_neg (divS_pow (divS_neg (divS_mul_int hxN hRI)) _)
  intro r
  obtain ⟨w, hw, e⟩ := hD r
  refine ⟨z ^ n * w, mul_mem (pow_mem hz n) hw, ?_⟩
  rw [e, pow_mul, hxk, mul_pow]; ring

end GlobalTheory.PrimInv

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ _ _ l _ A hl n L P hL hP hPL`. Establish `hnil : ∀ x ∈ A.nonunits, ∃ k : ℕ, ∃ z ∈ A, x ^ k = (l : Ω) * z`. Introduce `x hx`. Take `⟨k, z, hz, e⟩` from `GlobalTheory.T.valuationSubring_nonunits_pow_modEq_zero l A hl x hx`. Conclude with `⟨k, z, hz, by rw [sub_zero, pow_one] at e; exact e⟩`.

Establish `hPL' : PrimInv.LatS L P`. Introduce `r hr`. Conclude with `⟨(r * L).num, ((Rat.den_eq_one_iff _).1 (hPL r hr)).symm⟩`. Take `⟨Q, hQI, hQL, hQD⟩` from `PrimInv.core A (l : Ω) hnil L hL P hP hPL' n`. Use `⟨Q, hQI, fun r hr => ?_, fun r => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `hQL r hr`. Rewrite using `[hk]`. Simplify using the standard rewrite rules. Take `⟨z, hz, e⟩` from `hQD r`. Conclude with `⟨z, hz, by rw [← HahnSeries.coeff_sub, e]⟩`.
-/
theorem prim_inv_mod_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (P : HahnSeries ℚ Ω), 0 < L → Prim A P →
    (∀ r : ℚ, P.coeff r ≠ 0 → (r * L).den = 1) → ∃ Q : HahnSeries ℚ Ω, (∀ r, Q.coeff r ∈ A) ∧
    (∀ r : ℚ, Q.coeff r ≠ 0 → (r * L).den = 1) ∧ ∀ r, CgA A l n ((Q * P).coeff r) ((1 : HahnSeries ℚ Ω).coeff r) := by
  intro Ω _ _ _ l _ A hl n L P hL hP hPL
  have hnil : ∀ x ∈ A.nonunits, ∃ k : ℕ, ∃ z ∈ A, x ^ k = (l : Ω) * z := by
    intro x hx
    obtain ⟨k, z, hz, e⟩ := GlobalTheory.T.valuationSubring_nonunits_pow_modEq_zero l A hl x hx
    exact ⟨k, z, hz, by rw [sub_zero, pow_one] at e; exact e⟩
  have hPL' : PrimInv.LatS L P := by
    intro r hr
    exact ⟨(r * L).num, ((Rat.den_eq_one_iff _).1 (hPL r hr)).symm⟩
  obtain ⟨Q, hQI, hQL, hQD⟩ := PrimInv.core A (l : Ω) hnil L hL P hP hPL' n
  refine ⟨Q, hQI, fun r hr => ?_, fun r => ?_⟩
  · obtain ⟨k, hk⟩ := hQL r hr
    rw [hk]; simp
  · obtain ⟨z, hz, e⟩ := hQD r
    exact ⟨z, hz, by rw [← HahnSeries.coeff_sub, e]⟩

end GlobalTheory
