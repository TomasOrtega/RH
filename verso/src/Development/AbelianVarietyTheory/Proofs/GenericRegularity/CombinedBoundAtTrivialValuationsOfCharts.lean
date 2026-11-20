import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.RegModelC
import Development.AbelianVarietyTheory.Definitions.RegularCharts.SCharts
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtGeo
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree

noncomputable section

namespace GlobalTheory.Reg.TrivBound

open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/- English proof (translation)
Establish `hw' : algebraMap V (FractionRing V) w ≠ 0`. Introduce `h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])`. Establish `h1` using `IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal V) (K := FractionRing V) w`. Establish `h0 : valV V (algebraMap V (FractionRing V) w) ≠ 0` using `valV_ne_zero hw'`. Establish `h2 : WithZero.log (valV V (algebraMap V (FractionRing V) w)) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ))` using `(WithZero.log_le_log h0 one_ne_zero).2 h1`.

Rewrite `h2` using `[WithZero.log_one]`. Unfold `vV`. Use linear arithmetic over natural numbers and integers.
-/
theorem vV_nonneg (w : V) (hw : w ≠ 0) : 0 ≤ vV V (algebraMap V (FractionRing V) w) := by
  have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
    intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal V) (K := FractionRing V) w
  have h0 : valV V (algebraMap V (FractionRing V) w) ≠ 0 := valV_ne_zero hw'
  have h2 : WithZero.log (valV V (algebraMap V (FractionRing V) w)) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) :=
    (WithZero.log_le_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vV
  omega

/- English proof (translation)
Establish `h1 : (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V) (algebraMap V _ u) = 1` using `(IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := FractionRing V) (IsDiscreteValuationRing.maximalIdeal V)).2 hu`. Unfold `vV valV`. Rewrite using `[h1, WithZero.log_one, neg_zero]`.
-/
theorem vV_unit (u : V) (hu : u ∉ maximalIdeal V) : vV V (algebraMap V (FractionRing V) u) = 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V) (algebraMap V _ u) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := FractionRing V)
      (IsDiscreteValuationRing.maximalIdeal V)).2 hu
  unfold vV valV
  rw [h1, WithZero.log_one, neg_zero]

/- English proof (translation)
Establish `h0 : valV V y ≠ 0` using `valV_ne_zero hy`. Establish `hle : valV V y ≤ 1`. Rewrite using `[← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one]`. Unfold `vV at h`. Use linear arithmetic over natural numbers and integers.

Take `⟨w, hw⟩` from `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V) (K := FractionRing V) y (fun v => by`. Establish `hv : v = IsDiscreteValuationRing.maximalIdeal V`. Establish `hm : v.asIdeal.IsMaximal` using `v.isPrime.isMaximal v.ne_bot`. Use `ext1`. Conclude with `IsLocalRing.eq_maximalIdeal hm`.

Rewrite using `[hv]`. Conclude with `hle)`. Conclude with `⟨w, hw⟩`.
-/
theorem mem_of_vV_nonneg (y : FractionRing V) (hy : y ≠ 0) (h : 0 ≤ vV V y) :
    ∃ w : V, algebraMap V (FractionRing V) w = y := by
  have h0 : valV V y ≠ 0 := valV_ne_zero hy
  have hle : valV V y ≤ 1 := by
    rw [← WithZero.log_le_log h0 one_ne_zero, WithZero.log_one]
    unfold vV at h
    omega
  obtain ⟨w, hw⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := V)
    (K := FractionRing V) y (fun v => by
      have hv : v = IsDiscreteValuationRing.maximalIdeal V := by
        have hm : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
        ext1
        exact IsLocalRing.eq_maximalIdeal hm
      rw [hv]
      exact hle)
  exact ⟨w, hw⟩

/- English proof (translation)
Distinguish the cases in `hw : w = 0`. Rewrite using `[hw, map_zero, nval_zero]`. Conclude with `le_top`. Establish `hw' : algebraMap V (FractionRing V) w ≠ 0`. Introduce `h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])`.

Rewrite using `[nval_of_ne hw']`. Conclude with `EReal.coe_nonneg.2 (div_nonneg (by exact_mod_cast vV_nonneg w hw) (Nat.cast_nonneg e))`.
-/
theorem nval_nonneg (e : ℕ) (w : V) : 0 ≤ nval V e (algebraMap V (FractionRing V) w) := by
  by_cases hw : w = 0
  · rw [hw, map_zero, nval_zero]
    exact le_top
  · have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
      intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
    rw [nval_of_ne hw']
    exact EReal.coe_nonneg.2 (div_nonneg (by exact_mod_cast vV_nonneg w hw) (Nat.cast_nonneg e))

/- English proof (translation)
Establish `hu0 : u ≠ 0` using `fun h => hu (h ▸ (maximalIdeal V).zero_mem)`. Establish `hu' : algebraMap V (FractionRing V) u ≠ 0`. Introduce `h; apply hu0; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])`. Rewrite using `[nval_of_ne hu', vV_unit u hu]`. Simplify using the standard rewrite rules.
-/
theorem nval_unit (e : ℕ) (u : V) (hu : u ∉ maximalIdeal V) : nval V e (algebraMap V (FractionRing V) u) = 0 := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ (maximalIdeal V).zero_mem)
  have hu' : algebraMap V (FractionRing V) u ≠ 0 := by
    intro h; apply hu0; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  rw [nval_of_ne hu', vV_unit u hu]
  simp

/- English proof (translation)
Introduce `h; apply hx; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])`.
-/
theorem ne_zero_map {x : V} (hx : x ≠ 0) : algebraMap V (FractionRing V) x ≠ 0 := by
  intro h; apply hx; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])

variable {A : Type} [CommRing A] [IsDomain A]

/- English proof (translation)
Take `⟨x, s, hs, hfs, rfl⟩` from `h`. Establish `has : a * s = x * b`. Apply `IsFractionRing.injective A (FractionRing A)` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hab, ← hfs]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hφ : φ a * φ s = φ x * φ b` using `by rw [← map_mul, ← map_mul, has]`. Distinguish the cases in `ha : φ a = 0`. Establish `hx : φ x = 0`. Rewrite `hφ` using `[ha, zero_mul]`. Conclude with `(mul_eq_zero.1 hφ.symm).resolve_right hb`.

Rewrite using `[ha, hx, map_zero, nval_zero, nval_of_ne (ne_zero_map hs), nval_of_ne (ne_zero_map hb), EReal.top_sub_coe, EReal.top_sub_coe]`. Establish `hx : φ x ≠ 0`. Introduce `hx`. Rewrite `hφ` using `[hx, zero_mul]`. Conclude with `mul_ne_zero ha hs hφ`.

Establish `hv` using `congrArg (vV V) (congrArg (algebraMap V (FractionRing V)) hφ)`. Rewrite `hv` using `[map_mul, map_mul, vV_mul (ne_zero_map ha) (ne_zero_map hs), vV_mul (ne_zero_map hx) (ne_zero_map hb)]`. Rewrite using `[nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb), nval_of_ne (ne_zero_map hx), nval_of_ne (ne_zero_map hs), ← EReal.coe_sub, ← EReal.coe_sub, div_sub_div_same, div_sub_div_same]`. Use `congr 2`. Establish `: ((vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) : ℝ) - (vV V (algebraMap V (FractionRing V) (φ s)) : ℤ) = ((vV V (algebraMap V (FractionRing V) (φ a)) : ℤ) : ℝ) - (vV V (algebraMap V (FractionRing V) (φ b)) : ℤ)`.

Establish `: (vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) - vV V (algebraMap V (FractionRing V) (φ s)) = vV V (algebraMap V (FractionRing V) (φ a)) - vV V (algebraMap V (FractionRing V) (φ b))` using `by omega`. Conclude with `this` after adjusting the coercions. Conclude with `this`.
-/
theorem chval_eq (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a b : A)
    (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a) (hb : φ b ≠ 0) :
    r = nval V e (algebraMap V (FractionRing V) (φ a)) - nval V e (algebraMap V (FractionRing V) (φ b)) := by
  obtain ⟨x, s, hs, hfs, rfl⟩ := h
  have has : a * s = x * b := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_mul, ← hab, ← hfs]
    ring
  have hφ : φ a * φ s = φ x * φ b := by rw [← map_mul, ← map_mul, has]
  by_cases ha : φ a = 0
  · have hx : φ x = 0 := by
      rw [ha, zero_mul] at hφ
      exact (mul_eq_zero.1 hφ.symm).resolve_right hb
    rw [ha, hx, map_zero, nval_zero, nval_of_ne (ne_zero_map hs), nval_of_ne (ne_zero_map hb),
      EReal.top_sub_coe, EReal.top_sub_coe]
  · have hx : φ x ≠ 0 := by
      intro hx
      rw [hx, zero_mul] at hφ
      exact mul_ne_zero ha hs hφ
    have hv := congrArg (vV V) (congrArg (algebraMap V (FractionRing V)) hφ)
    rw [map_mul, map_mul, vV_mul (ne_zero_map ha) (ne_zero_map hs),
      vV_mul (ne_zero_map hx) (ne_zero_map hb)] at hv
    rw [nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb), nval_of_ne (ne_zero_map hx),
      nval_of_ne (ne_zero_map hs), ← EReal.coe_sub, ← EReal.coe_sub, div_sub_div_same, div_sub_div_same]
    congr 2
    have : ((vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) : ℝ) -
        (vV V (algebraMap V (FractionRing V) (φ s)) : ℤ) =
        ((vV V (algebraMap V (FractionRing V) (φ a)) : ℤ) : ℝ) - (vV V (algebraMap V (FractionRing V) (φ b)) : ℤ) := by
      have : (vV V (algebraMap V (FractionRing V) (φ x)) : ℤ) - vV V (algebraMap V (FractionRing V) (φ s)) =
          vV V (algebraMap V (FractionRing V) (φ a)) - vV V (algebraMap V (FractionRing V) (φ b)) := by omega
      exact_mod_cast this
    exact this

/- English proof (translation)
Distinguish the cases in `ha : φ a = 0`. Conclude with `⟨0, by rw [ha, zero_mul]⟩`. Rewrite `hr` using `[chval_eq φ e f r h a b hab hb, nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb), ← EReal.coe_sub, EReal.coe_nonneg, div_sub_div_same]`. Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`. Establish `hle : (vV V (algebraMap V (FractionRing V) (φ b)) : ℝ) ≤ vV V (algebraMap V (FractionRing V) (φ a))`.

Use `(div_nonneg_iff.1 hr)` as an intermediate fact. Break down `this with ⟨h1, -⟩ | ⟨-, h2⟩` into its components or cases. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle' : vV V (algebraMap V (FractionRing V) (φ b)) ≤ vV V (algebraMap V (FractionRing V) (φ a))`.

Conclude with `hle` after adjusting the coercions. Use `set y := algebraMap V (FractionRing V) (φ a) / algebraMap V (FractionRing V) (φ b)`. Establish `hy0 : y ≠ 0` using `div_ne_zero (ne_zero_map ha) (ne_zero_map hb)`. Establish `hyv : vV V y + vV V (algebraMap V (FractionRing V) (φ b)) = vV V (algebraMap V (FractionRing V) (φ a))`. Rewrite using `[← vV_mul hy0 (ne_zero_map hb), div_mul_cancel₀ _ (ne_zero_map hb)]`.

Take `⟨w, hw⟩` from `mem_of_vV_nonneg y hy0 (by omega)`. Use `⟨w, IsFractionRing.injective V (FractionRing V) ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hw, div_mul_cancel₀ _ (ne_zero_map hb)]`.
-/
theorem chval_div (φ : A →+* V) (e : ℕ) (he : 0 < e) (f : FractionRing A) (r : EReal) (h : ChV φ e f r)
    (hr : 0 ≤ r) (a b : A) (hab : f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a)
    (hb : φ b ≠ 0) : ∃ w : V, φ a = w * φ b := by
  by_cases ha : φ a = 0
  · exact ⟨0, by rw [ha, zero_mul]⟩
  rw [chval_eq φ e f r h a b hab hb, nval_of_ne (ne_zero_map ha), nval_of_ne (ne_zero_map hb),
    ← EReal.coe_sub, EReal.coe_nonneg, div_sub_div_same] at hr
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hle : (vV V (algebraMap V (FractionRing V) (φ b)) : ℝ) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    have := (div_nonneg_iff.1 hr)
    rcases this with ⟨h1, -⟩ | ⟨-, h2⟩
    · linarith
    · linarith
  have hle' : vV V (algebraMap V (FractionRing V) (φ b)) ≤ vV V (algebraMap V (FractionRing V) (φ a)) := by
    exact_mod_cast hle
  set y := algebraMap V (FractionRing V) (φ a) / algebraMap V (FractionRing V) (φ b)
  have hy0 : y ≠ 0 := div_ne_zero (ne_zero_map ha) (ne_zero_map hb)
  have hyv : vV V y + vV V (algebraMap V (FractionRing V) (φ b)) = vV V (algebraMap V (FractionRing V) (φ a)) := by
    rw [← vV_mul hy0 (ne_zero_map hb), div_mul_cancel₀ _ (ne_zero_map hb)]
  obtain ⟨w, hw⟩ := mem_of_vV_nonneg y hy0 (by omega)
  refine ⟨w, IsFractionRing.injective V (FractionRing V) ?_⟩
  rw [map_mul, hw, div_mul_cancel₀ _ (ne_zero_map hb)]

/- English proof (translation)
Establish `hs0 : φ s ≠ 0` using `fun h0 => hs (h0 ▸ (maximalIdeal V).zero_mem)`. Rewrite using `[chval_eq φ e f r h a s hfs hs0, nval_unit e _ hs, sub_zero]`. Conclude with `nval_nonneg e _`.
-/
theorem chval_nonneg (φ : A →+* V) (e : ℕ) (f : FractionRing A) (r : EReal) (h : ChV φ e f r) (a s : A)
    (hfs : f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) (hs : φ s ∉ maximalIdeal V) :
    0 ≤ r := by
  have hs0 : φ s ≠ 0 := fun h0 => hs (h0 ▸ (maximalIdeal V).zero_mem)
  rw [chval_eq φ e f r h a s hfs hs0, nval_unit e _ hs, sub_zero]
  exact nval_nonneg e _

end

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]

def vr (e : ℕ) (x : V) : ℝ := (vV V (algebraMap V (FractionRing V) x) : ℝ) / e

/- English proof (translation)
Rewrite using `[nval_of_ne (ne_zero_map hx)]`. Both sides reduce to the same expression.
-/
theorem nval_eq_vr (e : ℕ) {x : V} (hx : x ≠ 0) :
    nval V e (algebraMap V (FractionRing V) x) = (vr e x : EReal) := by
  rw [nval_of_ne (ne_zero_map hx)]
  rfl

/- English proof (translation)
Unfold `vr`. Rewrite using `[map_mul, vV_mul (ne_zero_map hx) (ne_zero_map hy)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vr_mul (e : ℕ) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) : vr e (x * y) = vr e x + vr e y := by
  unfold vr
  rw [map_mul, vV_mul (ne_zero_map hx) (ne_zero_map hy)]
  push_cast
  ring

/- English proof (translation)
Establish `h` using `vV_unit (V := V) 1 (fun h => (maximalIdeal V).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance) h)`. Unfold `vr`. Rewrite using `[h]`. Simplify using the standard rewrite rules.
-/
theorem vr_one (e : ℕ) : vr e (1 : V) = 0 := by
  have h := vV_unit (V := V) 1
    (fun h => (maximalIdeal V).ne_top_iff_one.1 (Ideal.IsPrime.ne_top inferInstance) h)
  unfold vr
  rw [h]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, s, hs, hfs, hu⟩`. Establish `hx : φ x ≠ 0`. Introduce `hx`. Rewrite `hu` using `[hx, map_zero, nval_zero, nval_of_ne (ne_zero_map hs), EReal.top_sub_coe]`.

Conclude with `EReal.coe_ne_top u hu`. Use `⟨x, s, hs, hx, hfs, ?_⟩` and prove the remaining obligations. Rewrite `hu` using `[nval_eq_vr e hx, nval_eq_vr e hs, ← EReal.coe_sub]`. Conclude with `EReal.coe_injective hu`. Introduce and unpack `⟨x, s, hs, hx, hfs, hu⟩`.

Use `⟨x, s, hs, hfs, ?_⟩` and prove the remaining obligations. Rewrite using `[nval_eq_vr e hx, nval_eq_vr e hs, ← EReal.coe_sub, hu]`.
-/
theorem chval_fin_iff (φ : A →+* V) (e : ℕ) (f : FractionRing A) (u : ℝ) :
    ChV φ e f (u : EReal) ↔ ∃ x s : A, φ s ≠ 0 ∧ φ x ≠ 0 ∧
      f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) x ∧ u = vr e (φ x) - vr e (φ s) := by
  constructor
  · rintro ⟨x, s, hs, hfs, hu⟩
    have hx : φ x ≠ 0 := by
      intro hx
      rw [hx, map_zero, nval_zero, nval_of_ne (ne_zero_map hs), EReal.top_sub_coe] at hu
      exact EReal.coe_ne_top u hu
    refine ⟨x, s, hs, hx, hfs, ?_⟩
    rw [nval_eq_vr e hx, nval_eq_vr e hs, ← EReal.coe_sub] at hu
    exact EReal.coe_injective hu
  · rintro ⟨x, s, hs, hx, hfs, hu⟩
    refine ⟨x, s, hs, hfs, ?_⟩
    rw [nval_eq_vr e hx, nval_eq_vr e hs, ← EReal.coe_sub, hu]

/- English proof (translation)
Take `⟨x1, s1, hs1, hx1, hf1, hu1⟩` from `(chval_fin_iff φ e f1 u1).1 h1`. Take `⟨x2, s2, hs2, hx2, hf2, hu2⟩` from `(chval_fin_iff φ e f2 u2).1 h2`. Use `(chval_fin_iff φ e _ _).2 ⟨x1 * x2, s1 * s2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_ne_zero hs1 hs2`.

Rewrite using `[map_mul]`. Conclude with `mul_ne_zero hx1 hx2`. Rewrite using `[map_mul, map_mul, ← hf1, ← hf2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_mul, vr_mul e hx1 hx2, vr_mul e hs1 hs2, hu1, hu2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chval_fin_mul (φ : A →+* V) (e : ℕ) {f1 f2 : FractionRing A} {u1 u2 : ℝ}
    (h1 : ChV φ e f1 (u1 : EReal)) (h2 : ChV φ e f2 (u2 : EReal)) :
    ChV φ e (f1 * f2) ((u1 + u2 : ℝ) : EReal) := by
  obtain ⟨x1, s1, hs1, hx1, hf1, hu1⟩ := (chval_fin_iff φ e f1 u1).1 h1
  obtain ⟨x2, s2, hs2, hx2, hf2, hu2⟩ := (chval_fin_iff φ e f2 u2).1 h2
  refine (chval_fin_iff φ e _ _).2 ⟨x1 * x2, s1 * s2, ?_, ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hs1 hs2
  · rw [map_mul]; exact mul_ne_zero hx1 hx2
  · rw [map_mul, map_mul, ← hf1, ← hf2]; ring
  · rw [map_mul, map_mul, vr_mul e hx1 hx2, vr_mul e hs1 hs2, hu1, hu2]; ring

/- English proof (translation)
Apply the tactic sequence `refine (chval_fin_iff φ e _ _).2 ⟨1, 1, ?_, ?_, ?_, ?_⟩ <;> simp [vr_one]`.
-/
theorem chval_fin_one (φ : A →+* V) (e : ℕ) : ChV φ e (1 : FractionRing A) ((0 : ℝ) : EReal) := by
  refine (chval_fin_iff φ e _ _).2 ⟨1, 1, ?_, ?_, ?_, ?_⟩ <;> simp [vr_one]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using chval_fin_one φ e`. Consider the case `succ N ih`. Use `chval_fin_mul φ e ih h` as an intermediate fact. Rewrite using `[pow_succ]`.

Use `this using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chval_fin_pow (φ : A →+* V) (e : ℕ) {f : FractionRing A} {u : ℝ} (h : ChV φ e f (u : EReal))
    (N : ℕ) : ChV φ e (f ^ N) (((N : ℝ) * u : ℝ) : EReal) := by
  induction N with
  | zero => simpa using chval_fin_one φ e
  | succ N ih =>
    have := chval_fin_mul φ e ih h
    rw [pow_succ]
    convert this using 2
    push_cast
    ring

/- English proof (translation)
Take `⟨x, s, hs, hx, hfs, hu⟩` from `(chval_fin_iff φ e f u).1 h`. Establish `hx0 : x ≠ 0` using `fun h0 => hx (by rw [h0, map_zero])`. Establish `hxK : algebraMap A (FractionRing A) x ≠ 0` using `fun h0 => hx0 (IsFractionRing.injective A _ (by rw [h0, map_zero]))`. Establish `hf0 : f ≠ 0`. Introduce `h0`.

Rewrite `hfs` using `[h0, zero_mul]`. Conclude with `hxK hfs.symm`. Use `(chval_fin_iff φ e _ _).2 ⟨s, x, hx, hs, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfs]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hu]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chval_fin_inv (φ : A →+* V) (e : ℕ) {f : FractionRing A} {u : ℝ} (h : ChV φ e f (u : EReal)) :
    ChV φ e f⁻¹ ((-u : ℝ) : EReal) := by
  obtain ⟨x, s, hs, hx, hfs, hu⟩ := (chval_fin_iff φ e f u).1 h
  have hx0 : x ≠ 0 := fun h0 => hx (by rw [h0, map_zero])
  have hxK : algebraMap A (FractionRing A) x ≠ 0 := fun h0 => hx0 (IsFractionRing.injective A _ (by rw [h0, map_zero]))
  have hf0 : f ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hfs
    exact hxK hfs.symm
  refine (chval_fin_iff φ e _ _).2 ⟨s, x, hx, hs, ?_, ?_⟩
  · rw [← hfs]
    field_simp
  · rw [hu]; ring

/- English proof (translation)
Use `(chval_fin_iff φ e _ _).2 ⟨a, 1, ?_, ha, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `one_ne_zero`. Rewrite using `[map_one, mul_one]`. Rewrite using `[map_one, vr_one, sub_zero]`.
-/
theorem chval_fin_alg (φ : A →+* V) (e : ℕ) (a : A) (ha : φ a ≠ 0) :
    ChV φ e (algebraMap A (FractionRing A) a) ((vr e (φ a) : ℝ) : EReal) := by
  refine (chval_fin_iff φ e _ _).2 ⟨a, 1, ?_, ha, ?_, ?_⟩
  · rw [map_one]; exact one_ne_zero
  · rw [map_one, mul_one]
  · rw [map_one, vr_one, sub_zero]

/- English proof (translation)
Break down `Int.eq_nat_or_neg Z with ⟨N, rfl | rfl⟩` into its components or cases. Rewrite using `[zpow_natCast]`. Conclude with `chval_fin_pow φ e h N` after adjusting the coercions. Rewrite using `[zpow_neg, zpow_natCast]`. Use `chval_fin_inv φ e (chval_fin_pow φ e h N)` as an intermediate fact.

Use `this using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chval_fin_zpow (φ : A →+* V) (e : ℕ) {f : FractionRing A} {u : ℝ} (h : ChV φ e f (u : EReal))
    (Z : ℤ) : ChV φ e (f ^ Z) (((Z : ℝ) * u : ℝ) : EReal) := by
  rcases Int.eq_nat_or_neg Z with ⟨N, rfl | rfl⟩
  · rw [zpow_natCast]
    exact_mod_cast chval_fin_pow φ e h N
  · rw [zpow_neg, zpow_natCast]
    have := chval_fin_inv φ e (chval_fin_pow φ e h N)
    convert this using 2
    push_cast
    ring

end

section

/- English proof (translation)
Simplify using `[vV, valV]`.
-/
theorem vV_zero' {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    vV (K' := FractionRing V) V 0 = 0 := by
  simp [vV, valV]

/- English proof (translation)
Use `Formalism.L2.Pj.RegC.key_centre g x hx0 (fun V _ _ _ _ _ φ a b hab hb hφx => ?_) qq hqq` and prove the remaining obligations. Take `⟨e, r, he, hr, hr0⟩` from `hpts V φ hφx`. Conclude with `chval_div φ.toRingHom e he g r hr hr0 a b hab hb`.
-/
theorem transfer'' {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (g : FractionRing A) (x : A) (hx0 : x ≠ 0)
    (hpts : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V), φ x ≠ 0 →
        ∃ (e : ℕ) (r : EReal), 0 < e ∧ ChV φ.toRingHom e g r ∧ 0 ≤ r)
    (qq : Ideal A) [qq.IsPrime] (hqq : qq ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) :
    ∃ a s : A, s ∉ qq ∧ g * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  refine Formalism.L2.Pj.RegC.key_centre g x hx0 (fun V _ _ _ _ _ φ a b hab hb hφx => ?_) qq hqq
  obtain ⟨e, r, he, hr, hr0⟩ := hpts V φ hφx
  exact chval_div φ.toRingHom e he g r hr hr0 a b hab hb

/- English proof (translation)
Use `set ϖA : FractionRing A := algebraMap A (FractionRing A) (algebraMap O A ϖ)`. Use `set g : FractionRing A := ϖA ^ Aexp * fe ^ B * (fw ^ N)⁻¹`. Establish `hgval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V] (φ : A →ₐ[O] V) (e : ℕ) (w t : ℝ), algebraMap O V ϖ ≠ 0 → ChV φ.toRingHom e fw (w : EReal) → ChV φ.toRingHom e fe (t : EReal) → ChV φ.toRingHom e g (((Aexp : ℝ) * vr e (algebraMap O V ϖ) + B …`. Introduce `V _ _ _ _ φ e w t hϖ hW hT`. Establish `h1 : φ.toRingHom (algebraMap O A ϖ) ≠ 0`.

Rewrite using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]`. Conclude with `hϖ`. Establish `hϖv` using `chval_fin_alg φ.toRingHom e (algebraMap O A ϖ) h1`. Rewrite using `[show φ.toRingHom (algebraMap O A ϖ) = algebraMap O V ϖ by`. Rewrite `hϖv` using `[AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]]`.

Conclude with `chval_fin_mul _ _ (chval_fin_mul _ _ (chval_fin_zpow _ _ hϖv Aexp) (chval_fin_pow _ _ hT B)) (chval_fin_inv _ _ (chval_fin_pow _ _ hW N))`. Establish `hyeK : algebraMap A (FractionRing A) ye ≠ 0` using `fun h => hye (IsFractionRing.injective A _ (by rw [h, map_zero]))`. Take `⟨a, s, hs, hgs⟩` from `transfer'' (O := O) g (x * ye) (mul_ne_zero hx hye) (fun V _ _ _ _ _ φ' hφ' => by`. Rewrite `hφ'` using `[map_mul]`. Establish `hφ'x : φ' x ≠ 0` using `left_ne_zero_of_mul hφ'`.

Establish `hφ'y : φ' ye ≠ 0` using `right_ne_zero_of_mul hφ'`. Take `⟨e', W', T', he', hϖ', hW', hT', hT0, hb⟩` from `halg V φ' hφ'x`. Establish `hϖ0 : algebraMap O V ϖ ≠ 0`. Introduce `h0`. Rewrite `hϖ'` using `[h0, map_zero, vV_zero', zero_mul]`.

Use linear arithmetic over natural numbers and integers. Establish `hP : ∀ k : ℕ, φ' ((algebraMap O A ϖ * x) ^ k) ≠ 0`. Introduce `k`. Rewrite using `[map_pow, map_mul, AlgHom.commutes]`. Conclude with `pow_ne_zero _ (mul_ne_zero hϖ0 hφ'x)`.

Establish `hTe` using `chval_eq φ'.toRingHom e' fe T' hT' ye _ hfe (hP te)`. Establish `hTf : T' = ((vr e' (φ' ye) - vr e' (φ' ((algebraMap O A ϖ * x) ^ te)) : ℝ) : EReal)`. Rewrite using `[hTe, EReal.coe_sub, ← nval_eq_vr e' hφ'y, ← nval_eq_vr e' (hP te)]`. Both sides reduce to the same expression. Take `⟨xw, sw, hsw, hfws, hWv⟩` from `hW'`.

Establish `hrel : fw * algebraMap A (FractionRing A) yw = algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ tw)`. Rewrite using `[← hfw]`. Clear the denominators using the available nonvanishing facts. Establish `hxy : xw * yw = sw * (algebraMap O A ϖ * x) ^ tw`. Apply `IsFractionRing.injective A (FractionRing A)` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul, ← hfws, ← hrel]`. Expand and normalize the polynomial expressions, which then agree. Establish `hxw : φ' xw ≠ 0`. Introduce `h0`. Use `congrArg φ' hxy` as an intermediate fact.

Rewrite `this` using `[map_mul, map_mul, h0, zero_mul]`. Conclude with `mul_ne_zero hsw (hP tw) this.symm`. Establish `hWf : W' = ((vr e' (φ' xw) - vr e' (φ' sw) : ℝ) : EReal)`. Rewrite using `[hWv, EReal.coe_sub]`. Conclude with `congrArg₂ (· - ·) (nval_eq_vr e' hxw) (nval_eq_vr e' hsw)`.

Use `set w' := vr e' (φ' xw) - vr e' (φ' sw)`. Use `set t' := vr e' (φ' ye) - vr e' (φ' ((algebraMap O A ϖ * x) ^ te))`. Establish `hWc : ChV φ'.toRingHom e' fw (w' : EReal)` using `hWf ▸ ⟨xw, sw, hsw, hfws, hWv⟩`. Establish `hTc : ChV φ'.toRingHom e' fe (t' : EReal)` using `hTf ▸ hT'`. Establish `ht0 : 0 ≤ t'` using `by rw [hTf] at hT0; exact_mod_cast hT0`.

Establish `hwb : w' ≤ nu0 + c' * t'`. Use `hb (by rw [hTf]; exact EReal.coe_ne_top _)` as an intermediate fact. Rewrite `this` using `[hWf, hTf, ← EReal.coe_mul, ← EReal.coe_add]`. Conclude with `this` after adjusting the coercions. Establish `hκ : vr e' (algebraMap O V ϖ) * eO = 1`.

Unfold `vr`. Establish `hv : ((vV (K'` using `FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) : ℤ) : ℝ) * eO = e' := by`. Conclude with `hϖ'` after adjusting the coercions. Establish `he'r : (0 : ℝ) < e'` using `by exact_mod_cast he'`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨e', _, he', hgval V φ' e' w' t' hϖ0 hWc hTc, ?_⟩` and prove the remaining obligations. Establish `heOr : (0 : ℝ) < eO` using `by exact_mod_cast heO`. Establish `h1 : (N : ℝ) * nu0 ≤ Aexp * vr e' (algebraMap O V ϖ)`. Establish `hv1 : vr e' (algebraMap O V ϖ) = 1 / eO`.

Rewrite using `[eq_div_iff (ne_of_gt heOr)]`. Conclude with `hκ`. Establish `: (Aexp : ℝ) * vr e' (algebraMap O V ϖ) = Aexp / eO`. Rewrite using `[hv1, mul_one_div]`. Rewrite using `[this, le_div_iff₀ heOr]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (N : ℝ) * c' * t' ≤ B * t'` using `mul_le_mul_of_nonneg_right hB ht0`. Establish `h3 : (N : ℝ) * w' ≤ N * (nu0 + c' * t')` using `mul_le_mul_of_nonneg_left hwb (Nat.cast_nonneg N)`. Conclude with `EReal.coe_nonneg.2 (by nlinarith))`. Use the proof step `((maximalIdeal V).comap φ.toRingHom) hqq`.

Establish `hval` using `hgval V φ e w t hφϖ hW hT`. Use `chval_nonneg φ.toRingHom e g _ hval a s hgs hs` as an intermediate fact. Establish `h0` using `EReal.coe_nonneg.1 this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem comb_core {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (ϖ : O) (eO : ℕ) (heO : 0 < eO)
    (fw fe : FractionRing A) (hfw0 : fw ≠ 0) (x : A) (hx : x ≠ 0)
    (ye : A) (hye : ye ≠ 0) (te : ℕ)
    (hfe : fe * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ te) = algebraMap A (FractionRing A) ye)
    (yw : A) (tw : ℕ)
    (hfw : fw⁻¹ * algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ tw) = algebraMap A (FractionRing A) yw)
    (nu0 c' : ℝ) (N : ℕ) (Aexp : ℤ) (B : ℕ) (hA : (eO : ℝ) * N * nu0 ≤ Aexp) (hB : (N : ℝ) * c' ≤ B)
    (halg : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V), φ x ≠ 0 → ∃ (e : ℕ) (W T : EReal), 0 < e ∧
        vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) * (eO : ℤ) = e ∧
        ChV φ.toRingHom e fw W ∧ ChV φ.toRingHom e fe T ∧ 0 ≤ T ∧
        (T ≠ ⊤ → W ≤ (nu0 : EReal) + (c' : EReal) * T))
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V] (φ : A →ₐ[O] V)
    (hφx : φ x ≠ 0) (hφϖ : algebraMap O V ϖ ≠ 0)
    (hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤)
    (e : ℕ) (w t : ℝ) (hW : ChV φ.toRingHom e fw (w : EReal)) (hT : ChV φ.toRingHom e fe (t : EReal)) :
    (N : ℝ) * w ≤ Aexp * vr e (algebraMap O V ϖ) + B * t := by
  classical
  set ϖA : FractionRing A := algebraMap A (FractionRing A) (algebraMap O A ϖ)
  set g : FractionRing A := ϖA ^ Aexp * fe ^ B * (fw ^ N)⁻¹

  have hgval : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      (φ : A →ₐ[O] V) (e : ℕ) (w t : ℝ), algebraMap O V ϖ ≠ 0 → ChV φ.toRingHom e fw (w : EReal) →
      ChV φ.toRingHom e fe (t : EReal) →
      ChV φ.toRingHom e g (((Aexp : ℝ) * vr e (algebraMap O V ϖ) + B * t + -((N : ℝ) * w) : ℝ) : EReal) := by
    intro V _ _ _ _ φ e w t hϖ hW hT
    have h1 : φ.toRingHom (algebraMap O A ϖ) ≠ 0 := by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]; exact hϖ
    have hϖv := chval_fin_alg φ.toRingHom e (algebraMap O A ϖ) h1
    rw [show φ.toRingHom (algebraMap O A ϖ) = algebraMap O V ϖ by
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]] at hϖv
    exact chval_fin_mul _ _ (chval_fin_mul _ _ (chval_fin_zpow _ _ hϖv Aexp) (chval_fin_pow _ _ hT B))
      (chval_fin_inv _ _ (chval_fin_pow _ _ hW N))
  have hyeK : algebraMap A (FractionRing A) ye ≠ 0 := fun h => hye (IsFractionRing.injective A _ (by rw [h, map_zero]))
  obtain ⟨a, s, hs, hgs⟩ := transfer'' (O := O) g (x * ye) (mul_ne_zero hx hye)
    (fun V _ _ _ _ _ φ' hφ' => by
      rw [map_mul] at hφ'
      have hφ'x : φ' x ≠ 0 := left_ne_zero_of_mul hφ'
      have hφ'y : φ' ye ≠ 0 := right_ne_zero_of_mul hφ'
      obtain ⟨e', W', T', he', hϖ', hW', hT', hT0, hb⟩ := halg V φ' hφ'x
      have hϖ0 : algebraMap O V ϖ ≠ 0 := by
        intro h0
        rw [h0, map_zero, vV_zero', zero_mul] at hϖ'
        omega
      have hP : ∀ k : ℕ, φ' ((algebraMap O A ϖ * x) ^ k) ≠ 0 := by
        intro k
        rw [map_pow, map_mul, AlgHom.commutes]
        exact pow_ne_zero _ (mul_ne_zero hϖ0 hφ'x)

      have hTe := chval_eq φ'.toRingHom e' fe T' hT' ye _ hfe (hP te)
      have hTf : T' = ((vr e' (φ' ye) - vr e' (φ' ((algebraMap O A ϖ * x) ^ te)) : ℝ) : EReal) := by
        rw [hTe, EReal.coe_sub, ← nval_eq_vr e' hφ'y, ← nval_eq_vr e' (hP te)]
        rfl

      obtain ⟨xw, sw, hsw, hfws, hWv⟩ := hW'
      have hrel : fw * algebraMap A (FractionRing A) yw = algebraMap A (FractionRing A) ((algebraMap O A ϖ * x) ^ tw) := by
        rw [← hfw]; field_simp
      have hxy : xw * yw = sw * (algebraMap O A ϖ * x) ^ tw := by
        apply IsFractionRing.injective A (FractionRing A)
        rw [map_mul, map_mul, ← hfws, ← hrel]; ring
      have hxw : φ' xw ≠ 0 := by
        intro h0
        have := congrArg φ' hxy
        rw [map_mul, map_mul, h0, zero_mul] at this
        exact mul_ne_zero hsw (hP tw) this.symm
      have hWf : W' = ((vr e' (φ' xw) - vr e' (φ' sw) : ℝ) : EReal) := by
        rw [hWv, EReal.coe_sub]
        exact congrArg₂ (· - ·) (nval_eq_vr e' hxw) (nval_eq_vr e' hsw)
      set w' := vr e' (φ' xw) - vr e' (φ' sw)
      set t' := vr e' (φ' ye) - vr e' (φ' ((algebraMap O A ϖ * x) ^ te))
      have hWc : ChV φ'.toRingHom e' fw (w' : EReal) := hWf ▸ ⟨xw, sw, hsw, hfws, hWv⟩
      have hTc : ChV φ'.toRingHom e' fe (t' : EReal) := hTf ▸ hT'
      have ht0 : 0 ≤ t' := by rw [hTf] at hT0; exact_mod_cast hT0
      have hwb : w' ≤ nu0 + c' * t' := by
        have := hb (by rw [hTf]; exact EReal.coe_ne_top _)
        rw [hWf, hTf, ← EReal.coe_mul, ← EReal.coe_add] at this
        exact_mod_cast this
      have hκ : vr e' (algebraMap O V ϖ) * eO = 1 := by
        unfold vr
        have hv : ((vV (K' := FractionRing V) V (algebraMap V (FractionRing V) (algebraMap O V ϖ)) : ℤ) : ℝ) * eO = e' := by
          exact_mod_cast hϖ'
        have he'r : (0 : ℝ) < e' := by exact_mod_cast he'
        field_simp
        linarith
      refine ⟨e', _, he', hgval V φ' e' w' t' hϖ0 hWc hTc, ?_⟩
      have heOr : (0 : ℝ) < eO := by exact_mod_cast heO
      have h1 : (N : ℝ) * nu0 ≤ Aexp * vr e' (algebraMap O V ϖ) := by
        have hv1 : vr e' (algebraMap O V ϖ) = 1 / eO := by
          rw [eq_div_iff (ne_of_gt heOr)]; exact hκ
        have : (Aexp : ℝ) * vr e' (algebraMap O V ϖ) = Aexp / eO := by
          rw [hv1, mul_one_div]
        rw [this, le_div_iff₀ heOr]
        linarith
      have h2 : (N : ℝ) * c' * t' ≤ B * t' := mul_le_mul_of_nonneg_right hB ht0
      have h3 : (N : ℝ) * w' ≤ N * (nu0 + c' * t') := mul_le_mul_of_nonneg_left hwb (Nat.cast_nonneg N)
      exact EReal.coe_nonneg.2 (by nlinarith))
    ((maximalIdeal V).comap φ.toRingHom) hqq
  have hval := hgval V φ e w t hφϖ hW hT
  have := chval_nonneg φ.toRingHom e g _ hval a s hgs hs
  have h0 := EReal.coe_nonneg.1 this
  linarith

end

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {A : Type} [CommRing A] [IsDomain A]

/- English proof (translation)
Take `⟨x, s, hs, -, rfl⟩` from `h`. Rewrite using `[nval_eq_vr e hs]`. Distinguish the cases in `hx : φ x = 0`. Rewrite using `[hx, map_zero, nval_zero, EReal.top_sub_coe]`. Conclude with `top_ne_bot`.

Rewrite using `[nval_eq_vr e hx, ← EReal.coe_sub]`. Conclude with `EReal.coe_ne_bot _`.
-/
theorem chval_ne_bot {φ : A →+* V} {e : ℕ} {f : FractionRing A} {r : EReal} (h : ChV φ e f r) : r ≠ ⊥ := by
  obtain ⟨x, s, hs, -, rfl⟩ := h
  rw [nval_eq_vr e hs]
  by_cases hx : φ x = 0
  · rw [hx, map_zero, nval_zero, EReal.top_sub_coe]; exact top_ne_bot
  · rw [nval_eq_vr e hx, ← EReal.coe_sub]; exact EReal.coe_ne_bot _

/- English proof (translation)
Assemble the required witnesses or components as `⟨r.toReal, (EReal.coe_toReal h h').symm⟩`.
-/
theorem fin_of_ne_top {r : EReal} (h : r ≠ ⊤) (h' : r ≠ ⊥) : ∃ t : ℝ, r = (t : EReal) :=
  ⟨r.toReal, (EReal.coe_toReal h h').symm⟩

/- English proof (translation)
Take `⟨x, s, hs, hfs, rfl⟩` from `h`. Establish `hx : x = 0`. Rewrite `hfs` using `[zero_mul]`. Conclude with `IsFractionRing.injective A (FractionRing A) (by rw [← hfs, map_zero])`. Rewrite using `[hx, map_zero, map_zero, nval_zero, nval_eq_vr e hs, EReal.top_sub_coe]`.
-/
theorem chval_zero {φ : A →+* V} {e : ℕ} {r : EReal} (h : ChV φ e (0 : FractionRing A) r) : r = ⊤ := by
  obtain ⟨x, s, hs, hfs, rfl⟩ := h
  have hx : x = 0 := by
    rw [zero_mul] at hfs
    exact IsFractionRing.injective A (FractionRing A) (by rw [← hfs, map_zero])
  rw [hx, map_zero, map_zero, nval_zero, nval_eq_vr e hs, EReal.top_sub_coe]

/- English proof (translation)
Take `⟨x1, s1, hs1, hf1, rfl⟩` from `h1`. Establish `hrel : algebraMap A (FractionRing A) xk * f1 * algebraMap A (FractionRing A) s1 = algebraMap A (FractionRing A) (xk * x1)` using `by rw [mul_assoc, hf1, map_mul]`. Rewrite using `[chval_eq φ e _ r2 h2 (xk * x1) s1 hrel hs1, map_mul, map_mul, nval_mul, nval_eq_vr e hs1]`. Establish `h0` using `nval_nonneg e (φ xk)`. Distinguish the cases in `hx : φ x1 = 0`.

Establish `hX` using `nval_ne_bot (V := V) e (algebraMap V (FractionRing V) (φ xk))`. Rewrite using `[hx, map_zero, nval_zero]`. Conclude with `EReal.sub_le_sub (le_of_eq (EReal.add_top_of_ne_bot hX).symm) le_rfl`. Rewrite using `[nval_eq_vr e hx]`. Break down `eq_or_ne (nval V e (algebraMap V (FractionRing V) (φ xk))) ⊤ with ht | ht` into its components or cases.

Rewrite using `[ht, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), EReal.top_sub_coe]`. Conclude with `le_top`. Take `⟨u, hu⟩` from `fin_of_ne_top ht (nval_ne_bot (V := V) e _)`. Rewrite using `[hu, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]`. Rewrite `h0` using `[hu]`.

Use `EReal.coe_nonneg.1 h0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ratio_ge {φ : A →+* V} {e : ℕ} {f1 : FractionRing A} {r1 r2 : EReal} {xk : A}
    (h1 : ChV φ e f1 r1) (h2 : ChV φ e (algebraMap A (FractionRing A) xk * f1) r2) : r1 ≤ r2 := by
  obtain ⟨x1, s1, hs1, hf1, rfl⟩ := h1
  have hrel : algebraMap A (FractionRing A) xk * f1 * algebraMap A (FractionRing A) s1 =
      algebraMap A (FractionRing A) (xk * x1) := by rw [mul_assoc, hf1, map_mul]
  rw [chval_eq φ e _ r2 h2 (xk * x1) s1 hrel hs1, map_mul, map_mul, nval_mul, nval_eq_vr e hs1]
  have h0 := nval_nonneg e (φ xk)
  by_cases hx : φ x1 = 0
  · have hX := nval_ne_bot (V := V) e (algebraMap V (FractionRing V) (φ xk))
    rw [hx, map_zero, nval_zero]
    exact EReal.sub_le_sub (le_of_eq (EReal.add_top_of_ne_bot hX).symm) le_rfl
  · rw [nval_eq_vr e hx]
    rcases eq_or_ne (nval V e (algebraMap V (FractionRing V) (φ xk))) ⊤ with ht | ht
    · rw [ht, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _), EReal.top_sub_coe]; exact le_top
    · obtain ⟨u, hu⟩ := fin_of_ne_top ht (nval_ne_bot (V := V) e _)
      rw [hu, ← EReal.coe_add, ← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      rw [hu] at h0
      have := EReal.coe_nonneg.1 h0
      linarith

/- English proof (translation)
Take `⟨xw, sw, hsw, hfws, hWv⟩` from `hW`. Establish `hrel' : fw * algebraMap A (FractionRing A) yw = algebraMap A (FractionRing A) P`. Rewrite using `[← hrel]`. Clear the denominators using the available nonvanishing facts. Establish `hxy : xw * yw = sw * P`.

Apply `IsFractionRing.injective A (FractionRing A)` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← hfws, ← hrel']`. Expand and normalize the polynomial expressions, which then agree. Establish `hxw : φ xw ≠ 0`. Introduce `h0`.

Use `congrArg φ hxy` as an intermediate fact. Rewrite `this` using `[map_mul, map_mul, h0, zero_mul]`. Conclude with `mul_ne_zero hsw hP this.symm`. Conclude with `⟨vr e (φ xw) - vr e (φ sw), by rw [hWv, nval_eq_vr e hxw, nval_eq_vr e hsw, EReal.coe_sub]⟩`.
-/
theorem w_fin {φ : A →+* V} {e : ℕ} {fw : FractionRing A} {W : EReal} (hW : ChV φ e fw W) (P yw : A)
    (hrel : fw⁻¹ * algebraMap A (FractionRing A) P = algebraMap A (FractionRing A) yw) (hfw0 : fw ≠ 0)
    (hP : φ P ≠ 0) : ∃ w : ℝ, W = (w : EReal) := by
  obtain ⟨xw, sw, hsw, hfws, hWv⟩ := hW
  have hrel' : fw * algebraMap A (FractionRing A) yw = algebraMap A (FractionRing A) P := by
    rw [← hrel]; field_simp
  have hxy : xw * yw = sw * P := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_mul, ← hfws, ← hrel']; ring
  have hxw : φ xw ≠ 0 := by
    intro h0
    have := congrArg φ hxy
    rw [map_mul, map_mul, h0, zero_mul] at this
    exact mul_ne_zero hsw hP this.symm
  exact ⟨vr e (φ xw) - vr e (φ sw), by rw [hWv, nval_eq_vr e hxw, nval_eq_vr e hsw, EReal.coe_sub]⟩

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `hδ0 : 0 < w - nu - c' * t` using `by linarith`. Establish `heOr : (0 : ℝ) < eO` using `by exact_mod_cast heO`. Take `⟨N, hN⟩` from `exists_nat_gt ((1 / eO + t) / (w - nu - c' * t))`.

Establish `hNr : (0 : ℝ) < N` using `lt_of_le_of_lt (div_nonneg (by positivity) hδ0.le) hN`. Establish `hN0 : 0 < N` using `by exact_mod_cast hNr`. Establish `h1` using `h N hN0`. Establish `hc1 : (⌈(eO : ℝ) * N * nu⌉ : ℝ) ≤ eO * N * nu + 1` using `(Int.ceil_lt_add_one _).le`. Establish `hc2 : (⌈(N : ℝ) * c'⌉₊ : ℝ) ≤ N * c' + 1` using `(Nat.ceil_lt_add_one (by positivity)).le`.

Establish `h2 : (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) ≤ N * nu + 1 / eO`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : (⌈(N : ℝ) * c'⌉₊ : ℝ) * t ≤ (N * c' + 1) * t` using `mul_le_mul_of_nonneg_right hc2 ht`. Establish `key : (N : ℝ) * (w - nu - c' * t) ≤ 1 / eO + t` using `by nlinarith`. Use `(div_lt_iff₀ hδ0).1 hN` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem limit_lam (w t nu c' : ℝ) (eO : ℕ) (heO : 0 < eO) (ht : 0 ≤ t) (hc' : 0 ≤ c')
    (h : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) + (⌈(N : ℝ) * c'⌉₊ : ℝ) * t) :
    w ≤ nu + c' * t := by
  by_contra hlt
  push Not at hlt
  have hδ0 : 0 < w - nu - c' * t := by linarith
  have heOr : (0 : ℝ) < eO := by exact_mod_cast heO
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / eO + t) / (w - nu - c' * t))
  have hNr : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by positivity) hδ0.le) hN
  have hN0 : 0 < N := by exact_mod_cast hNr
  have h1 := h N hN0
  have hc1 : (⌈(eO : ℝ) * N * nu⌉ : ℝ) ≤ eO * N * nu + 1 := (Int.ceil_lt_add_one _).le
  have hc2 : (⌈(N : ℝ) * c'⌉₊ : ℝ) ≤ N * c' + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) ≤ N * nu + 1 / eO := by
    calc (⌈(eO : ℝ) * N * nu⌉ : ℝ) * (1 / eO) ≤ (eO * N * nu + 1) * (1 / eO) :=
          mul_le_mul_of_nonneg_right hc1 (by positivity)
      _ = N * nu + 1 / eO := by field_simp
  have h3 : (⌈(N : ℝ) * c'⌉₊ : ℝ) * t ≤ (N * c' + 1) * t := mul_le_mul_of_nonneg_right hc2 ht
  have key : (N : ℝ) * (w - nu - c' * t) ≤ 1 / eO + t := by nlinarith
  have := (div_lt_iff₀ hδ0).1 hN
  linarith

/- English proof (translation)
Use `limit_lam w t 0 c' 1 one_pos ht hc' (fun N hN => by` as an intermediate fact. Use `h N hN` as an intermediate fact. Simplify using `only [mul_zero, Int.ceil_zero, Int.cast_zero, zero_mul, zero_add]`. Conclude with `this)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem limit_triv (w t c' : ℝ) (ht : 0 ≤ t) (hc' : 0 ≤ c')
    (h : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(N : ℝ) * c'⌉₊ : ℝ) * t) : w ≤ c' * t := by
  have := limit_lam w t 0 c' 1 one_pos ht hc' (fun N hN => by
    have := h N hN
    simp only [mul_zero, Int.ceil_zero, Int.cast_zero, zero_mul, zero_add]
    exact this)
  linarith

end

end GlobalTheory.Reg.TrivBound

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.TrivBound

open IsLocalRing Formalism.L2.PjFree

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Introduce `q hq`. Take `⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩` from `hQ q hq`. Establish `hx0 : x ≠ 0` using `fun h => hφx (by rw [h, map_zero])`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible S.O`. Establish `hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤`.

Establish `hm : maximalIdeal S.O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Rewrite using `[hm, Ideal.map_span, Set.image_singleton, sup_comm]`. Conclude with `hcen ϖ hϖ`. Take `⟨a', s', hs', hfs'⟩` from `transfer'' (O := S.O) (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by`. Take `⟨ioV, e', hov, -, v, hv, hChV⟩` from `S.pts j V φ ⟨x, hxE, hφx⟩`.

Conclude with `⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq`. Conclude with `chval_nonneg φ.toRingHom 1 (S.ch j F) _ (hChV a n F hF) a' s' hfs' hs'`.
-/
theorem nonneg_triv {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {a n} {F : Rul Xo c} (hF : F ∈ sec Xo c a n)
    (h0 : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) : ∀ q ∈ trivSet Xo c, 0 ≤ q F := by
  intro q hq
  obtain ⟨j, V, _, _, _, _, φ, hcen, -, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    have hm : maximalIdeal S.O = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
    exact hcen ϖ hϖ
  obtain ⟨a', s', hs', hfs'⟩ := transfer'' (O := S.O) (S.ch j F) x hx0 (fun V _ _ _ _ _ φ hφx => by
    obtain ⟨ioV, e', hov, -, v, hv, hChV⟩ := S.pts j V φ ⟨x, hxE, hφx⟩
    exact ⟨e', v F, hov.1, hChV a n F hF, h0 v hv⟩) ((maximalIdeal V).comap φ.toRingHom) hqq
  exact chval_nonneg φ.toRingHom 1 (S.ch j F) _ (hChV a n F hF) a' s' hfs' hs'

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `q hq hT`. Take `⟨kj, hkj⟩` from `hF`. Take `⟨j, V, _, _, _, _, φ, hcen, hunit, ⟨x, hxE, hφx⟩, hChV⟩` from `hQ q hq`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible S.O`. Establish `heO : 0 < S.eO` using `S.overO.1`.

Establish `hx0 : x ≠ 0` using `fun h => hφx (by rw [h, map_zero])`. Establish `hu` using `hunit ϖ hϖ`. Establish `hϖ0 : algebraMap S.O V ϖ ≠ 0` using `hu.ne_zero`. Take `⟨hfw0, hrat, hinv⟩` from `hkj j`. Take `⟨yw, tw, hyw⟩` from `hinv x hxE ϖ hϖ`.

Take `⟨ye, te, hye⟩` from `S.reg j aE nE et het x hxE ϖ hϖ`. Establish `hP : ∀ k : ℕ, φ ((algebraMap S.O (S.A j) ϖ * x) ^ k) ≠ 0` using `fun k => by`. Rewrite using `[map_pow, map_mul, AlgHom.commutes]`. Conclude with `pow_ne_zero _ (mul_ne_zero hϖ0 hφx)`. Establish `hWc` using `hChV aL nL (ws (kj j)) (hws _)`.

Establish `hTc` using `hChV aE nE et het`. Take `⟨w, hw⟩` from `w_fin hWc _ yw hyw hfw0 (hP tw)`. Take `⟨t, ht⟩` from `fin_of_ne_top hT (chval_ne_bot hTc)`. Establish `hye0 : ye ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hye` using `[map_zero]`. Establish `hPK : algebraMap (S.A j) (FractionRing (S.A j)) ((algebraMap S.O (S.A j) ϖ * x) ^ te) ≠ 0`. Introduce `h0`. Apply `hP te` to reduce the goal to its premises. Rewrite using `[IsFractionRing.injective (S.A j) (FractionRing (S.A j)) (h0.trans (map_zero _).symm), map_zero]`.

Establish `hfe0 : S.ch j et = 0` using `(mul_eq_zero.1 hye).resolve_right hPK`. Rewrite `hTc` using `[hfe0]`. Conclude with `hT (chval_zero hTc)`. Establish `ht0 : 0 ≤ t`. Use `nonneg_triv S hQ het (fun v' hv' => (hyp v' hv').1) q hq` as an intermediate fact.

Rewrite `this` using `[ht]`. Conclude with `this` after adjusting the coercions. Establish `hκ : vr 1 (algebraMap S.O V ϖ) = 0`. Unfold `vr`. Rewrite using `[vV_unit _ (fun h => (IsLocalRing.mem_maximalIdeal _).1 h hu)]`.

Simplify using the standard rewrite rules. Establish `hqq : (maximalIdeal V).comap φ.toRingHom ⊔ Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤`. Establish `hm : maximalIdeal S.O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Rewrite using `[hm, Ideal.map_span, Set.image_singleton, sup_comm]`. Conclude with `hcen ϖ hϖ`.

Establish `key : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(N : ℝ) * c'⌉₊ : ℝ) * t`. Introduce `N _`. Use `comb_core ϖ S.eO heO (S.ch j (ws (kj j))) (S.ch j et) hfw0 x hx0 ye hye0 te hye yw tw hyw nu c' N ⌈(S.eO : ℝ) * N * nu⌉ ⌈(N : ℝ) * c'⌉₊ (Int.le_ceil _) (Nat.le_ceil _) (fun V' _ _ _ _ _ φ' hφ'x => by` as an intermediate fact. Take `⟨ioV', e', hov', hϖ', v', hv', hch'⟩` from `S.pts j V' φ' ⟨x, hxE, hφ'x⟩`. Use `⟨e', v' (ws (kj j)), v' et, hov'.1, hϖ' ϖ hϖ, hch' aL nL _ (hws _), hch' aE nE et het, (hyp v' hv').1, fun hT' => ?_⟩` and prove the remaining obligations.

Use `le_trans (le_iInf fun k => ?_) ((hyp v' hv').2 hT')` and prove the remaining obligations. Take `⟨xk, hxk⟩` from `hrat k`. Establish `h2` using `hch' aL nL (ws k) (hws k)`. Rewrite `h2` using `[hxk]`. Conclude with `ratio_ge (hch' aL nL _ (hws _)) h2)`.

Use `V φ hφx hϖ0 hqq 1 w t (hw ▸ hWc) (ht ▸ hTc)`. Rewrite `this` using `[hκ, mul_zero, zero_add]`. Conclude with `this`. Establish `hlim` using `limit_triv w t c' ht0 hc' key`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem comb_triv {la : HeightOneSpectrum (𝓞 c.F)}
    (S : SCharts Xo c la) (hQ : S.CovQ) {m : ℕ} (ws : Fin m → Rul Xo c) (hF : S.FamW ws)
    {aL nL} (hws : ∀ k, ws k ∈ sec Xo c aL nL)
    {aE nE} {et : Rul Xo c} (het : et ∈ sec Xo c aE nE)
    (nu c' : ℝ) (hc' : 0 ≤ c')
    (hyp : ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v et ∧
      (v et ≠ ⊤ → (⨅ k, v (ws k)) ≤ (nu : EReal) + (c' : EReal) * v et)) :
    ∀ q ∈ trivSet Xo c, q et ≠ ⊤ → (⨅ k, q (ws k)) ≤ (c' : EReal) * q et := by
  intro q hq hT
  obtain ⟨kj, hkj⟩ := hF
  obtain ⟨j, V, _, _, _, _, φ, hcen, hunit, ⟨x, hxE, hφx⟩, hChV⟩ := hQ q hq
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S.O
  have heO : 0 < S.eO := S.overO.1
  have hx0 : x ≠ 0 := fun h => hφx (by rw [h, map_zero])
  have hu := hunit ϖ hϖ
  have hϖ0 : algebraMap S.O V ϖ ≠ 0 := hu.ne_zero
  obtain ⟨hfw0, hrat, hinv⟩ := hkj j
  obtain ⟨yw, tw, hyw⟩ := hinv x hxE ϖ hϖ
  obtain ⟨ye, te, hye⟩ := S.reg j aE nE et het x hxE ϖ hϖ
  have hP : ∀ k : ℕ, φ ((algebraMap S.O (S.A j) ϖ * x) ^ k) ≠ 0 := fun k => by
    rw [map_pow, map_mul, AlgHom.commutes]; exact pow_ne_zero _ (mul_ne_zero hϖ0 hφx)
  have hWc := hChV aL nL (ws (kj j)) (hws _)
  have hTc := hChV aE nE et het
  obtain ⟨w, hw⟩ := w_fin hWc _ yw hyw hfw0 (hP tw)
  obtain ⟨t, ht⟩ := fin_of_ne_top hT (chval_ne_bot hTc)
  have hye0 : ye ≠ 0 := by
    rintro rfl
    rw [map_zero] at hye
    have hPK : algebraMap (S.A j) (FractionRing (S.A j)) ((algebraMap S.O (S.A j) ϖ * x) ^ te) ≠ 0 := by
      intro h0
      apply hP te
      rw [IsFractionRing.injective (S.A j) (FractionRing (S.A j)) (h0.trans (map_zero _).symm), map_zero]
    have hfe0 : S.ch j et = 0 := (mul_eq_zero.1 hye).resolve_right hPK
    rw [hfe0] at hTc
    exact hT (chval_zero hTc)
  have ht0 : 0 ≤ t := by
    have := nonneg_triv S hQ het (fun v' hv' => (hyp v' hv').1) q hq
    rw [ht] at this
    exact_mod_cast this
  have hκ : vr 1 (algebraMap S.O V ϖ) = 0 := by
    unfold vr
    rw [vV_unit _ (fun h => (IsLocalRing.mem_maximalIdeal _).1 h hu)]
    simp
  have hqq : (maximalIdeal V).comap φ.toRingHom ⊔
      Ideal.map (algebraMap S.O (S.A j)) (maximalIdeal S.O) ≠ ⊤ := by
    have hm : maximalIdeal S.O = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    rw [hm, Ideal.map_span, Set.image_singleton, sup_comm]
    exact hcen ϖ hϖ
  have key : ∀ N : ℕ, 0 < N → (N : ℝ) * w ≤ (⌈(N : ℝ) * c'⌉₊ : ℝ) * t := by
    intro N _
    have := comb_core ϖ S.eO heO (S.ch j (ws (kj j))) (S.ch j et) hfw0 x hx0 ye hye0 te hye yw tw hyw
      nu c' N ⌈(S.eO : ℝ) * N * nu⌉ ⌈(N : ℝ) * c'⌉₊ (Int.le_ceil _) (Nat.le_ceil _)
      (fun V' _ _ _ _ _ φ' hφ'x => by
        obtain ⟨ioV', e', hov', hϖ', v', hv', hch'⟩ := S.pts j V' φ' ⟨x, hxE, hφ'x⟩
        refine ⟨e', v' (ws (kj j)), v' et, hov'.1, hϖ' ϖ hϖ, hch' aL nL _ (hws _),
          hch' aE nE et het, (hyp v' hv').1, fun hT' => ?_⟩
        refine le_trans (le_iInf fun k => ?_) ((hyp v' hv').2 hT')
        obtain ⟨xk, hxk⟩ := hrat k
        have h2 := hch' aL nL (ws k) (hws k)
        rw [hxk] at h2
        exact ratio_ge (hch' aL nL _ (hws _)) h2)
      V φ hφx hϖ0 hqq 1 w t (hw ▸ hWc) (ht ▸ hTc)
    rw [hκ, mul_zero, zero_add] at this
    exact this
  have hlim := limit_triv w t c' ht0 hc' key
  calc (⨅ k, q (ws k)) ≤ q (ws (kj j)) := iInf_le _ _
    _ = (w : EReal) := hw
    _ ≤ ((c' * t : ℝ) : EReal) := EReal.coe_le_coe_iff.2 hlim
    _ = (c' : EReal) * q et := by rw [ht, EReal.coe_mul]

/- English proof (translation)
Use `⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `q.triv a ha`. Rewrite using `[← hu]`. Conclude with `vV_unit (u : q.T.V) (fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit)`.
-/
theorem ordQ_mem_trivSet (q : QPt Xo c) : ordQ Xo c q ∈ trivSet Xo c := by
  refine ⟨q.T, q.ι, q.y, fun a ha => ?_, rfl⟩
  obtain ⟨u, hu⟩ := q.triv a ha
  rw [← hu]
  exact vV_unit (u : q.T.V) (fun h => (IsLocalRing.mem_maximalIdeal _).1 h u.isUnit)

end

end GlobalTheory.Reg.TrivBound

namespace GlobalTheory.Reg

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hS hN C hC aL nL aE nE k ws et c' hc' hws het ⟨la, nu, hyp⟩ q`. Establish `hws' : ∀ i, ws i ∈ sec Xo c aL nL` using `fun i => hC _ _ (hws i)`. Establish `het' : et ∈ sec Xo c aE nE` using `hC _ _ het`. Take `⟨S, hF, hQ⟩` from `(hS la).2 aL nL k ws hws' (hN la aL nL k ws hws' fun v hv => (hyp v hv).2.1)`. Conclude with `⟨TrivBound.nonneg_triv S hQ het' (fun v hv => (hyp v hv).1) _ (TrivBound.ordQ_mem_trivSet q), TrivBound.comb_triv S hQ ws hF hws' het' nu c' hc' (fun v hv => ⟨(hyp v hv).1, (hyp v hv).2.2⟩) _ (TrivBound.ordQ_mem_trivSet q)⟩`.
-/
theorem combined_bound_at_trivial_valuations_of_charts :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ la : HeightOneSpectrum (𝓞 c.F), (∃ S : SCharts Xo c la, S.CovQ) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → Formalism.L2.PjFree.NoCommonZero Xo c ws → ∃ S : SCharts Xo c la, S.FamW ws ∧ S.CovQ) → (∀ (la : HeightOneSpectrum (𝓞 c.F)) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ sec Xo c a n) → (∀ v ∈ Formalism.L2.PjFree.valSet Xo c (Formalism.L2.PjFree.algCls Xo c) la, ∃ i, v (ws i) ≠ ⊤) → Formalism.L2.PjFree.NoCommonZero Xo c ws) → ∀ C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c), (∀ a n, C a n ≤ sec Xo c a n) → Formalism.L2.PjFree.RegularityR2Quotient Xo c C := by
  intro E _ _ _ H Dw l Xo c hS hN C hC aL nL aE nE k ws et c' hc' hws het ⟨la, nu, hyp⟩ q
  have hws' : ∀ i, ws i ∈ sec Xo c aL nL := fun i => hC _ _ (hws i)
  have het' : et ∈ sec Xo c aE nE := hC _ _ het
  obtain ⟨S, hF, hQ⟩ := (hS la).2 aL nL k ws hws' (hN la aL nL k ws hws' fun v hv => (hyp v hv).2.1)
  exact ⟨TrivBound.nonneg_triv S hQ het' (fun v hv => (hyp v hv).1) _ (TrivBound.ordQ_mem_trivSet q),
    TrivBound.comb_triv S hQ ws hF hws' het' nu c' hc' (fun v hv => ⟨(hyp v hv).1, (hyp v hv).2.2⟩) _
      (TrivBound.ordQ_mem_trivSet q)⟩

end GlobalTheory.Reg
