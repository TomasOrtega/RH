import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.TorsionIntegral

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.weierstrass_uniformisation.2.1 L`. Take `⟨h1, e1⟩` from `he w hw`. Take `⟨h2', e2⟩` from `he _ h2`. Establish `hy : L.derivWeierstrassP w ≠ 0` using `fun h => h2 ((GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).1 h)`. Establish `hne : L.derivWeierstrassP w / 2 ≠ (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP w) (L.derivWeierstrassP w / 2)`.

Simplify using `[GlobalTheory.latticeCurve]`. Introduce `h`. Apply `hy` to reduce the goal to its premises. Take the linear combination `h`. Rewrite `e2` using `[QuotientAddGroup.mk_add, map_add, e1, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne]`.

Establish `e3` using `(WeierstrassCurve.Affine.Point.some.inj e2).1`. Rewrite `e3` using `[WeierstrassCurve.Affine.slope_of_Y_ne rfl hne]`. Simplify using `[GlobalTheory.latticeCurve] at e3`. Establish `hsq` using `L.derivWeierstrassP_sq w hw`. Rewrite using `[← e3, ← hsq]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hsq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dbl (L : PeriodPair) {w : ℂ} (hw : w ∉ L.lattice) (h2 : w + w ∉ L.lattice) :
    L.weierstrassP (w + w) * (4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) =
      (L.weierstrassP w ^ 2 + L.g₂ / 4) ^ 2 + 2 * L.g₃ * L.weierstrassP w := by
  obtain ⟨e, he⟩ := GlobalTheory.weierstrass_uniformisation.2.1 L
  obtain ⟨h1, e1⟩ := he w hw
  obtain ⟨h2', e2⟩ := he _ h2
  have hy : L.derivWeierstrassP w ≠ 0 := fun h => h2 ((GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).1 h)
  have hne : L.derivWeierstrassP w / 2 ≠
      (GlobalTheory.latticeCurve L).toAffine.negY (L.weierstrassP w) (L.derivWeierstrassP w / 2) := by
    simp [GlobalTheory.latticeCurve]
    intro h; apply hy; linear_combination h
  rw [QuotientAddGroup.mk_add, map_add, e1, WeierstrassCurve.Affine.Point.add_self_of_Y_ne hne] at e2
  have e3 := (WeierstrassCurve.Affine.Point.some.inj e2).1
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hne] at e3
  simp [GlobalTheory.latticeCurve] at e3
  have hsq := L.derivWeierstrassP_sq w hw
  rw [← e3, ← hsq]
  field_simp
  rw [hsq]
  ring

/- English proof (translation)
Establish `h` using `(GlobalTheory.weierstrass_uniformisation.1 L).isUnit.ne_zero`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Simplify using `[GlobalTheory.latticeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]`. Take the linear combination `h0`.
-/
theorem disc (L : PeriodPair) : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
  have h := (GlobalTheory.weierstrass_uniformisation.1 L).isUnit.ne_zero
  intro h0
  apply h
  simp [GlobalTheory.latticeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination h0

/- English proof (translation)
Establish `h3` using `(GlobalTheory.weierstrassP_add L hz hw hne).1`. Establish `hw' : -w ∉ L.lattice` using `fun h => hw (by simpa using neg_mem h)`. Establish `h4` using `(GlobalTheory.weierstrassP_add L hz hw' (by rwa [L.weierstrassP_neg])).1`. Rewrite `h4` using `[L.weierstrassP_neg, L.derivWeierstrassP_neg, ← sub_eq_add_neg]`. Establish `s1` using `L.derivWeierstrassP_sq z hz`.

Establish `s2` using `L.derivWeierstrassP_sq w hw`. Establish `hd : L.weierstrassP z - L.weierstrassP w ≠ 0` using `sub_ne_zero.2 hne`. Generalize the expression as in `L.weierstrassP (z + w) = x3 at *`. Generalize the expression as in `L.weierstrassP (z - w) = x4 at *`. Generalize the expression as in `L.weierstrassP z = x1 at *`.

Generalize the expression as in `L.weierstrassP w = x2 at *`. Generalize the expression as in `L.derivWeierstrassP z = y1 at *`. Generalize the expression as in `L.derivWeierstrassP w = y2 at *`. Establish `a3 : x3 * (x1 - x2) ^ 2 = (y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2) - y1 * y2 / 2`. Rewrite using `[h3]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `a4 : x4 * (x1 - x2) ^ 2 = (y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2) + y1 * y2 / 2`. Rewrite using `[h4]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Prove the components needed by the constructor for the conclusion. Take the linear combination `a3 + a4 + s1 / 2 + s2 / 2`. Apply `mul_right_cancel₀ (pow_ne_zero 2 hd)` to reduce the goal to its premises. Establish `: (x3 * (x1 - x2) ^ 2) * (x4 * (x1 - x2) ^ 2) = ((y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2)) ^ 2 - y1 ^ 2 * y2 ^ 2 / 4`.

Rewrite using `[a3, a4]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `this` using `[s1, s2]`. Take the linear combination `this`.
-/
theorem sum_prod (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hne : L.weierstrassP z ≠ L.weierstrassP w) :
    (L.weierstrassP (z + w) + L.weierstrassP (z - w)) * (L.weierstrassP z - L.weierstrassP w) ^ 2 =
      2 * L.weierstrassP z * L.weierstrassP w * (L.weierstrassP z + L.weierstrassP w)
        - L.g₂ / 2 * (L.weierstrassP z + L.weierstrassP w) - L.g₃ ∧
    L.weierstrassP (z + w) * L.weierstrassP (z - w) * (L.weierstrassP z - L.weierstrassP w) ^ 2 =
      (L.weierstrassP z * L.weierstrassP w + L.g₂ / 4) ^ 2
        + L.g₃ * (L.weierstrassP z + L.weierstrassP w) := by
  have h3 := (GlobalTheory.weierstrassP_add L hz hw hne).1
  have hw' : -w ∉ L.lattice := fun h => hw (by simpa using neg_mem h)
  have h4 := (GlobalTheory.weierstrassP_add L hz hw' (by rwa [L.weierstrassP_neg])).1
  rw [L.weierstrassP_neg, L.derivWeierstrassP_neg, ← sub_eq_add_neg] at h4
  have s1 := L.derivWeierstrassP_sq z hz
  have s2 := L.derivWeierstrassP_sq w hw
  have hd : L.weierstrassP z - L.weierstrassP w ≠ 0 := sub_ne_zero.2 hne
  generalize L.weierstrassP (z + w) = x3 at *
  generalize L.weierstrassP (z - w) = x4 at *
  generalize L.weierstrassP z = x1 at *
  generalize L.weierstrassP w = x2 at *
  generalize L.derivWeierstrassP z = y1 at *
  generalize L.derivWeierstrassP w = y2 at *
  have a3 : x3 * (x1 - x2) ^ 2 = (y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2) - y1 * y2 / 2 := by
    rw [h3]; field_simp; ring
  have a4 : x4 * (x1 - x2) ^ 2 = (y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2) + y1 * y2 / 2 := by
    rw [h4]; field_simp; ring
  constructor
  · linear_combination a3 + a4 + s1 / 2 + s2 / 2
  · apply mul_right_cancel₀ (pow_ne_zero 2 hd)
    have : (x3 * (x1 - x2) ^ 2) * (x4 * (x1 - x2) ^ 2) =
        ((y1 ^ 2 + y2 ^ 2) / 4 - (x1 - x2) ^ 2 * (x1 + x2)) ^ 2 - y1 ^ 2 * y2 ^ 2 / 4 := by
      rw [a3, a4]; ring
    rw [s1, s2] at this
    linear_combination this

def IsRecip (L : PeriodPair) (z s : ℂ) : Prop :=
  (z ∈ L.lattice ∧ s = 0) ∨ (z ∉ L.lattice ∧ L.weierstrassP z * s = 1)

/- English proof (translation)
Establish `h` using `dbl L hw h2`. Establish `hx : L.weierstrassP w ≠ 0` using `left_ne_zero_of_mul_eq_one hs`. Take `rfl : s = (L.weierstrassP w)⁻¹` from `eq_inv_of_mul_eq_one_right hs`. Generalize the expression as in `L.weierstrassP (w + w) = y at *`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `32 * h`.
-/
theorem dbl_recip (L : PeriodPair) {w s : ℂ} (hw : w ∉ L.lattice) (hs : L.weierstrassP w * s = 1)
    (h2 : w + w ∉ L.lattice) :
    L.weierstrassP (w + w) * (2 * (s + s) - L.g₂ / 2 * s * s * (s + s) - L.g₃ * s ^ 2 * s ^ 2) =
      (1 + L.g₂ / 4 * s * s) ^ 2 + L.g₃ * s * s * (s + s) := by
  have h := dbl L hw h2
  have hx : L.weierstrassP w ≠ 0 := left_ne_zero_of_mul_eq_one hs
  obtain rfl : s = (L.weierstrassP w)⁻¹ := eq_inv_of_mul_eq_one_right hs
  generalize L.weierstrassP (w + w) = y at *
  field_simp
  linear_combination 32 * h

/- English proof (translation)
Establish `hx2 : L.weierstrassP w ≠ 0` using `left_ne_zero_of_mul_eq_one h2`. Break down `h1 with ⟨hz, rfl⟩ | ⟨hz, h1⟩` into its components or cases. Establish `a : z + w ∉ L.lattice` using `fun h => hw (by simpa using sub_mem h hz)`. Establish `b : z - w ∉ L.lattice` using `fun h => hw (by simpa using sub_mem hz h)`. Establish `c : L.weierstrassP (z + w) = L.weierstrassP w` using `(GlobalTheory.weierstrassP_eq_iff L a hw).2 (Or.inl (by simpa using hz))`.

Establish `d : L.weierstrassP (z - w) = L.weierstrassP w` using `(GlobalTheory.weierstrassP_eq_iff L b hw).2 (Or.inr (by simpa using hz))`. Break down `h4 with h4 | h4` into its components or cases. Conclude with `absurd h4.1 b`. Use `Or.inr ⟨a, ?_⟩` and prove the remaining obligations. Rewrite `h4` using `[d]`.

Rewrite using `[c]`. Simplify using `only [mul_zero, zero_mul, add_zero, zero_add, one_pow, div_one, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]`. Take the linear combination `2 * h2 - h4.2`. Establish `hx1 : L.weierstrassP z ≠ 0` using `left_ne_zero_of_mul_eq_one h1`. Distinguish the cases in `hne : L.weierstrassP z = L.weierstrassP w`.

Establish `hs : s1 = s2`. Rewrite `h1` using `[hne]`. Conclude with `mul_left_cancel₀ hx2 (h1.trans h2.symm)`. Substitute `hs` using the available equality. Distinguish the cases in `hm : z - w ∈ L.lattice`.

Establish `h40 : s4 = 0`. Break down `h4 with h4 | h4` into its components or cases. Conclude with `h4.2`. Conclude with `absurd hm h4.1`. Substitute `h40` using the available equality.

Distinguish the cases in `hww : w + w ∈ L.lattice`. Use `Or.inl ⟨by simpa [sub_add_add_cancel, add_assoc] using add_mem hm hww, ?_⟩` and prove the remaining obligations. Establish `hy` using `(GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).2 hww`. Establish `hsq` using `L.derivWeierstrassP_sq w hw`. Rewrite `hsq` using `[hy]`.

Rewrite using `[sub_zero, div_eq_zero_iff]`. Use `left`. Take `rfl : s1 = (L.weierstrassP w)⁻¹` from `eq_inv_of_mul_eq_one_right h2`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-2 * hsq`.

Establish `a : z + w ∉ L.lattice` using `fun h => hww (by`. Use `sub_mem h hm` as an intermediate fact. Rewrite using `[show z + w - (z - w) = w + w by ring] at this)` and apply the resulting hypothesis. Establish `c : L.weierstrassP (z + w) = L.weierstrassP (w + w)` using `(GlobalTheory.weierstrassP_eq_iff L a hww).2 (Or.inl (by simpa using hm))`. Use `Or.inr ⟨a, ?_⟩` and prove the remaining obligations.

Rewrite using `[c, sub_zero, ← mul_div_assoc, dbl_recip L hw h2 hww, div_self hD]`. Establish `hp : z + w ∈ L.lattice` using `((GlobalTheory.weierstrassP_eq_iff L hz hw).1 hne).resolve_left hm`. Establish `hww : w + w ∉ L.lattice` using `fun h => hm (by`. Use `sub_mem hp h` as an intermediate fact. Rewrite using `[show z + w - (w + w) = z - w by ring] at this)` and apply the resulting hypothesis.

Establish `c : L.weierstrassP (z - w) = L.weierstrassP (w + w)` using `(GlobalTheory.weierstrassP_eq_iff L hm hww).2 (Or.inr (by`. Rewrite using `[show z - w + (w + w) = z + w by ring]))` and apply the resulting hypothesis. Establish `h4'` using `(h4.resolve_left (fun h => hm h.1)).2`. Rewrite `h4'` using `[c]`. Use `Or.inl ⟨hp, ?_⟩` and prove the remaining obligations.

Rewrite using `[sub_eq_zero, div_eq_iff hD, ← dbl_recip L hw h2 hww]`. Take the linear combination `(-(2 * (s1 + s1) - L.g₂ / 2 * s1 * s1 * (s1 + s1) - L.g₃ * s1 ^ 2 * s1 ^ 2)) * h4'`. Establish `hn` using `mt (GlobalTheory.weierstrassP_eq_iff L hz hw).2 hne`. Rewrite `hn` using `[not_or]`. Establish `h4'` using `(h4.resolve_left (fun h => hn.1 h.1)).2`.

Take `⟨hs, hp⟩` from `sum_prod L hz hw hne`. Use `Or.inr ⟨hn.2, ?_⟩` and prove the remaining obligations. Generalize the expression as in `L.weierstrassP (z + w) = x3 at *`. Generalize the expression as in `L.weierstrassP (z - w) = x4 at *`. Generalize the expression as in `L.weierstrassP z = x1 at *`.

Generalize the expression as in `L.weierstrassP w = x2 at *`. Establish `eN : 2 * (s1 + s2) - L.g₂ / 2 * s1 * s2 * (s1 + s2) - L.g₃ * s1 ^ 2 * s2 ^ 2 = (x3 + x4) * ((x1 - x2) ^ 2 * s1 ^ 2 * s2 ^ 2)`. Take `rfl : s1 = x1⁻¹` from `eq_inv_of_mul_eq_one_right h1`. Take `rfl : s2 = x2⁻¹` from `eq_inv_of_mul_eq_one_right h2`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-2 * hs`. Establish `eD : (1 + L.g₂ / 4 * s1 * s2) ^ 2 + L.g₃ * s1 * s2 * (s1 + s2) = (x3 * x4) * ((x1 - x2) ^ 2 * s1 ^ 2 * s2 ^ 2)`. Take `rfl : s1 = x1⁻¹` from `eq_inv_of_mul_eq_one_right h1`. Take `rfl : s2 = x2⁻¹` from `eq_inv_of_mul_eq_one_right h2`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-16 * hp`. Rewrite `hD` using `[eD]`. Rewrite using `[eN, eD, mul_div_mul_right _ _ (right_ne_zero_of_mul hD)]`. Establish `h34` using `left_ne_zero_of_mul hD`. Establish `hx3` using `left_ne_zero_of_mul h34`.

Establish `hx4` using `right_ne_zero_of_mul h34`. Take `rfl : s4 = x4⁻¹` from `eq_inv_of_mul_eq_one_right h4'`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem recip_add (L : PeriodPair) {z w s1 s2 s4 : ℂ} (h1 : IsRecip L z s1)
    (hw : w ∉ L.lattice) (h2 : L.weierstrassP w * s2 = 1) (h4 : IsRecip L (z - w) s4)
    (hD : (1 + L.g₂ / 4 * s1 * s2) ^ 2 + L.g₃ * s1 * s2 * (s1 + s2) ≠ 0) :
    IsRecip L (z + w) ((2 * (s1 + s2) - L.g₂ / 2 * s1 * s2 * (s1 + s2) - L.g₃ * s1 ^ 2 * s2 ^ 2) /
      ((1 + L.g₂ / 4 * s1 * s2) ^ 2 + L.g₃ * s1 * s2 * (s1 + s2)) - s4) := by
  have hx2 : L.weierstrassP w ≠ 0 := left_ne_zero_of_mul_eq_one h2
  rcases h1 with ⟨hz, rfl⟩ | ⟨hz, h1⟩
  · have a : z + w ∉ L.lattice := fun h => hw (by simpa using sub_mem h hz)
    have b : z - w ∉ L.lattice := fun h => hw (by simpa using sub_mem hz h)
    have c : L.weierstrassP (z + w) = L.weierstrassP w :=
      (GlobalTheory.weierstrassP_eq_iff L a hw).2 (Or.inl (by simpa using hz))
    have d : L.weierstrassP (z - w) = L.weierstrassP w :=
      (GlobalTheory.weierstrassP_eq_iff L b hw).2 (Or.inr (by simpa using hz))
    rcases h4 with h4 | h4
    · exact absurd h4.1 b
    · refine Or.inr ⟨a, ?_⟩
      rw [d] at h4
      rw [c]
      simp only [mul_zero, zero_mul, add_zero, zero_add, one_pow, div_one, sub_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      linear_combination 2 * h2 - h4.2
  have hx1 : L.weierstrassP z ≠ 0 := left_ne_zero_of_mul_eq_one h1
  by_cases hne : L.weierstrassP z = L.weierstrassP w
  · have hs : s1 = s2 := by
      rw [hne] at h1; exact mul_left_cancel₀ hx2 (h1.trans h2.symm)
    subst hs
    by_cases hm : z - w ∈ L.lattice
    · have h40 : s4 = 0 := by
        rcases h4 with h4 | h4
        · exact h4.2
        · exact absurd hm h4.1
      subst h40
      by_cases hww : w + w ∈ L.lattice
      · refine Or.inl ⟨by simpa [sub_add_add_cancel, add_assoc] using add_mem hm hww, ?_⟩
        have hy := (GlobalTheory.derivWeierstrassP_eq_zero_iff L hw).2 hww
        have hsq := L.derivWeierstrassP_sq w hw
        rw [hy] at hsq
        rw [sub_zero, div_eq_zero_iff]
        left
        obtain rfl : s1 = (L.weierstrassP w)⁻¹ := eq_inv_of_mul_eq_one_right h2
        field_simp
        linear_combination -2 * hsq
      · have a : z + w ∉ L.lattice := fun h => hww (by
          have := sub_mem h hm
          rwa [show z + w - (z - w) = w + w by ring] at this)
        have c : L.weierstrassP (z + w) = L.weierstrassP (w + w) :=
          (GlobalTheory.weierstrassP_eq_iff L a hww).2 (Or.inl (by simpa using hm))
        refine Or.inr ⟨a, ?_⟩
        rw [c, sub_zero, ← mul_div_assoc, dbl_recip L hw h2 hww, div_self hD]
    · have hp : z + w ∈ L.lattice := ((GlobalTheory.weierstrassP_eq_iff L hz hw).1 hne).resolve_left hm
      have hww : w + w ∉ L.lattice := fun h => hm (by
          have := sub_mem hp h
          rwa [show z + w - (w + w) = z - w by ring] at this)
      have c : L.weierstrassP (z - w) = L.weierstrassP (w + w) :=
        (GlobalTheory.weierstrassP_eq_iff L hm hww).2 (Or.inr (by
          rwa [show z - w + (w + w) = z + w by ring]))
      have h4' := (h4.resolve_left (fun h => hm h.1)).2
      rw [c] at h4'
      refine Or.inl ⟨hp, ?_⟩
      rw [sub_eq_zero, div_eq_iff hD, ← dbl_recip L hw h2 hww]
      linear_combination (-(2 * (s1 + s1) - L.g₂ / 2 * s1 * s1 * (s1 + s1) - L.g₃ * s1 ^ 2 * s1 ^ 2)) * h4'
  · have hn := mt (GlobalTheory.weierstrassP_eq_iff L hz hw).2 hne
    rw [not_or] at hn
    have h4' := (h4.resolve_left (fun h => hn.1 h.1)).2
    obtain ⟨hs, hp⟩ := sum_prod L hz hw hne
    refine Or.inr ⟨hn.2, ?_⟩
    generalize L.weierstrassP (z + w) = x3 at *
    generalize L.weierstrassP (z - w) = x4 at *
    generalize L.weierstrassP z = x1 at *
    generalize L.weierstrassP w = x2 at *
    have eN : 2 * (s1 + s2) - L.g₂ / 2 * s1 * s2 * (s1 + s2) - L.g₃ * s1 ^ 2 * s2 ^ 2 =
        (x3 + x4) * ((x1 - x2) ^ 2 * s1 ^ 2 * s2 ^ 2) := by
      obtain rfl : s1 = x1⁻¹ := eq_inv_of_mul_eq_one_right h1
      obtain rfl : s2 = x2⁻¹ := eq_inv_of_mul_eq_one_right h2
      field_simp
      linear_combination -2 * hs
    have eD : (1 + L.g₂ / 4 * s1 * s2) ^ 2 + L.g₃ * s1 * s2 * (s1 + s2) =
        (x3 * x4) * ((x1 - x2) ^ 2 * s1 ^ 2 * s2 ^ 2) := by
      obtain rfl : s1 = x1⁻¹ := eq_inv_of_mul_eq_one_right h1
      obtain rfl : s2 = x2⁻¹ := eq_inv_of_mul_eq_one_right h2
      field_simp
      linear_combination -16 * hp
    rw [eD] at hD
    rw [eN, eD, mul_div_mul_right _ _ (right_ne_zero_of_mul hD)]
    have h34 := left_ne_zero_of_mul hD
    have hx3 := left_ne_zero_of_mul h34
    have hx4 := right_ne_zero_of_mul h34
    obtain rfl : s4 = x4⁻¹ := eq_inv_of_mul_eq_one_right h4'
    field_simp
    ring

open IsLocalRing in
/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Conclude with `⟨⟨0, by simp, Or.inl (by simp)⟩, ⟨1, by simp, Or.inr (by simpa using ⟨ht, hs⟩)⟩⟩`. Consider the case `succ k ih`. Take `⟨⟨b, hb, rb⟩, ⟨a, ha, ra⟩⟩` from `ih`.

Use `⟨⟨a, ha, ra⟩, ?_⟩` and prove the remaining obligations. Set `h : W` to `⟨2⁻¹, h2⟩`. Set `g2 : W` to `⟨L.g₂, hg2⟩`. Set `g3 : W` to `⟨L.g₃, hg3⟩`. Set `D : W` to `(1 + g2 * h ^ 2 * a * s ^ 2) ^ 2 + g3 * a * s ^ 3 * (a + 1)`.

Set `N : W` to `2 * (a + 1) - g2 * h * a * s ^ 2 * (a + 1) - g3 * a ^ 2 * s ^ 3`. Establish `hD1 : residue W D = 1` using `by simp [D, hs0]`. Establish `hN1 : residue W N = 2 * (residue W a + 1)` using `by simp [N, hs0, map_ofNat]`. Establish `hDu : IsUnit D` using `(residue_ne_zero_iff_isUnit D).1 (by rw [hD1]; exact one_ne_zero)`. Take `⟨d, hd⟩` from `hDu.exists_right_inv`.

Establish `hd1 : residue W d = 1`. Use `congrArg (residue W) hd` as an intermediate fact. Rewrite `this` using `[map_mul, hD1, one_mul, map_one]`. Then use the resulting hypothesis. Establish `hdC : (D : ℂ) * d = 1` using `by exact_mod_cast congrArg (fun x : W => (x : ℂ)) hd`. Establish `eD : (1 + L.g₂ / 4 * (a * s) * s) ^ 2 + L.g₃ * (a * s) * s * (a * s + s) = (D : ℂ)`.

Simplify using `[D, h, g2, g3]`. Expand and normalize the polynomial expressions, which then agree. Establish `eN : 2 * (a * s + s) - L.g₂ / 2 * (a * s) * s * (a * s + s) - L.g₃ * (a * s) ^ 2 * s ^ 2 = (N : ℂ) * s`. Establish `: ((2 : W) : ℂ) = 2` using `rfl`. Simplify using `[N, h, g2, g3, this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hD0 : (D : ℂ) ≠ 0` using `left_ne_zero_of_mul_eq_one hdC`. Establish `key` using `recip_add L (s4 := b * s) ra ht hs (by rwa [show ((k + 1 : ℕ) : ℂ) * t - t = k * t by push_cast; ring]) (by rw [eD]; exact hD0)`. Rewrite `key` using `[eD, eN]`. Use `⟨N * d - b, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, map_mul, hN1, hd1, ha, hb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `key using 1` and compare the differences between its conclusion and the goal. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right hdC]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem multiples (L : PeriodPair) (W : ValuationSubring ℂ) (h2 : (2 : ℂ)⁻¹ ∈ W)
    (hg2 : L.g₂ ∈ W) (hg3 : L.g₃ ∈ W) {t : ℂ} (ht : t ∉ L.lattice) (s : W)
    (hs : L.weierstrassP t * s = 1) (hs0 : residue W s = 0) (k : ℕ) :
    (∃ a : W, residue W a = (k : ResidueField W) ^ 2 ∧ IsRecip L (k * t) (a * s)) ∧
    (∃ a : W, residue W a = ((k + 1 : ℕ) : ResidueField W) ^ 2 ∧
      IsRecip L ((k + 1 : ℕ) * t) (a * s)) := by
  induction k with
  | zero =>
    exact ⟨⟨0, by simp, Or.inl (by simp)⟩, ⟨1, by simp, Or.inr (by simpa using ⟨ht, hs⟩)⟩⟩
  | succ k ih =>
    obtain ⟨⟨b, hb, rb⟩, ⟨a, ha, ra⟩⟩ := ih
    refine ⟨⟨a, ha, ra⟩, ?_⟩
    let h : W := ⟨2⁻¹, h2⟩
    let g2 : W := ⟨L.g₂, hg2⟩
    let g3 : W := ⟨L.g₃, hg3⟩
    let D : W := (1 + g2 * h ^ 2 * a * s ^ 2) ^ 2 + g3 * a * s ^ 3 * (a + 1)
    let N : W := 2 * (a + 1) - g2 * h * a * s ^ 2 * (a + 1) - g3 * a ^ 2 * s ^ 3
    have hD1 : residue W D = 1 := by simp [D, hs0]
    have hN1 : residue W N = 2 * (residue W a + 1) := by simp [N, hs0, map_ofNat]
    have hDu : IsUnit D := (residue_ne_zero_iff_isUnit D).1 (by rw [hD1]; exact one_ne_zero)
    obtain ⟨d, hd⟩ := hDu.exists_right_inv
    have hd1 : residue W d = 1 := by
      have := congrArg (residue W) hd
      rwa [map_mul, hD1, one_mul, map_one] at this
    have hdC : (D : ℂ) * d = 1 := by exact_mod_cast congrArg (fun x : W => (x : ℂ)) hd
    have eD : (1 + L.g₂ / 4 * (a * s) * s) ^ 2 + L.g₃ * (a * s) * s * (a * s + s) = (D : ℂ) := by
      simp [D, h, g2, g3]; ring
    have eN : 2 * (a * s + s) - L.g₂ / 2 * (a * s) * s * (a * s + s) - L.g₃ * (a * s) ^ 2 * s ^ 2 =
        (N : ℂ) * s := by
      have : ((2 : W) : ℂ) = 2 := rfl
      simp [N, h, g2, g3, this]; ring
    have hD0 : (D : ℂ) ≠ 0 := left_ne_zero_of_mul_eq_one hdC
    have key := recip_add L (s4 := b * s) ra ht hs
      (by rwa [show ((k + 1 : ℕ) : ℂ) * t - t = k * t by push_cast; ring]) (by rw [eD]; exact hD0)
    rw [eD, eN] at key
    refine ⟨N * d - b, ?_, ?_⟩
    · rw [map_sub, map_mul, hN1, hd1, ha, hb]; push_cast; ring
    · convert key using 1
      · push_cast; ring
      · rw [div_eq_mul_inv, ← eq_inv_of_mul_eq_one_right hdC]; push_cast; ring

open IsLocalRing in
/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hx0 : L.weierstrassP t ≠ 0` using `fun h => hx (h ▸ W.zero_mem)`. Take `⟨hs, hs0⟩` from `ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1 ((W.inv_mem_nonunits_iff).2 (Or.inr hx))`. Take `⟨a, ha, ra⟩` from `(multiples L W h2 hg2 hg3 ht ⟨_, hs⟩ (mul_inv_cancel₀ hx0) ((residue_eq_zero_iff _).2 hs0) m).1`. Establish `h0` using `(ra.resolve_right (fun h => h.1 hmt)).2`.

Establish `ha0 : a = 0`. Simplify `h0` using `[hx0]`. Establish `hu : (m : W) * ⟨_, hm⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hm0]`.

Use `congrArg (residue W) hu` as an intermediate fact. Rewrite `ha` using `[ha0, map_zero]`. Rewrite `this` using `[map_mul, map_natCast, pow_eq_zero_iff two_ne_zero |>.1 ha.symm, zero_mul, map_one]`. Conclude with `zero_ne_one this`.
-/
theorem integral (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ) (h2 : (2 : ℂ)⁻¹ ∈ W)
    (hg2 : L.g₂ ∈ W) (hg3 : L.g₃ ∈ W) (hm0 : m ≠ 0) (hm : (m : ℂ)⁻¹ ∈ W) {t : ℂ}
    (hmt : (m : ℂ) * t ∈ L.lattice) (ht : t ∉ L.lattice) : L.weierstrassP t ∈ W := by
  by_contra hx
  have hx0 : L.weierstrassP t ≠ 0 := fun h => hx (h ▸ W.zero_mem)
  obtain ⟨hs, hs0⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.1
    ((W.inv_mem_nonunits_iff).2 (Or.inr hx))
  obtain ⟨a, ha, ra⟩ := (multiples L W h2 hg2 hg3 ht ⟨_, hs⟩ (mul_inv_cancel₀ hx0)
    ((residue_eq_zero_iff _).2 hs0) m).1
  have h0 := (ra.resolve_right (fun h => h.1 hmt)).2
  have ha0 : a = 0 := by
    simpa [hx0] using h0
  have hu : (m : W) * ⟨_, hm⟩ = 1 := by
    apply Subtype.ext
    simp [hm0]
  have := congrArg (residue W) hu
  rw [ha0, map_zero] at ha
  rw [map_mul, map_natCast, pow_eq_zero_iff two_ne_zero |>.1 ha.symm, zero_mul, map_one] at this
  exact zero_ne_one this

open IsLocalRing in

/- English proof (translation)
Introduce `L W m h2 _ hg2 hg3 hΔ hodd hm`. Establish `hI : ∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W` using `fun t a b => integral L W m h2 hg2 hg3 hodd.pos.ne' hm a b`. Use `⟨hI, fun t t' a b a' b' hn => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Establish `hne : L.weierstrassP t ≠ L.weierstrassP t'` using `mt (GlobalTheory.weierstrassP_eq_iff L b b').1 hc`.

Rewrite `hc` using `[not_or]`. Take `⟨hs, hp⟩` from `sum_prod L b b' hne`. Set `x1 : W` to `⟨_, hI t a b⟩`. Set `x2 : W` to `⟨_, hI t' a' b'⟩`. Set `x3 : W` to `⟨_, hI (t + t') (by rw [mul_add]; exact add_mem a a') hc.2⟩`.

Set `x4 : W` to `⟨_, hI (t - t') (by rw [mul_sub]; exact sub_mem a a') hc.1⟩`. Set `g2 : W` to `⟨L.g₂, hg2⟩`. Set `g3 : W` to `⟨L.g₃, hg3⟩`. Set `h : W` to `⟨2⁻¹, h2⟩`. Set `e : W` to `⟨_, hΔ⟩`.

Establish `c2 : ((2 : W) : ℂ) = 2` using `rfl`. Establish `c27 : ((27 : W) : ℂ) = 27` using `rfl`. Establish `e1 : (x3 + x4) * (x1 - x2) ^ 2 = 2 * x1 * x2 * (x1 + x2) - g2 * h * (x1 + x2) - g3`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[x1, x2, x3, x4, g2, g3, h, c2]`.

Take the linear combination `hs`. Establish `e2 : x3 * x4 * (x1 - x2) ^ 2 = (x1 * x2 + g2 * h ^ 2) ^ 2 + g3 * (x1 + x2)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[x1, x2, x3, x4, g2, g3, h]`. Take the linear combination `hp`.

Establish `e3 : 2 * h = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[h, c2]`. Establish `e4 : (g2 ^ 3 - 27 * g3 ^ 2) * e = 1`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[g2, g3, e, c27, disc L]`. Establish `e5 : residue W (x1 - x2) = 0` using `(residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hn)`. Establish `f1` using `congrArg (residue W) e1`. Establish `f2` using `congrArg (residue W) e2`. Establish `f3` using `congrArg (residue W) e3`.

Establish `f4` using `congrArg (residue W) e4`. Simplify using `only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one] at f1 f2 f3 f4 e5`. Rewrite `e5` using `[sub_eq_zero]`. Rewrite `f1`, `f2` using `[← e5]`. Generalize the expression as in `residue W x1 = x at *`.

Generalize the expression as in `residue W g2 = A at *`. Generalize the expression as in `residue W g3 = B at *`. Generalize the expression as in `residue W h = u at *`. Establish `k1 : 4 * x ^ 3 - A * x - B = 0` using `by linear_combination (A * x) * f3 - f1`. Establish `k2 : (4 * x ^ 2 + A) ^ 2 + 32 * B * x = 0`.

Establish `hA : 4 * (x * x + A * u ^ 2) = 4 * x ^ 2 + A`. Take the linear combination `A * (2 * u + 1) * f3`. Rewrite using `[← hA]`. Take the linear combination `-16 * f2`. Establish `k3 : A ^ 3 - 27 * B ^ 2 = 0`.

Take the linear combination `(A - 3 * x ^ 2) * k2 + (12 * x ^ 3 + 5 * A * x + 27 * B) * k1`. Rewrite `f4` using `[k3, zero_mul]`. Conclude with `zero_ne_one f4`.
-/
theorem torsion_integral_distinct : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ),
    (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W →
    Odd m → (m : ℂ)⁻¹ ∈ W →
    (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧
    ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice →
      t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits →
      t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  intro L W m h2 _ hg2 hg3 hΔ hodd hm
  have hI : ∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W :=
    fun t a b => integral L W m h2 hg2 hg3 hodd.pos.ne' hm a b
  refine ⟨hI, fun t t' a b a' b' hn => ?_⟩
  by_contra hc
  have hne : L.weierstrassP t ≠ L.weierstrassP t' := mt (GlobalTheory.weierstrassP_eq_iff L b b').1 hc
  rw [not_or] at hc
  obtain ⟨hs, hp⟩ := sum_prod L b b' hne
  let x1 : W := ⟨_, hI t a b⟩
  let x2 : W := ⟨_, hI t' a' b'⟩
  let x3 : W := ⟨_, hI (t + t') (by rw [mul_add]; exact add_mem a a') hc.2⟩
  let x4 : W := ⟨_, hI (t - t') (by rw [mul_sub]; exact sub_mem a a') hc.1⟩
  let g2 : W := ⟨L.g₂, hg2⟩
  let g3 : W := ⟨L.g₃, hg3⟩
  let h : W := ⟨2⁻¹, h2⟩
  let e : W := ⟨_, hΔ⟩
  have c2 : ((2 : W) : ℂ) = 2 := rfl
  have c27 : ((27 : W) : ℂ) = 27 := rfl
  have e1 : (x3 + x4) * (x1 - x2) ^ 2 = 2 * x1 * x2 * (x1 + x2) - g2 * h * (x1 + x2) - g3 := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h, c2]
    linear_combination hs
  have e2 : x3 * x4 * (x1 - x2) ^ 2 = (x1 * x2 + g2 * h ^ 2) ^ 2 + g3 * (x1 + x2) := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h]
    linear_combination hp
  have e3 : 2 * h = 1 := by
    apply Subtype.ext
    simp [h, c2]
  have e4 : (g2 ^ 3 - 27 * g3 ^ 2) * e = 1 := by
    apply Subtype.ext
    simp [g2, g3, e, c27, disc L]
  have e5 : residue W (x1 - x2) = 0 :=
    (residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hn)
  have f1 := congrArg (residue W) e1
  have f2 := congrArg (residue W) e2
  have f3 := congrArg (residue W) e3
  have f4 := congrArg (residue W) e4
  simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one] at f1 f2 f3 f4 e5
  rw [sub_eq_zero] at e5
  rw [← e5] at f1 f2
  generalize residue W x1 = x at *
  generalize residue W g2 = A at *
  generalize residue W g3 = B at *
  generalize residue W h = u at *
  have k1 : 4 * x ^ 3 - A * x - B = 0 := by linear_combination (A * x) * f3 - f1
  have k2 : (4 * x ^ 2 + A) ^ 2 + 32 * B * x = 0 := by
    have hA : 4 * (x * x + A * u ^ 2) = 4 * x ^ 2 + A := by
      linear_combination A * (2 * u + 1) * f3
    rw [← hA]; linear_combination -16 * f2
  have k3 : A ^ 3 - 27 * B ^ 2 = 0 := by
    linear_combination (A - 3 * x ^ 2) * k2 + (12 * x ^ 3 + 5 * A * x + 27 * B) * k1
  rw [k3, zero_mul] at f4
  exact zero_ne_one f4

end GlobalTheory.TorsionIntegral
