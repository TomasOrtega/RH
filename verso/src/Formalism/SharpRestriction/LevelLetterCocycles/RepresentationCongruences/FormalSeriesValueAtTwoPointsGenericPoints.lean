import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

namespace ContPA

/- English proof (translation)
Conclude with `(Ideal.span_le.mpr (by simp [Set.insert_subset_iff, ha, hb])) hz`.
-/
theorem mem_of_mem_span_pair {R : Type*} [CommRing R] {a b z : R} {J : Ideal R}
    (hz : z ∈ Ideal.span {a, b}) (ha : a ∈ J) (hb : b ∈ J) : z ∈ J := by
  exact (Ideal.span_le.mpr (by simp [Set.insert_subset_iff, ha, hb])) hz

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Conclude with `Ideal.mul_mem_right c _ (Ideal.subset_span (Set.mem_insert a {b}))`.
-/
theorem mem_pair_left_of_dvd {R : Type*} [CommRing R] {a b z : R} (h : a ∣ z) :
    z ∈ Ideal.span {a, b} := by
  obtain ⟨c, rfl⟩ := h
  exact Ideal.mul_mem_right c _ (Ideal.subset_span (Set.mem_insert a {b}))

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Conclude with `I.mul_mem_right c ha`.
-/
private lemma mem_of_dvd_lemma {R : Type*} [CommRing R] {I : Ideal R} {a b : R} (h : a ∣ b)
    (ha : a ∈ I) : b ∈ I := by
  obtain ⟨c, rfl⟩ := h
  exact I.mul_mem_right c ha

/- English proof (translation)
Take `⟨s, hs⟩` from `Ideal.mem_span_singleton'.mp h`. Establish `hx : x = x' + s * t` using `by rw [hs]; ring`. Rewrite using `[hx, add_pow]`. Use `Ideal.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hmn : m < n + 1` using `Finset.mem_range.mp hm`.

Distinguish the cases in `ham : a ≤ m`. Apply `mem_of_dvd_lemma (a := x' ^ a)` to reduce the goal to its premises. Establish `h1 : x' ^ a ∣ x' ^ m` using `pow_dvd_pow x' ham`. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_right h1 _) _`. Conclude with `Ideal.subset_span (by simp)`.

Apply `mem_of_dvd_lemma (a := t ^ (n + 1 - a))` to reduce the goal to its premises. Establish `h1 : t ^ (n + 1 - a) ∣ t ^ (n - m)` using `pow_dvd_pow t (by omega)`. Establish `h2 : t ^ (n - m) ∣ (s * t) ^ (n - m)` using `by rw [mul_pow]; exact dvd_mul_left _ _`. Conclude with `Dvd.dvd.mul_right (Dvd.dvd.mul_left (h1.trans h2) _) _`. Conclude with `Ideal.subset_span (by simp)`.
-/
theorem pow_mem_span_of_sub {R : Type*} [CommRing R] {x x' t : R}
    (h : x - x' ∈ Ideal.span {t}) (n a : ℕ) :
    x ^ n ∈ Ideal.span {t ^ (n + 1 - a), x' ^ a} := by
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h
  have hx : x = x' + s * t := by rw [hs]; ring
  rw [hx, add_pow]
  refine Ideal.sum_mem _ fun m hm => ?_
  have hmn : m < n + 1 := Finset.mem_range.mp hm
  by_cases ham : a ≤ m
  · apply mem_of_dvd_lemma (a := x' ^ a)
    · have h1 : x' ^ a ∣ x' ^ m := pow_dvd_pow x' ham
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h1 _) _
    · exact Ideal.subset_span (by simp)
  · apply mem_of_dvd_lemma (a := t ^ (n + 1 - a))
    · have h1 : t ^ (n + 1 - a) ∣ t ^ (n - m) := pow_dvd_pow t (by omega)
      have h2 : t ^ (n - m) ∣ (s * t) ^ (n - m) := by rw [mul_pow]; exact dvd_mul_left _ _
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (h1.trans h2) _) _
    · exact Ideal.subset_span (by simp)

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/- English proof (translation)
Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.mpr hc`. Assume the negation of the conclusion as `hm`. Establish `hm' : (m : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hm)`. Establish `hne : (1 : O) ∉ IsLocalRing.maximalIdeal O` using `(Ideal.ne_top_iff_one _).mp (inferInstance : (IsLocalRing.maximalIdeal O).IsMaximal).ne_top`. Apply `hne` to reduce the goal to its premises.

Establish `h1 : (a : O) * (l : O) + (b : O) * (m : O) = 1`. Conclude with `congrArg (Int.cast : ℤ → O) hab` after adjusting the coercions. Rewrite using `[← h1]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm')`.
-/
private lemma isUnit_natCast_sp_complex_sections {l m : ℕ} (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hc : Nat.Coprime l m) : IsUnit (m : O) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hc
  by_contra hm
  have hm' : (m : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hm)
  have hne : (1 : O) ∉ IsLocalRing.maximalIdeal O :=
    (Ideal.ne_top_iff_one _).mp (inferInstance : (IsLocalRing.maximalIdeal O).IsMaximal).ne_top
  apply hne
  have h1 : (a : O) * (l : O) + (b : O) * (m : O) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  rw [← h1]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hm')

/- English proof (translation)
Take `⟨m, hm⟩` from `pow_padicValNat_dvd (p := l) (n := n)`. Establish `hnd : ¬ l ∣ m`. Introduce and unpack `⟨c, rfl⟩`. Apply `pow_succ_padicValNat_not_dvd (p := l) hn` to reduce the goal to its premises. Conclude with `⟨c, by rw [pow_succ, mul_assoc]; exact hm⟩`.

Establish `hu` using `isUnit_natCast_sp_complex_sections hl ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Establish `hc : (n : O) = (l : O) ^ padicValNat l n * (m : O)`. Conclude with `congrArg (Nat.cast : ℕ → O) hm` after adjusting the coercions. Rewrite using `[hc, IsUnit.unit_spec, mul_comm]`.
-/
theorem natCast_unit_mul {l : ℕ} [hp : Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    {n : ℕ} (hn : n ≠ 0) : ∃ v : Oˣ, (n : O) = v * (l : O) ^ padicValNat l n := by
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := l) (n := n)
  have hnd : ¬ l ∣ m := by
    rintro ⟨c, rfl⟩
    apply pow_succ_padicValNat_not_dvd (p := l) hn
    exact ⟨c, by rw [pow_succ, mul_assoc]; exact hm⟩
  have hu := isUnit_natCast_sp_complex_sections hl ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd)
  refine ⟨hu.unit, ?_⟩
  have hc : (n : O) = (l : O) ^ padicValNat l n * (m : O) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → O) hm
  rw [hc, IsUnit.unit_spec, mul_comm]

/- English proof (translation)
Take `⟨v, hv⟩` from `natCast_unit_mul hl hn`. Rewrite using `[hv]`. Conclude with `mul_ne_zero v.ne_zero (pow_ne_zero _ hl0)`.
-/
theorem natCast_ne_zero' {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) : (n : O) ≠ 0 := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv]
  exact mul_ne_zero v.ne_zero (pow_ne_zero _ hl0)

/- English proof (translation)
Conclude with `(ENat.coe_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hl0)).symm`.
-/
theorem addVal_l {l : ℕ} (hl0 : (l : O) ≠ 0) :
    IsDiscreteValuationRing.addVal O (l : O) = ((IsDiscreteValuationRing.addVal O (l : O)).toNat : ℕ∞) := by
  exact (ENat.coe_toNat ((IsDiscreteValuationRing.addVal_eq_top_iff).not.mpr hl0)).symm

/- English proof (translation)
Take `⟨v, hv⟩` from `natCast_unit_mul hl hn`. Rewrite using `[hv, AddValuation.map_mul, AddValuation.map_pow, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]`. Take `⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k` from `⟨_, addVal_l hl0⟩`. Rewrite using `[hk, ENat.toNat_coe, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem addVal_natCast {l : ℕ} [Fact l.Prime] (hl : (l : O) ∈ IsLocalRing.maximalIdeal O)
    (hl0 : (l : O) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    IsDiscreteValuationRing.addVal O (n : O) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * padicValNat l n : ℕ) : ℕ∞) := by
  obtain ⟨v, hv⟩ := natCast_unit_mul hl hn
  rw [hv, AddValuation.map_mul, AddValuation.map_pow, IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

/- English proof (translation)
Take `⟨n, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ`. Use `⟨v, ?_⟩` and prove the remaining obligations. Rewrite using `[IsDiscreteValuationRing.addVal_def _ v hϖ n hv, ENat.toNat_coe]`. Conclude with `hv`.
-/
theorem l_unit_mul {ϖ : O} (hϖ : Irreducible ϖ) {l : ℕ} (hl0 : (l : O) ≠ 0) :
    ∃ v : Oˣ, (l : O) = v * ϖ ^ (IsDiscreteValuationRing.addVal O (l : O)).toNat := by
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  refine ⟨v, ?_⟩
  rw [IsDiscreteValuationRing.addVal_def _ v hϖ n hv, ENat.toNat_coe]
  exact hv

/- English proof (translation)
Take `⟨v, hv⟩` from `l_unit_mul hϖ hl0`. Establish `h : ϖ ^ k ∣ (l : O) ^ n`. Rewrite using `[hv, mul_pow, ← pow_mul]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow ϖ hk) _`. Establish `h2` using `map_dvd (C : O →+* O⟦X⟧) h`.

Rewrite `h2` using `[map_pow, map_pow]`. Conclude with `h2`.
-/
theorem C_l_pow_dvd {ϖ : O} (hϖ : Irreducible ϖ) {l : ℕ} (hl0 : (l : O) ≠ 0) {n k : ℕ}
    (hk : k ≤ (IsDiscreteValuationRing.addVal O (l : O)).toNat * n) :
    (C ϖ : O⟦X⟧) ^ k ∣ (C (l : O) : O⟦X⟧) ^ n := by
  obtain ⟨v, hv⟩ := l_unit_mul hϖ hl0
  have h : ϖ ^ k ∣ (l : O) ^ n := by
    rw [hv, mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_left (pow_dvd_pow ϖ hk) _
  have h2 := map_dvd (C : O →+* O⟦X⟧) h
  rw [map_pow, map_pow] at h2
  exact h2

/- English proof (translation)
Establish `hw0 : w.order = 0`. Take `⟨u, rfl⟩` from `hw`. Establish `h` using `congrArg PowerSeries.order u.mul_inv`. Rewrite `h` using `[PowerSeries.order_mul, PowerSeries.order_one]`. Establish `h2 : PowerSeries.order (u : K⟦X⟧) ≤ 0`.

Rewrite using `[← h]`. Conclude with `le_self_add`. Conclude with `le_antisymm h2 (by simp)`. Rewrite using `[PowerSeries.order_mul, hw0, PowerSeries.order_X_pow, zero_add]`.
-/
private lemma order_unit_mul_X_pow_lemma_3 {K : Type*} [Field K] {w : K⟦X⟧} (hw : IsUnit w) (n : ℕ) :
    (w * X ^ n).order = (n : ℕ∞) := by
  have hw0 : w.order = 0 := by
    obtain ⟨u, rfl⟩ := hw
    have h := congrArg PowerSeries.order u.mul_inv
    rw [PowerSeries.order_mul, PowerSeries.order_one] at h
    have h2 : PowerSeries.order (u : K⟦X⟧) ≤ 0 := by
      rw [← h]; exact le_self_add
    exact le_antisymm h2 (by simp)
  rw [PowerSeries.order_mul, hw0, PowerSeries.order_X_pow, zero_add]

/- English proof (translation)
Establish `hord : (f.map (IsLocalRing.residue O)).order = n`. Rewrite using `[h]`. Conclude with `order_unit_mul_X_pow_lemma_3 hw n`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `IsDist`.

Introduce `h0`. Rewrite `hord` using `[h0, PowerSeries.order_zero]`. Conclude with `ENat.top_ne_coe n hord`. Unfold `wdeg`. Rewrite using `[hord]`.

Both sides reduce to the same expression.
-/
theorem dist_of_map_eq {f : O⟦X⟧} {w : (IsLocalRing.ResidueField O)⟦X⟧} (hw : IsUnit w) (n : ℕ)
    (h : f.map (IsLocalRing.residue O) = w * X ^ n) : IsDist f ∧ wdeg f = n := by
  have hord : (f.map (IsLocalRing.residue O)).order = n := by
    rw [h]; exact order_unit_mul_X_pow_lemma_3 hw n
  refine ⟨?_, ?_⟩
  · unfold IsDist
    intro h0
    rw [h0, PowerSeries.order_zero] at hord
    exact ENat.top_ne_coe n hord
  · unfold wdeg
    rw [hord]
    rfl

/- English proof (translation)
The claim follows from `dist_of_map_eq isUnit_one n (by simp)`.
-/
theorem dist_X_pow (n : ℕ) : IsDist ((X : O⟦X⟧) ^ n) ∧ wdeg ((X : O⟦X⟧) ^ n) = n := dist_of_map_eq isUnit_one n (by simp)

section P1
variable {l : ℕ} [hlp : Fact l.Prime] {p1 e u : O⟦X⟧}

/- English proof (translation)
Establish `h0 : IsLocalRing.residue O (l : O) = 0` using `(IsLocalRing.residue_eq_zero_iff _).mpr hl`. Establish `h0' : (l : IsLocalRing.ResidueField O) = 0`. Rewrite using `[← map_natCast (IsLocalRing.residue O)]`. Conclude with `h0`. Establish `h0'' : ((l : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0`.

Rewrite using `[← map_natCast (C : IsLocalRing.ResidueField O →+* (IsLocalRing.ResidueField O)⟦X⟧) l, h0', map_zero]`. Rewrite using `[hp]`. Simplify using `[h0, h0', h0'']`.
-/
theorem residue_map_p1_eq (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hp : p1 = C (l : O) * e + u * X ^ l) :
    p1.map (IsLocalRing.residue O) = u.map (IsLocalRing.residue O) * X ^ l := by
  have h0 : IsLocalRing.residue O (l : O) = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hl
  have h0' : (l : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O)]; exact h0
  have h0'' : ((l : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0 := by
    rw [← map_natCast (C : IsLocalRing.ResidueField O →+* (IsLocalRing.ResidueField O)⟦X⟧) l, h0', map_zero]
  rw [hp]
  simp [h0, h0', h0'']

/- English proof (translation)
The claim follows from `dist_of_map_eq ((hu.map (PowerSeries.map (IsLocalRing.residue O))).pow y) (l * y) (by rw [map_pow, residue_map_p1_eq hl hp, mul_pow, ← pow_mul])`.
-/
theorem isDist_p1_pow_wdeg (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    IsDist (p1 ^ y) ∧ wdeg (p1 ^ y) = l * y := dist_of_map_eq ((hu.map (PowerSeries.map (IsLocalRing.residue O))).pow y) (l * y)
    (by rw [map_pow, residue_map_p1_eq hl hp, mul_pow, ← pow_mul])

/- English proof (translation)
Conclude with `dist_of_map_eq (hu.map (PowerSeries.map (IsLocalRing.residue O))) l (residue_map_p1_eq hl hp)`.
-/
theorem isDist_p1_wdeg (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) : IsDist p1 ∧ wdeg p1 = l := by
  exact dist_of_map_eq (hu.map (PowerSeries.map (IsLocalRing.residue O))) l (residue_map_p1_eq hl hp)

/- English proof (translation)
Establish `hinv : (↑(hu.unit⁻¹) : O⟦X⟧) * u = 1` using `hu.unit.inv_mul`. Establish `hX : (X : O⟦X⟧) ^ l = ↑(hu.unit⁻¹) * (p1 + -(C (l : O) * e))`. Rewrite using `[hp]`. Take the linear combination `(-(X ^ l : O⟦X⟧)) * hinv`. Rewrite using `[pow_mul, hX, mul_pow, add_pow, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem X_pow_expand (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (a : ℕ) :
    (X : O⟦X⟧) ^ (l * a) = ∑ i ∈ Finset.range (a + 1),
      ((↑(hu.unit⁻¹) : O⟦X⟧) ^ a * (-e) ^ (a - i)) * C ((a.choose i : O) * (l : O) ^ (a - i)) * p1 ^ i := by
  have hinv : (↑(hu.unit⁻¹) : O⟦X⟧) * u = 1 := hu.unit.inv_mul
  have hX : (X : O⟦X⟧) ^ l = ↑(hu.unit⁻¹) * (p1 + -(C (l : O) * e)) := by
    rw [hp]
    linear_combination (-(X ^ l : O⟦X⟧)) * hinv
  rw [pow_mul, hX, mul_pow, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_natCast]
  ring

/- English proof (translation)
Rewrite using `[hp, add_comm (C (l : O) * e), add_pow]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, map_pow, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem p1_pow_eq_sum_choose_mul_X_pow_l_pow (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    p1 ^ y = ∑ i ∈ Finset.range (y + 1),
      (u ^ i * e ^ (y - i)) * C ((y.choose i : O) * (l : O) ^ (y - i)) * ((X : O⟦X⟧) ^ l) ^ i := by
  rw [hp, add_comm (C (l : O) * e), add_pow]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_natCast]
  ring

/- English proof (translation)
Establish `hc : a.choose i ≠ 0` using `(Nat.choose_pos hi).ne'`. Rewrite using `[AddValuation.map_mul, addVal_natCast hl hl0 hc, AddValuation.map_pow]`. Take `⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k` from `⟨_, addVal_l hl0⟩`. Rewrite using `[hk, ENat.toNat_coe, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem addVal_coef (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    IsDiscreteValuationRing.addVal O ((a.choose i : O) * (l : O) ^ (a - i)) =
      (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (a - i + padicValNat l (a.choose i)) : ℕ) : ℕ∞) := by
  have hc : a.choose i ≠ 0 := (Nat.choose_pos hi).ne'
  rw [AddValuation.map_mul, addVal_natCast hl hl0 hc, AddValuation.map_pow]
  obtain ⟨k, hk⟩ : ∃ k : ℕ, IsDiscreteValuationRing.addVal O (l : O) = k := ⟨_, addVal_l hl0⟩
  rw [hk, ENat.toNat_coe, nsmul_eq_mul]
  push_cast
  ring

/- English proof (translation)
The claim follows from `mul_ne_zero (natCast_ne_zero' hl hl0 (Nat.choose_pos hi).ne') (pow_ne_zero _ hl0)`.
-/
theorem coef_ne_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) {a i : ℕ} (hi : i ≤ a) :
    (a.choose i : O) * (l : O) ^ (a - i) ≠ 0 := mul_ne_zero (natCast_ne_zero' hl hl0 (Nat.choose_pos hi).ne') (pow_ne_zero _ hl0)

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

/- English proof (translation)
Take `⟨hX, hD⟩` from `isDist_p1_wdeg hl hu hp`. Establish `hD' : 1 ≤ wdeg p1` using `by rw [hD]; exact hlp.out.one_lt.le`. Establish `key` using `Mprime_cont hϖ hX hD' (Finset.range (a + 1)) (fun i => (↑(hu.unit⁻¹) : O⟦X⟧) ^ a * (-e) ^ (a - i)) (fun i _ => ((hu.unit⁻¹).isUnit.pow _).mul (he.neg.pow _)) (fun i => (a.choose i : O) * (l : O) ^ (a - i)) (fun i hi => coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp …`. Rewrite using `[X_pow_expand hu hp a, key]`. Establish `hset : (Finset.range (a + 1)).filter (· < y) = Finset.range (min a (y - 1) + 1)`.

Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset]`. Use `iInf_congr (fun i => iInf_congr (fun hi => ?_))` and prove the remaining obligations.

Establish `hi' : i ≤ a` using `by simp only [Finset.mem_range] at hi; omega`. Conclude with `addVal_coef hl hl0 hi'`.
-/
theorem content_p1_pow_X_pow_eq_iInf (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (a y : ℕ) (hy : 1 ≤ y) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ (l * a)) =
      ⨅ i ∈ Finset.range (min a (y - 1) + 1),
        (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (a - i + padicValNat l (a.choose i)) : ℕ) : ℕ∞) := by
  obtain ⟨hX, hD⟩ := isDist_p1_wdeg hl hu hp
  have hD' : 1 ≤ wdeg p1 := by rw [hD]; exact hlp.out.one_lt.le
  have key := Mprime_cont hϖ hX hD' (Finset.range (a + 1))
    (fun i => (↑(hu.unit⁻¹) : O⟦X⟧) ^ a * (-e) ^ (a - i))
    (fun i _ => ((hu.unit⁻¹).isUnit.pow _).mul (he.neg.pow _))
    (fun i => (a.choose i : O) * (l : O) ^ (a - i))
    (fun i hi => coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) y
  rw [X_pow_expand hu hp a, key]
  have hset : (Finset.range (a + 1)).filter (· < y) = Finset.range (min a (y - 1) + 1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hset]
  refine iInf_congr (fun i => iInf_congr (fun hi => ?_))
  have hi' : i ≤ a := by simp only [Finset.mem_range] at hi; omega
  exact addVal_coef hl hl0 hi'

/- English proof (translation)
Take `⟨hX, hD⟩` from `dist_X_pow (O := O) l`. Establish `hD' : 1 ≤ wdeg ((X : O⟦X⟧) ^ l)` using `by rw [hD]; exact hlp.out.one_lt.le`. Establish `key` using `Mprime_cont hϖ hX hD' (Finset.range (y + 1)) (fun i => u ^ i * e ^ (y - i)) (fun i _ => (hu.pow _).mul (he.pow _)) (fun i => (y.choose i : O) * (l : O) ^ (y - i)) (fun i hi => coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) be`. Rewrite using `[pow_mul, p1_pow_eq_sum_choose_mul_X_pow_l_pow hp y, key]`. Establish `hset : (Finset.range (y + 1)).filter (· < be) = Finset.range (min y (be - 1) + 1)`.

Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hset]`. Use `iInf_congr (fun i => iInf_congr (fun hi => ?_))` and prove the remaining obligations.

Establish `hi' : i ≤ y` using `by simp only [Finset.mem_range] at hi; omega`. Conclude with `addVal_coef hl hl0 hi'`.
-/
theorem formalSeriesValueAtTwoPoints_genericPoints (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (y be : ℕ) (hbe : 1 ≤ be) :
    cont ϖ ((X : O⟦X⟧) ^ (l * be)) (p1 ^ y) =
      ⨅ i ∈ Finset.range (min y (be - 1) + 1),
        (((IsDiscreteValuationRing.addVal O (l : O)).toNat * (y - i + padicValNat l (y.choose i)) : ℕ) : ℕ∞) := by
  obtain ⟨hX, hD⟩ := dist_X_pow (O := O) l
  have hD' : 1 ≤ wdeg ((X : O⟦X⟧) ^ l) := by rw [hD]; exact hlp.out.one_lt.le
  have key := Mprime_cont hϖ hX hD' (Finset.range (y + 1))
    (fun i => u ^ i * e ^ (y - i))
    (fun i _ => (hu.pow _).mul (he.pow _))
    (fun i => (y.choose i : O) * (l : O) ^ (y - i))
    (fun i hi => coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) be
  rw [pow_mul, p1_pow_eq_sum_choose_mul_X_pow_l_pow hp y, key]
  have hset : (Finset.range (y + 1)).filter (· < be) = Finset.range (min y (be - 1) + 1) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hset]
  refine iInf_congr (fun i => iInf_congr (fun hi => ?_))
  have hi' : i ≤ y := by simp only [Finset.mem_range] at hi; omega
  exact addVal_coef hl hl0 hi'

/- English proof (translation)
Use `le_antisymm ?_ (by simp)` and prove the remaining obligations. Unfold `cont`. Use `iSup₂_le fun k hk => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Simplify using the standard rewrite rules.

It suffices to derive a contradiction. Take `⟨a', c', hac⟩` from `Ideal.mem_span_pair.mp hk`. Establish `hϖ0 : IsLocalRing.residue O ϖ = 0` using `(IsLocalRing.residue_eq_zero_iff ϖ).mpr ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))`. Establish `hm` using `congrArg (PowerSeries.map (IsLocalRing.residue O)) hac`. Simplify using `only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero, zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm`.

Establish `e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y = PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y)` using `by ring`. Rewrite `hm` using `[e1]`. Establish `ho` using `congrArg PowerSeries.order hm`. Rewrite `ho` using `[PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow]`. Establish `h2 : ((l * y : ℕ) : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + ((l * y : ℕ) : ℕ∞)` using `le_add_self`.

Rewrite `h2` using `[ho]`. Establish `h3 : l * y ≤ b` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem content_p1_pow_X_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (y b : ℕ) (hlt : b < l * y) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : ((l * y : ℕ) : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + ((l * y : ℕ) : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : l * y ≤ b := by exact_mod_cast h2
    omega

/- English proof (translation)
Use `le_antisymm ?_ (by simp)` and prove the remaining obligations. Unfold `cont`. Use `iSup₂_le fun k hk => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Simplify using the standard rewrite rules.

It suffices to derive a contradiction. Take `⟨a', c', hac⟩` from `Ideal.mem_span_pair.mp hk`. Establish `hϖ0 : IsLocalRing.residue O ϖ = 0` using `(IsLocalRing.residue_eq_zero_iff ϖ).mpr ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))`. Establish `hm` using `congrArg (PowerSeries.map (IsLocalRing.residue O)) hac`. Simplify using `only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero, zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm`.

Establish `e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y = PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y)` using `by ring`. Rewrite `hm` using `[e1]`. Establish `ho` using `congrArg PowerSeries.order hm`. Rewrite `ho` using `[PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow]`. Establish `h2 : (B : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + (B : ℕ∞)` using `le_add_self`.

Rewrite `h2` using `[ho]`. Establish `h3 : B ≤ l * y` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem content_X_pow_p1_pow_eq_zero (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hu : IsUnit u)
    (hp : p1 = C (l : O) * e + u * X ^ l) (B y : ℕ) (hlt : l * y < B) :
    cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y) = 0 := by
  refine le_antisymm ?_ (by simp)
  unfold cont
  refine iSup₂_le fun k hk => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp
  · exfalso
    obtain ⟨a', c', hac⟩ := Ideal.mem_span_pair.mp hk
    have hϖ0 : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).mpr
      ((IsLocalRing.mem_maximalIdeal ϖ).mpr (mem_nonunits_iff.mpr hϖ.not_isUnit))
    have hm := congrArg (PowerSeries.map (IsLocalRing.residue O)) hac
    simp only [map_add, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X, hϖ0, map_zero,
      zero_pow hk0.ne', mul_zero, zero_add, residue_map_p1_eq hl hp] at hm
    have e1 : (PowerSeries.map (IsLocalRing.residue O) u * X ^ l) ^ y =
        PowerSeries.map (IsLocalRing.residue O) u ^ y * X ^ (l * y) := by ring
    rw [e1] at hm
    have ho := congrArg PowerSeries.order hm
    rw [PowerSeries.order_mul, order_unit_mul_X_pow_lemma_3 ((hu.map _).pow y), PowerSeries.order_X_pow] at ho
    have h2 : (B : ℕ∞) ≤ PowerSeries.order (PowerSeries.map (IsLocalRing.residue O) c') + (B : ℕ∞) :=
      le_add_self
    rw [ho] at h2
    have h3 : B ≤ l * y := by exact_mod_cast h2
    omega

omit hϖ in
/- English proof (translation)
Establish `h1 : padicValNat l (n.choose i) ≤ Nat.log l n`. Rewrite using `[← Nat.factorization_def _ hlp.out]`. Conclude with `Nat.factorization_choose_le_log`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem padicValNat_choose_le_logb (n i : ℕ) : (padicValNat l (n.choose i) : ℝ) ≤ Real.logb l n := by
  have h1 : padicValNat l (n.choose i) ≤ Nat.log l n := by
    rw [← Nat.factorization_def _ hlp.out]
    exact Nat.factorization_choose_le_log
  calc (padicValNat l (n.choose i) : ℝ) ≤ (Nat.log l n : ℝ) := by exact_mod_cast h1
    _ ≤ Real.logb l n := Real.natLog_le_logb n l

/- English proof (translation)
Use `set E := (IsDiscreteValuationRing.addVal O (l : O)).toNat`. Establish `hl2 : 2 ≤ l` using `hlp.out.two_le`. Establish `hab : l * (b / l) ≤ b` using `Nat.mul_div_le b l`. Establish `hab2 : b < l * (b / l + 1)`. Establish `h1` using `Nat.div_add_mod b l`.

Establish `h2` using `Nat.mod_lt b (by omega : 0 < l)`. Rewrite using `[mul_add, mul_one]`. Use linear arithmetic over natural numbers and integers. Generalize the expression as in `b / l = a at hab hab2`. Take `⟨hg, -⟩` from `isDist_p1_pow_wdeg hl hu hp y`.

Establish `hm2` using `m2 hϖ hg ((X : O⟦X⟧) ^ (l * (a + 1) - b)) ((X : O⟦X⟧) ^ b)`. Rewrite `hm2` using `[← pow_add, Nat.sub_add_cancel hab2.le, content_p1_pow_X_pow_eq_iInf hϖ hl hl0 he hu hp (a + 1) y hy]`. Use `set i0 := min (a + 1) (y - 1) with hi0`. Establish `hmem : i0 ∈ Finset.range (min (a + 1) (y - 1) + 1)` using `Finset.mem_range.mpr (by omega)`. Establish `hle` using `hm2.trans (iInf₂_le i0 hmem)`.

Use `⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ?_⟩` and prove the remaining obligations. Establish `hnat` using `ENat.toNat_le_of_le_natCast hle`. Use `(Nat.cast_le.mpr hnat).trans ?_` and prove the remaining obligations. Use `push_cast`. Use `mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)` and prove the remaining obligations.

Distinguish the cases in `hcase : a + 1 ≤ y - 1`. Establish `: i0 = a + 1` using `by omega`. Rewrite using `[this, Nat.sub_self, Nat.choose_self, padicValNat_one_right]`. Simplify using the standard rewrite rules. Establish `hi : i0 = y - 1` using `by omega`.

Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Establish `hv` using `padicValNat_choose_le_logb (l := l) (a + 1) i0`. Establish `hlog : Real.logb l ((a + 1 : ℕ) : ℝ) ≤ Real.logb l b`. Apply `Real.logb_le_logb_of_le (by exact_mod_cast hlp.out.one_lt) (by positivity)` to reduce the goal to its premises. Establish `: a + 1 ≤ b`.

Establish `: 2 * a ≤ l * a` using `Nat.mul_le_mul_right a hl2`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `hsub : ((a + 1 - i0 : ℕ) : ℝ) = (a : ℝ) + 2 - y`. Rewrite using `[Nat.cast_sub (by omega)]`.

Establish `: (i0 : ℝ) + 1 = y` using `by exact_mod_cast (show i0 + 1 = y by omega)`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hal : (a : ℝ) ≤ b / l`. Rewrite using `[le_div_iff₀ (by positivity)]`.

Establish `: ((l * a : ℕ) : ℝ) ≤ b` using `by exact_mod_cast hab`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hsub]`. Move the coercions through the operations in `at hv hlog`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem content_p1_pow_X_pow_le_general (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (y b : ℕ) (hy : 1 ≤ y) (hb : 1 ≤ b) :
    cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b) ≠ ⊤ ∧
    ((cont ϖ (p1 ^ y) ((X : O⟦X⟧) ^ b)).toNat : ℝ) ≤
      (IsDiscreteValuationRing.addVal O (l : O)).toNat * max 0 ((b : ℝ) / l - y + 2 + Real.logb l b) := by
  set E := (IsDiscreteValuationRing.addVal O (l : O)).toNat
  have hl2 : 2 ≤ l := hlp.out.two_le
  have hab : l * (b / l) ≤ b := Nat.mul_div_le b l
  have hab2 : b < l * (b / l + 1) := by
    have h1 := Nat.div_add_mod b l
    have h2 := Nat.mod_lt b (by omega : 0 < l)
    rw [mul_add, mul_one]; omega
  generalize b / l = a at hab hab2
  obtain ⟨hg, -⟩ := isDist_p1_pow_wdeg hl hu hp y
  have hm2 := m2 hϖ hg ((X : O⟦X⟧) ^ (l * (a + 1) - b)) ((X : O⟦X⟧) ^ b)
  rw [← pow_add, Nat.sub_add_cancel hab2.le, content_p1_pow_X_pow_eq_iInf hϖ hl hl0 he hu hp (a + 1) y hy] at hm2
  set i0 := min (a + 1) (y - 1) with hi0
  have hmem : i0 ∈ Finset.range (min (a + 1) (y - 1) + 1) := Finset.mem_range.mpr (by omega)
  have hle := hm2.trans (iInf₂_le i0 hmem)
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ?_⟩
  have hnat := ENat.toNat_le_of_le_natCast hle
  refine (Nat.cast_le.mpr hnat).trans ?_
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  by_cases hcase : a + 1 ≤ y - 1
  · have : i0 = a + 1 := by omega
    rw [this, Nat.sub_self, Nat.choose_self, padicValNat_one_right]
    simp
  · have hi : i0 = y - 1 := by omega
    refine le_trans ?_ (le_max_right _ _)
    have hv := padicValNat_choose_le_logb (l := l) (a + 1) i0
    have hlog : Real.logb l ((a + 1 : ℕ) : ℝ) ≤ Real.logb l b := by
      apply Real.logb_le_logb_of_le (by exact_mod_cast hlp.out.one_lt) (by positivity)
      have : a + 1 ≤ b := by
        have : 2 * a ≤ l * a := Nat.mul_le_mul_right a hl2
        omega
      exact_mod_cast this
    have hsub : ((a + 1 - i0 : ℕ) : ℝ) = (a : ℝ) + 2 - y := by
      rw [Nat.cast_sub (by omega)]
      have : (i0 : ℝ) + 1 = y := by exact_mod_cast (show i0 + 1 = y by omega)
      push_cast; linarith
    have hal : (a : ℝ) ≤ b / l := by
      rw [le_div_iff₀ (by positivity)]
      have : ((l * a : ℕ) : ℝ) ≤ b := by exact_mod_cast hab
      push_cast at this; linarith
    rw [hsub]
    push_cast at hv hlog
    linarith

omit hϖ in
/- English proof (translation)
Rewrite using `[Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hlp.out.pos h), p1_pow_eq_sum_choose_mul_X_pow_l_pow hp]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Nat.mul_div_cancel_left _ hlp.out.pos, ← pow_mul]`.
-/
theorem p1_pow_eq_sum_image_choose_mul_X_pow (hp : p1 = C (l : O) * e + u * X ^ l) (y : ℕ) :
    p1 ^ y = ∑ j ∈ (Finset.range (y + 1)).image (l * ·),
      (u ^ (j / l) * e ^ (y - j / l)) * C ((y.choose (j / l) : O) * (l : O) ^ (y - j / l)) * (X : O⟦X⟧) ^ j := by
  rw [Finset.sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hlp.out.pos h), p1_pow_eq_sum_choose_mul_X_pow_l_pow hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Nat.mul_div_cancel_left _ hlp.out.pos, ← pow_mul]

/- English proof (translation)
Use `set E := (IsDiscreteValuationRing.addVal O (l : O)).toNat`. Establish `hlpos : 0 < l` using `hlp.out.pos`. Take `⟨hX, hD⟩` from `dist_X_pow (O := O) 1`. Rewrite `hX`, `hD` using `[pow_one]`. Establish `key` using `Mprime_cont hϖ hX (by rw [hD]) ((Finset.range (y + 1)).image (l * ·)) (fun j => u ^ (j / l) * e ^ (y - j / l)) (fun j _ => (hu.pow _).mul (he.pow _)) (fun j => (y.choose (j / l) : O) * (l : O) ^ (y - j / l)) (fun j hj => by`.

Take `⟨i, hi, rfl⟩` from `Finset.mem_image.mp hj`. Rewrite using `[Nat.mul_div_cancel_left i hlpos]`. Conclude with `coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) B`. Rewrite using `[p1_pow_eq_sum_image_choose_mul_X_pow hp y, key]`. Use `set i0 := min y ((B - 1) / l) with hi0`.

Establish `hq : l * ((B - 1) / l) ≤ B - 1` using `Nat.mul_div_le (B - 1) l`. Establish `hq2 : B ≤ l * ((B - 1) / l + 1)`. Establish `h1` using `Nat.div_add_mod (B - 1) l`. Establish `h2` using `Nat.mod_lt (B - 1) hlpos`. Rewrite using `[mul_add, mul_one]`.

Use linear arithmetic over natural numbers and integers. Establish `hmem : l * i0 ∈ ((Finset.range (y + 1)).image (l * ·)).filter (· < B)`. Rewrite using `[Finset.mem_filter, Finset.mem_image]`. Use `⟨⟨i0, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: l * i0 ≤ l * ((B - 1) / l)` using `Nat.mul_le_mul_left l (min_le_right _ _)`.

Use linear arithmetic over natural numbers and integers. Establish `hle` using `iInf₂_le (f := fun j (_ : j ∈ ((Finset.range (y + 1)).image (l * ·)).filter (· < B)) => IsDiscreteValuationRing.addVal O ((y.choose (j / l) : O) * (l : O) ^ (y - j / l))) (l * i0) hmem`. Simplify using `only [Nat.mul_div_cancel_left i0 hlpos] at hle`. Establish `hi0y : i0 ≤ y` using `by omega`. Rewrite `hle` using `[addVal_coef hl hl0 hi0y]`.

Use `⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ?_⟩` and prove the remaining obligations. Establish `hnat` using `ENat.toNat_le_of_le_natCast hle`. Use `(Nat.cast_le.mpr hnat).trans ?_` and prove the remaining obligations. Use `push_cast`. Use `mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)` and prove the remaining obligations.

Distinguish the cases in `hcase : y ≤ (B - 1) / l`. Establish `: i0 = y` using `by omega`. Rewrite using `[this, Nat.sub_self, Nat.choose_self, padicValNat_one_right]`. Simplify using the standard rewrite rules. Establish `hi : i0 = (B - 1) / l` using `by omega`.

Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Establish `hv` using `padicValNat_choose_le_logb (l := l) y i0`. Establish `hsub : ((y - i0 : ℕ) : ℝ) = (y : ℝ) - i0` using `by rw [Nat.cast_sub (by omega)]`. Establish `hBl : (B : ℝ) / l ≤ i0 + 1`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Establish `: (B : ℝ) ≤ ((l * ((B - 1) / l + 1) : ℕ) : ℝ)` using `by exact_mod_cast hq2`. Rewrite `this` using `[← hi]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Move the coercions through the operations in `[hsub]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem content_X_pow_p1_pow_le (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) (hl0 : (l : O) ≠ 0) (he : IsUnit e)
    (hu : IsUnit u) (hp : p1 = C (l : O) * e + u * X ^ l) (B y : ℕ) (hB : 1 ≤ B) :
    cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y) ≠ ⊤ ∧
    ((cont ϖ ((X : O⟦X⟧) ^ B) (p1 ^ y)).toNat : ℝ) ≤
      (IsDiscreteValuationRing.addVal O (l : O)).toNat * max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) := by
  set E := (IsDiscreteValuationRing.addVal O (l : O)).toNat
  have hlpos : 0 < l := hlp.out.pos
  obtain ⟨hX, hD⟩ := dist_X_pow (O := O) 1
  rw [pow_one] at hX hD
  have key := Mprime_cont hϖ hX (by rw [hD]) ((Finset.range (y + 1)).image (l * ·))
    (fun j => u ^ (j / l) * e ^ (y - j / l))
    (fun j _ => (hu.pow _).mul (he.pow _))
    (fun j => (y.choose (j / l) : O) * (l : O) ^ (y - j / l))
    (fun j hj => by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      rw [Nat.mul_div_cancel_left i hlpos]
      exact coef_ne_zero hl hl0 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) B
  rw [p1_pow_eq_sum_image_choose_mul_X_pow hp y, key]
  set i0 := min y ((B - 1) / l) with hi0
  have hq : l * ((B - 1) / l) ≤ B - 1 := Nat.mul_div_le (B - 1) l
  have hq2 : B ≤ l * ((B - 1) / l + 1) := by
    have h1 := Nat.div_add_mod (B - 1) l
    have h2 := Nat.mod_lt (B - 1) hlpos
    rw [mul_add, mul_one]; omega
  have hmem : l * i0 ∈ ((Finset.range (y + 1)).image (l * ·)).filter (· < B) := by
    rw [Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨i0, Finset.mem_range.mpr (by omega), rfl⟩, ?_⟩
    have : l * i0 ≤ l * ((B - 1) / l) := Nat.mul_le_mul_left l (min_le_right _ _)
    omega
  have hle := iInf₂_le (f := fun j (_ : j ∈ ((Finset.range (y + 1)).image (l * ·)).filter (· < B)) =>
    IsDiscreteValuationRing.addVal O ((y.choose (j / l) : O) * (l : O) ^ (y - j / l))) (l * i0) hmem
  simp only [Nat.mul_div_cancel_left i0 hlpos] at hle
  have hi0y : i0 ≤ y := by omega
  rw [addVal_coef hl hl0 hi0y] at hle
  refine ⟨ne_top_of_le_ne_top (ENat.natCast_ne_top _) hle, ?_⟩
  have hnat := ENat.toNat_le_of_le_natCast hle
  refine (Nat.cast_le.mpr hnat).trans ?_
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  by_cases hcase : y ≤ (B - 1) / l
  · have : i0 = y := by omega
    rw [this, Nat.sub_self, Nat.choose_self, padicValNat_one_right]
    simp
  · have hi : i0 = (B - 1) / l := by omega
    refine le_trans ?_ (le_max_right _ _)
    have hv := padicValNat_choose_le_logb (l := l) y i0
    have hsub : ((y - i0 : ℕ) : ℝ) = (y : ℝ) - i0 := by rw [Nat.cast_sub (by omega)]
    have hBl : (B : ℝ) / l ≤ i0 + 1 := by
      rw [div_le_iff₀ (by positivity)]
      have : (B : ℝ) ≤ ((l * ((B - 1) / l + 1) : ℕ) : ℝ) := by exact_mod_cast hq2
      rw [← hi] at this
      push_cast at this; linarith
    push_cast [hsub]
    linarith

end P1

end ContPA

end Formalism.MainNotions.N.FrobeniusPowerSeries
