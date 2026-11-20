import Mathlib
import ReciprocityTheory.GaloisValuations.Global

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField

namespace GlobalTheory.CycInertial

variable {K : Type} [Field K] {Γ : Type} [LinearOrderedCommGroupWithZero Γ]

/- English proof (translation)
Establish `hz1 : w z ≤ 1`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h2 : w z ^ n = 1` using `by rw [← map_pow, hz, map_one]`. Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hn`.

Rewrite `h2` using `[pow_succ]`. Establish `h3` using `mul_le_mul' (one_le_pow₀ h.le : 1 ≤ w z ^ m) (le_refl (w z))`. Rewrite `h3` using `[one_mul, h2]`. Conclude with `absurd h (not_lt.mpr h3)`. Take `⟨r, hr⟩` from `r`.

Use `show w r ≤ 1`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx => rw [Set.mem_singleton_iff.mp hx]`. Conclude with `hz1`. Consider the case `algebraMap m`.

Rewrite using `[algebraMap_int_eq, eq_intCast]`. Conclude with `(Valuation.mem_integer_iff w _).mp (intCast_mem _ m)`. Consider the case `add x y _ _ ihx ihy => exact (w.map_add x y).trans (max_le ihx ihy)`. Consider the case `mul x y _ _ ihx ihy => rw [map_mul]`. Conclude with `mul_le_one' ihx ihy`.
-/
theorem val_le_one (w : Valuation K Γ) {z : K} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1)
    (r : Algebra.adjoin ℤ ({z} : Set K)) : w (r : K) ≤ 1 := by
  have hz1 : w z ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : w z ^ n = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [pow_succ] at h2
    have h3 := mul_le_mul' (one_le_pow₀ h.le : 1 ≤ w z ^ m) (le_refl (w z))
    rw [one_mul, h2] at h3
    exact absurd h (not_lt.mpr h3)
  obtain ⟨r, hr⟩ := r
  show w r ≤ 1
  induction hr using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.mp hx]; exact hz1
  | algebraMap m =>
    rw [algebraMap_int_eq, eq_intCast]
    exact (Valuation.mem_integer_iff w _).mp (intCast_mem _ m)
  | add x y _ _ ihx ihy => exact (w.map_add x y).trans (max_le ihx ihy)
  | mul x y _ _ ihx ihy => rw [map_mul]; exact mul_le_one' ihx ihy

noncomputable def gen (z : K) : Algebra.adjoin ℤ ({z} : Set K) :=
  ⟨z, Algebra.subset_adjoin rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coe_gen (z : K) : (gen z : K) = z := rfl

/- English proof (translation)
Take `⟨r, hr⟩` from `r`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `rfl` from `Set.mem_singleton_iff.mp hx`. Conclude with `⟨1, 1, Subtype.ext (by simp)⟩`.

Consider the case `algebraMap m => exact ⟨m, 0, Subtype.ext (by simp)⟩`. Consider the case `add x y hx hy ihx ihy`. Take `⟨m₁, s₁, h₁⟩` from `ihx`. Take `⟨m₂, s₂, h₂⟩` from `ihy`. Use `⟨m₁ + m₂, s₁ + s₂, Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `e₁` using `congrArg Subtype.val h₁`. Establish `e₂` using `congrArg Subtype.val h₂`. Move the coercions through the operations in `[coe_gen, Subtype.coe_mk] at e₁ e₂ ⊢`. Rewrite using `[e₁, e₂]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `mul x y hx hy ihx ihy`. Take `⟨m₁, s₁, h₁⟩` from `ihx`. Take `⟨m₂, s₂, h₂⟩` from `ihy`. Use `⟨m₁ * m₂, (m₁ : Algebra.adjoin ℤ ({z} : Set K)) * s₂ + s₁ * m₂ + (gen z - 1) * s₁ * s₂, Subtype.ext ?_⟩` and prove the remaining obligations. Establish `e₁` using `congrArg Subtype.val h₁`.

Establish `e₂` using `congrArg Subtype.val h₂`. Move the coercions through the operations in `[coe_gen, Subtype.coe_mk] at e₁ e₂ ⊢`. Rewrite using `[e₁, e₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_int (z : K) (r : Algebra.adjoin ℤ ({z} : Set K)) :
    ∃ (m : ℤ) (s : Algebra.adjoin ℤ ({z} : Set K)), r = m + (gen z - 1) * s := by
  obtain ⟨r, hr⟩ := r
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨1, 1, Subtype.ext (by simp)⟩
  | algebraMap m => exact ⟨m, 0, Subtype.ext (by simp)⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨m₁, s₁, h₁⟩ := ihx
    obtain ⟨m₂, s₂, h₂⟩ := ihy
    refine ⟨m₁ + m₂, s₁ + s₂, Subtype.ext ?_⟩
    have e₁ := congrArg Subtype.val h₁
    have e₂ := congrArg Subtype.val h₂
    push_cast [coe_gen, Subtype.coe_mk] at e₁ e₂ ⊢
    rw [e₁, e₂]; ring
  | mul x y hx hy ihx ihy =>
    obtain ⟨m₁, s₁, h₁⟩ := ihx
    obtain ⟨m₂, s₂, h₂⟩ := ihy
    refine ⟨m₁ * m₂, (m₁ : Algebra.adjoin ℤ ({z} : Set K)) * s₂ + s₁ * m₂ + (gen z - 1) * s₁ * s₂,
      Subtype.ext ?_⟩
    have e₁ := congrArg Subtype.val h₁
    have e₂ := congrArg Subtype.val h₂
    push_cast [coe_gen, Subtype.coe_mk] at e₁ e₂ ⊢
    rw [e₁, e₂]; ring

/- English proof (translation)
Establish `hn : l ^ k ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Take `⟨r, hr⟩` from `exists_add_pow_prime_pow_eq hl (gen z - 1) 1 k`. Establish `e` using `congrArg Subtype.val hr`. Move the coercions through the operations in `[coe_gen] at e`. Establish `key : (z - 1) ^ (l ^ k) = -((l : K) * (z - 1) * (r : K))`.

Take the linear combination `-e + hz`. Establish `h₁ : w (z - 1) ≤ 1` using `by simpa using val_le_one w hn hz (gen z - 1)`. Establish `h₂ : w (r : K) ≤ 1` using `val_le_one w hn hz r`. Establish `h₃ : w (z - 1) ^ (l ^ k) < 1`. Rewrite using `[← map_pow, key, Valuation.map_neg, map_mul, map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `absurd h₃ (not_lt.mpr (one_le_pow₀ h))`.
-/
theorem val_sub_one_lt (w : Valuation K Γ) {l k : ℕ} (hl : l.Prime) (hw : w (l : K) < 1)
    {z : K} (hz : z ^ (l ^ k) = 1) : w (z - 1) < 1 := by
  have hn : l ^ k ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (gen z - 1) 1 k
  have e := congrArg Subtype.val hr
  push_cast [coe_gen] at e
  have key : (z - 1) ^ (l ^ k) = -((l : K) * (z - 1) * (r : K)) := by
    linear_combination -e + hz
  have h₁ : w (z - 1) ≤ 1 := by simpa using val_le_one w hn hz (gen z - 1)
  have h₂ : w (r : K) ≤ 1 := val_le_one w hn hz r
  have h₃ : w (z - 1) ^ (l ^ k) < 1 := by
    rw [← map_pow, key, Valuation.map_neg, map_mul, map_mul]
    calc w (l : K) * w (z - 1) * w (r : K) ≤ w (l : K) * 1 * 1 :=
          mul_le_mul' (mul_le_mul' le_rfl h₁) h₂
      _ < 1 := by simpa using hw
  by_contra h
  push_neg at h
  exact absurd h₃ (not_lt.mpr (one_le_pow₀ h))

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Establish `hζ : IsPrimitiveRoot (z ^ l ^ k) l`. Use `hz.pow_of_dvd (pow_ne_zero k hl.ne_zero) (pow_dvd_pow l k.le_succ)` as an intermediate fact. Rewrite `this` using `[pow_succ, Nat.mul_div_cancel_left _ (pow_pos hl.pos k)]`. Then use the resulting hypothesis. Establish `hsum` using `hζ.geom_sum_eq_zero hl.one_lt`.

Establish `key : (l : Algebra.adjoin ℤ ({z} : Set K)) = ∑ i ∈ Finset.range l, (1 - (gen z ^ l ^ k) ^ i)`. Apply `Subtype.ext` to reduce the goal to its premises. Move the coercions through the operations in `[coe_gen]`. Rewrite using `[Finset.sum_sub_distrib, hsum]`. Simplify using the standard rewrite rules.

Rewrite using `[key]`. Use `Finset.dvd_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← neg_sub ((gen z ^ l ^ k) ^ i) 1, dvd_neg, ← pow_mul]`. Conclude with `sub_one_dvd_pow_sub_one _ _`.
-/
theorem sub_one_dvd [CharZero K] {l k : ℕ} [Fact l.Prime] {z : K}
    (hz : IsPrimitiveRoot z (l ^ (k + 1))) :
    gen z - 1 ∣ (l : Algebra.adjoin ℤ ({z} : Set K)) := by
  have hl := (Fact.out : l.Prime)
  have hζ : IsPrimitiveRoot (z ^ l ^ k) l := by
    have := hz.pow_of_dvd (pow_ne_zero k hl.ne_zero) (pow_dvd_pow l k.le_succ)
    rwa [pow_succ, Nat.mul_div_cancel_left _ (pow_pos hl.pos k)] at this
  have hsum := hζ.geom_sum_eq_zero hl.one_lt
  have key : (l : Algebra.adjoin ℤ ({z} : Set K)) =
      ∑ i ∈ Finset.range l, (1 - (gen z ^ l ^ k) ^ i) := by
    apply Subtype.ext
    push_cast [coe_gen]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  rw [key]
  refine Finset.dvd_sum fun i _ => ?_
  rw [← neg_sub ((gen z ^ l ^ k) ^ i) 1, dvd_neg, ← pow_mul]
  exact sub_one_dvd_pow_sub_one _ _

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Establish `hn : l ^ (k + 1) ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Take `⟨m, s, rfl⟩` from `exists_int z u`. Establish `hm : ¬ (l : ℤ) ∣ m`. Introduce and unpack `⟨c, rfl⟩`.

Apply `hu` to reduce the goal to its premises. Take `⟨t, ht⟩` from `sub_one_dvd hz`. Conclude with `⟨t * c + s, by push_cast; rw [ht]; ring⟩`. Establish `hint : ∀ a : ℤ, w (a : K) ≤ 1` using `fun a => by`. Simplify using `using val_le_one w hn hz.pow_eq_one (a : Algebra.adjoin ℤ ({z} : Set K))`.

Establish `hwm : w (m : K) = 1`. Use `le_antisymm (hint m) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨a, b, hab⟩` from `(Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hl).irreducible).mpr hm`.

Establish `e : ((a * l + b * m : ℤ) : K) = 1` using `by rw [hab]; simp`. Move the coercions through the operations in `at e`. Establish `h₀` using `w.map_add ((a : K) * l) ((b : K) * m)`. Rewrite `h₀` using `[e, map_one, map_mul, map_mul]`. Establish `h₁ : w (a : K) * w (l : K) < 1` using `lt_of_le_of_lt (by simpa using mul_le_mul' (hint a) (le_refl (w (l : K)))) hw`.

Establish `h₂ : w (b : K) * w (m : K) < 1` using `lt_of_le_of_lt (by simpa using mul_le_mul' (hint b) (le_refl (w (m : K)))) h`. Conclude with `absurd h₀ (not_le.mpr (max_lt h₁ h₂))`. Establish `hzs : w ((z - 1) * s) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Move the coercions through the operations in `[coe_gen]`. Rewrite using `[Valuation.map_add_eq_of_lt_left _ (by rw [hwm]; exact hzs), hwm]`.
-/
theorem val_eq_one [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1))) (u : Algebra.adjoin ℤ ({z} : Set K))
    (hu : ¬ gen z - 1 ∣ u) : w (u : K) = 1 := by
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  obtain ⟨m, s, rfl⟩ := exists_int z u
  have hm : ¬ (l : ℤ) ∣ m := by
    rintro ⟨c, rfl⟩
    apply hu
    obtain ⟨t, ht⟩ := sub_one_dvd hz
    exact ⟨t * c + s, by push_cast; rw [ht]; ring⟩
  have hint : ∀ a : ℤ, w (a : K) ≤ 1 := fun a => by
    simpa using val_le_one w hn hz.pow_eq_one (a : Algebra.adjoin ℤ ({z} : Set K))
  have hwm : w (m : K) = 1 := by
    refine le_antisymm (hint m) ?_
    by_contra h
    push_neg at h
    obtain ⟨a, b, hab⟩ :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hl).irreducible).mpr hm
    have e : ((a * l + b * m : ℤ) : K) = 1 := by rw [hab]; simp
    push_cast at e
    have h₀ := w.map_add ((a : K) * l) ((b : K) * m)
    rw [e, map_one, map_mul, map_mul] at h₀
    have h₁ : w (a : K) * w (l : K) < 1 :=
      lt_of_le_of_lt (by simpa using mul_le_mul' (hint a) (le_refl (w (l : K)))) hw
    have h₂ : w (b : K) * w (m : K) < 1 :=
      lt_of_le_of_lt (by simpa using mul_le_mul' (hint b) (le_refl (w (m : K)))) h
    exact absurd h₀ (not_le.mpr (max_lt h₁ h₂))
  have hzs : w ((z - 1) * s) < 1 := by
    rw [map_mul]
    calc w (z - 1) * w (s : K) ≤ w (z - 1) * 1 :=
          mul_le_mul' le_rfl (val_le_one w hn hz.pow_eq_one s)
      _ < 1 := by rw [mul_one]; exact val_sub_one_lt w hl hw hz.pow_eq_one
  push_cast [coe_gen]
  rw [Valuation.map_add_eq_of_lt_left _ (by rw [hwm]; exact hzs), hwm]

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Establish `hn : l ^ (k + 1) ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Establish `: IsNoetherianRing (Algebra.adjoin ℤ ({z} : Set K))` using `isNoetherianRing_of_fg ⟨{z}, by simp⟩`. Establish `hz1 : w (z - 1) < 1` using `val_sub_one_lt w hl hw hz.pow_eq_one`. Establish `hz0 : z - 1 ≠ 0` using `fun h => hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)`.

Establish `hnz : gen z - 1 ≠ 0` using `fun h => hz0 (by simpa using congrArg Subtype.val h)`. Establish `hnu : ¬ IsUnit (gen z - 1)`. Introduce `h`. Take `⟨y, hy⟩` from `isUnit_iff_exists_inv.mp h`. Establish `e` using `congrArg (fun t : Algebra.adjoin ℤ ({z} : Set K) => w (t : K)) hy`.

Move the coercions through the operations in `[coe_gen] at e`. Rewrite `e` using `[map_mul, map_one]`. Establish `h₁ : w (z - 1) * w (y : K) < 1` using `(mul_le_mul' (le_refl (w (z - 1))) (val_le_one w hn hz.pow_eq_one y)).trans_lt (by rwa [mul_one])`. Conclude with `absurd e h₁.ne`. Take `⟨b, s₀, hs₀, hseq⟩` from `WfDvdMonoid.max_power_factor' hs hnu`.

Establish `hs₀' : s₀ ≠ 0` using `by rintro rfl; exact hs₀ (dvd_zero _)`. Establish `hs₀K : (s₀ : K) ≠ 0` using `by exact_mod_cast hs₀'`. Distinguish the cases in `hr : r = 0`. Use `left`. Use `⟨0, 1, fun h => hnu (isUnit_iff_dvd_one.mpr h), ?_⟩` and prove the remaining obligations.

Substitute `hr` using the available equality. Simplify using the standard rewrite rules. Take `⟨a, r₀, hr₀, hreq⟩` from `WfDvdMonoid.max_power_factor' hr hnu`. Break down `le_or_gt b a with hab | hab` into its components or cases. Use `left`.

Take `⟨c, rfl⟩ : ∃ c, a = b + c` from `⟨a - b, by omega⟩`. Use `⟨(gen z - 1) ^ c * r₀, s₀, hs₀, ?_⟩` and prove the remaining obligations. Rewrite using `[hreq, hseq]`. Move the coercions through the operations in `[coe_gen]`. Rewrite using `[div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K) hs₀K]`.

Expand and normalize the polynomial expressions, which then agree. Use `right`. Take `⟨c, rfl⟩ : ∃ c, b = a + c + 1` from `⟨b - a - 1, by omega⟩`. Use `⟨r₀, (gen z - 1) ^ c * s₀, hr₀, mul_ne_zero (pow_ne_zero _ hnz) hs₀', ?_⟩` and prove the remaining obligations. Rewrite using `[hreq, hseq]`.

Move the coercions through the operations in `[coe_gen]`. Rewrite using `[div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K) (mul_ne_zero hz0 (mul_ne_zero (pow_ne_zero _ hz0) hs₀K))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_shape [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1))) (r s : Algebra.adjoin ℤ ({z} : Set K))
    (hs : s ≠ 0) :
    (∃ r' u : Algebra.adjoin ℤ ({z} : Set K), ¬ gen z - 1 ∣ u ∧ (r : K) / s = r' / u) ∨
    (∃ u s' : Algebra.adjoin ℤ ({z} : Set K), ¬ gen z - 1 ∣ u ∧ s' ≠ 0 ∧
      (r : K) / s = u / ((z - 1) * s')) := by
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have : IsNoetherianRing (Algebra.adjoin ℤ ({z} : Set K)) :=
    isNoetherianRing_of_fg ⟨{z}, by simp⟩
  have hz1 : w (z - 1) < 1 := val_sub_one_lt w hl hw hz.pow_eq_one
  have hz0 : z - 1 ≠ 0 := fun h =>
    hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)
  have hnz : gen z - 1 ≠ 0 := fun h => hz0 (by simpa using congrArg Subtype.val h)
  have hnu : ¬ IsUnit (gen z - 1) := by
    intro h
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp h
    have e := congrArg (fun t : Algebra.adjoin ℤ ({z} : Set K) => w (t : K)) hy
    push_cast [coe_gen] at e
    rw [map_mul, map_one] at e
    have h₁ : w (z - 1) * w (y : K) < 1 :=
      (mul_le_mul' (le_refl (w (z - 1))) (val_le_one w hn hz.pow_eq_one y)).trans_lt
        (by rwa [mul_one])
    exact absurd e h₁.ne
  obtain ⟨b, s₀, hs₀, hseq⟩ := WfDvdMonoid.max_power_factor' hs hnu
  have hs₀' : s₀ ≠ 0 := by rintro rfl; exact hs₀ (dvd_zero _)
  have hs₀K : (s₀ : K) ≠ 0 := by exact_mod_cast hs₀'
  by_cases hr : r = 0
  · left
    refine ⟨0, 1, fun h => hnu (isUnit_iff_dvd_one.mpr h), ?_⟩
    subst hr
    simp
  obtain ⟨a, r₀, hr₀, hreq⟩ := WfDvdMonoid.max_power_factor' hr hnu
  rcases le_or_gt b a with hab | hab
  · left
    obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
    refine ⟨(gen z - 1) ^ c * r₀, s₀, hs₀, ?_⟩
    rw [hreq, hseq]
    push_cast [coe_gen]
    rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K) hs₀K]
    ring
  · right
    obtain ⟨c, rfl⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    refine ⟨r₀, (gen z - 1) ^ c * s₀, hr₀, mul_ne_zero (pow_ne_zero _ hnz) hs₀', ?_⟩
    rw [hreq, hseq]
    push_cast [coe_gen]
    rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hz0) hs₀K)
      (mul_ne_zero hz0 (mul_ne_zero (pow_ne_zero _ hz0) hs₀K))]
    ring

/- English proof (translation)
Introduce `h`. Establish `hl` using `(Fact.out : l.Prime)`. Establish `hn : l ^ (k + 1) ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Establish `hz0 : z - 1 ≠ 0` using `fun h => hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)`. Establish `hsK : (s : K) ≠ 0` using `by exact_mod_cast hs`.

Establish `hd0 : (z - 1) * (s : K) ≠ 0` using `mul_ne_zero hz0 hsK`. Establish `hd : w ((z - 1) * s) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `e : (u : K) = u / ((z - 1) * s) * ((z - 1) * s)` using `(div_mul_cancel₀ _ hd0).symm`.

Establish `e'` using `congrArg w e`. Rewrite `e'` using `[map_mul, val_eq_one w hw hz u hu]`. Establish `h₁ : w ((u : K) / ((z - 1) * s)) * w ((z - 1) * s) < 1` using `lt_of_le_of_lt (by simpa using mul_le_mul' h (le_refl (w ((z - 1) * s)))) hd`. Conclude with `absurd e' (ne_of_gt h₁)`.
-/
theorem not_le_one [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1))) (u s : Algebra.adjoin ℤ ({z} : Set K))
    (hu : ¬ gen z - 1 ∣ u) (hs : s ≠ 0) : ¬ w ((u : K) / ((z - 1) * s)) ≤ 1 := by
  intro h
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hz0 : z - 1 ≠ 0 := fun h =>
    hz.ne_one (Nat.one_lt_pow (Nat.succ_ne_zero k) hl.one_lt) (sub_eq_zero.mp h)
  have hsK : (s : K) ≠ 0 := by exact_mod_cast hs
  have hd0 : (z - 1) * (s : K) ≠ 0 := mul_ne_zero hz0 hsK
  have hd : w ((z - 1) * s) < 1 := by
    rw [map_mul]
    calc w (z - 1) * w (s : K) ≤ w (z - 1) * 1 :=
          mul_le_mul' le_rfl (val_le_one w hn hz.pow_eq_one s)
      _ < 1 := by rw [mul_one]; exact val_sub_one_lt w hl hw hz.pow_eq_one
  have e : (u : K) = u / ((z - 1) * s) * ((z - 1) * s) := (div_mul_cancel₀ _ hd0).symm
  have e' := congrArg w e
  rw [map_mul, val_eq_one w hw hz u hu] at e'
  have h₁ : w ((u : K) / ((z - 1) * s)) * w ((z - 1) * s) < 1 :=
    lt_of_le_of_lt (by simpa using mul_le_mul' h (le_refl (w ((z - 1) * s)))) hd
  exact absurd e' (ne_of_gt h₁)

/- English proof (translation)
Take `⟨i, -, hi⟩` from `hz.eq_pow_of_pow_eq_one (ξ := τ z) (by rw [← map_pow, hz.pow_eq_one, map_one])`. Take `⟨c, hc⟩` from `sub_one_dvd_pow_sub_one (gen z) i`. Establish `ec` using `congrArg Subtype.val hc`. Move the coercions through the operations in `[coe_gen] at ec`. Take `⟨r, hr⟩` from `r`.

Use `show ∃ t : Algebra.adjoin ℤ ({z} : Set K), τ r = r + (z - 1) * t`. Proceed by induction on `hr using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Rewrite using `[Set.mem_singleton_iff.mp hx]`. Use `⟨c - 1, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[← hi]`. Take the linear combination `ec`. Consider the case `algebraMap m => exact ⟨0, by simp⟩`. Consider the case `add x y hx hy ihx ihy`.

Take `⟨t₁, h₁⟩` from `ihx`. Take `⟨t₂, h₂⟩` from `ihy`. Conclude with `⟨t₁ + t₂, by push_cast; rw [map_add, h₁, h₂]; ring⟩`. Consider the case `mul x y hx hy ihx ihy`. Take `⟨t₁, h₁⟩` from `ihx`.

Take `⟨t₂, h₂⟩` from `ihy`. Use `⟨t₁ * ⟨y, hy⟩ + ⟨x, hx⟩ * t₂ + (gen z - 1) * t₁ * t₂, ?_⟩` and prove the remaining obligations. Move the coercions through the operations in `[coe_gen, Subtype.coe_mk]`. Rewrite using `[map_mul, h₁, h₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one {z : K} {n : ℕ} [NeZero n] (hz : IsPrimitiveRoot z n)
    (τ : K →+* K) (r : Algebra.adjoin ℤ ({z} : Set K)) :
    ∃ t : Algebra.adjoin ℤ ({z} : Set K), τ r = r + (z - 1) * t := by
  obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one (ξ := τ z) (by rw [← map_pow, hz.pow_eq_one, map_one])
  obtain ⟨c, hc⟩ := sub_one_dvd_pow_sub_one (gen z) i
  have ec := congrArg Subtype.val hc
  push_cast [coe_gen] at ec
  obtain ⟨r, hr⟩ := r
  show ∃ t : Algebra.adjoin ℤ ({z} : Set K), τ r = r + (z - 1) * t
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    refine ⟨c - 1, ?_⟩
    push_cast
    rw [← hi]
    linear_combination ec
  | algebraMap m => exact ⟨0, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨t₁, h₁⟩ := ihx
    obtain ⟨t₂, h₂⟩ := ihy
    exact ⟨t₁ + t₂, by push_cast; rw [map_add, h₁, h₂]; ring⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨t₁, h₁⟩ := ihx
    obtain ⟨t₂, h₂⟩ := ihy
    refine ⟨t₁ * ⟨y, hy⟩ + ⟨x, hx⟩ * t₂ + (gen z - 1) * t₁ * t₂, ?_⟩
    push_cast [coe_gen, Subtype.coe_mk]
    rw [map_mul, h₁, h₂]
    ring

/- English proof (translation)
Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `absurd h (not_lt.mpr zero_le)`. Assume the negation of the conclusion as `h'`. Use `push_neg at h'`.

Establish `h₁` using `mul_le_mul' (le_refl a) h'`. Rewrite `h₁` using `[mul_one, mul_inv_cancel₀ ha]`. Conclude with `absurd h (not_lt.mpr h₁)`.
-/
private theorem inv_lt_one_of_one_lt' {a : Γ} (h : 1 < a) : a⁻¹ < 1 := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact absurd h (not_lt.mpr zero_le)
  by_contra h'
  push_neg at h'
  have h₁ := mul_le_mul' (le_refl a) h'
  rw [mul_one, mul_inv_cancel₀ ha] at h₁
  exact absurd h (not_lt.mpr h₁)

/- English proof (translation)
Establish `hl` using `(Fact.out : l.Prime)`. Establish `hn : l ^ (k + 1) ≠ 0` using `pow_ne_zero _ hl.ne_zero`. Establish `: NeZero (l ^ (k + 1))` using `⟨hn⟩`. Establish `hz1` using `val_sub_one_lt w hl hw hz.pow_eq_one`. Establish `small : ∀ t : Algebra.adjoin ℤ ({z} : Set K), w ((z - 1) * t) < 1` using `fun t => by`.

Rewrite using `[map_mul]`. Conclude with `(mul_le_mul' le_rfl (val_le_one w hn hz.pow_eq_one t)).trans_lt (by rwa [mul_one])`. Establish `part1 : ∀ x, w x ≤ 1 → w (τ x - x) < 1`. Introduce `x hx`. Take `⟨r, s, hs, rfl⟩` from `hfrac x`.

Break down `exists_shape w hw hz r s hs with ⟨r', u, hu, he⟩ | ⟨u, s', hu, hs', he⟩` into its components or cases. Rewrite `hx`, the goal using `[he]`. Establish `hu1` using `val_eq_one w hw hz u hu`. Establish `hu0 : (u : K) ≠ 0` using `fun h => by simp [h] at hu1`. Take `⟨t₁, h₁⟩` from `ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one hz τ r'`.

Take `⟨t₂, h₂⟩` from `ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one hz τ u`. Establish `hτu : w (τ u) = 1`. Rewrite using `[h₂, Valuation.map_add_eq_of_lt_left _ (by rw [hu1]; exact small t₂), hu1]`. Establish `hτu0 : τ (u : K) ≠ 0` using `fun h => by simp [h] at hτu`. Establish `e : τ ((r' : K) / u) - r' / u = (z - 1) * ((t₁ * u - r' * t₂ : Algebra.adjoin ℤ ({z} : Set K)) : K) / (τ u * u)`.

Rewrite using `[map_div₀, div_sub_div _ _ hτu0 hu0]`. Use `push_cast`. Rewrite using `[h₁, h₂]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, map_div₀, Valuation.map_mul w (τ _) _, hτu, hu1, mul_one, div_one]`.

Conclude with `small _`. It suffices to derive a contradiction. Rewrite `hx` using `[he]`. Conclude with `not_le_one w hw hz u s' hu hs' hx`. Use `⟨part1, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hx push_neg at hx`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`. Establish `hy : w x⁻¹ < 1` using `by rw [map_inv₀]; exact inv_lt_one_of_one_lt' hx`.

Establish `hτy : w (τ x⁻¹) < 1`. Establish `e : τ x⁻¹ = (τ x⁻¹ - x⁻¹) + x⁻¹` using `by ring`. Rewrite using `[e]`. Conclude with `(w.map_add _ _).trans_lt (max_lt (part1 _ hy.le) hy)`. Rewrite `hτy` using `[map_inv₀, map_inv₀]`.

Establish `hτx0 : w (τ x) ≠ 0`. Rewrite using `[Valuation.ne_zero_iff, map_ne_zero]`. Conclude with `hx0`. Establish `h₁` using `mul_le_mul' h (le_refl (w (τ x))⁻¹)`. Rewrite `h₁` using `[mul_inv_cancel₀ hτx0, one_mul]`.

Conclude with `absurd hτy (not_lt.mpr h₁)`. Establish `e : τ x = (τ x - x) + x` using `by ring`. Rewrite using `[e]`. Conclude with `(w.map_add _ _).trans (max_le (part1 x h).le h)`.
-/
theorem core [CharZero K] (w : Valuation K Γ) {l k : ℕ} [Fact l.Prime] (hw : w (l : K) < 1)
    {z : K} (hz : IsPrimitiveRoot z (l ^ (k + 1)))
    (hfrac : ∀ x : K, ∃ r s : Algebra.adjoin ℤ ({z} : Set K), s ≠ 0 ∧ x = r / s) (τ : K →+* K) :
    (∀ x, w x ≤ 1 → w (τ x - x) < 1) ∧ (∀ x, w (τ x) ≤ 1 ↔ w x ≤ 1) := by
  have hl := (Fact.out : l.Prime)
  have hn : l ^ (k + 1) ≠ 0 := pow_ne_zero _ hl.ne_zero
  have : NeZero (l ^ (k + 1)) := ⟨hn⟩
  have hz1 := val_sub_one_lt w hl hw hz.pow_eq_one
  have small : ∀ t : Algebra.adjoin ℤ ({z} : Set K), w ((z - 1) * t) < 1 := fun t => by
    rw [map_mul]
    exact (mul_le_mul' le_rfl (val_le_one w hn hz.pow_eq_one t)).trans_lt (by rwa [mul_one])
  have part1 : ∀ x, w x ≤ 1 → w (τ x - x) < 1 := by
    intro x hx
    obtain ⟨r, s, hs, rfl⟩ := hfrac x
    rcases exists_shape w hw hz r s hs with ⟨r', u, hu, he⟩ | ⟨u, s', hu, hs', he⟩
    · rw [he] at hx ⊢
      have hu1 := val_eq_one w hw hz u hu
      have hu0 : (u : K) ≠ 0 := fun h => by simp [h] at hu1
      obtain ⟨t₁, h₁⟩ := ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one hz τ r'
      obtain ⟨t₂, h₂⟩ := ringHom_adjoin_primitiveRoot_eq_add_mul_sub_one hz τ u
      have hτu : w (τ u) = 1 := by
        rw [h₂, Valuation.map_add_eq_of_lt_left _ (by rw [hu1]; exact small t₂), hu1]
      have hτu0 : τ (u : K) ≠ 0 := fun h => by simp [h] at hτu
      have e : τ ((r' : K) / u) - r' / u =
          (z - 1) * ((t₁ * u - r' * t₂ : Algebra.adjoin ℤ ({z} : Set K)) : K) / (τ u * u) := by
        rw [map_div₀, div_sub_div _ _ hτu0 hu0]
        push_cast
        rw [h₁, h₂]
        ring
      rw [e, map_div₀, Valuation.map_mul w (τ _) _, hτu, hu1, mul_one, div_one]
      exact small _
    · exfalso
      rw [he] at hx
      exact not_le_one w hw hz u s' hu hs' hx
  refine ⟨part1, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hx
    push_neg at hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have hy : w x⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt' hx
    have hτy : w (τ x⁻¹) < 1 := by
      have e : τ x⁻¹ = (τ x⁻¹ - x⁻¹) + x⁻¹ := by ring
      rw [e]
      exact (w.map_add _ _).trans_lt (max_lt (part1 _ hy.le) hy)
    rw [map_inv₀, map_inv₀] at hτy
    have hτx0 : w (τ x) ≠ 0 := by
      rw [Valuation.ne_zero_iff, map_ne_zero]
      exact hx0
    have h₁ := mul_le_mul' h (le_refl (w (τ x))⁻¹)
    rw [mul_inv_cancel₀ hτx0, one_mul] at h₁
    exact absurd hτy (not_lt.mpr h₁)
  · have e : τ x = (τ x - x) + x := by ring
    rw [e]
    exact (w.map_add _ _).trans (max_le (part1 x h).le h)

/- English proof (translation)
Establish `: CharZero Ω` using `algebraRat.charZero (R := Ω)`. Establish `hcoe : ∀ P : Polynomial ℤ, ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ) P : IntermediateField.adjoin ℚ {ζ}) : Ω) = Polynomial.aeval ζ P`. Introduce `P`. Establish `h` using `Polynomial.aeval_algHom_apply (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).toIntAlgHom (IntermediateField.AdjoinSimple.gen ℚ ζ) P`. Simplify using `using h.symm`.

Take `⟨p, q, hpq⟩` from `(IntermediateField.mem_adjoin_simple_iff (F := ℚ) (x : Ω)).mp x.2`. Take `⟨bp, hbp, hP⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p`. Take `⟨bq, hbq, hQ⟩` from `IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q`. Establish `hbp0 : (bp : Ω) ≠ 0` using `by exact_mod_cast nonZeroDivisors.ne_zero hbp`. Establish `hbq0 : (bq : Ω) ≠ 0` using `by exact_mod_cast nonZeroDivisors.ne_zero hbq`.

Establish `eP : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) = bp * Polynomial.aeval ζ p`. Rewrite using `[← Polynomial.aeval_map_algebraMap (A := ℚ), hP]`. Simplify using `[zsmul_eq_mul]`. Establish `eQ : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) q) = bq * Polynomial.aeval ζ q`. Rewrite using `[← Polynomial.aeval_map_algebraMap (A := ℚ), hQ]`.

Simplify using `[zsmul_eq_mul]`. Distinguish the cases in `hB : Polynomial.aeval ζ q = 0`. Use `⟨0, 1, one_ne_zero, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `[hpq, hB]`. Use `⟨(bq : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} : Set (IntermediateField.adjoin ℚ {ζ}))) * ⟨Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p), Polynomial.aeval_mem_adjoin_singleton ℤ _⟩, (bp : A …` and prove the remaining obligations.

Introduce `h`. Establish `h'` using `congrArg (fun t : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} : Set (IntermediateField.adjoin ℚ {ζ})) => ((t : IntermediateField.adjoin ℚ {ζ}) : Ω)) h`. Move the coercions through the operations in `[Subtype.coe_mk, hcoe] at h'`. Rewrite `h'` using `[eQ]`. Conclude with `mul_ne_zero hbp0 (mul_ne_zero hbq0 hB) h'`.

Apply `Subtype.ext` to reduce the goal to its premises. Move the coercions through the operations in `[Subtype.coe_mk, hcoe]`. Rewrite using `[eP, eQ, hpq]`. Clear the denominators using the available nonvanishing facts.
-/
theorem frac (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ζ : Ω) (x : IntermediateField.adjoin ℚ {ζ}) :
    ∃ r s : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ})), s ≠ 0 ∧ x = r / s := by
  have : CharZero Ω := algebraRat.charZero (R := Ω)
  have hcoe : ∀ P : Polynomial ℤ,
      ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ) P :
        IntermediateField.adjoin ℚ {ζ}) : Ω) = Polynomial.aeval ζ P := by
    intro P
    have h := Polynomial.aeval_algHom_apply
      (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).toIntAlgHom
      (IntermediateField.AdjoinSimple.gen ℚ ζ) P
    simpa using h.symm
  obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (F := ℚ) (x : Ω)).mp x.2
  obtain ⟨bp, hbp, hP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) p
  obtain ⟨bq, hbq, hQ⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) q
  have hbp0 : (bp : Ω) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hbp
  have hbq0 : (bq : Ω) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hbq
  have eP : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p) =
      bp * Polynomial.aeval ζ p := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ), hP]
    simp [zsmul_eq_mul]
  have eQ : Polynomial.aeval ζ (IsLocalization.integerNormalization (nonZeroDivisors ℤ) q) =
      bq * Polynomial.aeval ζ q := by
    rw [← Polynomial.aeval_map_algebraMap (A := ℚ), hQ]
    simp [zsmul_eq_mul]
  by_cases hB : Polynomial.aeval ζ q = 0
  · refine ⟨0, 1, one_ne_zero, Subtype.ext ?_⟩
    simp [hpq, hB]
  refine ⟨(bq : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ}))) *
      ⟨Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) p),
        Polynomial.aeval_mem_adjoin_singleton ℤ _⟩,
    (bp : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ}))) *
      ⟨Polynomial.aeval (IntermediateField.AdjoinSimple.gen ℚ ζ)
        (IsLocalization.integerNormalization (nonZeroDivisors ℤ) q),
        Polynomial.aeval_mem_adjoin_singleton ℤ _⟩, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun t : Algebra.adjoin ℤ ({IntermediateField.AdjoinSimple.gen ℚ ζ} :
      Set (IntermediateField.adjoin ℚ {ζ})) => ((t : IntermediateField.adjoin ℚ {ζ}) : Ω)) h
    push_cast [Subtype.coe_mk, hcoe] at h'
    rw [eQ] at h'
    exact mul_ne_zero hbp0 (mul_ne_zero hbq0 hB) h'
  · apply Subtype.ext
    push_cast [Subtype.coe_mk, hcoe]
    rw [eP, eQ, hpq]
    field_simp

/- English proof (translation)
Introduce `Ω _ _ l k _ A hA ζ hζ τ`. Break down `k with _ | k` into its components or cases. Rewrite `hζ` using `[pow_zero, IsPrimitiveRoot.one_right_iff]`. Substitute `hζ` using the available equality. Establish `hτ : ∀ x : IntermediateField.adjoin ℚ {(1 : Ω)}, τ x = x`.

Introduce `x`. Establish `hx : (x : Ω) ∈ (⊥ : IntermediateField ℚ Ω)`. Rewrite using `[← IntermediateField.adjoin_simple_eq_bot_iff.mpr (one_mem _)]`. Conclude with `x.2`. Take `⟨q, hq⟩` from `IntermediateField.mem_bot.mp hx`.

Establish `e : x = algebraMap ℚ _ q` using `Subtype.ext (by simpa using hq.symm)`. Rewrite using `[e, AlgEquiv.commutes]`. Conclude with `⟨fun x _ => by simp [hτ x], fun x => by simp [hτ x]⟩`. Establish `: CharZero (IntermediateField.adjoin ℚ {ζ})` using `algebraRat.charZero (R := IntermediateField.adjoin ℚ {ζ})`. Establish `hg : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen ℚ ζ) (l ^ (k + 1))` using `IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω) (by simpa using hζ) (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).injective`.

Establish `hw : (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω)) (l : IntermediateField.adjoin ℚ {ζ}) < 1`. Simplify `hA` using `[Valuation.comap_apply]`. Take `⟨h₁, h₂⟩` from `core (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω)) hw hg (frac Ω ζ) τ.toRingHom`. Use `⟨fun x hx => ?_, fun x => ?_⟩` and prove the remaining obligations. Simplify `h₁ x (by simpa [Valuation.comap_apply] using hx)` using `[Valuation.comap_apply]`.

Simplify `h₂ x` using `[Valuation.comap_apply]`.
-/
theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (l k : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ k) → ∀ τ : (IntermediateField.adjoin ℚ {ζ}) ≃ₐ[ℚ] (IntermediateField.adjoin ℚ {ζ}), (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) ∧ (∀ x : IntermediateField.adjoin ℚ {ζ}, A.valuation ((τ x : IntermediateField.adjoin ℚ {ζ}) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) := by
  intro Ω _ _ l k _ A hA ζ hζ τ
  rcases k with _ | k
  · rw [pow_zero, IsPrimitiveRoot.one_right_iff] at hζ
    subst hζ
    have hτ : ∀ x : IntermediateField.adjoin ℚ {(1 : Ω)}, τ x = x := by
      intro x
      have hx : (x : Ω) ∈ (⊥ : IntermediateField ℚ Ω) := by
        rw [← IntermediateField.adjoin_simple_eq_bot_iff.mpr (one_mem _)]
        exact x.2
      obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hx
      have e : x = algebraMap ℚ _ q := Subtype.ext (by simpa using hq.symm)
      rw [e, AlgEquiv.commutes]
    exact ⟨fun x _ => by simp [hτ x], fun x => by simp [hτ x]⟩
  · have : CharZero (IntermediateField.adjoin ℚ {ζ}) :=
      algebraRat.charZero (R := IntermediateField.adjoin ℚ {ζ})
    have hg : IsPrimitiveRoot (IntermediateField.AdjoinSimple.gen ℚ ζ) (l ^ (k + 1)) :=
      IsPrimitiveRoot.of_map_of_injective (f := algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω)
        (by simpa using hζ) (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω).injective
    have hw : (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω))
        (l : IntermediateField.adjoin ℚ {ζ}) < 1 := by
      simpa [Valuation.comap_apply] using hA
    obtain ⟨h₁, h₂⟩ := core (A.valuation.comap (algebraMap (IntermediateField.adjoin ℚ {ζ}) Ω))
      hw hg (frac Ω ζ) τ.toRingHom
    refine ⟨fun x hx => ?_, fun x => ?_⟩
    · simpa [Valuation.comap_apply] using h₁ x (by simpa [Valuation.comap_apply] using hx)
    · simpa [Valuation.comap_apply] using h₂ x

end GlobalTheory.CycInertial
