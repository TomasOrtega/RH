import Mathlib
import GroundTheory.FunctionField.PlaceDefs
import GroundTheory.FunctionField.PlaceBasic
import GroundTheory.FunctionField.Approximation
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

open Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `fun h0 => hx (h0 ▸ isAlgebraic_zero)`. Establish `hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0` using `fun p hp h0 => hx ⟨p, hp, h0⟩`. Distinguish the cases in `h0 : h = 0`. Conclude with `⟨0, 0, 0, 1, by simp, fun h' => absurd h0 h', by simp [h0]⟩`. Take `⟨r₀, s₀, rfl⟩` from `(IntermediateField.mem_adjoin_simple_iff k _).1 hh`.

Establish `hr₀ : r₀ ≠ 0` using `by rintro rfl; simp at h0`. Establish `hs₀ : s₀ ≠ 0` using `by rintro rfl; simp at h0`. Take `⟨r₁, hr₁, hr₁'⟩` from `r₀.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr₀ 0`. Take `⟨s₁, hs₁, hs₁'⟩` from `s₀.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hs₀ 0`. Simplify using `only [map_zero, sub_zero] at hr₁ hs₁ hr₁' hs₁'`.

Rewrite `hr₁'`, `hs₁'` using `[Polynomial.X_dvd_iff]`. Generalize the expression as in `r₀.rootMultiplicity 0 = a at hr₁`. Generalize the expression as in `s₀.rootMultiplicity 0 = b at hs₁`. Substitute `hr₁ hs₁` using the available equality. Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : X ∣ r₁ * C (s₁.coeff 0) - C (r₁.coeff 0) * s₁ := by`.

Rewrite using `[Polynomial.X_dvd_iff, coeff_sub, coeff_mul_C, coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨(a : ℤ) - b, r₁.coeff 0 / s₁.coeff 0, r, s₁ * C (s₁.coeff 0), ?_, fun _ => div_ne_zero hr₁' hs₁', ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_mul_C]`. Conclude with `mul_ne_zero hs₁' hs₁'`.

Establish `hxr : x * aeval x r = aeval x r₁ * algebraMap k K (s₁.coeff 0) - algebraMap k K (r₁.coeff 0) * aeval x s₁`. Use `congrArg (aeval x) hr` as an intermediate fact. Simplify using `only [map_sub, map_mul, aeval_C, aeval_X] at this`. Rewrite using `[← this]`. Establish `hs₁0 : s₁ ≠ 0` using `fun h => hs₁' (by rw [h, coeff_zero])`.

Establish `hB : aeval x s₁ ≠ 0` using `hne s₁ hs₁0`. Establish `hc₀ : algebraMap k K (s₁.coeff 0) ≠ 0` using `(_root_.map_ne_zero _).2 hs₁'`. Simplify using `only [map_mul, map_pow, aeval_X, aeval_C]`. Rewrite using `[← mul_div_assoc x, hxr, map_div₀, zpow_sub₀ hx0, zpow_natCast, zpow_natCast]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_zpow_mul_of_mem_adjoin {x : K} (hx : Transcendental k x) {h : K}
    (hh : h ∈ IntermediateField.adjoin k {x}) :
    ∃ m : ℤ, ∃ c : k, ∃ r s : k[X], s.coeff 0 ≠ 0 ∧ (h ≠ 0 → c ≠ 0) ∧
      h = x ^ m * (algebraMap k K c + x * (aeval x r / aeval x s)) := by
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  have hne : ∀ p : k[X], p ≠ 0 → aeval x p ≠ 0 := fun p hp h0 => hx ⟨p, hp, h0⟩
  by_cases h0 : h = 0
  · exact ⟨0, 0, 0, 1, by simp, fun h' => absurd h0 h', by simp [h0]⟩
  obtain ⟨r₀, s₀, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff k _).1 hh
  have hr₀ : r₀ ≠ 0 := by rintro rfl; simp at h0
  have hs₀ : s₀ ≠ 0 := by rintro rfl; simp at h0
  obtain ⟨r₁, hr₁, hr₁'⟩ := r₀.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hr₀ 0
  obtain ⟨s₁, hs₁, hs₁'⟩ := s₀.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hs₀ 0
  simp only [map_zero, sub_zero] at hr₁ hs₁ hr₁' hs₁'
  rw [Polynomial.X_dvd_iff] at hr₁' hs₁'
  generalize r₀.rootMultiplicity 0 = a at hr₁
  generalize s₀.rootMultiplicity 0 = b at hs₁
  subst hr₁ hs₁
  obtain ⟨r, hr⟩ : X ∣ r₁ * C (s₁.coeff 0) - C (r₁.coeff 0) * s₁ := by
    rw [Polynomial.X_dvd_iff, coeff_sub, coeff_mul_C, coeff_C_mul]
    ring
  refine ⟨(a : ℤ) - b, r₁.coeff 0 / s₁.coeff 0, r, s₁ * C (s₁.coeff 0), ?_,
    fun _ => div_ne_zero hr₁' hs₁', ?_⟩
  · rw [coeff_mul_C]; exact mul_ne_zero hs₁' hs₁'
  · have hxr : x * aeval x r = aeval x r₁ * algebraMap k K (s₁.coeff 0) -
        algebraMap k K (r₁.coeff 0) * aeval x s₁ := by
      have := congrArg (aeval x) hr
      simp only [map_sub, map_mul, aeval_C, aeval_X] at this
      rw [← this]
    have hs₁0 : s₁ ≠ 0 := fun h => hs₁' (by rw [h, coeff_zero])
    have hB : aeval x s₁ ≠ 0 := hne s₁ hs₁0
    have hc₀ : algebraMap k K (s₁.coeff 0) ≠ 0 := (_root_.map_ne_zero _).2 hs₁'
    simp only [map_mul, map_pow, aeval_X, aeval_C]
    rw [← mul_div_assoc x, hxr, map_div₀, zpow_sub₀ hx0, zpow_natCast, zpow_natCast]
    field_simp
    ring

namespace Place

variable [IsFunctionField k K]

/- English proof (translation)
Rewrite `hx`, the goal using `[v.valuation_le_one_iff]`. Conclude with `(v.ring.valuation_le_one_iff _).1 (v.valuation_aeval_le_one hx p)`.
-/
theorem valuation_aeval_le_one' (v : Place k K) {x : K} (hx : v.valuation x ≤ 1) (p : k[X]) :
    v.valuation (aeval x p) ≤ 1 := by
  rw [v.valuation_le_one_iff] at hx ⊢
  exact (v.ring.valuation_le_one_iff _).1 (v.valuation_aeval_le_one hx p)

/- English proof (translation)
Take `⟨q, hq⟩` from `Polynomial.X_dvd_sub_C (p := p)`. Establish `h : aeval x p - algebraMap k K (p.coeff 0) = x * aeval x q`. Use `congrArg (aeval x) hq` as an intermediate fact. Simplify `this` using `only [map_sub, map_mul, aeval_C, aeval_X]`. Rewrite using `[h, map_mul]`.

Conclude with `mul_le_of_le_one_right' (v.valuation_aeval_le_one' hx q)`.
-/
theorem valuation_aeval_sub_coeff_zero_le (v : Place k K) {x : K} (hx : v.valuation x ≤ 1)
    (p : k[X]) : v.valuation (aeval x p - algebraMap k K (p.coeff 0)) ≤ v.valuation x := by
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have h : aeval x p - algebraMap k K (p.coeff 0) = x * aeval x q := by
    have := congrArg (aeval x) hq
    simpa only [map_sub, map_mul, aeval_C, aeval_X] using this
  rw [h, map_mul]
  exact mul_le_of_le_one_right' (v.valuation_aeval_le_one' hx q)

/- English proof (translation)
Establish `h1` using `v.valuation_algebraMap' hs`. Establish `hlt : v.valuation (aeval x s - algebraMap k K (s.coeff 0)) < v.valuation (algebraMap k K (s.coeff 0))`. Rewrite using `[h1]`. Conclude with `lt_of_le_of_lt (v.valuation_aeval_sub_coeff_zero_le hx.le s) hx`. Establish `: aeval x s = algebraMap k K (s.coeff 0) + (aeval x s - algebraMap k K (s.coeff 0))`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Valuation.map_add_eq_of_lt_left _ hlt, h1]`.
-/
theorem valuation_aeval_eq_one (v : Place k K) {x : K} (hx : v.valuation x < 1) {s : k[X]}
    (hs : s.coeff 0 ≠ 0) : v.valuation (aeval x s) = 1 := by
  have h1 := v.valuation_algebraMap' hs
  have hlt : v.valuation (aeval x s - algebraMap k K (s.coeff 0)) <
      v.valuation (algebraMap k K (s.coeff 0)) := by
    rw [h1]; exact lt_of_le_of_lt (v.valuation_aeval_sub_coeff_zero_le hx.le s) hx
  have : aeval x s = algebraMap k K (s.coeff 0) + (aeval x s - algebraMap k K (s.coeff 0)) := by
    ring
  rw [this, Valuation.map_add_eq_of_lt_left _ hlt, h1]

/- English proof (translation)
Rewrite using `[map_mul, map_div₀, v.valuation_aeval_eq_one hx hs, div_one]`. Conclude with `mul_le_of_le_one_right' (v.valuation_aeval_le_one' hx.le r)`.
-/
theorem valuation_mul_aeval_div_le (v : Place k K) {x : K} (hx : v.valuation x < 1)
    (r : k[X]) {s : k[X]} (hs : s.coeff 0 ≠ 0) :
    v.valuation (x * (aeval x r / aeval x s)) ≤ v.valuation x := by
  rw [map_mul, map_div₀, v.valuation_aeval_eq_one hx hs, div_one]
  exact mul_le_of_le_one_right' (v.valuation_aeval_le_one' hx.le r)

/- English proof (translation)
Introduce `e`. Proceed by induction on `e with`. Consider the case `zero => intro d _`. Use function extensionality and compare the values at `a`. Conclude with `a.elim0`.

Consider the case `succ e ih`. Introduce `d hd`. Rewrite `hd` using `[Fin.sum_univ_succ]`. Use `set T := ∑ a : Fin e, ∑ α, algebraMap k K (d a.succ α) * (π ^ (a : ℕ) * s α) with hT`. Establish `hsplit : ∑ a : Fin e, ∑ α, algebraMap k K (d a.succ α) * (π ^ ((a.succ : Fin (e + 1)) : ℕ) * s α) = π * T`.

Rewrite using `[hT, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.val_succ, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hd` using `[hsplit]`. Establish `hT1 : v.valuation T ≤ 1`. Use `Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun α _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_pow]`.

Use `mul_le_one' ?_ (mul_le_one' (pow_le_one' hπ.le _) (hs1 α))` and prove the remaining obligations. Distinguish the cases in `hd0 : d a.succ α = 0`. Rewrite using `[hd0, map_zero, map_zero]`. Conclude with `zero_le`. Rewrite using `[v.valuation_algebraMap' hd0]`.

Establish `hπT : v.valuation (π * T) ≤ v.valuation π`. Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_right' hT1`. Establish `h0 : d 0 = 0`. Apply `hs` to reduce the goal to its premises.

Establish `hsum0 : (∑ α, algebraMap k K (d 0 α) * s α) = (∑ α, algebraMap k K (d 0 α) * (π ^ ((0 : Fin (e + 1)) : ℕ) * s α) + π * T) - π * T`. Simplify using the standard rewrite rules. Rewrite using `[hsum0]`. Use `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ (lt_of_le_of_lt hπT hπ))` and prove the remaining obligations. Use `lt_of_le_of_lt hd ?_` and prove the remaining obligations.

Rewrite using `[pow_succ]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hπ.le _)) hπ`. Establish `hTle : v.valuation T ≤ v.valuation π ^ e`. Establish `hd' : v.valuation (π * T) ≤ v.valuation π ^ e * v.valuation π`. Rewrite using `[← pow_succ]`.

Simplify `hd` using `[h0]`. Rewrite `hd'` using `[map_mul, mul_comm]`. Conclude with `le_of_mul_le_mul_right hd' (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hπ0))`. Establish `hrest` using `ih (fun a => d a.succ) hTle`. Use function extensionality and compare the values at `a`.

Use `Fin.cases h0 (fun b => ?_) a` and prove the remaining obligations. Conclude with `congrFun hrest b`.
-/
theorem eq_zero_of_valuation_sum_le (v : Place k K) {f : ℕ} {s : Fin f → K}
    (hs1 : ∀ α, v.valuation (s α) ≤ 1)
    (hs : ∀ d : Fin f → k, v.valuation (∑ α, algebraMap k K (d α) * s α) < 1 → d = 0)
    {π : K} (hπ0 : π ≠ 0) (hπ : v.valuation π < 1) :
    ∀ (e : ℕ) (d : Fin e → Fin f → k),
      v.valuation (∑ a, ∑ α, algebraMap k K (d a α) * (π ^ (a : ℕ) * s α)) ≤
        v.valuation π ^ e → d = 0 := by
  intro e
  induction e with
  | zero => intro d _; funext a; exact a.elim0
  | succ e ih =>
    intro d hd
    rw [Fin.sum_univ_succ] at hd
    set T := ∑ a : Fin e, ∑ α, algebraMap k K (d a.succ α) * (π ^ (a : ℕ) * s α) with hT
    have hsplit : ∑ a : Fin e, ∑ α, algebraMap k K (d a.succ α) * (π ^ ((a.succ : Fin (e + 1)) : ℕ) * s α)
        = π * T := by
      rw [hT, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [Fin.val_succ, pow_succ]
      ring
    rw [hsplit] at hd
    have hT1 : v.valuation T ≤ 1 := by
      refine Valuation.map_sum_le _ fun a _ => Valuation.map_sum_le _ fun α _ => ?_
      rw [map_mul, map_mul, map_pow]
      refine mul_le_one' ?_ (mul_le_one' (pow_le_one' hπ.le _) (hs1 α))
      by_cases hd0 : d a.succ α = 0
      · rw [hd0, map_zero, map_zero]; exact zero_le
      · rw [v.valuation_algebraMap' hd0]
    have hπT : v.valuation (π * T) ≤ v.valuation π := by
      rw [map_mul]; exact mul_le_of_le_one_right' hT1
    have h0 : d 0 = 0 := by
      apply hs
      have hsum0 : (∑ α, algebraMap k K (d 0 α) * s α) =
          (∑ α, algebraMap k K (d 0 α) * (π ^ ((0 : Fin (e + 1)) : ℕ) * s α) + π * T) - π * T := by
        simp
      rw [hsum0]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ (lt_of_le_of_lt hπT hπ))
      refine lt_of_le_of_lt hd ?_
      rw [pow_succ]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hπ.le _)) hπ
    have hTle : v.valuation T ≤ v.valuation π ^ e := by
      have hd' : v.valuation (π * T) ≤ v.valuation π ^ e * v.valuation π := by
        rw [← pow_succ]
        simpa [h0] using hd
      rw [map_mul, mul_comm] at hd'
      exact le_of_mul_le_mul_right hd' (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hπ0))
    have hrest := ih (fun a => d a.succ) hTle
    funext a
    refine Fin.cases h0 (fun b => ?_) a
    exact congrFun hrest b

/- English proof (translation)
Set `b : Module.Basis (Fin v.deg) k v.ResidueField` to `Module.finBasisOfFinrankEq k v.ResidueField (rfl : Module.finrank k v.ResidueField = v.deg)`. Use `choose s' hs' using fun α : Fin v.deg => IsLocalRing.residue_surjective (b α)`. Use `⟨fun α => (s' α : K), fun α => (v.valuation_le_one_iff _).2 (s' α).2, fun d hd => ?_⟩` and prove the remaining obligations. Establish `hmem : (∑ α, algebraMap k K (d α) * (s' α : K)) = ((∑ α, algebraMap k v.ring (d α) * s' α : v.ring) : K)`. Simplify using the standard rewrite rules.

Rewrite `hd` using `[hmem, v.valuation_lt_one_iff, ← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, map_sum]`. Establish `h : ∑ α, d α • b α = 0`. Rewrite using `[← hd]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, hs', Algebra.smul_def, IsScalarTower.algebraMap_apply k v.ring v.ResidueField, IsLocalRing.ResidueField.algebraMap_eq]`.

Conclude with `funext fun α => Fintype.linearIndependent_iff.1 b.linearIndependent d h α`.
-/
theorem exists_lift_basis (v : Place k K) :
    ∃ s : Fin v.deg → K, (∀ α, v.valuation (s α) ≤ 1) ∧
      ∀ d : Fin v.deg → k, v.valuation (∑ α, algebraMap k K (d α) * s α) < 1 → d = 0 := by
  let b : Module.Basis (Fin v.deg) k v.ResidueField := Module.finBasisOfFinrankEq k v.ResidueField
    (rfl : Module.finrank k v.ResidueField = v.deg)
  choose s' hs' using fun α : Fin v.deg => IsLocalRing.residue_surjective (b α)
  refine ⟨fun α => (s' α : K), fun α => (v.valuation_le_one_iff _).2 (s' α).2, fun d hd => ?_⟩
  have hmem : (∑ α, algebraMap k K (d α) * (s' α : K)) =
      ((∑ α, algebraMap k v.ring (d α) * s' α : v.ring) : K) := by
    simp
  rw [hmem, v.valuation_lt_one_iff, ← ValuationSubring.valuation_lt_one_iff,
    ← IsLocalRing.residue_eq_zero_iff, map_sum] at hd
  have h : ∑ α, d α • b α = 0 := by
    rw [← hd]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_mul, hs', Algebra.smul_def, IsScalarTower.algebraMap_apply k v.ring v.ResidueField,
      IsLocalRing.ResidueField.algebraMap_eq]
  exact funext fun α => Fintype.linearIndependent_iff.1 b.linearIndependent d h α

/- English proof (translation)
Establish `hx0 : x ≠ 0` using `fun h0 => hx (h0 ▸ isAlgebraic_zero)`. Use `finiteDimensional_adjoin hx` as an intermediate fact. Use `choose s hs1 hs using fun v : Place k K => v.exists_lift_basis`. Use `choose π hπ using fun v : Place k K => v.exists_ord_eq_one`. Establish `hπ0 : ∀ v : Place k K, π v ≠ 0` using `fun v => v.ne_zero_of_ord_ne_zero (by rw [hπ]; norm_num)`.

Establish `hπv : ∀ v : Place k K, v.valuation (π v) = WithZero.exp (-1)` using `fun v => by`. Rewrite using `[v.valuation_eq_exp_neg_ord (hπ0 v), hπ]`. Establish `hxv : ∀ v : Place k K, v.valuation x = WithZero.exp (-v.ord x)` using `fun v => v.valuation_eq_exp_neg_ord hx0`. Establish `hx1 : ∀ v ∈ S, v.valuation x < 1` using `fun v hv => by`. Rewrite using `[hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Use `hS v hv` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `choose y hy using fun (v : Place k K) (a : ℕ) (α : Fin v.deg) => exists_approx S (fun w => if w = v then π v ^ a * s v α else 0) (fun w => w.ord x)`. Set `ι` to `Σ v : S, Fin (v.1.ord x).toNat × Fin v.1.deg`. Set `Y : ι → K` to `fun i => y i.1.1 i.2.1 i.2.2`.

Establish `hP1 : ∀ i : ι, ∀ w ∈ S, w ≠ i.1.1 → w.valuation (Y i) ≤ w.valuation x`. Introduce `i w hw hne`. Use `hy i.1.1 i.2.1 i.2.2 w hw` as an intermediate fact. Rewrite `this` using `[if_neg hne, sub_zero]`. Rewrite using `[hxv]`.

Conclude with `this`. Establish `hP2 : ∀ i : ι, i.1.1.valuation (Y i - π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2) ≤ i.1.1.valuation x`. Introduce `i`. Use `hy i.1.1 i.2.1 i.2.2 i.1.1 i.1.2` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`.

Rewrite using `[hxv]`. Conclude with `this`. Establish `hP3 : ∀ i : ι, ∀ w ∈ S, w.valuation (Y i) ≤ 1`. Introduce `i w hw`. Distinguish the cases in `hwi : w = i.1.1`.

Substitute `hwi` using the available equality. Establish `h2 : Y i = (Y i - π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2) + π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2` using `by ring`. Rewrite using `[h2]`. Use `Valuation.map_add_le _ ((hP2 i).trans (hx1 _ hw).le) ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, hπv]`.

Conclude with `mul_le_one' (pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) _) (hs1 _ _)`. Conclude with `(hP1 i w hw hwi).trans (hx1 w hw).le`. Establish `hli : LinearIndependent (IntermediateField.adjoin k {x}) Y`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨i₀, hi₀⟩` from `hne`. Use `choose m c r t ht hc hgeq using fun i => exists_eq_zpow_mul_of_mem_adjoin hx (g i).2`. Establish `hsum : ∑ i, (g i : K) * Y i = 0` using `by simpa [Algebra.smul_def] using hg`.

Set `T` to `Finset.univ.filter fun i => (g i : K) ≠ 0`. Establish `hT : T.Nonempty` using `⟨i₀, by`. Simplify using `only [T, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `fun h => hi₀ (Subtype.ext h)⟩`. Take `⟨j, hjT, hjmin⟩` from `T.exists_min_image m hT`.

Establish `hgj : (g j : K) ≠ 0` using `by simpa [T] using hjT`. Set `d : ι → k` to `fun i => if (g i : K) ≠ 0 ∧ m i = m j then c i else 0`. Establish `hA : ∀ w ∈ S, w.valuation (∑ i, algebraMap k K (d i) * Y i) ≤ w.valuation x`. Introduce `w hw`. Establish `heq : ∑ i, algebraMap k K (d i) * Y i = ∑ i, (algebraMap k K (d i) - x ^ (-m j) * g i) * Y i`.

Simplify using `only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hsum, mul_zero, sub_zero]`. Rewrite using `[heq]`. Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `le_trans (mul_le_mul' ?_ (hP3 i w hw)) (le_of_eq (mul_one _))` and prove the remaining obligations.

Distinguish the cases in `hgi : (g i : K) = 0`. Establish `hgi' : g i = 0` using `Subtype.ext hgi`. Establish `hdi : d i = 0` using `by simp [d, hgi']`. Rewrite using `[hdi, hgi, map_zero, mul_zero, sub_zero, map_zero]`. Conclude with `zero_le`.

Establish `hmij : m j ≤ m i` using `hjmin i (by`. Simplify using `only [T, Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `hgi)`. Use `set W := algebraMap k K (c i) + x * (aeval x (r i) / aeval x (t i)) with hW`. Establish `hW1 : w.valuation W ≤ 1`.

Use `Valuation.map_add_le _ ?_ ((w.valuation_mul_aeval_div_le (hx1 w hw) _ (ht i)).trans (hx1 w hw).le)` and prove the remaining obligations. Distinguish the cases in `hci : c i = 0`. Rewrite using `[hci, map_zero, map_zero]`. Conclude with `zero_le`. Rewrite using `[w.valuation_algebraMap' hci]`.

Rewrite using `[hgeq i]`. Break down `hmij.lt_or_eq with hlt | heq'` into its components or cases. Establish `hdi : d i = 0`. Simplify using `only [d, ne_eq, hgi, not_false_eq_true, true_and]`. Rewrite using `[if_neg (by omega)]`.

Take `⟨n, hn⟩ : ∃ n : ℕ, m i - m j = n + 1` from `⟨(m i - m j - 1).toNat, by omega⟩`. Establish `hpow : x ^ (-m j) * (x ^ m i * W) = x ^ (n + 1) * W`. Rewrite using `[← mul_assoc, ← zpow_add₀ hx0, show -m j + m i = ((n + 1 : ℕ) : ℤ) by push_cast; omega, zpow_natCast]`. Rewrite using `[hdi, map_zero, zero_sub, hpow, Valuation.map_neg, map_mul, map_pow, pow_succ]`. Use `le_trans (mul_le_of_le_one_right' hW1) ?_` and prove the remaining obligations.

Conclude with `mul_le_of_le_one_left' (pow_le_one' (hx1 w hw).le _)`. Establish `hdi : d i = c i`. Simplify using `only [d, ne_eq, hgi, not_false_eq_true, true_and]`. Rewrite using `[if_pos heq'.symm]`. Establish `hpow : x ^ (-m j) * (x ^ m i * W) = W`.

Rewrite using `[← mul_assoc, ← zpow_add₀ hx0, ← heq', neg_add_cancel, zpow_zero, one_mul]`. Rewrite using `[hdi, hpow, hW, sub_add_cancel_left, Valuation.map_neg]`. Conclude with `w.valuation_mul_aeval_div_le (hx1 w hw) _ (ht i)`. Take `⟨⟨v, hvS⟩, a₀, α₀⟩` from `j`. Establish `hcj : d ⟨⟨v, hvS⟩, a₀, α₀⟩ ≠ 0`.

Simplify using `only [d, ne_eq, hgj, not_false_eq_true, and_self, if_true]`. Conclude with `hc _ hgj`. Set `v₀ : S` to `⟨v, hvS⟩`. Set `B : ι → K` to `fun i => if i.1 = v₀ then π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2 else 0`. Establish `hBsum : ∑ i, algebraMap k K (d i) * B i = ∑ a : Fin (v.ord x).toNat, ∑ α : Fin v.deg, algebraMap k K (d ⟨v₀, a, α⟩) * (π v ^ (a : ℕ) * s v α)`.

Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single v₀]`. Rewrite using `[Fintype.sum_prod_type]`. Simplify using `[B, v₀]`. Introduce `b _ hb`. Use `Finset.sum_eq_zero fun p _ => ?_` and prove the remaining obligations.

Simplify using `[B, hb]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hrest : v.valuation (∑ i, algebraMap k K (d i) * (Y i - B i)) ≤ v.valuation x`. Use `Valuation.map_sum_le _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul]`. Use `le_trans (mul_le_of_le_one_left' ?_) ?_` and prove the remaining obligations. Distinguish the cases in `hdi : d i = 0`. Rewrite using `[hdi, map_zero, map_zero]`. Conclude with `zero_le`.

Rewrite using `[v.valuation_algebraMap' hdi]`. Take `⟨⟨w, hw⟩, a, α⟩` from `i`. Distinguish the cases in `hwv : w = v`. Substitute `hwv` using the available equality. Establish `hB : B ⟨⟨w, hw⟩, a, α⟩ = π w ^ (a : ℕ) * s w α` using `if_pos rfl`.

Rewrite using `[hB]`. Conclude with `hP2 ⟨⟨w, hw⟩, a, α⟩`. Establish `hB : B ⟨⟨w, hw⟩, a, α⟩ = 0` using `if_neg (fun h => hwv (congrArg Subtype.val h))`. Rewrite using `[hB, sub_zero]`. Conclude with `hP1 _ v hvS (fun h => hwv h.symm)`.

Establish `hmain : v.valuation (∑ a : Fin (v.ord x).toNat, ∑ α : Fin v.deg, algebraMap k K (d ⟨v₀, a, α⟩) * (π v ^ (a : ℕ) * s v α)) ≤ v.valuation (π v) ^ (v.ord x).toNat`. Establish `hpe : v.valuation (π v) ^ (v.ord x).toNat = v.valuation x`. Rewrite using `[hπv, ← WithZero.exp_nsmul, hxv, nsmul_eq_mul, Int.toNat_of_nonneg (hS v hvS).le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hpe, ← hBsum]`. Establish `h3 : ∑ i, algebraMap k K (d i) * B i = ∑ i, algebraMap k K (d i) * Y i - ∑ i, algebraMap k K (d i) * (Y i - B i)`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h3]`. Conclude with `le_trans (Valuation.map_sub _ _ _) (max_le (hA v hvS) hrest)`. Establish `hzero` using `v.eq_zero_of_valuation_sum_le (hs1 v) (hs v) (hπ0 v) (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega) _ _ hmain`. Conclude with `hcj (congrFun (congrFun hzero a₀) α₀)`. Establish `hcard` using `hli.fintype_card_le_finrank`.

Establish `hι : Fintype.card ι = ∑ v ∈ S, (v.ord x).toNat * v.deg`. Simplify using `only [ι, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]`. Conclude with `Finset.sum_coe_sort S (fun v => (v.ord x).toNat * v.deg)`. Rewrite using `[← hι]`. Conclude with `hcard`.
-/
theorem sum_ord_mul_deg_le {x : K} (hx : Transcendental k x) (S : Finset (Place k K))
    (hS : ∀ v ∈ S, 0 < v.ord x) :
    ∑ v ∈ S, (v.ord x).toNat * v.deg ≤ Module.finrank (IntermediateField.adjoin k {x}) K := by
  classical
  have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ isAlgebraic_zero)
  have := finiteDimensional_adjoin hx
  choose s hs1 hs using fun v : Place k K => v.exists_lift_basis
  choose π hπ using fun v : Place k K => v.exists_ord_eq_one
  have hπ0 : ∀ v : Place k K, π v ≠ 0 := fun v => v.ne_zero_of_ord_ne_zero (by rw [hπ]; norm_num)
  have hπv : ∀ v : Place k K, v.valuation (π v) = WithZero.exp (-1) := fun v => by
    rw [v.valuation_eq_exp_neg_ord (hπ0 v), hπ]
  have hxv : ∀ v : Place k K, v.valuation x = WithZero.exp (-v.ord x) :=
    fun v => v.valuation_eq_exp_neg_ord hx0
  have hx1 : ∀ v ∈ S, v.valuation x < 1 := fun v hv => by
    rw [hxv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; have := hS v hv; omega
  choose y hy using fun (v : Place k K) (a : ℕ) (α : Fin v.deg) =>
    exists_approx S (fun w => if w = v then π v ^ a * s v α else 0) (fun w => w.ord x)
  let ι := Σ v : S, Fin (v.1.ord x).toNat × Fin v.1.deg
  let Y : ι → K := fun i => y i.1.1 i.2.1 i.2.2
  have hP1 : ∀ i : ι, ∀ w ∈ S, w ≠ i.1.1 → w.valuation (Y i) ≤ w.valuation x := by
    intro i w hw hne
    have := hy i.1.1 i.2.1 i.2.2 w hw
    rw [if_neg hne, sub_zero] at this
    rw [hxv]; exact this
  have hP2 : ∀ i : ι, i.1.1.valuation (Y i - π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2) ≤
      i.1.1.valuation x := by
    intro i
    have := hy i.1.1 i.2.1 i.2.2 i.1.1 i.1.2
    rw [if_pos rfl] at this
    rw [hxv]; exact this
  have hP3 : ∀ i : ι, ∀ w ∈ S, w.valuation (Y i) ≤ 1 := by
    intro i w hw
    by_cases hwi : w = i.1.1
    · subst hwi
      have h2 : Y i = (Y i - π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2) +
          π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2 := by ring
      rw [h2]
      refine Valuation.map_add_le _ ((hP2 i).trans (hx1 _ hw).le) ?_
      rw [map_mul, map_pow, hπv]
      exact mul_le_one' (pow_le_one' (by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega) _)
        (hs1 _ _)
    · exact (hP1 i w hw hwi).trans (hx1 w hw).le
  have hli : LinearIndependent (IntermediateField.adjoin k {x}) Y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    choose m c r t ht hc hgeq using fun i => exists_eq_zpow_mul_of_mem_adjoin hx (g i).2
    have hsum : ∑ i, (g i : K) * Y i = 0 := by simpa [Algebra.smul_def] using hg
    let T := Finset.univ.filter fun i => (g i : K) ≠ 0
    have hT : T.Nonempty := ⟨i₀, by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun h => hi₀ (Subtype.ext h)⟩
    obtain ⟨j, hjT, hjmin⟩ := T.exists_min_image m hT
    have hgj : (g j : K) ≠ 0 := by simpa [T] using hjT
    let d : ι → k := fun i => if (g i : K) ≠ 0 ∧ m i = m j then c i else 0
    have hA : ∀ w ∈ S, w.valuation (∑ i, algebraMap k K (d i) * Y i) ≤ w.valuation x := by
      intro w hw
      have heq : ∑ i, algebraMap k K (d i) * Y i =
          ∑ i, (algebraMap k K (d i) - x ^ (-m j) * g i) * Y i := by
        simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hsum, mul_zero,
          sub_zero]
      rw [heq]
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      refine le_trans (mul_le_mul' ?_ (hP3 i w hw)) (le_of_eq (mul_one _))
      by_cases hgi : (g i : K) = 0
      · have hgi' : g i = 0 := Subtype.ext hgi
        have hdi : d i = 0 := by simp [d, hgi']
        rw [hdi, hgi, map_zero, mul_zero, sub_zero, map_zero]; exact zero_le
      · have hmij : m j ≤ m i := hjmin i (by
          simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]; exact hgi)
        set W := algebraMap k K (c i) + x * (aeval x (r i) / aeval x (t i)) with hW
        have hW1 : w.valuation W ≤ 1 := by
          refine Valuation.map_add_le _ ?_ ((w.valuation_mul_aeval_div_le (hx1 w hw) _ (ht i)).trans
            (hx1 w hw).le)
          by_cases hci : c i = 0
          · rw [hci, map_zero, map_zero]; exact zero_le
          · rw [w.valuation_algebraMap' hci]
        rw [hgeq i]
        rcases hmij.lt_or_eq with hlt | heq'
        · have hdi : d i = 0 := by
            simp only [d, ne_eq, hgi, not_false_eq_true, true_and]
            rw [if_neg (by omega)]
          obtain ⟨n, hn⟩ : ∃ n : ℕ, m i - m j = n + 1 := ⟨(m i - m j - 1).toNat, by omega⟩
          have hpow : x ^ (-m j) * (x ^ m i * W) = x ^ (n + 1) * W := by
            rw [← mul_assoc, ← zpow_add₀ hx0, show -m j + m i = ((n + 1 : ℕ) : ℤ) by push_cast; omega,
              zpow_natCast]
          rw [hdi, map_zero, zero_sub, hpow, Valuation.map_neg, map_mul, map_pow, pow_succ]
          refine le_trans (mul_le_of_le_one_right' hW1) ?_
          exact mul_le_of_le_one_left' (pow_le_one' (hx1 w hw).le _)
        · have hdi : d i = c i := by
            simp only [d, ne_eq, hgi, not_false_eq_true, true_and]
            rw [if_pos heq'.symm]
          have hpow : x ^ (-m j) * (x ^ m i * W) = W := by
            rw [← mul_assoc, ← zpow_add₀ hx0, ← heq', neg_add_cancel, zpow_zero, one_mul]
          rw [hdi, hpow, hW, sub_add_cancel_left, Valuation.map_neg]
          exact w.valuation_mul_aeval_div_le (hx1 w hw) _ (ht i)
    obtain ⟨⟨v, hvS⟩, a₀, α₀⟩ := j
    have hcj : d ⟨⟨v, hvS⟩, a₀, α₀⟩ ≠ 0 := by
      simp only [d, ne_eq, hgj, not_false_eq_true, and_self, if_true]
      exact hc _ hgj
    let v₀ : S := ⟨v, hvS⟩
    let B : ι → K := fun i => if i.1 = v₀ then π i.1.1 ^ (i.2.1 : ℕ) * s i.1.1 i.2.2 else 0
    have hBsum : ∑ i, algebraMap k K (d i) * B i =
        ∑ a : Fin (v.ord x).toNat, ∑ α : Fin v.deg,
          algebraMap k K (d ⟨v₀, a, α⟩) * (π v ^ (a : ℕ) * s v α) := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single v₀]
      · rw [Fintype.sum_prod_type]
        simp [B, v₀]
      · intro b _ hb
        refine Finset.sum_eq_zero fun p _ => ?_
        simp [B, hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hrest : v.valuation (∑ i, algebraMap k K (d i) * (Y i - B i)) ≤ v.valuation x := by
      refine Valuation.map_sum_le _ fun i _ => ?_
      rw [map_mul]
      refine le_trans (mul_le_of_le_one_left' ?_) ?_
      · by_cases hdi : d i = 0
        · rw [hdi, map_zero, map_zero]; exact zero_le
        · rw [v.valuation_algebraMap' hdi]
      · obtain ⟨⟨w, hw⟩, a, α⟩ := i
        by_cases hwv : w = v
        · subst hwv
          have hB : B ⟨⟨w, hw⟩, a, α⟩ = π w ^ (a : ℕ) * s w α := if_pos rfl
          rw [hB]; exact hP2 ⟨⟨w, hw⟩, a, α⟩
        · have hB : B ⟨⟨w, hw⟩, a, α⟩ = 0 := if_neg (fun h => hwv (congrArg Subtype.val h))
          rw [hB, sub_zero]
          exact hP1 _ v hvS (fun h => hwv h.symm)
    have hmain : v.valuation (∑ a : Fin (v.ord x).toNat, ∑ α : Fin v.deg,
        algebraMap k K (d ⟨v₀, a, α⟩) * (π v ^ (a : ℕ) * s v α)) ≤
        v.valuation (π v) ^ (v.ord x).toNat := by
      have hpe : v.valuation (π v) ^ (v.ord x).toNat = v.valuation x := by
        rw [hπv, ← WithZero.exp_nsmul, hxv, nsmul_eq_mul, Int.toNat_of_nonneg (hS v hvS).le]
        congr 1; ring
      rw [hpe, ← hBsum]
      have h3 : ∑ i, algebraMap k K (d i) * B i =
          ∑ i, algebraMap k K (d i) * Y i - ∑ i, algebraMap k K (d i) * (Y i - B i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h3]
      exact le_trans (Valuation.map_sub _ _ _) (max_le (hA v hvS) hrest)
    have hzero := v.eq_zero_of_valuation_sum_le (hs1 v) (hs v) (hπ0 v)
      (by rw [hπv, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega) _ _ hmain
    exact hcj (congrFun (congrFun hzero a₀) α₀)
  have hcard := hli.fintype_card_le_finrank
  have hι : Fintype.card ι = ∑ v ∈ S, (v.ord x).toNat * v.deg := by
    simp only [ι, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
    exact Finset.sum_coe_sort S (fun v => (v.ord x).toNat * v.deg)
  rw [← hι]
  exact hcard

/- English proof (translation)
Distinguish the cases in `hx0 : x = 0`. Use `Set.finite_empty` and compare the differences between its conclusion and the goal. Use extensionality with `v`. Simplify using `[hx0]`. Distinguish the cases in `halg : IsAlgebraic k x`.

Use `Set.finite_empty` and compare the differences between its conclusion and the goal. Use extensionality with `v`. Simplify using `[v.ord_eq_zero_of_isAlgebraic halg hx0]`. Assume the negation of the conclusion as `hinf`. Take `⟨S, hSsub, hcard⟩` from `Set.Infinite.exists_subset_card_eq hinf (Module.finrank (IntermediateField.adjoin k {x}) K + 1)`.

Establish `h` using `sum_ord_mul_deg_le halg S fun v hv => hSsub hv`. Establish `h2 : S.card ≤ ∑ v ∈ S, (v.ord x).toNat * v.deg`. Rewrite using `[Finset.card_eq_sum_ones]`. Use `Finset.sum_le_sum fun v hv => ?_` and prove the remaining obligations. Establish `h1 : 1 ≤ (v.ord x).toNat` using `by have := hSsub hv; simp only [Set.mem_ofPred_eq] at this; omega`.

Establish `h2` using `v.deg_pos`. Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers.
-/
theorem finite_ord_pos (x : K) : {v : Place k K | 0 < v.ord x}.Finite := by
  classical
  by_cases hx0 : x = 0
  · convert Set.finite_empty
    ext v
    simp [hx0]
  by_cases halg : IsAlgebraic k x
  · convert Set.finite_empty
    ext v
    simp [v.ord_eq_zero_of_isAlgebraic halg hx0]
  by_contra hinf
  obtain ⟨S, hSsub, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf
    (Module.finrank (IntermediateField.adjoin k {x}) K + 1)
  have h := sum_ord_mul_deg_le halg S fun v hv => hSsub hv
  have h2 : S.card ≤ ∑ v ∈ S, (v.ord x).toNat * v.deg := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun v hv => ?_
    have h1 : 1 ≤ (v.ord x).toNat := by have := hSsub hv; simp only [Set.mem_ofPred_eq] at this; omega
    have h2 := v.deg_pos
    nlinarith
  omega

/- English proof (translation)
Use `((finite_ord_pos x).union (finite_ord_pos x⁻¹)).subset fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Set.mem_union, ord_inv] at hv ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem finite_ord_ne_zero (x : K) : {v : Place k K | v.ord x ≠ 0}.Finite := by
  refine ((finite_ord_pos x).union (finite_ord_pos x⁻¹)).subset fun v hv => ?_
  simp only [Set.mem_ofPred_eq, Set.mem_union, ord_inv] at hv ⊢
  omega

end Place

end GroundTheory.FunctionField
