import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormPowSubPowLtOne

namespace GlobalTheory.Honda

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ← norm_neg y]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`.
-/
theorem unitFix_subMax {K : Type} [NormedField K] [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]; exact IsUltrametricDist.norm_add_le_max _ _

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one`. Consider the case `exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one`. Consider the case `(apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one ..)`.
-/
theorem unitFix_powSub {K : Type} [NormedField K] [IsUltrametricDist K] (a b : K) (ha : ‖a‖ ≤ 1)
    (hb : ‖b‖ ≤ 1) (hab : ‖a - b‖ < 1) : ∀ n : ℕ, ‖a ^ n - b ^ n‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one
  | exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one
  | (apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricPowerDifference.norm_pow_sub_pow_lt_one ..)

/- English proof (translation)
Rewrite using `[pow_two]`. Both sides reduce to the same expression.
-/
theorem unitFix_sq_apply {K : Type} [NormedField K] (σ : K →+* K) (x : K) : (σ ^ 2) x = σ (σ x) := by
  rw [pow_two]; rfl

/- English proof (translation)
Take `⟨_, _, _, _, hiso, hfr⟩` from `hU`. Establish `hsx : ‖σ x‖ ≤ 1` using `by rw [hiso]; exact hx`. Establish `h1` using `hfr (σ x) hsx`. Establish `h2 : ‖(σ x) ^ l - (x ^ l) ^ l‖ < 1` using `unitFix_powSub _ _ hsx (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx) (hfr x hx) l`. Establish `hq : x ^ (l ^ 2) = (x ^ l) ^ l` using `by rw [← pow_mul, sq]`.

Establish `e2 : σ (σ x) - x ^ (l ^ 2) = (σ (σ x) - σ x ^ l) + ((σ x) ^ l - (x ^ l) ^ l)` using `by rw [hq]; ring`. Rewrite using `[unitFix_sq_apply, e2]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)`.
-/
theorem unitFix_frob2 {K : Type} [NormedField K] [IsUltrametricDist K] (l : ℕ) (σ : K →+* K) (hU : Unr K l σ)
    (x : K) (hx : ‖x‖ ≤ 1) : ‖(σ ^ 2) x - x ^ (l ^ 2)‖ < 1 := by
  obtain ⟨_, _, _, _, hiso, hfr⟩ := hU
  have hsx : ‖σ x‖ ≤ 1 := by rw [hiso]; exact hx
  have h1 := hfr (σ x) hsx
  have h2 : ‖(σ x) ^ l - (x ^ l) ^ l‖ < 1 :=
    unitFix_powSub _ _ hsx (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx) (hfr x hx) l
  have hq : x ^ (l ^ 2) = (x ^ l) ^ l := by rw [← pow_mul, sq]
  have e2 : σ (σ x) - x ^ (l ^ 2) = (σ (σ x) - σ x ^ l) + ((σ x) ^ l - (x ^ l) ^ l) := by rw [hq]; ring
  rw [unitFix_sq_apply, e2]
  exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

/- English proof (translation)
Establish `hdeg : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree < (Polynomial.X ^ m : Polynomial K).natDegree`. Rewrite using `[Polynomial.natDegree_X_pow]; exact lt_of_le_of_lt Polynomial.natDegree_linear_le (by omega)`. Establish `hmon : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).Monic` using `(Polynomial.monic_X_pow m).sub_of_left (Polynomial.degree_lt_degree hdeg)`. Establish `hnd : 0 < (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).natDegree`. Rewrite using `[Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg, Polynomial.natDegree_X_pow]`.

Use linear arithmetic over natural numbers and integers. Establish `hco : ∀ n, ‖(Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).coeff n‖ ≤ 1`. Introduce `n`. Simplify using `only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]`. Use `(unitFix_subMax _ _).trans (max_le ?_ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))` and prove the remaining obligations.

Apply the tactic sequence `split_ifs <;> simp`. Apply the tactic sequence `split_ifs <;> simp [ha]`. Apply the tactic sequence `split_ifs <;> simp [hb]`. Take `⟨y, hy, hev⟩` from `hR _ hmon hnd hco`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Establish `e : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).eval y = y ^ m - a * y - b`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hev` using `[e]`. Then use the resulting hypothesis.
-/
theorem unitFix_root {K : Type} [NormedField K] [IsUltrametricDist K] (hR : ResAlg K) (m : ℕ) (hm : 2 ≤ m)
    (a b : K) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ∃ y : K, ‖y‖ ≤ 1 ∧ ‖y ^ m - a * y - b‖ < 1 := by
  classical
  have hdeg : (Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree
      < (Polynomial.X ^ m : Polynomial K).natDegree := by
    rw [Polynomial.natDegree_X_pow]; exact lt_of_le_of_lt Polynomial.natDegree_linear_le (by omega)
  have hmon : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).Monic :=
    (Polynomial.monic_X_pow m).sub_of_left (Polynomial.degree_lt_degree hdeg)
  have hnd : 0 < (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).natDegree := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdeg, Polynomial.natDegree_X_pow]; omega
  have hco : ∀ n, ‖(Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).coeff n‖ ≤ 1 := by
    intro n
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
      Polynomial.coeff_X, Polynomial.coeff_C]
    refine (unitFix_subMax _ _).trans
      (max_le ?_ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
    · split_ifs <;> simp
    · split_ifs <;> simp [ha]
    · split_ifs <;> simp [hb]
  obtain ⟨y, hy, hev⟩ := hR _ hmon hnd hco
  refine ⟨y, hy, ?_⟩
  have e : (Polynomial.X ^ m - (Polynomial.C a * Polynomial.X + Polynomial.C b)).eval y = y ^ m - a * y - b := by
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow]
    ring
  rwa [e] at hev

/- English proof (translation)
Establish `hU'` using `hU`. Take `⟨hp, h2, hl1, hdisc, hiso, hfr⟩` from `hU'`. Establish `hl0 : (l : K) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hπ0 : (l : K) ^ n ≠ 0` using `pow_ne_zero _ hl0`. Establish `hπn : ‖(l : K) ^ n‖ = ‖(l : K)‖ ^ n` using `norm_pow _ _`.

Establish `hπpos : 0 < ‖(l : K) ^ n‖` using `norm_pos_iff.mpr hπ0`. Establish `hbn : ‖(ε - c * (σ ^ 2) ε) / (l : K) ^ n‖ ≤ 1`. Rewrite using `[norm_div, div_le_one hπpos, hπn]`. Conclude with `hε`. Establish `hc0 : c ≠ 0` using `by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc`.

Establish `hci : ‖c⁻¹‖ = 1` using `by rw [norm_inv, hc, inv_one]`. Establish `hq : 2 ≤ l ^ 2` using `le_trans (by omega : 2 ≤ l) (Nat.le_self_pow (by norm_num) l)`. Take `⟨y, hy, hroot⟩` from `unitFix_root hR (l ^ 2) hq c⁻¹ (c⁻¹ * ((ε - c * (σ ^ 2) ε) / (l : K) ^ n)) hci.le (by rw [norm_mul, hci, one_mul]; exact hbn)`. Establish `hfy` using `unitFix_frob2 l σ hU y hy`. Establish `hσπ : (σ ^ 2) ((l : K) ^ n) = (l : K) ^ n` using `by rw [map_pow, map_natCast]`.

Use `⟨(l : K) ^ n * y, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_mul, ← hπn]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) hy`. Use `set b : K := (ε - c * (σ ^ 2) ε) / (l : K) ^ n with hb`. Establish `e : (ε + (l : K) ^ n * y) - c * (σ ^ 2) (ε + (l : K) ^ n * y) = (l : K) ^ n * (b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y))`.

Rewrite using `[map_add, map_mul, hσπ, hb]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : b + y - c * y ^ (l ^ 2) = -c * (y ^ (l ^ 2) - c⁻¹ * y - c⁻¹ * b)` using `by field_simp; ring`. Establish `hlt : ‖b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y)‖ < 1`.

Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[e2, norm_mul, norm_neg, hc, one_mul]`. Conclude with `hroot`. Rewrite using `[norm_mul, hc, one_mul, ← norm_neg, neg_sub]`. Conclude with `hfy`.

Rewrite using `[e, norm_mul, hπn, pow_succ]`. Conclude with `mul_le_mul_of_nonneg_left (hdisc _ hlt) (pow_nonneg (norm_nonneg _) _)`.
-/
theorem unitFix_step {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K)
    (hU : Unr K l σ) (hR : ResAlg K) (c : K) (hc : ‖c‖ = 1) (n : ℕ) (ε : K)
    (hε : ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n) :
    ∃ η : K, ‖η‖ ≤ ‖(l : K)‖ ^ n ∧ ‖(ε + η) - c * (σ ^ 2) (ε + η)‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hπ0 : (l : K) ^ n ≠ 0 := pow_ne_zero _ hl0
  have hπn : ‖(l : K) ^ n‖ = ‖(l : K)‖ ^ n := norm_pow _ _
  have hπpos : 0 < ‖(l : K) ^ n‖ := norm_pos_iff.mpr hπ0
  have hbn : ‖(ε - c * (σ ^ 2) ε) / (l : K) ^ n‖ ≤ 1 := by
    rw [norm_div, div_le_one hπpos, hπn]; exact hε
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hq : 2 ≤ l ^ 2 := le_trans (by omega : 2 ≤ l) (Nat.le_self_pow (by norm_num) l)
  obtain ⟨y, hy, hroot⟩ := unitFix_root hR (l ^ 2) hq c⁻¹ (c⁻¹ * ((ε - c * (σ ^ 2) ε) / (l : K) ^ n)) hci.le
    (by rw [norm_mul, hci, one_mul]; exact hbn)
  have hfy := unitFix_frob2 l σ hU y hy
  have hσπ : (σ ^ 2) ((l : K) ^ n) = (l : K) ^ n := by rw [map_pow, map_natCast]
  refine ⟨(l : K) ^ n * y, ?_, ?_⟩
  · rw [norm_mul, ← hπn]; exact mul_le_of_le_one_right (norm_nonneg _) hy
  · set b : K := (ε - c * (σ ^ 2) ε) / (l : K) ^ n with hb
    have e : (ε + (l : K) ^ n * y) - c * (σ ^ 2) (ε + (l : K) ^ n * y)
        = (l : K) ^ n * (b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y)) := by
      rw [map_add, map_mul, hσπ, hb]; field_simp; ring
    have e2 : b + y - c * y ^ (l ^ 2) = -c * (y ^ (l ^ 2) - c⁻¹ * y - c⁻¹ * b) := by field_simp; ring
    have hlt : ‖b + y - c * y ^ (l ^ 2) + c * (y ^ (l ^ 2) - (σ ^ 2) y)‖ < 1 := by
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [e2, norm_mul, norm_neg, hc, one_mul]; exact hroot
      · rw [norm_mul, hc, one_mul, ← norm_neg, neg_sub]; exact hfy
    rw [e, norm_mul, hπn, pow_succ]
    exact mul_le_mul_of_nonneg_left (hdisc _ hlt) (pow_nonneg (norm_nonneg _) _)

/- English proof (translation)
Establish `hU'` using `hU`. Take `⟨hp, h2, hl1, hdisc, hiso, hfr⟩` from `hU'`. Establish `hc0 : c ≠ 0` using `by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc`. Establish `hci : ‖c⁻¹‖ = 1` using `by rw [norm_inv, hc, inv_one]`. Establish `hq : 4 ≤ l ^ 2` using `by nlinarith`.

Take `⟨m, hm⟩ : ∃ m, l ^ 2 = m + 1` from `⟨l ^ 2 - 1, by omega⟩`. Establish `hm2 : 2 ≤ m` using `by omega`. Take `⟨x, hx, hroot⟩` from `unitFix_root hR m hm2 0 c⁻¹ (by simp) hci.le`. Simplify using `only [zero_mul, sub_zero] at hroot`. Establish `hx1 : ‖x‖ = 1`.

Use `le_antisymm hx (not_lt.mp fun hlt => ?_)` and prove the remaining obligations. Establish `hxm : ‖x ^ m‖ < 1` using `by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt (by omega)`. Establish `: ‖c⁻¹‖ < 1`. Establish `e : c⁻¹ = x ^ m - (x ^ m - c⁻¹)` using `by ring`. Rewrite using `[e]`.

Conclude with `lt_of_le_of_lt (unitFix_subMax _ _) (max_lt hxm hroot)`. Rewrite `this` using `[hci]`. Conclude with `lt_irrefl _ this`. Use `⟨x, hx1, ?_⟩` and prove the remaining obligations. Establish `hfx` using `unitFix_frob2 l σ hU x hx`.

Establish `e : x - c * (σ ^ 2) x = -(c * x) * (x ^ m - c⁻¹) + c * (x ^ (l ^ 2) - (σ ^ 2) x)`. Rewrite using `[hm, pow_succ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[pow_one]`.

Apply `hdisc` to reduce the goal to its premises. Rewrite using `[e]`. Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]`. Conclude with `hroot`.

Rewrite using `[norm_mul, hc, one_mul, ← norm_neg, neg_sub]`. Conclude with `hfx`.
-/
theorem unitFix_init {K : Type} [NormedField K] [IsUltrametricDist K] (l : ℕ) (σ : K →+* K)
    (hU : Unr K l σ) (hR : ResAlg K) (c : K) (hc : ‖c‖ = 1) :
    ∃ ε : K, ‖ε‖ = 1 ∧ ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ 1 := by
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hq : 4 ≤ l ^ 2 := by nlinarith
  obtain ⟨m, hm⟩ : ∃ m, l ^ 2 = m + 1 := ⟨l ^ 2 - 1, by omega⟩
  have hm2 : 2 ≤ m := by omega
  obtain ⟨x, hx, hroot⟩ := unitFix_root hR m hm2 0 c⁻¹ (by simp) hci.le
  simp only [zero_mul, sub_zero] at hroot
  have hx1 : ‖x‖ = 1 := by
    refine le_antisymm hx (not_lt.mp fun hlt => ?_)
    have hxm : ‖x ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hlt (by omega)
    have : ‖c⁻¹‖ < 1 := by
      have e : c⁻¹ = x ^ m - (x ^ m - c⁻¹) := by ring
      rw [e]; exact lt_of_le_of_lt (unitFix_subMax _ _) (max_lt hxm hroot)
    rw [hci] at this; exact lt_irrefl _ this
  refine ⟨x, hx1, ?_⟩
  have hfx := unitFix_frob2 l σ hU x hx
  have e : x - c * (σ ^ 2) x = -(c * x) * (x ^ m - c⁻¹) + c * (x ^ (l ^ 2) - (σ ^ 2) x) := by
    rw [hm, pow_succ]; field_simp; ring
  rw [pow_one]
  apply hdisc
  rw [e]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]; exact hroot
  · rw [norm_mul, hc, one_mul, ← norm_neg, neg_sub]; exact hfx

/- English proof (translation)
Introduce `K _ _ _ _ l σ hU hR c hc`. Establish `hU'` using `hU`. Take `⟨hp, h2, hl1, hdisc, hiso, hfr⟩` from `hU'`. Take `⟨ε0, hε0n, hε0⟩` from `unitFix_init l σ hU hR c hc`. Establish `hstep : ∀ (n : ℕ) (ε : K), ∃ η : K, ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n → ‖η‖ ≤ ‖(l : K)‖ ^ n ∧ ‖(ε + η) - c * (σ ^ 2) (ε + η)‖ ≤ ‖(l : K)‖ ^ (n + 1)`.

Introduce `n ε`. Distinguish the cases in `h : ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n`. Take `⟨η, h1⟩` from `unitFix_step l σ hU hR c hc n ε h`. Conclude with `⟨η, fun _ => h1⟩`. Conclude with `⟨0, fun h' => absurd h' h⟩`.

Use `choose g hg using hstep`. Set `e : ℕ → K` to `fun k => Nat.rec ε0 (fun k x => x + g (k + 1) x) k`. Establish `he0 : e 0 = ε0` using `rfl`. Establish `hes : ∀ k, e (k + 1) = e k + g (k + 1) (e k)` using `fun k => rfl`. Establish `hpow : ∀ k : ℕ, ‖(l : K)‖ ^ (k + 1) < 1` using `fun k => pow_lt_one₀ (norm_nonneg _) hl1 (by omega)`.

Establish `hinv : ∀ k, ‖e k‖ = 1 ∧ ‖e k - c * (σ ^ 2) (e k)‖ ≤ ‖(l : K)‖ ^ (k + 1)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨he0 ▸ hε0n, by rw [he0]; simpa using hε0⟩`. Consider the case `succ k ih`.

Take `⟨hη, herr⟩` from `hg (k + 1) (e k) ih.2`. Use `⟨?_, by rw [hes]; exact herr⟩` and prove the remaining obligations. Establish `hlt : ‖g (k + 1) (e k)‖ < ‖e k‖` using `by rw [ih.1]; exact lt_of_le_of_lt hη (hpow k)`. Rewrite using `[hes, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, ih.1]`. Establish `hcs : CauchySeq e`.

Use `cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 (fun k => ?_)` and prove the remaining obligations. Rewrite using `[dist_eq_norm, hes, sub_add_cancel_left, norm_neg, ← pow_succ']`. Conclude with `(hg (k + 1) (e k) (hinv k).2).1`. Take `⟨ε, hlim⟩` from `cauchySeq_tendsto_of_complete hcs`. Establish `hτc : Continuous (fun x : K => (σ ^ 2) x)` using `AddMonoidHomClass.continuous_of_bound (σ ^ 2) 1 (fun x => by`.

Rewrite using `[one_mul, unitFix_sq_apply, hiso, hiso])`. Establish `hcont : Continuous (fun x : K => x - c * (σ ^ 2) x)` using `continuous_id.sub (continuous_const.mul hτc)`. Establish `h1 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds (ε - c * (σ ^ 2) ε))` using `(hcont.tendsto ε).comp hlim`. Establish `h0 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds 0)` using `squeeze_zero_norm (fun k => (hinv k).2) ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1).comp (Filter.tendsto_add_atTop_nat 1))`. Establish `heq : ε - c * (σ ^ 2) ε = 0` using `tendsto_nhds_unique h1 h0`.

Use `⟨ε, ?_, sub_eq_zero.mp heq⟩` and prove the remaining obligations. Establish `hn : Filter.Tendsto (fun k => ‖e k‖) Filter.atTop (nhds ‖ε‖)` using `(continuous_norm.tendsto ε).comp hlim`. Establish `hfun : (fun k => ‖e k‖) = fun _ => (1 : ℝ)` using `funext fun k => (hinv k).1`. Rewrite `hn` using `[hfun]`. Conclude with `tendsto_nhds_unique hn tendsto_const_nhds`.
-/
theorem unit_solution_twisted_frobenius : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K]
    [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ c : K, ‖c‖ = 1 →
    ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * (σ ^ 2) ε := by
  intro K _ _ _ _ l σ hU hR c hc
  have hU' := hU
  obtain ⟨hp, h2, hl1, hdisc, hiso, hfr⟩ := hU'
  obtain ⟨ε0, hε0n, hε0⟩ := unitFix_init l σ hU hR c hc
  have hstep : ∀ (n : ℕ) (ε : K), ∃ η : K, ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n →
      ‖η‖ ≤ ‖(l : K)‖ ^ n ∧ ‖(ε + η) - c * (σ ^ 2) (ε + η)‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    intro n ε
    by_cases h : ‖ε - c * (σ ^ 2) ε‖ ≤ ‖(l : K)‖ ^ n
    · obtain ⟨η, h1⟩ := unitFix_step l σ hU hR c hc n ε h
      exact ⟨η, fun _ => h1⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose g hg using hstep
  let e : ℕ → K := fun k => Nat.rec ε0 (fun k x => x + g (k + 1) x) k
  have he0 : e 0 = ε0 := rfl
  have hes : ∀ k, e (k + 1) = e k + g (k + 1) (e k) := fun k => rfl
  have hpow : ∀ k : ℕ, ‖(l : K)‖ ^ (k + 1) < 1 := fun k => pow_lt_one₀ (norm_nonneg _) hl1 (by omega)
  have hinv : ∀ k, ‖e k‖ = 1 ∧ ‖e k - c * (σ ^ 2) (e k)‖ ≤ ‖(l : K)‖ ^ (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨he0 ▸ hε0n, by rw [he0]; simpa using hε0⟩
    | succ k ih =>
      obtain ⟨hη, herr⟩ := hg (k + 1) (e k) ih.2
      refine ⟨?_, by rw [hes]; exact herr⟩
      have hlt : ‖g (k + 1) (e k)‖ < ‖e k‖ := by rw [ih.1]; exact lt_of_le_of_lt hη (hpow k)
      rw [hes, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, ih.1]
  have hcs : CauchySeq e := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 (fun k => ?_)
    rw [dist_eq_norm, hes, sub_add_cancel_left, norm_neg, ← pow_succ']
    exact (hg (k + 1) (e k) (hinv k).2).1
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcs
  have hτc : Continuous (fun x : K => (σ ^ 2) x) := AddMonoidHomClass.continuous_of_bound (σ ^ 2) 1 (fun x => by
    rw [one_mul, unitFix_sq_apply, hiso, hiso])
  have hcont : Continuous (fun x : K => x - c * (σ ^ 2) x) := continuous_id.sub (continuous_const.mul hτc)
  have h1 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds (ε - c * (σ ^ 2) ε)) :=
    (hcont.tendsto ε).comp hlim
  have h0 : Filter.Tendsto (fun k => e k - c * (σ ^ 2) (e k)) Filter.atTop (nhds 0) :=
    squeeze_zero_norm (fun k => (hinv k).2)
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1).comp (Filter.tendsto_add_atTop_nat 1))
  have heq : ε - c * (σ ^ 2) ε = 0 := tendsto_nhds_unique h1 h0
  refine ⟨ε, ?_, sub_eq_zero.mp heq⟩
  have hn : Filter.Tendsto (fun k => ‖e k‖) Filter.atTop (nhds ‖ε‖) := (continuous_norm.tendsto ε).comp hlim
  have hfun : (fun k => ‖e k‖) = fun _ => (1 : ℝ) := funext fun k => (hinv k).1
  rw [hfun] at hn
  exact tendsto_nhds_unique hn tendsto_const_nhds

end GlobalTheory.Honda
