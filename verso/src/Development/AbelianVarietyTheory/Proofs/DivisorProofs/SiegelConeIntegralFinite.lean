import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.SiegelSet.ConeDecay

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]`. Use `lintegral_congr fun a => ?_` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_succ]`. Both sides reduce to the same expression. Conclude with `Finset.aemeasurable_fun_prod _ fun i _ => (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)`.
-/
theorem lintegral_pi_prod {r : ℕ} {E : Fin r → Type} {mE : ∀ i, MeasurableSpace (E i)}
    {μ : ∀ i, Measure (E i)} [∀ i, SigmaFinite (μ i)] {f : ∀ i, E i → ℝ≥0∞} (hf : ∀ i, AEMeasurable (f i) (μ i)) :
    ∫⁻ x : ∀ i, E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
      Fin.prod_univ_succ, ← ih fun i => hf _, ← lintegral_prod_mul (hf 0)]
    · refine lintegral_congr fun a => ?_
      rw [Fin.prod_univ_succ]
      rfl
    · exact Finset.aemeasurable_fun_prod _ fun i _ =>
        (hf _).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval (fun i : Fin n => μ i.succ) i)

/- English proof (translation)
Simplify using `only [GlobalTheory.SiegelSet.cone, Set.setOf_and, Set.setOf_forall]`. Conclude with `(MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => measurableSet_le (measurable_const.mul (measurable_pi_apply j)) (measurable_pi_apply i)).int …`.
-/
theorem measurableSet_cone (r : ℕ) (c : ℝ) : MeasurableSet (GlobalTheory.SiegelSet.cone r c) := by
  simp only [GlobalTheory.SiegelSet.cone, Set.setOf_and, Set.setOf_forall]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_le (measurable_const.mul (measurable_pi_apply j)) (measurable_pi_apply i)).inter
     (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => measurableSet_le measurable_const (measurable_pi_apply i)))

/- English proof (translation)
Use `set b := min c 1`. Establish `hb0 : 0 < b` using `lt_min hc one_pos`. Establish `hb1 : b ≤ 1` using `min_le_right _ _`. Establish `hbc : b ≤ c` using `min_le_left _ _`. Establish `key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → b ^ (k + 1) ≤ t i`.

Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro i hi; rw [zero_add, pow_one]; exact hbc.trans (ht.2.2 i (by omega))`. Consider the case `succ k ih`. Introduce `i hi`.

Establish `hj : i.val + 1 < r` using `by omega`. Establish `h1` using `ih ⟨i.val + 1, hj⟩ (by simp only; omega)`. Establish `h2` using `ht.2.1 i ⟨i.val + 1, hj⟩ rfl`. Combine the equalities or inequalities in the displayed calculation. Use `key (r - 1 - i.val) i (by omega)` as an intermediate fact.

Conclude with `(pow_le_pow_of_le_one hb0.le hb1 (by omega)).trans this`.
-/
theorem le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ} (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) :
    min c 1 ^ r ≤ t i := by
  set b := min c 1
  have hb0 : 0 < b := lt_min hc one_pos
  have hb1 : b ≤ 1 := min_le_right _ _
  have hbc : b ≤ c := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → b ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero => intro i hi; rw [zero_add, pow_one]; exact hbc.trans (ht.2.2 i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp only; omega)
      have h2 := ht.2.1 i ⟨i.val + 1, hj⟩ rfl
      calc b ^ (k + 1 + 1) = b * b ^ (k + 1) := by ring
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul hbc h1 (by positivity) hc.le
        _ ≤ t i := h2
  have := key (r - 1 - i.val) i (by omega)
  exact (pow_le_pow_of_le_one hb0.le hb1 (by omega)).trans this

/- English proof (translation)
Establish `ht0 : 0 < t` using `hm.trans_le ht`. Establish `hmi : 1 ≤ m⁻¹` using `(one_le_inv₀ hm).2 hm1`. Establish `hA : 1 ≤ m⁻¹ ^ K` using `one_le_pow₀ hmi`. Establish `hB : 1 ≤ (1 + t) ^ K` using `one_le_pow₀ (by linarith)`. Take `⟨k, rfl | rfl⟩` from `Int.eq_nat_or_neg e`.

Establish `hk : k ≤ K` using `by omega`. Rewrite using `[zpow_natCast]`. Combine the equalities or inequalities in the displayed calculation. Establish `hk : k ≤ K` using `by omega`. Rewrite using `[zpow_neg, zpow_natCast]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem zpow_le_of_le {m t : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) (ht : m ≤ t) {K : ℕ} {e : ℤ} (h1 : -(K : ℤ) ≤ e)
    (h2 : e ≤ K) : t ^ e ≤ m⁻¹ ^ K * (1 + t) ^ K := by
  have ht0 : 0 < t := hm.trans_le ht
  have hmi : 1 ≤ m⁻¹ := (one_le_inv₀ hm).2 hm1
  have hA : 1 ≤ m⁻¹ ^ K := one_le_pow₀ hmi
  have hB : 1 ≤ (1 + t) ^ K := one_le_pow₀ (by linarith)
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg e
  · have hk : k ≤ K := by omega
    rw [zpow_natCast]
    calc t ^ k ≤ (1 + t) ^ k := pow_le_pow_left₀ ht0.le (by linarith) k
      _ ≤ (1 + t) ^ K := pow_le_pow_right₀ (by linarith) hk
      _ ≤ m⁻¹ ^ K * (1 + t) ^ K := le_mul_of_one_le_left (by positivity) hA
  · have hk : k ≤ K := by omega
    rw [zpow_neg, zpow_natCast]
    calc (t ^ k)⁻¹ ≤ (m ^ k)⁻¹ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hm.le ht k)
      _ = m⁻¹ ^ k := (inv_pow m k).symm
      _ ≤ m⁻¹ ^ K := pow_le_pow_right₀ hmi hk
      _ ≤ m⁻¹ ^ K * (1 + t) ^ K := le_mul_of_one_le_right (by positivity) hB

/- English proof (translation)
Establish `hx1 : 0 < 1 + x` using `by linarith`. Establish `e : ((a * (1 + x)) ^ (K + 2))⁻¹ * (M * (1 + x) ^ K) = M / a ^ (K + 2) * ((1 + x) ^ 2)⁻¹`. Rewrite using `[mul_pow, pow_add (1 + x)]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Conclude with `mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by nlinarith)) (by positivity)`.
-/
theorem factor_le {a M x : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (hx : 0 ≤ x) (K : ℕ) :
    ((a * (1 + x)) ^ (K + 2))⁻¹ * (M * (1 + x) ^ K) ≤ M / a ^ (K + 2) * (1 + x ^ 2)⁻¹ := by
  have hx1 : 0 < 1 + x := by linarith
  have e : ((a * (1 + x)) ^ (K + 2))⁻¹ * (M * (1 + x) ^ K) = M / a ^ (K + 2) * ((1 + x) ^ 2)⁻¹ := by
    rw [mul_pow, pow_add (1 + x)]
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by nlinarith)) (by positivity)

end GlobalTheory.SiegelSet.ConeDecay

namespace GlobalTheory.SiegelSet.ConeDecay

/- English proof (translation)
Establish `hpos : ∀ i, 0 < t i` using `fun i => hm.trans_le (htm i)`. Establish `ha0 : 0 < m ^ r` using `pow_pos hm r`. Establish `ha1 : m ^ r ≤ 1` using `pow_le_one₀ hm.le hm1`. Establish `hP0 : 0 ≤ ∏ i, t i` using `Finset.prod_nonneg fun i _ => (hpos i).le`. Establish `hB : ∀ j, m ^ r * (1 + t j) ≤ 1 + ∏ i, t i`.

Introduce `j`. Establish `e` using `Finset.mul_prod_erase Finset.univ t (Finset.mem_univ j)`. Establish `hQ : m ^ r ≤ ∏ i ∈ Finset.univ.erase j, t i`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left hQ (hpos j).le` as an intermediate fact.

Use polynomial arithmetic with `[hpos j]`. Establish `h1 : ∏ j, (m ^ r * (1 + t j)) ^ (K + 2) ≤ (1 + ∏ i, t i) ^ ((K + 2) * r)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ((∏ i : Fin r, t i ^ (2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1))) * ∏ i, t i)⁻¹ ≤ ∏ j, m⁻¹ ^ K * (1 + t j) ^ K`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]`.

Use `Finset.prod_le_prod (fun i _ => inv_nonneg.2 (mul_nonneg (zpow_nonneg (hpos i).le _) (hpos i).le)) (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← zpow_add_one₀ (hpos i).ne', ← zpow_neg]`. Establish `hi : (i.val : ℤ) < r` using `by exact_mod_cast i.isLt`. Establish `hi0 : (0 : ℤ) ≤ i.val` using `by positivity`. Establish `hf0 : (0 : ℤ) ≤ f` using `by positivity`.

Establish `hn0 : (0 : ℤ) ≤ n` using `by positivity`. Establish `hKz : (K : ℤ) = 2 * (f : ℤ) * ((n : ℤ) + 2 * r + 1) + 1` using `by rw [hK]; push_cast; ring`. Establish `u1` using `mul_le_mul_of_nonneg_left (show (n : ℤ) - 2 * i.val - 1 ≤ n + 2 * r + 1 by linarith) hf0`. Establish `u2` using `mul_le_mul_of_nonneg_left (show 2 * (i.val : ℤ) + 1 - n ≤ n + 2 * r + 1 by linarith) hf0`. Apply `zpow_le_of_le hm hm1 (htm i)` to reduce the goal to its premises.

Rewrite using `[hKz]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hKz]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hD : 0 < ∏ j, (m ^ r * (1 + t j)) ^ (K + 2)` using `Finset.prod_pos fun j _ => pow_pos (mul_pos ha0 (by linarith [hpos j])) _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`. Use `_ ≤ ∏ j, (m⁻¹ ^ K / (m ^ r) ^ (K + 2) * (1 + t j ^ 2)⁻¹) := Finset.prod_le_prod (fun j _ => mul_nonneg (inv_nonneg.2 (pow_nonneg (mul_nonneg ha0.le (by linarith [hpos j])) _)) (mul_nonneg (pow_nonneg (inv_nonneg.2 hm.le) _) (pow_nonneg (by linarith [hpos j]) _))) (fun j _ => fact …`.
-/
theorem pointwise (f n r K : ℕ) (hK : K = 2 * f * (n + 2 * r + 1) + 1) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    {t : Fin r → ℝ} (htm : ∀ i, m ≤ t i) :
    ((1 + ∏ i, t i) ^ ((K + 2) * r))⁻¹ *
        ((∏ i : Fin r, t i ^ (2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1))) * ∏ i, t i)⁻¹ ≤
      ∏ j, (m⁻¹ ^ K / (m ^ r) ^ (K + 2) * (1 + t j ^ 2)⁻¹) := by
  have hpos : ∀ i, 0 < t i := fun i => hm.trans_le (htm i)
  have ha0 : 0 < m ^ r := pow_pos hm r
  have ha1 : m ^ r ≤ 1 := pow_le_one₀ hm.le hm1
  have hP0 : 0 ≤ ∏ i, t i := Finset.prod_nonneg fun i _ => (hpos i).le
  have hB : ∀ j, m ^ r * (1 + t j) ≤ 1 + ∏ i, t i := by
    intro j
    have e := Finset.mul_prod_erase Finset.univ t (Finset.mem_univ j)
    have hQ : m ^ r ≤ ∏ i ∈ Finset.univ.erase j, t i := by
      calc m ^ r ≤ m ^ (Finset.univ.erase j).card :=
            pow_le_pow_of_le_one hm.le hm1 ((Finset.card_erase_le).trans (by simp))
        _ = ∏ i ∈ Finset.univ.erase j, m := (Finset.prod_const m).symm
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => hm.le) (fun i _ => htm i)
    have := mul_le_mul_of_nonneg_left hQ (hpos j).le
    nlinarith [hpos j]
  have h1 : ∏ j, (m ^ r * (1 + t j)) ^ (K + 2) ≤ (1 + ∏ i, t i) ^ ((K + 2) * r) := by
    calc ∏ j, (m ^ r * (1 + t j)) ^ (K + 2) ≤ ∏ _j : Fin r, (1 + ∏ i, t i) ^ (K + 2) :=
          Finset.prod_le_prod (fun j _ => pow_nonneg (mul_nonneg ha0.le (by linarith [hpos j])) _)
            (fun j _ => pow_le_pow_left₀ (mul_nonneg ha0.le (by linarith [hpos j])) (hB j) _)
      _ = (1 + ∏ i, t i) ^ ((K + 2) * r) := by rw [Fin.prod_const, pow_mul]
  have h2 : ((∏ i : Fin r, t i ^ (2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1))) * ∏ i, t i)⁻¹ ≤
      ∏ j, m⁻¹ ^ K * (1 + t j) ^ K := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib]
    refine Finset.prod_le_prod (fun i _ => inv_nonneg.2 (mul_nonneg (zpow_nonneg (hpos i).le _) (hpos i).le))
      (fun i _ => ?_)
    rw [← zpow_add_one₀ (hpos i).ne', ← zpow_neg]
    have hi : (i.val : ℤ) < r := by exact_mod_cast i.isLt
    have hi0 : (0 : ℤ) ≤ i.val := by positivity
    have hf0 : (0 : ℤ) ≤ f := by positivity
    have hn0 : (0 : ℤ) ≤ n := by positivity
    have hKz : (K : ℤ) = 2 * (f : ℤ) * ((n : ℤ) + 2 * r + 1) + 1 := by rw [hK]; push_cast; ring
    have u1 := mul_le_mul_of_nonneg_left (show (n : ℤ) - 2 * i.val - 1 ≤ n + 2 * r + 1 by linarith) hf0
    have u2 := mul_le_mul_of_nonneg_left (show 2 * (i.val : ℤ) + 1 - n ≤ n + 2 * r + 1 by linarith) hf0
    apply zpow_le_of_le hm hm1 (htm i)
    · rw [hKz]; nlinarith
    · rw [hKz]; nlinarith
  have hD : 0 < ∏ j, (m ^ r * (1 + t j)) ^ (K + 2) :=
    Finset.prod_pos fun j _ => pow_pos (mul_pos ha0 (by linarith [hpos j])) _
  calc ((1 + ∏ i, t i) ^ ((K + 2) * r))⁻¹ *
        ((∏ i : Fin r, t i ^ (2 * (f : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1))) * ∏ i, t i)⁻¹
      ≤ (∏ j, (m ^ r * (1 + t j)) ^ (K + 2))⁻¹ * ∏ j, m⁻¹ ^ K * (1 + t j) ^ K :=
        mul_le_mul (inv_anti₀ hD h1) h2
          (inv_nonneg.2 (mul_nonneg (Finset.prod_nonneg fun i _ => zpow_nonneg (hpos i).le _) hP0))
          (inv_nonneg.2 hD.le)
    _ = ∏ j, ((m ^ r * (1 + t j)) ^ (K + 2))⁻¹ * (m⁻¹ ^ K * (1 + t j) ^ K) := by
        rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    _ ≤ ∏ j, (m⁻¹ ^ K / (m ^ r) ^ (K + 2) * (1 + t j ^ 2)⁻¹) :=
        Finset.prod_le_prod (fun j _ => mul_nonneg (inv_nonneg.2 (pow_nonneg (mul_nonneg ha0.le
            (by linarith [hpos j])) _)) (mul_nonneg (pow_nonneg (inv_nonneg.2 hm.le) _) (pow_nonneg (by linarith [hpos j]) _)))
          (fun j _ => factor_le ha0 (pow_nonneg (inv_nonneg.2 hm.le) _) (hpos j).le K)

end GlobalTheory.SiegelSet.ConeDecay

open GlobalTheory.SiegelSet.ConeDecay in

/- English proof (translation)
Introduce `F _ _ n r c hc`. Take `⟨K, hK⟩ : ∃ K : ℕ, K = 2 * Module.finrank ℚ F * (n + 2 * r + 1) + 1` from `⟨_, rfl⟩`. Establish `hb : 0 < min c 1` using `lt_min hc one_pos`. Take `⟨m, hmdef⟩ : ∃ m : ℝ, m = min c 1 ^ r` from `⟨_, rfl⟩`. Establish `hm : 0 < m` using `hmdef ▸ pow_pos hb r`.

Establish `hm1 : m ≤ 1` using `hmdef ▸ pow_le_one₀ hb.le (min_le_right _ _)`. Take `⟨C, hC⟩ : ∃ C : ℝ, C = m⁻¹ ^ K / (m ^ r) ^ (K + 2)` from `⟨_, rfl⟩`. Establish `hC0 : 0 ≤ C` using `hC ▸ div_nonneg (pow_nonneg (inv_nonneg.2 hm.le) _) (pow_nonneg (pow_nonneg hm.le _) _)`. Use `⟨(K + 2) * r, ?_⟩` and prove the remaining obligations. Establish `hmeas` using `measurableSet_cone r c`.

Establish `hg : Measurable fun x : ℝ => ENNReal.ofReal (C * (1 + x ^ 2)⁻¹)` using `by fun_prop`. Establish `hprod : ∫⁻ t : Fin r → ℝ, ∏ j, ENNReal.ofReal (C * (1 + t j ^ 2)⁻¹) = ∏ _j : Fin r, ∫⁻ x : ℝ, ENNReal.ofReal (C * (1 + x ^ 2)⁻¹)` using `lintegral_pi_prod (E := fun _ => ℝ) (μ := fun _ => volume) (f := fun _ x => ENNReal.ofReal (C * (1 + x ^ 2)⁻¹)) (fun _ => hg.aemeasurable)`. Establish `hone : ∫⁻ x : ℝ, ENNReal.ofReal (C * (1 + x ^ 2)⁻¹) < ⊤` using `(integrable_inv_one_add_sq.const_mul C).lintegral_lt_top`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono_ae ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun t ht => ?_))` and prove the remaining obligations.

Establish `hpos : ∀ i, 0 < t i` using `ht.1`. Rewrite using `[← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => (hpos i).le)) _)), ← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (f := fun j => C * (1 + t j ^ 2)⁻¹) (fun j _ => mul_nonneg hC0 (by positivity))]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Use `pointwise (Module.finrank ℚ F) n r K hK hm hm1 (t := t) (fun i => hmdef ▸ le_of_mem_cone hc ht i)` as an intermediate fact. Rewrite `this` using `[← hC]`.

Conclude with `this`. Use `_ ≤ ∫⁻ t : Fin r → ℝ, ∏ j, ENNReal.ofReal (C * (1 + t j ^ 2)⁻¹) := setLIntegral_le_lintegral _ _`. Use `_ = ∏ _j : Fin r, ∫⁻ x : ℝ, ENNReal.ofReal (C * (1 + x ^ 2)⁻¹) := hprod`. Use `_ < ⊤ := ENNReal.prod_lt_top fun _ _ => hone`.
-/
theorem GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) {c : ℝ}, 0 < c →
    ∃ L : ℕ, ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal ((1 + ∏ i, t i) ^ L)⁻¹ *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r c hc
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 2 * Module.finrank ℚ F * (n + 2 * r + 1) + 1 := ⟨_, rfl⟩
  have hb : 0 < min c 1 := lt_min hc one_pos
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = min c 1 ^ r := ⟨_, rfl⟩
  have hm : 0 < m := hmdef ▸ pow_pos hb r
  have hm1 : m ≤ 1 := hmdef ▸ pow_le_one₀ hb.le (min_le_right _ _)
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = m⁻¹ ^ K / (m ^ r) ^ (K + 2) := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC ▸ div_nonneg (pow_nonneg (inv_nonneg.2 hm.le) _) (pow_nonneg (pow_nonneg hm.le _) _)
  refine ⟨(K + 2) * r, ?_⟩
  have hmeas := measurableSet_cone r c
  have hg : Measurable fun x : ℝ => ENNReal.ofReal (C * (1 + x ^ 2)⁻¹) := by fun_prop
  have hprod : ∫⁻ t : Fin r → ℝ, ∏ j, ENNReal.ofReal (C * (1 + t j ^ 2)⁻¹) =
      ∏ _j : Fin r, ∫⁻ x : ℝ, ENNReal.ofReal (C * (1 + x ^ 2)⁻¹) :=
    lintegral_pi_prod (E := fun _ => ℝ) (μ := fun _ => volume) (f := fun _ x => ENNReal.ofReal (C * (1 + x ^ 2)⁻¹))
      (fun _ => hg.aemeasurable)
  have hone : ∫⁻ x : ℝ, ENNReal.ofReal (C * (1 + x ^ 2)⁻¹) < ⊤ :=
    (integrable_inv_one_add_sq.const_mul C).lintegral_lt_top
  calc _ ≤ ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ∏ j, ENNReal.ofReal (C * (1 + t j ^ 2)⁻¹) := by
        refine lintegral_mono_ae ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun t ht => ?_))
        have hpos : ∀ i, 0 < t i := ht.1
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg (add_nonneg zero_le_one
            (Finset.prod_nonneg fun i _ => (hpos i).le)) _)),
          ← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (f := fun j => C * (1 + t j ^ 2)⁻¹)
            (fun j _ => mul_nonneg hC0 (by positivity))]
        refine ENNReal.ofReal_le_ofReal ?_
        have := pointwise (Module.finrank ℚ F) n r K hK hm hm1 (t := t) (fun i => hmdef ▸ le_of_mem_cone hc ht i)
        rw [← hC] at this
        exact this
    _ ≤ ∫⁻ t : Fin r → ℝ, ∏ j, ENNReal.ofReal (C * (1 + t j ^ 2)⁻¹) := setLIntegral_le_lintegral _ _
    _ = ∏ _j : Fin r, ∫⁻ x : ℝ, ENNReal.ofReal (C * (1 + x ^ 2)⁻¹) := hprod
    _ < ⊤ := ENNReal.prod_lt_top fun _ _ => hone
