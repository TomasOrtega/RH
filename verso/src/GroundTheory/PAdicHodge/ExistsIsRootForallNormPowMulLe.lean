import Mathlib
import GroundTheory.PAdicHodge.ExtRobbaRootPoly
import GroundTheory.PAdicHodge.ExtRobbaUntilt
import GroundTheory.PAdicHodge.ExtRobbaNewton
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

open Polynomial

section Vieta

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F]

/- English proof (translation)
Establish `hsplit : g.Splits` using `IsAlgClosed.splits g`. Establish `hcard : Multiset.card g.roots = g.natDegree` using `splits_iff_card_roots.1 hsplit`. Establish `hg0 : g ≠ 0` using `by rintro rfl; exact h0 (by simp)`. Use `set S := g.roots with hS`. Use `set d := g.natDegree`.

Establish `hSne : S ≠ 0`. Introduce `h`. Rewrite `hcard` using `[h, Multiset.card_zero]`. Use linear arithmetic over natural numbers and integers. Take `⟨s0, hs0S⟩` from `Multiset.exists_mem_of_ne_zero hSne`.

Take `⟨s, hsS, hsmin⟩` from `S.toFinset.exists_min_image (fun t => ‖t‖₊) ⟨s0, Multiset.mem_toFinset.2 hs0S⟩`. Establish `hsS' : s ∈ S` using `Multiset.mem_toFinset.1 hsS`. Use `⟨s, (mem_roots hg0).1 hsS', fun j => ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Simplify using the standard rewrite rules.

Distinguish the cases in `hjd : j ≤ d`. Use `swap`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, mul_zero]; exact norm_nonneg _`. Establish `hs0 : s ≠ 0`. Introduce and unpack `rfl`.

Conclude with `h0 (by rw [coeff_zero_eq_eval_zero]; exact (mem_roots hg0).1 hsS')`. Establish `hspos : 0 < ‖s‖₊` using `nnnorm_pos.2 hs0`. Establish `hg : C g.leadingCoeff * (S.map fun a => X - C a).prod = g` using `C_leadingCoeff_mul_prod_multiset_X_sub_C hcard`. Establish `hc0 : ‖g.coeff 0‖₊ = ‖g.leadingCoeff‖₊ * (S.map fun a => ‖a‖₊).prod`. Rewrite using `[coeff_zero_eq_eval_zero]`.

Use `conv_lhs => rw [← hg]`. Rewrite using `[eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, nnnorm_mul]`. Use `congr 1`. Rewrite using `[nnnorm_multiset_prod', Multiset.map_map]`. Use `congr 1`.

Use `Multiset.map_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hcj` using `coeff_eq_esymm_roots_of_splits hsplit hjd`. Establish `hkey : ∀ T ∈ Multiset.powersetCard (d - j) S, ‖T.prod‖₊ ≤ (S.map fun a => ‖a‖₊).prod / ‖s‖₊ ^ j`. Introduce `T hT`.

Take `⟨hTS, hTc⟩` from `Multiset.mem_powersetCard.1 hT`. Rewrite using `[le_div_iff₀ (pow_pos hspos j), nnnorm_multiset_prod']`. Establish `hsplitS : S = T + (S - T)` using `(add_tsub_cancel_of_le hTS).symm`. Establish `hcardST : Multiset.card (S - T) = j`. Use `Multiset.card_add T (S - T)` as an intermediate fact.

Rewrite `this` using `[← hsplitS, hcard, hTc]`. Use linear arithmetic over natural numbers and integers. Establish `hpow : ‖s‖₊ ^ j ≤ ((S - T).map fun a => ‖a‖₊).prod`. Rewrite using `[← hcardST, ← Multiset.card_map (fun a => ‖a‖₊)]`. Use `Multiset.pow_card_le_prod fun x hx => ?_` and prove the remaining obligations.

Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.1 hx`. Conclude with `hsmin a (Multiset.mem_toFinset.2 (Multiset.mem_of_le (tsub_le_self) ha))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Multiset.prod_add, ← Multiset.map_add, ← hsplitS]`. Establish `hesymm : ‖S.esymm (d - j)‖₊ ≤ (S.map fun a => ‖a‖₊).prod / ‖s‖₊ ^ j`.

Rewrite using `[Multiset.esymm]`. Use `nnnorm_multiset_sum_le_of_forall fun x hx => ?_` and prove the remaining obligations. Take `⟨T, hT, rfl⟩` from `Multiset.mem_map.1 hx`. Conclude with `hkey T hT`. Establish `hcj' : ‖g.coeff j‖₊ ≤ ‖g.leadingCoeff‖₊ * ((S.map fun a => ‖a‖₊).prod / ‖s‖₊ ^ j)`.

Rewrite using `[hcj, nnnorm_mul, nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one, one_pow, mul_one]`. Conclude with `mul_le_mul_of_nonneg_left hesymm (by positivity)`. Establish `final : ‖s‖₊ ^ j * ‖g.coeff j‖₊ ≤ ‖g.coeff 0‖₊`. Rewrite using `[hc0]`. Combine the equalities or inequalities in the displayed calculation.

Clear the denominators using the available nonvanishing facts. Conclude with `final` after adjusting the coercions.
-/
theorem exists_isRoot_forall_norm_pow_mul_le {g : F[X]} (hd : 0 < g.natDegree)
    (h0 : g.coeff 0 ≠ 0) :
    ∃ s : F, g.IsRoot s ∧ ∀ j, ‖s‖ ^ j * ‖g.coeff j‖ ≤ ‖g.coeff 0‖ := by
  classical
  have hsplit : g.Splits := IsAlgClosed.splits g
  have hcard : Multiset.card g.roots = g.natDegree := splits_iff_card_roots.1 hsplit
  have hg0 : g ≠ 0 := by rintro rfl; exact h0 (by simp)
  set S := g.roots with hS
  set d := g.natDegree
  have hSne : S ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at hcard; omega
  obtain ⟨s0, hs0S⟩ := Multiset.exists_mem_of_ne_zero hSne
  obtain ⟨s, hsS, hsmin⟩ := S.toFinset.exists_min_image (fun t => ‖t‖₊)
    ⟨s0, Multiset.mem_toFinset.2 hs0S⟩
  have hsS' : s ∈ S := Multiset.mem_toFinset.1 hsS
  refine ⟨s, (mem_roots hg0).1 hsS', fun j => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  by_cases hjd : j ≤ d
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero, mul_zero]; exact norm_nonneg _
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact h0 (by rw [coeff_zero_eq_eval_zero]; exact (mem_roots hg0).1 hsS')
  have hspos : 0 < ‖s‖₊ := nnnorm_pos.2 hs0
  have hg : C g.leadingCoeff * (S.map fun a => X - C a).prod = g :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hc0 : ‖g.coeff 0‖₊ = ‖g.leadingCoeff‖₊ * (S.map fun a => ‖a‖₊).prod := by
    rw [coeff_zero_eq_eval_zero]
    conv_lhs => rw [← hg]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, nnnorm_mul]
    congr 1
    rw [nnnorm_multiset_prod', Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun a _ => ?_
    simp
  have hcj := coeff_eq_esymm_roots_of_splits hsplit hjd
  have hkey : ∀ T ∈ Multiset.powersetCard (d - j) S,
      ‖T.prod‖₊ ≤ (S.map fun a => ‖a‖₊).prod / ‖s‖₊ ^ j := by
    intro T hT
    obtain ⟨hTS, hTc⟩ := Multiset.mem_powersetCard.1 hT
    rw [le_div_iff₀ (pow_pos hspos j), nnnorm_multiset_prod']
    have hsplitS : S = T + (S - T) := (add_tsub_cancel_of_le hTS).symm
    have hcardST : Multiset.card (S - T) = j := by
      have := Multiset.card_add T (S - T)
      rw [← hsplitS, hcard, hTc] at this; omega
    have hpow : ‖s‖₊ ^ j ≤ ((S - T).map fun a => ‖a‖₊).prod := by
      rw [← hcardST, ← Multiset.card_map (fun a => ‖a‖₊)]
      refine Multiset.pow_card_le_prod fun x hx => ?_
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
      exact hsmin a (Multiset.mem_toFinset.2 (Multiset.mem_of_le (tsub_le_self) ha))
    calc (T.map fun a => ‖a‖₊).prod * ‖s‖₊ ^ j ≤ (T.map fun a => ‖a‖₊).prod *
          ((S - T).map fun a => ‖a‖₊).prod :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (S.map fun a => ‖a‖₊).prod := by
          rw [← Multiset.prod_add, ← Multiset.map_add, ← hsplitS]
  have hesymm : ‖S.esymm (d - j)‖₊ ≤ (S.map fun a => ‖a‖₊).prod / ‖s‖₊ ^ j := by
    rw [Multiset.esymm]
    refine nnnorm_multiset_sum_le_of_forall fun x hx => ?_
    obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.1 hx
    exact hkey T hT
  have hcj' : ‖g.coeff j‖₊ ≤ ‖g.leadingCoeff‖₊ * ((S.map fun a => ‖a‖₊).prod / ‖s‖₊ ^ j) := by
    rw [hcj, nnnorm_mul, nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one, one_pow, mul_one]
    exact mul_le_mul_of_nonneg_left hesymm (by positivity)
  have final : ‖s‖₊ ^ j * ‖g.coeff j‖₊ ≤ ‖g.coeff 0‖₊ := by
    rw [hc0]
    calc ‖s‖₊ ^ j * ‖g.coeff j‖₊
        ≤ ‖s‖₊ ^ j * (‖g.leadingCoeff‖₊ * ((S.map fun a => ‖a‖₊).prod / ‖s‖₊ ^ j)) :=
          mul_le_mul_of_nonneg_left hcj' (by positivity)
      _ = ‖g.leadingCoeff‖₊ * (S.map fun a => ‖a‖₊).prod := by
          field_simp
  exact_mod_cast final

end Vieta

namespace TeichLift

open Laurent Filter Topology UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] (T : TeichLift p L Γ)
  {ρ0 : Set.Ioo (0 : ℝ) 1}

/- English proof (translation)
Use `set a : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ, h.1, h.2.le⟩`. Use `set b : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ + η, by linarith [h.1], hηle⟩`. Establish `hy' : y' ≠ 0`. Introduce and unpack `rfl`. Use `hlt a le_rfl (by show ρ ≤ ρ + η; linarith)` as an intermediate fact.

Rewrite `this` using `[sub_zero]`. Conclude with `lt_irrefl _ this`. Take `⟨c, hc⟩` from `T.exists_approx_norm hy' a b (by show ρ ≤ ρ + η; linarith)`. Establish `h1` using `T.idx_eq_of_approx hy' h hη hηle hc`. Establish `h2` using `T.idx_eq_of_approx hy h hη hηle (c := c) fun σ hσ1 hσ2 => by`.

Establish `e1` using `hlt σ hσ1 hσ2`. Establish `e2` using `hc σ hσ1 hσ2`. Establish `e3 : T.extNorm ρ0 σ y' = T.extNorm ρ0 σ y`. Use `T.extNorm_eq_of_lt (x := y) (c := y') e1` as an intermediate fact. Conclude with `this`.

Use `T.extNorm_add_le σ (y - y') (y' - c)` as an intermediate fact. Rewrite `this` using `[sub_add_sub_cancel]`. Conclude with `this.trans_lt (max_lt e1 (e3 ▸ e2))`. Conclude with `⟨h2.1.trans h1.1.symm, h2.2.trans h1.2.symm⟩`.
-/
theorem idx_eq_of_near {y y' : T.RobbaExt ρ0} (hy : y ≠ 0) {ρ : ℝ} (h : 0 < ρ ∧ ρ < ρ0) {η : ℝ}
    (hη : 0 < η) (hηle : ρ + η ≤ ρ0)
    (hlt : ∀ σ : Set.Ioc (0 : ℝ) ρ0, ρ ≤ σ → (σ : ℝ) ≤ ρ + η →
      T.extNorm ρ0 σ (y - y') < T.extNorm ρ0 σ y) :
    T.lowIdx y ρ = T.lowIdx y' ρ ∧ T.highIdx y ρ = T.highIdx y' ρ := by
  set a : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ, h.1, h.2.le⟩
  set b : Set.Ioc (0 : ℝ) ρ0 := ⟨ρ + η, by linarith [h.1], hηle⟩
  have hy' : y' ≠ 0 := by
    rintro rfl
    have := hlt a le_rfl (by show ρ ≤ ρ + η; linarith)
    rw [sub_zero] at this
    exact lt_irrefl _ this
  obtain ⟨c, hc⟩ := T.exists_approx_norm hy' a b (by show ρ ≤ ρ + η; linarith)
  have h1 := T.idx_eq_of_approx hy' h hη hηle hc
  have h2 := T.idx_eq_of_approx hy h hη hηle (c := c) fun σ hσ1 hσ2 => by
    have e1 := hlt σ hσ1 hσ2
    have e2 := hc σ hσ1 hσ2
    have e3 : T.extNorm ρ0 σ y' = T.extNorm ρ0 σ y := by
      have := T.extNorm_eq_of_lt (x := y) (c := y') e1
      exact this
    have := T.extNorm_add_le σ (y - y') (y' - c)
    rw [sub_add_sub_cancel] at this
    exact this.trans_lt (max_lt e1 (e3 ▸ e2))
  exact ⟨h2.1.trans h1.1.symm, h2.2.trans h1.2.symm⟩

section Prim

variable {ξ : T.int} (hξ : T.IsPrimOne ξ)
include hξ

/- English proof (translation)
The claim follows from `T.mem_int_iff.1 ξ.2 n`.
-/
theorem norm_coeff_prim_le (n : ℕ) : ‖T.coeff (ξ : Γ) n‖ ≤ 1 :=
  T.mem_int_iff.1 ξ.2 n

/- English proof (translation)
Establish `hc` using `T.convergesAt_of_mem_int ξ.2 hρ0 hρ1`. Use `le_antisymm (gaussNorm_le fun n => ?_) (max_le ?_ ?_)` and prove the remaining obligations. Break down `lt_or_ge n 0 with hn | hn` into its components or cases. Rewrite using `[T.zcoeff_of_neg _ hn, norm_zero, zero_mul]`. Conclude with `le_max_of_le_right hρ0.le`.

Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le hn`. Rewrite using `[T.zcoeff_natCast, zpow_natCast]`. Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Use `le_max_of_le_right ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `hc.le_gaussNorm 0` as an intermediate fact. Rewrite `this` using `[show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, zpow_natCast, pow_zero, mul_one]`. Conclude with `this`. Use `hc.le_gaussNorm 1` as an intermediate fact.

Rewrite `this` using `[show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, hξ.norm_coeff_one, one_mul, Nat.cast_one, zpow_one]`. Conclude with `this`.
-/
theorem gaussNorm_prim {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    gaussNorm (T.zcoeff (ξ : Γ)) ρ = max ‖T.coeff (ξ : Γ) 0‖ ρ := by
  have hc := T.convergesAt_of_mem_int ξ.2 hρ0 hρ1
  refine le_antisymm (gaussNorm_le fun n => ?_) (max_le ?_ ?_)
  · rcases lt_or_ge n 0 with hn | hn
    · rw [T.zcoeff_of_neg _ hn, norm_zero, zero_mul]; exact le_max_of_le_right hρ0.le
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [T.zcoeff_natCast, zpow_natCast]
    rcases k with _ | k
    · simp
    · refine le_max_of_le_right ?_
      calc ‖T.coeff (ξ : Γ) (k + 1)‖ * ρ ^ (k + 1) ≤ 1 * ρ ^ (k + 1) :=
            mul_le_mul_of_nonneg_right (T.norm_coeff_prim_le hξ _) (by positivity)
        _ ≤ ρ := by rw [one_mul]; exact pow_le_of_le_one hρ0.le hρ1.le (by omega)
  · have := hc.le_gaussNorm 0
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, zpow_natCast, pow_zero,
      mul_one] at this
    exact this
  · have := hc.le_gaussNorm 1
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, hξ.norm_coeff_one, one_mul,
      Nat.cast_one, zpow_one] at this
    exact this

/- English proof (translation)
Use `set r := ‖T.coeff (ξ : Γ) 0‖`. Establish `hr0 : 0 < r` using `norm_pos_iff.2 hξ.coeff_zero_ne`. Establish `hr1 : r < 1` using `hξ.norm_coeff_zero_lt`. Establish `hc` using `T.convergesAt_of_mem_int ξ.2 hr0 hr1`. Establish `hne : T.zcoeff (ξ : Γ) ≠ 0`.

Introduce `h`. Use `congrFun h 0` as an intermediate fact. Rewrite `this` using `[show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast]`. Conclude with `hξ.coeff_zero_ne this`. Establish `hg : gaussNorm (T.zcoeff (ξ : Γ)) r = r` using `by rw [T.gaussNorm_prim hξ hr0 hr1, max_self]`.

Establish `hmem0 : (0 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) r`. Simplify using `only [domSet, Set.mem_setOf_eq, hg]`. Rewrite using `[show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast]`. Simplify using `[r]`. Establish `hmem1 : (1 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) r`.

Simplify using `only [domSet, Set.mem_setOf_eq, hg]`. Rewrite using `[show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, hξ.norm_coeff_one, one_mul, Nat.cast_one, zpow_one]`. Establish `hnot : ∀ n : ℤ, n ∈ domSet (T.zcoeff (ξ : Γ)) r → 0 ≤ n ∧ n ≤ 1`. Introduce `n hn`. Simplify using `only [domSet, Set.mem_setOf_eq, hg] at hn`.

Break down `lt_or_ge n 0 with h0 | h0` into its components or cases. Rewrite `hn` using `[T.zcoeff_of_neg _ h0, norm_zero, zero_mul]`. Conclude with `absurd hn hr0.ne`. Take `⟨k, rfl⟩` from `Int.eq_ofNat_of_zero_le h0`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hk`. Use `push_neg at hk`. Rewrite `hn` using `[T.zcoeff_natCast, zpow_natCast]`. Establish `hk2 : 2 ≤ k` using `by omega`. Establish `: ‖T.coeff (ξ : Γ) k‖ * r ^ k ≤ r ^ 2` using `(mul_le_mul_of_nonneg_right (T.norm_coeff_prim_le hξ k) (by positivity)).trans (by rw [one_mul]; exact pow_le_pow_of_le_one hr0.le hr1.le hk2)`.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨le_antisymm (lowIndex_le hr0 hc hne hmem0) (hnot _ (lowIndex_mem hr0 hc hne)).1, le_antisymm (hnot _ (highIndex_mem hr0 hc hne)).2 (le_highIndex hr0 hc hne hmem1)⟩` and prove the remaining obligations.
-/
theorem idx_prim_self :
    lowIndex (T.zcoeff (ξ : Γ)) ‖T.coeff (ξ : Γ) 0‖ = 0 ∧
      highIndex (T.zcoeff (ξ : Γ)) ‖T.coeff (ξ : Γ) 0‖ = 1 := by
  set r := ‖T.coeff (ξ : Γ) 0‖
  have hr0 : 0 < r := norm_pos_iff.2 hξ.coeff_zero_ne
  have hr1 : r < 1 := hξ.norm_coeff_zero_lt
  have hc := T.convergesAt_of_mem_int ξ.2 hr0 hr1
  have hne : T.zcoeff (ξ : Γ) ≠ 0 := by
    intro h; have := congrFun h 0; rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast] at this
    exact hξ.coeff_zero_ne this
  have hg : gaussNorm (T.zcoeff (ξ : Γ)) r = r := by rw [T.gaussNorm_prim hξ hr0 hr1, max_self]
  have hmem0 : (0 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) r := by
    simp only [domSet, Set.mem_setOf_eq, hg]
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, T.zcoeff_natCast]; simp [r]
  have hmem1 : (1 : ℤ) ∈ domSet (T.zcoeff (ξ : Γ)) r := by
    simp only [domSet, Set.mem_setOf_eq, hg]
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, T.zcoeff_natCast, hξ.norm_coeff_one, one_mul,
      Nat.cast_one, zpow_one]
  have hnot : ∀ n : ℤ, n ∈ domSet (T.zcoeff (ξ : Γ)) r → 0 ≤ n ∧ n ≤ 1 := by
    intro n hn
    simp only [domSet, Set.mem_setOf_eq, hg] at hn
    rcases lt_or_ge n 0 with h0 | h0
    · rw [T.zcoeff_of_neg _ h0, norm_zero, zero_mul] at hn; exact absurd hn hr0.ne
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    refine ⟨h0, ?_⟩
    by_contra hk
    push_neg at hk
    rw [T.zcoeff_natCast, zpow_natCast] at hn
    have hk2 : 2 ≤ k := by omega
    have : ‖T.coeff (ξ : Γ) k‖ * r ^ k ≤ r ^ 2 :=
      (mul_le_mul_of_nonneg_right (T.norm_coeff_prim_le hξ k) (by positivity)).trans
        (by rw [one_mul]; exact pow_le_pow_of_le_one hr0.le hr1.le hk2)
    nlinarith
  refine ⟨le_antisymm (lowIndex_le hr0 hc hne hmem0) (hnot _ (lowIndex_mem hr0 hc hne)).1,
    le_antisymm (hnot _ (highIndex_mem hr0 hc hne)).2 (le_highIndex hr0 hc hne hmem1)⟩

end Prim

end TeichLift

end GroundTheory.PAdicHodge
