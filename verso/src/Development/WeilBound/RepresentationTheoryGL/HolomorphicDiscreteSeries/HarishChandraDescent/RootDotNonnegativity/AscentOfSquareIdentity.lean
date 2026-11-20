import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace AscentPotential

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

/- English proof (translation)
Establish `h` using `(hS n ε M E hE hU w).1`. Rewrite `h` using `[hc, inner_smul_left, inner_self_eq_norm_sq_to_K]`. Simplify using `only [Complex.conj_ofReal] at h`. Establish `h1 : (((κ : ℂ) * ((‖w‖ : ℂ) ^ 2))).re = κ * ‖w‖ ^ 2`. Rewrite using `[← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]`.

Establish `h2 : ∑ a, ‖E a a w‖ ^ 2 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b w‖ ^ 2`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun b => ‖E a b w‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_filter.2 ⟨Finset.mem_univ a, rfl⟩)`. Establish `h3 : ∑ a, ‖E a a w‖ ^ 2 = nsq ω * ‖w‖ ^ 2`. Unfold `nsq dot`.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hwt a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hw : 0 < ‖w‖ ^ 2` using `by positivity`.

Establish `: nsq ω * ‖w‖ ^ 2 ≤ κ * ‖w‖ ^ 2`. Rewrite using `[← h3, ← h1]`. Conclude with `h2.trans (le_of_eq h.symm)`. Conclude with `le_of_mul_le_mul_right this hw`.
-/
theorem nsq_le_of_eig (hS : SqId) {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (hU : IsInfUnitary ε E) {ω : Fin n → ℝ} {κ : ℝ} {w : M} (hw0 : w ≠ 0) (hwt : IsWt E ω w)
    (hc : casimirK ε E w = (κ : ℂ) • w) : nsq ω ≤ κ := by
  have h := (hS n ε M E hE hU w).1
  rw [hc, inner_smul_left, inner_self_eq_norm_sq_to_K] at h
  simp only [Complex.conj_ofReal] at h
  have h1 : (((κ : ℂ) * ((‖w‖ : ℂ) ^ 2))).re = κ * ‖w‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h2 : ∑ a, ‖E a a w‖ ^ 2 ≤ ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), ‖E a b w‖ ^ 2 := by
    refine Finset.sum_le_sum fun a _ => ?_
    exact Finset.single_le_sum (f := fun b => ‖E a b w‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_filter.2 ⟨Finset.mem_univ a, rfl⟩)
  have h3 : ∑ a, ‖E a a w‖ ^ 2 = nsq ω * ‖w‖ ^ 2 := by
    unfold nsq dot
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hwt a, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hw : 0 < ‖w‖ ^ 2 := by positivity
  have : nsq ω * ‖w‖ ^ 2 ≤ κ * ‖w‖ ^ 2 := by
    rw [← h3, ← h1]; exact h2.trans (le_of_eq h.symm)
  exact le_of_mul_le_mul_right this hw

def pot (ω : Fin n → ℝ) : ℝ := ∑ c : Fin n, ((c : ℕ) : ℝ) * ω c

/- English proof (translation)
Unfold `pot`. Simplify using `only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem pot_root {a b : Fin n} (hab : a ≠ b) (ω : Fin n → ℝ) :
    pot (fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) = pot ω + (a : ℕ) - (b : ℕ) := by
  unfold pot
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Unfold `pot`. Establish `hc : ∀ c : Fin n, -(((c : ℕ) : ℝ) * (1 + |κ|)) ≤ ((c : ℕ) : ℝ) * ω c`. Introduce `c`. Establish `h1 : ω c ^ 2 ≤ nsq ω`. Unfold `nsq dot`.

Conclude with `Finset.single_le_sum (f := fun a => ω a * ω a) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ c) |>.trans_eq' (by ring)`. Establish `h2 : |ω c| ≤ 1 + |κ|`. Establish `: ω c ^ 2 ≤ |κ|` using `h1.trans (h.trans (le_abs_self κ))`. Use polynomial arithmetic with `[abs_nonneg (ω c), sq_abs (ω c)]`. Establish `h3 : (0 : ℝ) ≤ ((c : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Use `neg_abs_le (ω c)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h4 : ∑ c : Fin n, ((c : ℕ) : ℝ) ≤ (n : ℝ) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Establish `: 0 ≤ 1 + |κ|` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = ∑ c : Fin n, -(((c : ℕ) : ℝ) * (1 + |κ|)) := by rw [Finset.sum_mul, ← Finset.sum_neg_distrib]`. Use `_ ≤ _ := Finset.sum_le_sum fun c _ => hc c`.
-/
theorem pot_lower {ω : Fin n → ℝ} {κ : ℝ} (h : nsq ω ≤ κ) : -((n : ℝ) ^ 2 * (1 + |κ|)) ≤ pot ω := by
  unfold pot
  have hc : ∀ c : Fin n, -(((c : ℕ) : ℝ) * (1 + |κ|)) ≤ ((c : ℕ) : ℝ) * ω c := by
    intro c
    have h1 : ω c ^ 2 ≤ nsq ω := by
      unfold nsq dot
      exact Finset.single_le_sum (f := fun a => ω a * ω a) (fun _ _ => mul_self_nonneg _) (Finset.mem_univ c) |>.trans_eq' (by ring)
    have h2 : |ω c| ≤ 1 + |κ| := by
      have : ω c ^ 2 ≤ |κ| := h1.trans (h.trans (le_abs_self κ))
      nlinarith [abs_nonneg (ω c), sq_abs (ω c)]
    have h3 : (0 : ℝ) ≤ ((c : ℕ) : ℝ) := Nat.cast_nonneg _
    have := neg_abs_le (ω c)
    nlinarith
  have h4 : ∑ c : Fin n, ((c : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc ∑ c : Fin n, ((c : ℕ) : ℝ) ≤ ∑ _c : Fin n, (n : ℝ) :=
          Finset.sum_le_sum fun c _ => by exact_mod_cast c.2.le
      _ = (n : ℝ) ^ 2 := by simp [sq]
  calc -((n : ℝ) ^ 2 * (1 + |κ|)) ≤ -((∑ c : Fin n, ((c : ℕ) : ℝ)) * (1 + |κ|)) := by
        have : 0 ≤ 1 + |κ| := by positivity
        nlinarith
    _ = ∑ c : Fin n, -(((c : ℕ) : ℝ) * (1 + |κ|)) := by rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    _ ≤ _ := Finset.sum_le_sum fun c _ => hc c

/- English proof (translation)
Unfold `dot`. Simplify using `only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Combine the linear relations using `[hμ hab.le]`.
-/
theorem dot_root_nonneg {μ : Fin n → ℝ} (hμ : Antitone μ) {a b : Fin n} (hab : a < b) :
    0 ≤ dot (fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ := by
  unfold dot
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith [hμ hab.le]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `w ω hwN hwF hw0 hwt hc hd hm`. Distinguish the cases in `hhw : ∀ a b, a < b → ε a = ε b → E a b w = 0`.

Conclude with `⟨w, hwN, ω, hwF, hw0, ⟨hwt, hhw⟩, hc, hd⟩`. Use `push_neg at hhw`. Take `⟨a, b, hab, hε, hne⟩` from `hhw`. It suffices to derive a contradiction. Use `set ω' : Fin n → ℝ := fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)`.

Establish `hwt' : IsWt E ω' (E a b w)` using `fun c => kUnit_weight_shift hE hwt hab.ne c`. Establish `hc' : casimirK ε E (E a b w) = (κ : ℂ) • E a b w`. Use `LinearMap.congr_fun (casimirK_comm ε hE a b hε) w` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hc, map_smul]`.

Establish `h1` using `pot_lower (nsq_le_of_eig hS hE hU hne hwt' hc')`. Establish `h2` using `pot_root hab.ne ω`. Establish `h3 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ)` using `by exact_mod_cast hab`. Move the coercions through the operations in `at hm`. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `succ m ih`. Introduce `w ω hwN hwF hw0 hwt hc hd hm`. Distinguish the cases in `hhw : ∀ a b, a < b → ε a = ε b → E a b w = 0`. Conclude with `⟨w, hwN, ω, hwF, hw0, ⟨hwt, hhw⟩, hc, hd⟩`. Use `push_neg at hhw`.

Take `⟨a, b, hab, hε, hne⟩` from `hhw`. Use `set ω' : Fin n → ℝ := fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) with hω'`. Establish `hwt' : IsWt E ω' (E a b w)` using `fun c => kUnit_weight_shift hE hwt hab.ne c`. Establish `hc' : casimirK ε E (E a b w) = (κ : ℂ) • E a b w`. Use `LinearMap.congr_fun (casimirK_comm ε hE a b hε) w` as an intermediate fact.

Simplify using `only [Module.End.mul_apply] at this`. Rewrite using `[this, hc, map_smul]`. Use `ih (E a b w) ω' (hN a b w hwN) (hF a b hε w hwF) hne hwt' hc' ?_ ?_` and prove the remaining obligations. Establish `e : ω' - ν = (ω - ν) + fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)`. Use function extensionality and compare the values at `c`.

Simplify using `only [hω', Pi.sub_apply, Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `: dot ((ω - ν) + fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ = dot (ω - ν) μ + dot (fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ`. Unfold `dot`.

Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Rewrite using `[this]`. Combine the linear relations using `[dot_root_nonneg hμ hab]`. Establish `h2` using `pot_root hab.ne ω`. Establish `h3 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ)` using `by exact_mod_cast hab`.

Move the coercions through the operations in `at hm`. Use `show pot ω' + _ ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main (hS : SqId) {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (hU : IsInfUnitary ε E) (N F : Submodule ℂ M) (hN : Stab E N) (hF : IsKStableSub ε E F) (μ ν : Fin n → ℝ) (κ : ℝ)
    (hμ : Antitone μ) :
    ∀ m : ℕ, ∀ (w : M) (ω : Fin n → ℝ), w ∈ N → w ∈ F → w ≠ 0 → IsWt E ω w → casimirK ε E w = (κ : ℂ) • w →
      0 ≤ dot (ω - ν) μ → pot ω + (n : ℝ) ^ 2 * (1 + |κ|) ≤ m →
      ∃ y' ∈ N, ∃ L : Fin n → ℝ, y' ∈ F ∧ y' ≠ 0 ∧ IsKHWVec ε E L y' ∧ casimirK ε E y' = (κ : ℂ) • y' ∧
        0 ≤ dot (L - ν) μ := by
  intro m
  induction m with
  | zero =>
    intro w ω hwN hwF hw0 hwt hc hd hm
    by_cases hhw : ∀ a b, a < b → ε a = ε b → E a b w = 0
    · exact ⟨w, hwN, ω, hwF, hw0, ⟨hwt, hhw⟩, hc, hd⟩
    · push_neg at hhw
      obtain ⟨a, b, hab, hε, hne⟩ := hhw
      exfalso
      set ω' : Fin n → ℝ := fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)
      have hwt' : IsWt E ω' (E a b w) := fun c => kUnit_weight_shift hE hwt hab.ne c
      have hc' : casimirK ε E (E a b w) = (κ : ℂ) • E a b w := by
        have := LinearMap.congr_fun (casimirK_comm ε hE a b hε) w
        simp only [Module.End.mul_apply] at this
        rw [this, hc, map_smul]
      have h1 := pot_lower (nsq_le_of_eig hS hE hU hne hwt' hc')
      have h2 := pot_root hab.ne ω
      have h3 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast hab
      push_cast at hm
      linarith
  | succ m ih =>
    intro w ω hwN hwF hw0 hwt hc hd hm
    by_cases hhw : ∀ a b, a < b → ε a = ε b → E a b w = 0
    · exact ⟨w, hwN, ω, hwF, hw0, ⟨hwt, hhw⟩, hc, hd⟩
    · push_neg at hhw
      obtain ⟨a, b, hab, hε, hne⟩ := hhw
      set ω' : Fin n → ℝ := fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0) with hω'
      have hwt' : IsWt E ω' (E a b w) := fun c => kUnit_weight_shift hE hwt hab.ne c
      have hc' : casimirK ε E (E a b w) = (κ : ℂ) • E a b w := by
        have := LinearMap.congr_fun (casimirK_comm ε hE a b hε) w
        simp only [Module.End.mul_apply] at this
        rw [this, hc, map_smul]
      refine ih (E a b w) ω' (hN a b w hwN) (hF a b hε w hwF) hne hwt' hc' ?_ ?_
      · have e : ω' - ν = (ω - ν) + fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0) := by
          funext c; simp only [hω', Pi.sub_apply, Pi.add_apply]; ring
        rw [e]
        have : dot ((ω - ν) + fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ =
            dot (ω - ν) μ + dot (fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ := by
          unfold dot; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
        rw [this]
        linarith [dot_root_nonneg hμ hab]
      · have h2 := pot_root hab.ne ω
        have h3 : ((a : ℕ) : ℝ) + 1 ≤ (b : ℕ) := by exact_mod_cast hab
        push_cast at hm
        show pot ω' + _ ≤ _
        linarith

end AscentPotential

open AscentPotential in
/- English proof (translation)
Introduce `hS n ε M _ _ E hE hU N hN μ ν κ S y hyN hy hμ hS1 hS2`. Take `⟨F, hFd, hFk, hyF⟩` from `hy.fin`. Take `⟨y', hy'N, L, hy'F, hy'0, hhw, hc, hd⟩` from `main hS hE hU N F hN hFk μ ν κ hμ ⌈pot ν + (n : ℝ) ^ 2 * (1 + |κ|)⌉₊ y ν hyN hyF hy.ne hy.wt hy.cas (by simp [dot]) (Nat.le_ceil _)`. Use `⟨y', hy'N, L, hy'0, ⟨F, hFd, hFk, hy'F⟩, hhw, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `casimirK_khwVec ε hE hhw`.

Rewrite `h1` using `[hc]`. Establish `h2 : ((κ : ℂ) - ((nsq (L + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ)) • y' = 0`. Rewrite using `[sub_smul, h1, sub_self]`. Break down `smul_eq_zero.1 h2 with h | h` into its components or cases. Use `sub_eq_zero.1 h` as an intermediate fact.

Unfold `casValK`. Conclude with `this.symm` after adjusting the coercions. Conclude with `absurd h hy'0`. Establish `hL` using `nsq_le_of_eig hS hE hU hy'0 hhw.1 hc`. Establish `e : nsq (L - μ) = nsq (ν - μ) + nsq L - nsq ν - 2 * dot (L - ν) μ`.

Unfold `nsq dot`. Simplify using `only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ascent_of_square_identity : SqId → Ascent := by
  intro hS n ε M _ _ E hE hU N hN μ ν κ S y hyN hy hμ hS1 hS2
  obtain ⟨F, hFd, hFk, hyF⟩ := hy.fin
  obtain ⟨y', hy'N, L, hy'F, hy'0, hhw, hc, hd⟩ :=
    main hS hE hU N F hN hFk μ ν κ hμ ⌈pot ν + (n : ℝ) ^ 2 * (1 + |κ|)⌉₊ y ν hyN hyF hy.ne hy.wt hy.cas
      (by simp [dot]) (Nat.le_ceil _)
  refine ⟨y', hy'N, L, hy'0, ⟨F, hFd, hFk, hy'F⟩, hhw, ?_, ?_⟩
  · have h1 := casimirK_khwVec ε hE hhw
    rw [hc] at h1
    have h2 : ((κ : ℂ) - ((nsq (L + rhoC ε) - nsq (rhoC ε) : ℝ) : ℂ)) • y' = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · have := sub_eq_zero.1 h
      unfold casValK
      exact_mod_cast this.symm
    · exact absurd h hy'0
  · have hL := nsq_le_of_eig hS hE hU hy'0 hhw.1 hc
    have e : nsq (L - μ) = nsq (ν - μ) + nsq L - nsq ν - 2 * dot (L - ν) μ := by
      unfold nsq dot
      simp only [Pi.sub_apply, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [e]
    linarith

end PositivityTheory.RgHe3
