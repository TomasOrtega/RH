import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.HarishChandraDescent.Descent

noncomputable section

open Finset
open scoped InnerProductSpace

namespace PositivityTheory.RgHe3

open ReciprocityTheory.ChartRestriction.DS

namespace AscentPotential

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
theorem pot_root {a b : Fin n} (hab : a ≠ b) (ω : Fin n → ℝ) :
    pot (fun c => ω c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) = pot ω + (a : ℕ) - (b : ℕ) := by
  unfold pot
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Replace the relevant objects with their definitions.

Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
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
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dot_root_nonneg {μ : Fin n → ℝ} (hμ : Antitone μ) {a b : Fin n} (hab : a < b) :
    0 ≤ dot (fun c => (if c = a then (1 : ℝ) else 0) - (if c = b then 1 else 0)) μ := by
  unfold dot
  simp only [sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith [hμ hab.le]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails.

Supply the required witnesses or components. Extract witnesses or component facts from the available result. It suffices to derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact.

Establish an intermediate fact. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact.

Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion. A detailed English derivation is pending.
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
