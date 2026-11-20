import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowsInSpanOfRankNormalFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv.Recentre

variable {k : Type} [Field k] [ValuativeRel k]

/- English proof (translation)
Break down `isEmpty_or_nonempty (Fin r) with hr | hr` into its components or cases. Introduce `l`. Conclude with `isEmptyElim l`. Take `⟨l₀, -, hl₀⟩` from `Finset.exists_max_image Finset.univ (fun l => valuation k (s l)) Finset.univ_nonempty`. Establish `key : s l₀ = w l₀ - ∑ l, s l * E l l₀`.

Use `congrFun hs l₀` as an intermediate fact. Simplify using `only [Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply] at this`. Rewrite using `[← this]`. Simplify using `[Matrix.vecMul, dotProduct]`. Establish `hsum : valuation k (∑ l, s l * E l l₀) ≤ valuation k (s l₀) * δ`.

Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[map_mul]`. Conclude with `mul_le_mul' (hl₀ l (Finset.mem_univ _)) (hE l l₀)`. Establish `hμ : valuation k (s l₀) ≤ max b (valuation k (s l₀) * δ)`.

Combine the equalities or inequalities in the displayed calculation. Establish `hμb : valuation k (s l₀) ≤ b`. Break down `le_max_iff.1 hμ with h | h` into its components or cases. Conclude with `h`. Distinguish the cases in `h0 : valuation k (s l₀) = 0`.

Rewrite using `[h0]`. Conclude with `zero_le'`. It suffices to derive a contradiction. Establish `h2` using `mul_le_mul_left h (valuation k (s l₀))⁻¹`. Rewrite `h2` using `[mul_inv_cancel₀ h0, mul_comm (valuation k (s l₀)) δ, mul_assoc, mul_inv_cancel₀ h0, mul_one]`.

Conclude with `absurd hδ (not_lt.2 h2)`. Conclude with `fun l => (hl₀ l (Finset.mem_univ _)).trans hμb`.
-/
theorem vecMul_bound {r : ℕ} (E : Matrix (Fin r) (Fin r) k) (δ b : ValueGroupWithZero k)
    (hδ : δ < 1) (hE : ∀ l l', valuation k (E l l') ≤ δ) (s w : Fin r → k)
    (hw : ∀ l, valuation k (w l) ≤ b) (hs : s ᵥ* (1 + E) = w) : ∀ l, valuation k (s l) ≤ b := by
  rcases isEmpty_or_nonempty (Fin r) with hr | hr
  · intro l; exact isEmptyElim l
  obtain ⟨l₀, -, hl₀⟩ := Finset.exists_max_image Finset.univ (fun l => valuation k (s l)) Finset.univ_nonempty
  have key : s l₀ = w l₀ - ∑ l, s l * E l l₀ := by
    have := congrFun hs l₀
    simp only [Matrix.vecMul_add, Matrix.vecMul_one, Pi.add_apply] at this
    rw [← this]; simp [Matrix.vecMul, dotProduct]
  have hsum : valuation k (∑ l, s l * E l l₀) ≤ valuation k (s l₀) * δ := by
    apply Valuation.map_sum_le
    intro l _
    rw [map_mul]
    exact mul_le_mul' (hl₀ l (Finset.mem_univ _)) (hE l l₀)
  have hμ : valuation k (s l₀) ≤ max b (valuation k (s l₀) * δ) := by
    calc valuation k (s l₀) = valuation k (w l₀ - ∑ l, s l * E l l₀) := by rw [← key]
      _ ≤ max (valuation k (w l₀)) (valuation k (∑ l, s l * E l l₀)) := Valuation.map_sub _ _ _
      _ ≤ max b (valuation k (s l₀) * δ) := max_le_max (hw l₀) hsum
  have hμb : valuation k (s l₀) ≤ b := by
    rcases le_max_iff.1 hμ with h | h
    · exact h
    · by_cases h0 : valuation k (s l₀) = 0
      · rw [h0]; exact zero_le'
      · exfalso
        have h2 := mul_le_mul_left h (valuation k (s l₀))⁻¹
        rw [mul_inv_cancel₀ h0, mul_comm (valuation k (s l₀)) δ, mul_assoc, mul_inv_cancel₀ h0, mul_one] at h2
        exact absurd hδ (not_lt.2 h2)
  exact fun l => (hl₀ l (Finset.mem_univ _)).trans hμb

end GlobalTheory.RankCoinv.Recentre

/- English proof (translation)
Introduce `k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν1 hνϖ i₀ r c m C H Q hHi₀ hH hcm hHC hQ hHCQ hCi₀`. Establish `hlt : valuation k (ϖ : k) < 1` using `hϖ ▸ uniformizer_lt_one`. Establish `hv0 : valuation k (ϖ : k) ≠ 0` using `by simp`. Establish `vpow : ∀ n : ℕ, valuation k (((ϖ ^ n : kˣ)) : k) = valuation k (ϖ : k) ^ n` using `by intro n; simp`. Establish `vinv : valuation k ((((ϖ ^ c)⁻¹ : kˣ)) : k) = (valuation k (ϖ : k) ^ c)⁻¹` using `by simp`.

Distinguish the cases in `hex : ∃ X₂ ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m), X₂.rank ≤ r`. Use `swap`. Apply `Submodule.mem_sup_left` to reduce the goal to its premises. Use `⟨GlobalTheory.RankCoinv.boxFn_mem_SB _ _ _, fun Y hY => ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.RankCoinv.boxFn`.

Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `hYb`. Conclude with `hex ⟨Y, hYb, Nat.lt_succ_iff.1 hY⟩`. Take `⟨X₂, hX₂, hrk⟩` from `hex`. Use `set u := valuation k (ϖ : k) with hu`.

Establish `hQ' : ∀ j l, valuation k (Q j l) ≤ 1` using `fun j l => (Valuation.mem_integer_iff _ _).1 (hQ j l)`. Establish `hD : ∀ i j, valuation k ((X₂ - C) i j) ≤ u ^ m` using `fun i j => by`. Rewrite using `[Matrix.sub_apply, ← vpow]`. Conclude with `hX₂ i j`. Establish `hHb : ∀ l i, valuation k (H l i) ≤ (u ^ c)⁻¹` using `fun l i => (hH l i).trans_eq vinv`.

Establish `hHD : ∀ l j, valuation k ((H * (X₂ - C)) l j) ≤ (u ^ c)⁻¹ * u ^ m` using `fun l j => by`. Rewrite using `[Matrix.mul_apply]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[map_mul]`.

Conclude with `mul_le_mul' (hHb l i) (hD i j)`. Establish `hE : ∀ l l', valuation k ((H * (X₂ - C) * Q) l l') ≤ (u ^ c)⁻¹ * u ^ m` using `fun l l' => by`. Rewrite using `[Matrix.mul_apply]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hm1 : u ^ m ≤ u ^ (c + 1)` using `pow_le_pow_right_of_le_one' hlt.le hcm`. Establish `hδ : (u ^ c)⁻¹ * u ^ m < 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `hM : H * X₂ * Q = 1 + H * (X₂ - C) * Q`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, hHCQ]`. Normalize the expressions using the abelian group laws. Establish `hunit : IsUnit (H * X₂ * Q)`. Rewrite using `[← Matrix.vecMul_injective_iff_isUnit]`.

Introduce `a a' haa`. Establish `h0 : (a - a') ᵥ* (1 + H * (X₂ - C) * Q) = 0`. Rewrite using `[← hM, Matrix.sub_vecMul]`. Conclude with `sub_eq_zero.2 haa`. Use function extensionality and compare the values at `l`.

Establish `h1` using `GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ 0 hδ hE (a - a') 0 (fun _ => by simp) h0 l`. Establish `h2 : (a - a') l = 0` using `(Valuation.zero_iff _).1 (le_antisymm h1 zero_le')`. Conclude with `sub_eq_zero.1 h2`. Take `⟨s, hs⟩` from `GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X₂ H Q hrk hunit i₀`. Establish `hsw : s ᵥ* (1 + H * (X₂ - C) * Q) = X₂ i₀ ᵥ* Q`.

Rewrite using `[← hM, ← Matrix.vecMul_vecMul, ← hs]`. Establish `hX₂i₀ : ∀ j, valuation k (X₂ i₀ j) ≤ u ^ (c + 1)` using `fun j => by`. Establish `h1 : valuation k (X₂ i₀ j - C i₀ j) ≤ u ^ (c + 1)` using `((hX₂ i₀ j).trans_eq (vpow m)).trans hm1`. Establish `h2 : valuation k (C i₀ j) ≤ u ^ (c + 1)` using `(hCi₀ j).trans_eq (vpow _)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hw : ∀ l, valuation k ((X₂ i₀ ᵥ* Q) l) ≤ u ^ (c + 1)` using `fun l => by`. Simplify using `only [Matrix.vecMul, dotProduct]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsb` using `GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ _ hδ hE s _ hw hsw`. Establish `hsmall : ∀ j, valuation k ((s ᵥ* (H * (X₂ - C))) j) ≤ u ^ m` using `fun j => by`. Simplify using `only [Matrix.vecMul, dotProduct]`. Apply `Valuation.map_sum_le` to reduce the goal to its premises.

Introduce `l _`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ, mul_comm (u ^ c) u, mul_assoc, ← mul_assoc (u ^ c), mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]`. Use `_ ≤ 1 * u ^ m := mul_le_mul_left hlt.le _`.

Use `_ = u ^ m := one_mul _`. Use `set C' := Matrix.updateRow C i₀ 0 with hC'`. Establish `hHC' : H * C' = H * C`. Use extensionality with `l j`. Simplify using `only [Matrix.mul_apply, C', Matrix.updateRow_apply]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[hHi₀]`. Both sides reduce to the same expression.

Establish `hcore` using `GlobalTheory.T.box_function_twisted_coinvariant k A D ϖ hϖ ν β hν1 hνϖ i₀ r c m C' H Q hHi₀ hH hcm (by rw [hHC']; exact hHC) hQ (by rw [hHC']; exact hHCQ) (fun j => by simp [C'])`. Establish `hstep` using `GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C' H s hHi₀ hH (fun l => (hsb l).trans (by rw [vpow]; exact pow_le_pow_right_of_le_one' hlt.le (Nat.le_succ c)))`. Establish `e1 : s ᵥ* (H * C) = X₂ i₀ - s ᵥ* (H * (X₂ - C))`. Rewrite using `[Matrix.mul_sub, Matrix.vecMul_sub, ← hs, sub_sub_cancel]`. Establish `hC'' : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) = Matrix.updateRow C i₀ (X₂ i₀ - s ᵥ* (H * (X₂ - C)))`.

Rewrite using `[hHC', e1]`. Use extensionality with `i j`. Distinguish the cases in `hi : i = i₀`. Substitute `hi` using the available equality. Rewrite using `[Matrix.updateRow_self, Matrix.updateRow_self, hC', Matrix.updateRow_self, zero_add]`.

Rewrite using `[Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, hC', Matrix.updateRow_ne hi]`. Establish `hmem : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m)`. Rewrite using `[hC'']`. Introduce `i j`. Distinguish the cases in `hi : i = i₀`.

Substitute `hi` using the available equality. Rewrite using `[Matrix.updateRow_self]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Rewrite using `[Pi.sub_apply]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ max (valuation k (X₂ i j - C i j)) (valuation k ((s ᵥ* (H * (X₂ - C))) j)) := Valuation.map_sub _ _ _`. Use `_ ≤ u ^ m := max_le ((hX₂ i j).trans_eq (vpow m)) (hsmall j)`. Use `_ = _ := (vpow m).symm`. Rewrite using `[Matrix.updateRow_ne hi]`.

Simplify using the standard rewrite rules. Rewrite `hstep` using `[GlobalTheory.RankCoinv.boxFn_eq_of_mem hmem]`. Rewrite using `[← sub_add_cancel (GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m)) (GlobalTheory.RankCoinv.boxFn ϖ C' (fun _ => m))]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_right hstep) hcore`.
-/
theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_sup_twistSpan_of_small_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, valuation k (C i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k)) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν1 hνϖ i₀ r c m C H Q hHi₀ hH hcm hHC hQ hHCQ hCi₀
  classical
  have hlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hv0 : valuation k (ϖ : k) ≠ 0 := by simp
  have vpow : ∀ n : ℕ, valuation k (((ϖ ^ n : kˣ)) : k) = valuation k (ϖ : k) ^ n := by intro n; simp
  have vinv : valuation k ((((ϖ ^ c)⁻¹ : kˣ)) : k) = (valuation k (ϖ : k) ^ c)⁻¹ := by simp
  by_cases hex : ∃ X₂ ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m), X₂.rank ≤ r
  swap
  · apply Submodule.mem_sup_left
    refine ⟨GlobalTheory.RankCoinv.boxFn_mem_SB _ _ _, fun Y hY => ?_⟩
    unfold GlobalTheory.RankCoinv.boxFn
    apply Set.indicator_of_notMem
    intro hYb; exact hex ⟨Y, hYb, Nat.lt_succ_iff.1 hY⟩
  obtain ⟨X₂, hX₂, hrk⟩ := hex
  set u := valuation k (ϖ : k) with hu
  have hQ' : ∀ j l, valuation k (Q j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ j l)
  have hD : ∀ i j, valuation k ((X₂ - C) i j) ≤ u ^ m := fun i j => by
    rw [Matrix.sub_apply, ← vpow]; exact hX₂ i j
  have hHb : ∀ l i, valuation k (H l i) ≤ (u ^ c)⁻¹ := fun l i => (hH l i).trans_eq vinv
  have hHD : ∀ l j, valuation k ((H * (X₂ - C)) l j) ≤ (u ^ c)⁻¹ * u ^ m := fun l j => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro i _; rw [map_mul]
    exact mul_le_mul' (hHb l i) (hD i j)
  have hE : ∀ l l', valuation k ((H * (X₂ - C) * Q) l l') ≤ (u ^ c)⁻¹ * u ^ m := fun l l' => by
    rw [Matrix.mul_apply]; apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ (u ^ c)⁻¹ * u ^ m * 1 := mul_le_mul' (hHD l j) (hQ' j l')
      _ = _ := mul_one _
  have hm1 : u ^ m ≤ u ^ (c + 1) := pow_le_pow_right_of_le_one' hlt.le hcm
  have hδ : (u ^ c)⁻¹ * u ^ m < 1 := by
    calc (u ^ c)⁻¹ * u ^ m ≤ (u ^ c)⁻¹ * u ^ (c + 1) := mul_le_mul' le_rfl hm1
      _ = u := by rw [pow_succ, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ < 1 := hlt
  have hM : H * X₂ * Q = 1 + H * (X₂ - C) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hHCQ]; abel
  have hunit : IsUnit (H * X₂ * Q) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro a a' haa
    have h0 : (a - a') ᵥ* (1 + H * (X₂ - C) * Q) = 0 := by
      rw [← hM, Matrix.sub_vecMul]; exact sub_eq_zero.2 haa
    funext l
    have h1 := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ 0 hδ hE (a - a') 0 (fun _ => by simp) h0 l
    have h2 : (a - a') l = 0 := (Valuation.zero_iff _).1 (le_antisymm h1 zero_le')
    exact sub_eq_zero.1 h2
  obtain ⟨s, hs⟩ := GlobalTheory.T.rows_in_span_of_rank_normal_form k A D r X₂ H Q hrk hunit i₀
  have hsw : s ᵥ* (1 + H * (X₂ - C) * Q) = X₂ i₀ ᵥ* Q := by
    rw [← hM, ← Matrix.vecMul_vecMul, ← hs]
  have hX₂i₀ : ∀ j, valuation k (X₂ i₀ j) ≤ u ^ (c + 1) := fun j => by
    have h1 : valuation k (X₂ i₀ j - C i₀ j) ≤ u ^ (c + 1) := ((hX₂ i₀ j).trans_eq (vpow m)).trans hm1
    have h2 : valuation k (C i₀ j) ≤ u ^ (c + 1) := (hCi₀ j).trans_eq (vpow _)
    calc valuation k (X₂ i₀ j) = valuation k ((X₂ i₀ j - C i₀ j) + C i₀ j) := by rw [sub_add_cancel]
      _ ≤ _ := Valuation.map_add_le _ h1 h2
  have hw : ∀ l, valuation k ((X₂ i₀ ᵥ* Q) l) ≤ u ^ (c + 1) := fun l => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro j _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * 1 := mul_le_mul' (hX₂i₀ j) (hQ' j l)
      _ = _ := mul_one _
  have hsb := GlobalTheory.RankCoinv.Recentre.vecMul_bound _ _ _ hδ hE s _ hw hsw
  have hsmall : ∀ j, valuation k ((s ᵥ* (H * (X₂ - C))) j) ≤ u ^ m := fun j => by
    simp only [Matrix.vecMul, dotProduct]
    apply Valuation.map_sum_le; intro l _; rw [map_mul]
    calc _ ≤ u ^ (c + 1) * ((u ^ c)⁻¹ * u ^ m) := mul_le_mul' (hsb l) (hHD l j)
      _ = u * u ^ m := by
        rw [pow_succ, mul_comm (u ^ c) u, mul_assoc, ← mul_assoc (u ^ c), mul_inv_cancel₀ (pow_ne_zero _ hv0), one_mul]
      _ ≤ 1 * u ^ m := mul_le_mul_left hlt.le _
      _ = u ^ m := one_mul _
  set C' := Matrix.updateRow C i₀ 0 with hC'
  have hHC' : H * C' = H * C := by
    ext l j
    simp only [Matrix.mul_apply, C', Matrix.updateRow_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · subst h; simp [hHi₀]
    · rfl
  have hcore := GlobalTheory.T.box_function_twisted_coinvariant k A D ϖ hϖ ν β hν1 hνϖ i₀ r c m C' H Q hHi₀ hH hcm
    (by rw [hHC']; exact hHC) hQ (by rw [hHC']; exact hHCQ) (fun j => by simp [C'])
  have hstep := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C' H s hHi₀ hH
    (fun l => (hsb l).trans (by rw [vpow]; exact pow_le_pow_right_of_le_one' hlt.le (Nat.le_succ c)))
  have e1 : s ᵥ* (H * C) = X₂ i₀ - s ᵥ* (H * (X₂ - C)) := by
    rw [Matrix.mul_sub, Matrix.vecMul_sub, ← hs, sub_sub_cancel]
  have hC'' : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) =
      Matrix.updateRow C i₀ (X₂ i₀ - s ᵥ* (H * (X₂ - C))) := by
    rw [hHC', e1]
    ext i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self, Matrix.updateRow_self, hC', Matrix.updateRow_self, zero_add]
    · rw [Matrix.updateRow_ne hi, Matrix.updateRow_ne hi, hC', Matrix.updateRow_ne hi]
  have hmem : Matrix.updateRow C' i₀ (C' i₀ + s ᵥ* (H * C')) ∈ GlobalTheory.RankCoinv.box ϖ C (fun _ => m) := by
    rw [hC'']
    intro i j
    by_cases hi : i = i₀
    · subst hi
      rw [Matrix.updateRow_self]
      calc valuation k ((X₂ i - s ᵥ* (H * (X₂ - C))) j - C i j)
          = valuation k ((X₂ i j - C i j) - (s ᵥ* (H * (X₂ - C))) j) := by
            congr 1; rw [Pi.sub_apply]; ring
        _ ≤ max (valuation k (X₂ i j - C i j)) (valuation k ((s ᵥ* (H * (X₂ - C))) j)) :=
            Valuation.map_sub _ _ _
        _ ≤ u ^ m := max_le ((hX₂ i j).trans_eq (vpow m)) (hsmall j)
        _ = _ := (vpow m).symm
    · rw [Matrix.updateRow_ne hi]; simp
  rw [GlobalTheory.RankCoinv.boxFn_eq_of_mem hmem] at hstep
  rw [← sub_add_cancel (GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m)) (GlobalTheory.RankCoinv.boxFn ϖ C' (fun _ => m))]
  exact Submodule.add_mem _ (Submodule.mem_sup_right hstep) hcore
