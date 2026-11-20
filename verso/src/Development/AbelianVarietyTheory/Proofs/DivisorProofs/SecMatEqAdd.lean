import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableToGLEntry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroupStatement
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

variable {n : ℕ}

open scoped Matrix

/- English proof (translation)
Simplify using `[secMat, hi]`.
-/
theorem secMat_of_ne (ρ j : Fin n) (v : Fin n → ℂ) {i : Fin n} (hi : i ≠ ρ) (l : Fin n) :
    secMat ρ j v i l = if l = Equiv.swap j ρ i then 1 else 0 := by
  simp [secMat, hi]

/- English proof (translation)
Simplify using `[secMat]`.
-/
theorem secMat_self (ρ j : Fin n) (v : Fin n → ℂ) (l : Fin n) :
    secMat ρ j v ρ l = if l ≤ ρ then v l else 0 := by
  simp [secMat]

/- English proof (translation)
The claim follows from `Equiv.swap_apply_of_ne_of_ne (lt_of_le_of_lt hj hi).ne' hi.ne'`.
-/
theorem swap_of_lt' {ρ j i : Fin n} (hj : j ≤ ρ) (hi : ρ < i) : Equiv.swap j ρ i = i :=
  Equiv.swap_apply_of_ne_of_ne (lt_of_le_of_lt hj hi).ne' hi.ne'

/- English proof (translation)
Rewrite using `[← Matrix.vecMul_injective_iff_isUnit]`. Establish `key : ∀ e : Fin n → ℂ, e ᵥ* Matrix.of (secMat ρ j v) = 0 → e = 0`. Introduce `e he`. Establish `hcol : ∀ l, ∑ i, e i * secMat ρ j v i l = 0` using `fun l => by`. Use `congrFun he l` as an intermediate fact.

Simplify `this` using `[Matrix.vecMul, dotProduct]`. Establish `hρ : e ρ = 0`. Establish `h` using `hcol j`. Rewrite `h` using `[Finset.sum_eq_single ρ]`. Rewrite `h` using `[secMat_self, if_pos hj]`.

Conclude with `(mul_eq_zero.1 h).resolve_right hv`. Introduce `i _ hi`. Rewrite using `[secMat_of_ne _ _ _ hi, if_neg, mul_zero]`. Introduce `h'`. Apply `hi` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = ρ`. Rewrite using `[hi]`.

Conclude with `hρ`. Establish `h` using `hcol (Equiv.swap j ρ i)`. Rewrite `h` using `[Finset.sum_eq_single i]`. Rewrite `h` using `[secMat_of_ne _ _ _ hi, if_pos rfl, mul_one]`. Conclude with `h`.

Introduce `i' _ hi'`. Distinguish the cases in `h'' : i' = ρ`. Rewrite using `[h'', hρ, zero_mul]`. Rewrite using `[secMat_of_ne _ _ _ h'', if_neg, mul_zero]`. Introduce `h3`.

Conclude with `hi' ((Equiv.swap j ρ).injective h3).symm`. Simplify using the standard rewrite rules. Introduce `c d hcd`. Use `key (c - d) (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `(c - d) ᵥ* _ = 0`.

Rewrite using `[Matrix.sub_vecMul]`. Conclude with `sub_eq_zero.2 hcd)`. Conclude with `sub_eq_zero.1 this`.
-/
theorem isUnit_secMat (ρ j : Fin n) (hj : j ≤ ρ) (v : Fin n → ℂ) (hv : v j ≠ 0) :
    IsUnit (Matrix.of (secMat ρ j v)) := by
  rw [← Matrix.vecMul_injective_iff_isUnit]
  have key : ∀ e : Fin n → ℂ, e ᵥ* Matrix.of (secMat ρ j v) = 0 → e = 0 := by
    intro e he
    have hcol : ∀ l, ∑ i, e i * secMat ρ j v i l = 0 := fun l => by
      have := congrFun he l
      simpa [Matrix.vecMul, dotProduct] using this
    have hρ : e ρ = 0 := by
      have h := hcol j
      rw [Finset.sum_eq_single ρ] at h
      · rw [secMat_self, if_pos hj] at h
        exact (mul_eq_zero.1 h).resolve_right hv
      · intro i _ hi
        rw [secMat_of_ne _ _ _ hi, if_neg, mul_zero]
        intro h'
        apply hi
        calc i = Equiv.swap j ρ (Equiv.swap j ρ i) := (Equiv.swap_apply_self _ _ _).symm
          _ = Equiv.swap j ρ j := by rw [← h']
          _ = ρ := Equiv.swap_apply_left _ _
      · simp
    funext i
    by_cases hi : i = ρ
    · rw [hi]; exact hρ
    · have h := hcol (Equiv.swap j ρ i)
      rw [Finset.sum_eq_single i] at h
      · rw [secMat_of_ne _ _ _ hi, if_pos rfl, mul_one] at h
        exact h
      · intro i' _ hi'
        by_cases h'' : i' = ρ
        · rw [h'', hρ, zero_mul]
        · rw [secMat_of_ne _ _ _ h'', if_neg, mul_zero]
          intro h3
          exact hi' ((Equiv.swap j ρ).injective h3).symm
      · simp
  intro c d hcd
  have := key (c - d) (by
    change (c - d) ᵥ* _ = 0
    rw [Matrix.sub_vecMul]
    exact sub_eq_zero.2 hcd)
  exact sub_eq_zero.1 this

def secLin (ρ : Fin n) : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i l => if i = ρ ∧ l ≤ ρ then v l else 0
      map_add' := fun v w => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h]
      map_smul' := fun c v => by
        funext i l
        by_cases h : i = ρ ∧ l ≤ ρ <;> simp [h] }

/- English proof (translation)
Use function extensionality and compare the values at `i l`. Distinguish the cases in `hi : i = ρ`. Substitute `hi` using the available equality. Apply the tactic sequence `by_cases hl : l ≤ i <;> simp [secMat, secLin, hl]`. Simplify using `[secMat, secLin, hi]`.
-/
theorem secMat_eq_add (ρ j : Fin n) (v : Fin n → ℂ) : secMat ρ j v = secMat ρ j 0 + secLin ρ v := by
  funext i l
  by_cases hi : i = ρ
  · subst hi
    by_cases hl : l ≤ i <;> simp [secMat, secLin, hl]
  · simp [secMat, secLin, hi]

/- English proof (translation)
Introduce `n ρ j hj`. Use `⟨fun v hv => isUnit_secMat ρ j hj v hv, ?_, secLin ρ, secMat_eq_add ρ j⟩` and prove the remaining obligations. Introduce `g hg hgj`. Use `set v := rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) with hv`. Establish `hS` using `isUnit_secMat ρ j hj v hgj`.

Use `set S := toGL (Matrix.of (secMat ρ j v)) with hSdef`. Establish `hSv : (S : Matrix (Fin n) (Fin n) ℂ) = Matrix.of (secMat ρ j v)` using `val_toGL hS`. Establish `hSlev : S ∈ levSet n (ρ + 1)`. Introduce `i hi`. Establish `hiρ : ρ < i` using `by rw [Fin.lt_def]; omega`.

Use `⟨fun l hl => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_neg hl.ne]`. Rewrite using `[hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_pos rfl]`. Establish `hp : g * S⁻¹ ∈ levSet n (ρ + 1)` using `(GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).1 g hg _ ((GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 S hSlev)`. Use `set P := ((g * S⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hPdef`.

Establish `hPS : P * Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ)`. Rewrite using `[← hSv, hPdef, ← Units.val_mul, inv_mul_cancel_right]`. Set `w : Fin n → ℂ` to `fun i => if i = ρ then 1 else if i < ρ then 0 else (g : Matrix (Fin n) (Fin n) ℂ) ρ i`. Establish `hw : w ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ`. Use function extensionality and compare the values at `l`.

Simplify using `only [Matrix.vecMul, dotProduct, Matrix.of_apply]`. Distinguish the cases in `hl : l ≤ ρ`. Rewrite using `[Finset.sum_eq_single ρ]`. Simplify using `[w, secMat_self, hl, hv, rowCut]`. Introduce `i _ hi`.

Break down `lt_or_gt_of_ne hi with h | h` into its components or cases. Simplify using `[w, hi, h]`. Rewrite using `[secMat_of_ne _ _ _ hi, swap_of_lt' hj h, if_neg (lt_of_le_of_lt hl h).ne, mul_zero]`. Simplify using the standard rewrite rules. Establish `hlρ : ρ < l` using `lt_of_not_ge hl`.

Rewrite using `[Finset.sum_eq_single l]`. Simplify using `[w, secMat_of_ne _ _ _ hlρ.ne', swap_of_lt' hj hlρ, hlρ.ne', not_lt.2 hlρ.le]`. Introduce `i _ hi`. Distinguish the cases in `h1 : i = ρ`. Rewrite using `[h1, secMat_self, if_neg hl, mul_zero]`.

Break down `lt_or_gt_of_ne h1 with h | h` into its components or cases. Simplify using `[w, h1, h]`. Rewrite using `[secMat_of_ne _ _ _ h1, swap_of_lt' hj h, if_neg (Ne.symm hi), mul_zero]`. Simplify using the standard rewrite rules. Establish `hPw : P ρ ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ`.

Rewrite using `[← hPS]`. Use function extensionality and compare the values at `l`. Simplify using `[Matrix.vecMul, dotProduct, Matrix.mul_apply]`. Establish `hrow : P ρ = w` using `(Matrix.vecMul_injective_iff_isUnit.2 hS) (hPw.trans hw.symm)`. Introduce `i hi`.

Distinguish the cases in `hiρ : (i : ℕ) = ρ`. Establish `hie : i = ρ` using `Fin.ext hiρ`. Substitute `hie` using the available equality. Use `⟨fun l hl => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `P i l = 0`.

Rewrite using `[hrow]`. Simplify using `[w, hl, hl.ne]`. Express the relevant statement in the definitionally equal form `P i i = 1`. Rewrite using `[hrow]`. Simplify using `[w]`.

Conclude with `hp i (by omega)`.
-/
theorem secMat_main : ∀ (n : ℕ) (ρ j : Fin n), j ≤ ρ → (∀ v : Fin n → ℂ, v j ≠ 0 → IsUnit (Matrix.of (secMat ρ j v))) ∧ (∀ g ∈ levSet n (ρ + 1), rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 → g * (toGL (Matrix.of (secMat ρ j (rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)))))⁻¹ ∈ levSet n ρ) ∧ ∃ L : (Fin n → ℂ) →L[ℝ] (Fin n → Fin n → ℂ), ∀ v, secMat ρ j v = secMat ρ j 0 + L v := by
  intro n ρ j hj
  refine ⟨fun v hv => isUnit_secMat ρ j hj v hv, ?_, secLin ρ, secMat_eq_add ρ j⟩
  intro g hg hgj
  set v := rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) with hv
  have hS := isUnit_secMat ρ j hj v hgj
  set S := toGL (Matrix.of (secMat ρ j v)) with hSdef
  have hSv : (S : Matrix (Fin n) (Fin n) ℂ) = Matrix.of (secMat ρ j v) := val_toGL hS
  have hSlev : S ∈ levSet n (ρ + 1) := by
    intro i hi
    have hiρ : ρ < i := by rw [Fin.lt_def]; omega
    refine ⟨fun l hl => ?_, ?_⟩
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_neg hl.ne]
    · rw [hSv, Matrix.of_apply, secMat_of_ne _ _ _ hiρ.ne', swap_of_lt' hj hiρ, if_pos rfl]
  have hp : g * S⁻¹ ∈ levSet n (ρ + 1) :=
    (GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).1 g hg _ ((GlobalTheory.T.unipotentLowerRowsLeviSet_closed_subgroup n (ρ + 1)).2.1 S hSlev)
  set P := ((g * S⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) with hPdef
  have hPS : P * Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hSv, hPdef, ← Units.val_mul, inv_mul_cancel_right]
  let w : Fin n → ℂ := fun i => if i = ρ then 1 else if i < ρ then 0 else (g : Matrix (Fin n) (Fin n) ℂ) ρ i
  have hw : w ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    funext l
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply]
    by_cases hl : l ≤ ρ
    · rw [Finset.sum_eq_single ρ]
      · simp [w, secMat_self, hl, hv, rowCut]
      · intro i _ hi
        rcases lt_or_gt_of_ne hi with h | h
        · simp [w, hi, h]
        · rw [secMat_of_ne _ _ _ hi, swap_of_lt' hj h, if_neg (lt_of_le_of_lt hl h).ne, mul_zero]
      · simp
    · have hlρ : ρ < l := lt_of_not_ge hl
      rw [Finset.sum_eq_single l]
      · simp [w, secMat_of_ne _ _ _ hlρ.ne', swap_of_lt' hj hlρ, hlρ.ne', not_lt.2 hlρ.le]
      · intro i _ hi
        by_cases h1 : i = ρ
        · rw [h1, secMat_self, if_neg hl, mul_zero]
        · rcases lt_or_gt_of_ne h1 with h | h
          · simp [w, h1, h]
          · rw [secMat_of_ne _ _ _ h1, swap_of_lt' hj h, if_neg (Ne.symm hi), mul_zero]
      · simp
  have hPw : P ρ ᵥ* Matrix.of (secMat ρ j v) = (g : Matrix (Fin n) (Fin n) ℂ) ρ := by
    rw [← hPS]
    funext l
    simp [Matrix.vecMul, dotProduct, Matrix.mul_apply]
  have hrow : P ρ = w := (Matrix.vecMul_injective_iff_isUnit.2 hS) (hPw.trans hw.symm)
  intro i hi
  by_cases hiρ : (i : ℕ) = ρ
  · have hie : i = ρ := Fin.ext hiρ
    subst hie
    refine ⟨fun l hl => ?_, ?_⟩
    · change P i l = 0
      rw [hrow]
      simp [w, hl, hl.ne]
    · change P i i = 1
      rw [hrow]
      simp [w]
  · exact hp i (by omega)

end GlobalTheory.JSW
