import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.SfiniteMuN
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.ConvGrp

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL.Cv

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine PI.WBL

section PiRep

variable {k r : ℕ}

def inB (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (i : Fin (2 * r + k + 1)) : Decidable (inB k r i) := by unfold inB; infer_instance

def eB (k r : ℕ) (m : Fin k) : Fin (2 * r + k + 1) := ⟨r + m.val, by omega⟩

/- English proof (translation)
Introduce `m m' h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [eB] at this`. Conclude with `Fin.ext (by omega)`.
-/
theorem eB_inj : Function.Injective (eB k r) := by
  intro m m' h
  have := congrArg Fin.val h
  simp only [eB] at this
  exact Fin.ext (by omega)

/- English proof (translation)
Use `m.isLt` as an intermediate fact. Use `show r ≤ r + m.val ∧ r + m.val < r + k`. Conclude with `⟨by omega, by omega⟩`.
-/
theorem eB_inB (m : Fin k) : inB k r (eB k r m) := by
  have := m.isLt
  show r ≤ r + m.val ∧ r + m.val < r + k
  exact ⟨by omega, by omega⟩

/- English proof (translation)
Unfold `inB at hi`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [eB]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_eB_of_inB {i : Fin (2 * r + k + 1)} (hi : inB k r i) : i = eB k r ⟨i.val - r, by unfold inB at hi; omega⟩ := by
  unfold inB at hi
  apply Fin.ext
  simp only [eB]
  omega

def ub (c : Mx k r) : Matrix (Fin k) (Fin k) ℂ := fun m m' => c (eB k r m) (eB k r m')

/- English proof (translation)
Unfold `inB at hi hj`. Simplify using `only [blockW, dif_pos hi, dif_pos hj]`.
-/
theorem blockW_in {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : inB k r j) :
    blockW k r h i j = h ⟨i.val - r, by unfold inB at hi; omega⟩ ⟨j.val - r, by unfold inB at hj; omega⟩ := by
  unfold inB at hi hj
  simp only [blockW, dif_pos hi, dif_pos hj]

/- English proof (translation)
Unfold `inB at hi hj`. Simplify using `only [blockW, dif_pos hi, dif_neg hj]`.
-/
theorem blockW_in_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : ¬ inB k r j) :
    blockW k r h i j = 0 := by
  unfold inB at hi hj
  simp only [blockW, dif_pos hi, dif_neg hj]

/- English proof (translation)
Unfold `inB at hi`. Simplify using `only [blockW, dif_neg hi]`.
-/
theorem blockW_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : ¬ inB k r i) :
    blockW k r h i j = if i = j then 1 else 0 := by
  unfold inB at hi
  simp only [blockW, dif_neg hi]

/- English proof (translation)
Rewrite using `[blockW_in (eB_inB m) (eB_inB m')]`. Simplify using `[eB]`.
-/
theorem blockW_eB (h : Matrix (Fin k) (Fin k) ℂ) (m m' : Fin k) : blockW k r h (eB k r m) (eB k r m') = h m m' := by
  rw [blockW_in (eB_inB m) (eB_inB m')]
  simp [eB]

/- English proof (translation)
Rewrite using `[← Finset.sum_image (fun m _ m' _ h => eB_inj h)]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `l _ hl`. Apply `hF` to reduce the goal to its premises.

Introduce `hin`. Conclude with `hl (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (eq_eB_of_inB hin).symm⟩)`.
-/
theorem sum_block (F : Fin (2 * r + k + 1) → ℂ) (hF : ∀ l, ¬ inB k r l → F l = 0) :
    ∑ l, F l = ∑ m : Fin k, F (eB k r m) := by
  rw [← Finset.sum_image (fun m _ m' _ h => eB_inj h)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro l _ hl
  apply hF
  intro hin
  exact hl (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, (eq_eB_of_inB hin).symm⟩)

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : inB k r i`. Rewrite using `[sum_block _ (fun l hl => by rw [blockW_in_out hi hl, zero_mul])]`. Distinguish the cases in `hj : inB k r j`.

Rewrite using `[blockW_in hi hj, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[blockW_in hi (eB_inB m), blockW_in (eB_inB m) hj]`. Simplify using `[eB]`. Rewrite using `[blockW_in_out hi hj]`.

Conclude with `(Finset.sum_eq_zero fun m _ => by rw [blockW_in_out (eB_inB m) hj, mul_zero]).symm`. Rewrite using `[blockW_out hi, Finset.sum_eq_single i]`. Rewrite using `[blockW_out (h := h₁) hi, if_pos rfl, one_mul, blockW_out (h := h₂) hi]`. Introduce `l _ hl`. Rewrite using `[blockW_out (h := h₁) hi, if_neg (Ne.symm hl), zero_mul]`.

Simplify using the standard rewrite rules.
-/
theorem blockW_mul (h₁ h₂ : Matrix (Fin k) (Fin k) ℂ) :
    blockW k r (h₁ * h₂) = blockW k r h₁ * blockW k r h₂ := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : inB k r i
  · rw [sum_block _ (fun l hl => by rw [blockW_in_out hi hl, zero_mul])]
    by_cases hj : inB k r j
    · rw [blockW_in hi hj, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [blockW_in hi (eB_inB m), blockW_in (eB_inB m) hj]
      simp [eB]
    · rw [blockW_in_out hi hj]
      exact (Finset.sum_eq_zero fun m _ => by rw [blockW_in_out (eB_inB m) hj, mul_zero]).symm
  · rw [blockW_out hi, Finset.sum_eq_single i]
    · rw [blockW_out (h := h₁) hi, if_pos rfl, one_mul, blockW_out (h := h₂) hi]
    · intro l _ hl
      rw [blockW_out (h := h₁) hi, if_neg (Ne.symm hl), zero_mul]
    · simp

/- English proof (translation)
Unfold `inB at hm`. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_in_col {i m : Fin (2 * r + k + 1)} (hm : inB k r m) : Hpk k r i m = if i = m then 1 else 0 := by
  unfold inB at hm
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `inB at hi`. Establish `hil` using `i.isLt`. Distinguish the cases in `h : i.val = r + k`. Use `⟨i, by unfold inB; omega, -1, by norm_num, fun b => ?_⟩` and prove the remaining obligations. Establish `hbl` using `b.isLt`.

Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Use `⟨⟨2 * r + k - i.val, by omega⟩, by unfold inB; simp only; omega, 1, one_ne_zero, fun b => ?_⟩` and prove the remaining obligations. Establish `hbl` using `b.isLt`. Simplify using `only [Hpk, Fin.ext_iff, Fin.val_mk]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
private theorem Hpk_apply_wp_eq_ite {i : Fin (2 * r + k + 1)} (hi : ¬ inB k r i) :
    ∃ l : Fin (2 * r + k + 1), ¬ inB k r l ∧ ∃ s : ℂ, s ≠ 0 ∧ ∀ b, Hpk k r l b = if b = i then s else 0 := by
  unfold inB at hi
  have hil := i.isLt
  by_cases h : i.val = r + k
  · refine ⟨i, by unfold inB; omega, -1, by norm_num, fun b => ?_⟩
    have hbl := b.isLt
    simp only [Hpk, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
  · refine ⟨⟨2 * r + k - i.val, by omega⟩, by unfold inB; simp only; omega, 1, one_ne_zero, fun b => ?_⟩
    have hbl := b.isLt
    simp only [Hpk, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `hcol : ∀ l, ¬ inB k r l → ∀ a, c a l = if a = l then 1 else 0`. Introduce `l hl a`. Use `congrFun (hfix l hl) a` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply]`. Establish `hcU : cᴴ * Hpk k r * c = Hpk k r` using `hc`.

Establish `key : ∀ l, ¬ inB k r l → ∀ j, ∑ b, Hpk k r l b * c b j = Hpk k r l j`. Introduce `l hl j`. Use `congrFun (congrFun hcU l) j` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single l]`. Simplify using `[Matrix.conjTranspose_apply, hcol l hl]`. Introduce `a _ ha`.

Simplify using `[Matrix.conjTranspose_apply, hcol l hl, ha]`. Simplify using the standard rewrite rules. Use extensionality with `i j`. Distinguish the cases in `hj : inB k r j`. Distinguish the cases in `hi : inB k r i`.

Rewrite using `[blockW_in hi hj]`. Conclude with `congrArg₂ c (eq_eB_of_inB hi) (eq_eB_of_inB hj)`. Rewrite using `[blockW_out hi, if_neg (by rintro rfl; exact hi hj)]`. Take `⟨l, hl, s, hs, hrow⟩` from `Hpk_apply_wp_eq_ite hi`. Establish `h1` using `key l hl j`.

Rewrite `h1` using `[Finset.sum_eq_single i (fun b _ hb => by rw [hrow b, if_neg hb, zero_mul]) (by simp), hrow i, if_pos rfl, hpk_in_col hj, if_neg (by rintro rfl; exact hl hj)]`. Conclude with `(mul_eq_zero.mp h1).resolve_left hs`. Rewrite using `[hcol j hj i]`. Distinguish the cases in `hi : inB k r i`. Rewrite using `[blockW_in_out hi hj, if_neg (by rintro rfl; exact hj hi)]`.

Rewrite using `[blockW_out hi]`.
-/
theorem eq_blockW {c : Mx k r} (hc : c ∈ UH (Hpk k r))
    (hfix : ∀ l, ¬ inB k r l → c *ᵥ bvec l = bvec l) : c = blockW k r (ub c) := by
  have hcol : ∀ l, ¬ inB k r l → ∀ a, c a l = if a = l then 1 else 0 := by
    intro l hl a
    have := congrFun (hfix l hl) a
    simpa [Matrix.mulVec, dotProduct, bvec, Pi.single_apply] using this
  have hcU : cᴴ * Hpk k r * c = Hpk k r := hc
  have key : ∀ l, ¬ inB k r l → ∀ j, ∑ b, Hpk k r l b * c b j = Hpk k r l j := by
    intro l hl j
    have := congrFun (congrFun hcU l) j
    rw [Matrix.mul_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single l]
    · simp [Matrix.conjTranspose_apply, hcol l hl]
    · intro a _ ha
      simp [Matrix.conjTranspose_apply, hcol l hl, ha]
    · simp
  ext i j
  by_cases hj : inB k r j
  · by_cases hi : inB k r i
    · rw [blockW_in hi hj]
      exact congrArg₂ c (eq_eB_of_inB hi) (eq_eB_of_inB hj)
    · rw [blockW_out hi, if_neg (by rintro rfl; exact hi hj)]
      obtain ⟨l, hl, s, hs, hrow⟩ := Hpk_apply_wp_eq_ite hi
      have h1 := key l hl j
      rw [Finset.sum_eq_single i (fun b _ hb => by rw [hrow b, if_neg hb, zero_mul]) (by simp),
        hrow i, if_pos rfl, hpk_in_col hj, if_neg (by rintro rfl; exact hl hj)] at h1
      exact (mul_eq_zero.mp h1).resolve_left hs
  · rw [hcol j hj i]
    by_cases hi : inB k r i
    · rw [blockW_in_out hi hj, if_neg (by rintro rfl; exact hj hi)]
    · rw [blockW_out hi]

/- English proof (translation)
Establish `hz : ∀ a m, ¬ inB k r a → c a (eB k r m) = 0`. Introduce `a m ha`. Rewrite using `[hb, blockW_out ha, if_neg (by rintro rfl; exact ha (eB_inB m))]`. Establish `hcol : ∀ a m', ∑ b, Hpk k r a b * c b (eB k r m') = c a (eB k r m')`. Introduce `a m'`.

Establish `: ∀ b, Hpk k r a b * c b (eB k r m') = if a = b then c b (eB k r m') else 0`. Introduce `b`. Distinguish the cases in `hbin : inB k r b`. Apply the tactic sequence `rw [hpk_in_col hbin] split_ifs <;> simp only [one_mul, zero_mul]`. Rewrite using `[hz b m' hbin, mul_zero, ite_self]`.

Simplify using `only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `show (ub c)ᴴ * Formalism.REAL.Jm (allPos k) * ub c = Formalism.REAL.Jm (allPos k)`. Establish `hJ : Formalism.REAL.Jm (allPos k) = 1`. Unfold `Formalism.REAL.Jm allPos`. Simplify using the standard rewrite rules.

Rewrite using `[hJ, Matrix.mul_one]`. Use extensionality with `m m'`. Establish `hc' : cᴴ * (Hpk k r * c) = Hpk k r`. Rewrite using `[← Matrix.mul_assoc]`. Conclude with `hc`.

Establish `h1` using `congrFun (congrFun hc' (eB k r m)) (eB k r m')`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol] at h1`. Rewrite `h1` using `[sum_block _ (fun a ha => by rw [hz a m ha, star_zero, zero_mul])]`. Rewrite `h1` using `[hpk_in_col (eB_inB m')]`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply, ub, Matrix.one_apply]`.

Rewrite using `[h1]`. Simplify using `[eB_inj.eq_iff]`.
-/
theorem ub_unitary {c : Mx k r} (hc : c ∈ UH (Hpk k r)) (hb : c = blockW k r (ub c)) :
    ub c ∈ UJset (allPos k) := by
  have hz : ∀ a m, ¬ inB k r a → c a (eB k r m) = 0 := by
    intro a m ha
    rw [hb, blockW_out ha, if_neg (by rintro rfl; exact ha (eB_inB m))]
  have hcol : ∀ a m', ∑ b, Hpk k r a b * c b (eB k r m') = c a (eB k r m') := by
    intro a m'
    have : ∀ b, Hpk k r a b * c b (eB k r m') = if a = b then c b (eB k r m') else 0 := by
      intro b
      by_cases hbin : inB k r b
      · rw [hpk_in_col hbin]
        split_ifs <;> simp only [one_mul, zero_mul]
      · rw [hz b m' hbin, mul_zero, ite_self]
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  show (ub c)ᴴ * Formalism.REAL.Jm (allPos k) * ub c = Formalism.REAL.Jm (allPos k)
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    unfold Formalism.REAL.Jm allPos
    simp
  rw [hJ, Matrix.mul_one]
  ext m m'
  have hc' : cᴴ * (Hpk k r * c) = Hpk k r := by
    rw [← Matrix.mul_assoc]
    exact hc
  have h1 := congrFun (congrFun hc' (eB k r m)) (eB k r m')
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hcol] at h1
  rw [sum_block _ (fun a ha => by rw [hz a m ha, star_zero, zero_mul])] at h1
  rw [hpk_in_col (eB_inB m')] at h1
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ub, Matrix.one_apply]
  rw [h1]
  simp [eB_inj.eq_iff]

/- English proof (translation)
Take `⟨hgU, hgfix, hgz⟩` from `hg`. Take `⟨haU, hafix, haz⟩` from `ha`. Take `⟨hg1, hg2, hgi⟩` from `uh_inv hgU`. Take `⟨c, hc_def⟩ : ∃ c, c = g⁻¹ * a * g` from `⟨_, rfl⟩`. Rewrite using `[← hc_def]`.

Establish `hcU : c ∈ UH (Hpk k r)`. Rewrite using `[hc_def]`. Conclude with `uh_mul (uh_mul hgi haU) hgU`. Establish `hinvfix : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v`. Introduce `v hv`.

Combine the equalities or inequalities in the displayed calculation. Establish `hfixc : ∀ v, g *ᵥ v = v → a *ᵥ v = v → c *ᵥ v = v`. Introduce `v hv hav`. Rewrite using `[hc_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, hav, hinvfix v hv]`. Establish `hw : c *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))`.

Establish `hT' : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0`. Conclude with `(Real.sqrt_pos.mpr hT).ne'` after adjusting the coercions. Establish `hz' : g⁻¹ *ᵥ z = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hgz]`.

Use `_ = _ := by rw [Matrix.mulVec_mulVec, hg2, Matrix.one_mulVec]`. Establish `h1 : c *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))`. Rewrite using `[hc_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgz, haz, hz']`. Rewrite `h1` using `[Matrix.mulVec_smul]`. Conclude with `smul_right_injective _ hT' h1`.

Establish `hfixall : ∀ l, ¬ inB k r l → c *ᵥ bvec l = bvec l`. Introduce `l hl`. Unfold `inB at hl`. Establish `hll` using `l.isLt`. Distinguish the cases in `h1 : l.val < r`.

Use `hfixc _ (hgfix ⟨l.val, h1⟩).1 (hafix ⟨l.val, h1⟩).1` as an intermediate fact. Establish `e : eI k r ⟨l.val, h1⟩ = l` using `Fin.ext rfl`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Distinguish the cases in `h2 : l.val = r + k`. Establish `e : wI k r (Fin.last k) = l` using `Fin.ext (by simp [wI]; omega)`.

Rewrite using `[← e]`. Conclude with `hw`. Establish `h3 : 2 * r + k - l.val < r` using `by omega`. Use `hfixc _ (hgfix ⟨2 * r + k - l.val, h3⟩).2 (hafix ⟨2 * r + k - l.val, h3⟩).2` as an intermediate fact. Establish `e : esI k r ⟨2 * r + k - l.val, h3⟩ = l` using `Fin.ext (by simp [esI]; omega)`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Establish `hb` using `eq_blockW hcU hfixall`. Use `⟨ub_unitary hcU hb, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hc_def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg1, Matrix.one_mul, Matrix.mul_assoc, hg1, Matrix.mul_one]`.

Use `_ = g * blockW k r (ub c) * g⁻¹ := by rw [← hb]`.
-/
private theorem ub_conj_mem_UJset_and_eq_blockW {z : Fin (2 * r + k + 1) → ℂ} {g : Mx k r} (hT : 0 < Tz k r z)
    (hg : IsFrameW k r z g) {a : Mx k r} (ha : a ∈ UWset k r z) :
    ub (g⁻¹ * a * g) ∈ UJset (allPos k) ∧ a = g * blockW k r (ub (g⁻¹ * a * g)) * g⁻¹ := by
  obtain ⟨hgU, hgfix, hgz⟩ := hg
  obtain ⟨haU, hafix, haz⟩ := ha
  obtain ⟨hg1, hg2, hgi⟩ := uh_inv hgU
  obtain ⟨c, hc_def⟩ : ∃ c, c = g⁻¹ * a * g := ⟨_, rfl⟩
  rw [← hc_def]
  have hcU : c ∈ UH (Hpk k r) := by
    rw [hc_def]
    exact uh_mul (uh_mul hgi haU) hgU
  have hinvfix : ∀ v, g *ᵥ v = v → g⁻¹ *ᵥ v = v := by
    intro v hv
    calc g⁻¹ *ᵥ v = g⁻¹ *ᵥ (g *ᵥ v) := by rw [hv]
      _ = v := by rw [Matrix.mulVec_mulVec, hg2, Matrix.one_mulVec]
  have hfixc : ∀ v, g *ᵥ v = v → a *ᵥ v = v → c *ᵥ v = v := by
    intro v hv hav
    rw [hc_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, hav, hinvfix v hv]
  have hw : c *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k)) := by
    have hT' : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hT).ne'
    have hz' : g⁻¹ *ᵥ z = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) := by
      calc g⁻¹ *ᵥ z = g⁻¹ *ᵥ (g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k)))) := by
            rw [hgz]
        _ = _ := by rw [Matrix.mulVec_mulVec, hg2, Matrix.one_mulVec]
    have h1 : c *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) =
        ((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) := by
      rw [hc_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hgz, haz, hz']
    rw [Matrix.mulVec_smul] at h1
    exact smul_right_injective _ hT' h1
  have hfixall : ∀ l, ¬ inB k r l → c *ᵥ bvec l = bvec l := by
    intro l hl
    unfold inB at hl
    have hll := l.isLt
    by_cases h1 : l.val < r
    · have := hfixc _ (hgfix ⟨l.val, h1⟩).1 (hafix ⟨l.val, h1⟩).1
      have e : eI k r ⟨l.val, h1⟩ = l := Fin.ext rfl
      rwa [e] at this
    · by_cases h2 : l.val = r + k
      · have e : wI k r (Fin.last k) = l := Fin.ext (by simp [wI]; omega)
        rw [← e]
        exact hw
      · have h3 : 2 * r + k - l.val < r := by omega
        have := hfixc _ (hgfix ⟨2 * r + k - l.val, h3⟩).2 (hafix ⟨2 * r + k - l.val, h3⟩).2
        have e : esI k r ⟨2 * r + k - l.val, h3⟩ = l := Fin.ext (by simp [esI]; omega)
        rwa [e] at this
  have hb := eq_blockW hcU hfixall
  refine ⟨ub_unitary hcU hb, ?_⟩
  calc a = g * c * g⁻¹ := by
        rw [hc_def, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hg1, Matrix.one_mul, Matrix.mul_assoc, hg1,
          Matrix.mul_one]
    _ = g * blockW k r (ub c) * g⁻¹ := by rw [← hb]

/- English proof (translation)
Introduce `k r z u Wp _ _ π hz hT hπ`. Take `⟨g, hg, hH⟩` from `hπ`. Take `⟨_, _, ⟨⟨h1, hmul⟩, hiso, _⟩, _⟩` from `hH`. Take `⟨hg1, hg2, _⟩` from `uh_inv hg.1`. Establish `hb1 : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1`.

Use extensionality with `i j`. Rewrite using `[Matrix.one_apply]`. Distinguish the cases in `hi : inB k r i`. Distinguish the cases in `hj : inB k r j`. Rewrite using `[blockW_in hi hj, Matrix.one_apply]`.

Unfold `inB at hi hj`. Simplify using `only [Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[blockW_in_out hi hj, if_neg (by rintro rfl; exact hj hi)]`. Rewrite using `[blockW_out hi]`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `h1`. Simplify using `only [hb1, Matrix.mul_one, hg1] at e`. Conclude with `e`. Introduce `a ha b hb`.

Take `⟨hua, hea⟩` from `ub_conj_mem_UJset_and_eq_blockW hT hg ha`. Take `⟨hub, heb⟩` from `ub_conj_mem_UJset_and_eq_blockW hT hg hb`. Establish `hab : a * b = g * blockW k r (ub (g⁻¹ * a * g) * ub (g⁻¹ * b * g)) * g⁻¹`. Rewrite using `[blockW_mul]`. Use `conv_lhs => rw [hea, heb]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc g⁻¹ g, hg2, Matrix.one_mul]`. Establish `e` using `hmul _ hua _ hub`. Simplify using `only at e`. Rewrite using `[hab, e, ← hea, ← heb]`.

Introduce `a ha x`. Take `⟨hua, hea⟩` from `ub_conj_mem_UJset_and_eq_blockW hT hg ha`. Rewrite using `[hea]`. Conclude with `hiso _ hua x`.
-/
theorem piAll : PiAll := by
  intro k r z u Wp _ _ π hz hT hπ
  obtain ⟨g, hg, hH⟩ := hπ
  obtain ⟨_, _, ⟨⟨h1, hmul⟩, hiso, _⟩, _⟩ := hH
  obtain ⟨hg1, hg2, _⟩ := uh_inv hg.1
  have hb1 : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    ext i j
    rw [Matrix.one_apply]
    by_cases hi : inB k r i
    · by_cases hj : inB k r j
      · rw [blockW_in hi hj, Matrix.one_apply]
        unfold inB at hi hj
        simp only [Fin.ext_iff, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [blockW_in_out hi hj, if_neg (by rintro rfl; exact hj hi)]
    · rw [blockW_out hi]
  refine ⟨?_, ?_, ?_⟩
  · have e := h1
    simp only [hb1, Matrix.mul_one, hg1] at e
    exact e
  · intro a ha b hb
    obtain ⟨hua, hea⟩ := ub_conj_mem_UJset_and_eq_blockW hT hg ha
    obtain ⟨hub, heb⟩ := ub_conj_mem_UJset_and_eq_blockW hT hg hb
    have hab : a * b = g * blockW k r (ub (g⁻¹ * a * g) * ub (g⁻¹ * b * g)) * g⁻¹ := by
      rw [blockW_mul]
      conv_lhs => rw [hea, heb]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc g⁻¹ g, hg2, Matrix.one_mul]
    have e := hmul _ hua _ hub
    simp only at e
    rw [hab, e, ← hea, ← heb]
  · intro a ha x
    obtain ⟨hua, hea⟩ := ub_conj_mem_UJset_and_eq_blockW hT hg ha
    rw [hea]
    exact hiso _ hua x

/- English proof (translation)
Conclude with `ub_conj_mem_UJset_and_eq_blockW hT hg ha`.
-/
theorem frame_block {z : Fin (2 * r + k + 1) → ℂ} {g : Mx k r} (hT : 0 < Tz k r z) (hg : IsFrameW k r z g)
    {a : Mx k r} (ha : a ∈ UWset k r z) :
    ub (g⁻¹ * a * g) ∈ UJset (allPos k) ∧ a = g * blockW k r (ub (g⁻¹ * a * g)) * g⁻¹ := by
  exact ub_conj_mem_UJset_and_eq_blockW hT hg ha

/- English proof (translation)
Introduce `k r z u Wp _ _ π hz hT hπ x`. Take `⟨g, hg, hH⟩` from `hπ`. Take `⟨_, _, ⟨_, _, hcont⟩, _⟩` from `hH`. Establish `hF : Continuous fun a : Mx k r => ub (g⁻¹ * a * g)`. Use `continuous_matrix fun m m' => ?_` and prove the remaining obligations.

Conclude with `((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem (eB k r m) (eB k r m')`. Establish `hmaps : Set.MapsTo (fun a : Mx k r => ub (g⁻¹ * a * g)) (UWset k r z) (UJset (allPos k))` using `fun a ha => (frame_block hT hg ha).1`. Establish `h1 : ContinuousOn (fun a => π (g * blockW k r (ub (g⁻¹ * a * g)) * g⁻¹) x) (UWset k r z)` using `(hcont x).comp hF.continuousOn hmaps`. Use `h1.congr fun a ha => ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← (frame_block hT hg ha).2]`.
-/
theorem piContAll : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)),
    inWb k r z → 0 < Tz k r z → IsHCTypeW k r z u π → ∀ x : Wp, ContinuousOn (fun g => π g x) (UWset k r z) := by
  intro k r z u Wp _ _ π hz hT hπ x
  obtain ⟨g, hg, hH⟩ := hπ
  obtain ⟨_, _, ⟨_, _, hcont⟩, _⟩ := hH
  have hF : Continuous fun a : Mx k r => ub (g⁻¹ * a * g) := by
    refine continuous_matrix fun m m' => ?_
    exact ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem
      (eB k r m) (eB k r m')
  have hmaps : Set.MapsTo (fun a : Mx k r => ub (g⁻¹ * a * g)) (UWset k r z) (UJset (allPos k)) :=
    fun a ha => (frame_block hT hg ha).1
  have h1 : ContinuousOn (fun a => π (g * blockW k r (ub (g⁻¹ * a * g)) * g⁻¹) x) (UWset k r z) :=
    (hcont x).comp hF.continuousOn hmaps
  refine h1.congr fun a ha => ?_
  simp only
  rw [← (frame_block hT hg ha).2]

end PiRep

end PI.WBL.Cv
