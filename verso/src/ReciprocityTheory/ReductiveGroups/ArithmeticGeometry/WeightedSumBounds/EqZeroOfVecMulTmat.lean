import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero

namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}

def tmat (γ : Fin d → Fin d → PowerSeries C) : Matrix (Fin d) (Fin d) C :=
  Matrix.of fun a b => tangent (γ a) b

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `[Matrix.vecMul, dotProduct, tmat, Finset.sum_apply]`.
-/
theorem sum_smul_tangent (γ : Fin d → Fin d → PowerSeries C) (x : Fin d → C) :
    ∑ b, x b • tangent (γ b) = Matrix.vecMul x (tmat γ) := by
  funext c
  simp [Matrix.vecMul, dotProduct, tmat, Finset.sum_apply]

/- English proof (translation)
Introduce `h`. Rewrite `hdet` using `[h]`. Simplify using `at hdet`.
-/
theorem tmat_det_ne_zero {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0) :
    (tmat γ).det ≠ 0 := by
  intro h
  rw [h] at hdet
  simp at hdet

/- English proof (translation)
The claim follows from `isUnit_iff_ne_zero.mpr (tmat_det_ne_zero hdet)`.
-/
theorem tmat_isUnit_det {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0) :
    IsUnit (tmat γ).det := isUnit_iff_ne_zero.mpr (tmat_det_ne_zero hdet)

/- English proof (translation)
Set `S : Subring C` to `{ carrier := {x | 0 ≤ v x} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, AddValuation.map_mul] at *`. Conclude with `add_nonneg ha hb`. Use the proof step `one_mem' := by simp`. Use the proof step `add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)`.

Use the proof step `zero_mem' := by simp`. Use the proof step `neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }`. Establish `hent : ∀ a b, tmat γ a b ∈ S` using `fun a b => by show 0 ≤ v (tmat γ a b)`. Conclude with `(hγ a b).2 1`. Set `M' : Matrix (Fin d) (Fin d) S` to `fun a b => ⟨tmat γ a b, hent a b⟩`.

Establish `hM : tmat γ = S.subtype.mapMatrix M'`. Use extensionality with `a b`. Both sides reduce to the same expression. Establish `hadj : ∀ i j, (tmat γ).adjugate i j ∈ S`. Introduce `i j`.

Rewrite using `[hM, ← RingHom.map_adjugate]`. Use `first`. Consider the case `exact (M'.adjugate i j).2`. Consider the case `simp`. Establish `hdet_inv : v ((tmat γ).det⁻¹) = 0`.

Establish `h1 : v ((tmat γ).det⁻¹ * (tmat γ).det) = 0`. Rewrite using `[inv_mul_cancel₀ (tmat_det_ne_zero hdet), AddValuation.map_one]`. Rewrite `h1` using `[AddValuation.map_mul, hdet, add_zero]`. Then use the resulting hypothesis. Use `show 0 ≤ v ((tmat γ)⁻¹ i j)`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul, hdet_inv, zero_add]`.

Conclude with `hadj i j`.
-/
theorem isIntV_tmat_inv {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) (i j : Fin d) : IsIntV v ((tmat γ)⁻¹ i j) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hent : ∀ a b, tmat γ a b ∈ S := fun a b => by
    show 0 ≤ v (tmat γ a b)
    exact (hγ a b).2 1
  let M' : Matrix (Fin d) (Fin d) S := fun a b => ⟨tmat γ a b, hent a b⟩
  have hM : tmat γ = S.subtype.mapMatrix M' := by
    ext a b
    rfl
  have hadj : ∀ i j, (tmat γ).adjugate i j ∈ S := by
    intro i j
    rw [hM, ← RingHom.map_adjugate]
    first
    | exact (M'.adjugate i j).2
    | simp
  have hdet_inv : v ((tmat γ).det⁻¹) = 0 := by
    have h1 : v ((tmat γ).det⁻¹ * (tmat γ).det) = 0 := by
      rw [inv_mul_cancel₀ (tmat_det_ne_zero hdet), AddValuation.map_one]
    rwa [AddValuation.map_mul, hdet, add_zero] at h1
  show 0 ≤ v ((tmat γ)⁻¹ i j)
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, AddValuation.map_mul,
    hdet_inv, zero_add]
  exact hadj i j

/- English proof (translation)
Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (tmat_isUnit_det hdet), Matrix.vecMul_one]`.
-/
theorem vecMul_inv_tmat {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    (w : Fin d → C) : Matrix.vecMul (Matrix.vecMul w (tmat γ)⁻¹) (tmat γ) = w := by
  rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (tmat_isUnit_det hdet), Matrix.vecMul_one]

/- English proof (translation)
Establish `h2` using `congrArg (fun w => Matrix.vecMul w (tmat γ)⁻¹) h`. Simplify using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (tmat_isUnit_det hdet), Matrix.vecMul_one, Matrix.zero_vecMul] at h2`. Conclude with `h2`.
-/
theorem eq_zero_of_vecMul_tmat {γ : Fin d → Fin d → PowerSeries C} (hdet : v (tmat γ).det = 0)
    {x : Fin d → C} (h : Matrix.vecMul x (tmat γ) = 0) : x = 0 := by
  have h2 := congrArg (fun w => Matrix.vecMul w (tmat γ)⁻¹) h
  simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (tmat_isUnit_det hdet),
    Matrix.vecMul_one, Matrix.zero_vecMul] at h2
  exact h2

/- English proof (translation)
Set `S : Subring C` to `{ carrier := {x | 0 ≤ v x} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq, AddValuation.map_mul] at *`. Conclude with `add_nonneg ha hb`. Use the proof step `one_mem' := by simp`. Use the proof step `add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)`.

Use the proof step `zero_mem' := by simp`. Use the proof step `neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }`. Establish `hmem : Matrix.vecMul w (tmat γ)⁻¹ b ∈ S`. Simplify using `only [Matrix.vecMul, dotProduct]`. Conclude with `S.sum_mem fun c _ => S.mul_mem (hw c) (isIntV_tmat_inv hγ hdet c b)`.

Conclude with `hmem`.
-/
theorem isIntV_vecMul_inv {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) {w : Fin d → C} (hw : ∀ c, IsIntV v (w c)) (b : Fin d) :
    IsIntV v (Matrix.vecMul w (tmat γ)⁻¹ b) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hmem : Matrix.vecMul w (tmat γ)⁻¹ b ∈ S := by
    simp only [Matrix.vecMul, dotProduct]
    exact S.sum_mem fun c _ => S.mul_mem (hw c) (isIntV_tmat_inv hγ hdet c b)
  exact hmem

/- English proof (translation)
Introduce `b hb`. Use `set x' : Fin d → C := fun b => if ty b ≠ τ then x b else 0 with hx'`. Establish `hz : Matrix.vecMul x' (tmat γ) = 0`. Use function extensionality and compare the values at `c`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply]`.

Distinguish the cases in `hc : ty c = τ`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b' _`. Distinguish the cases in `hb' : ty b' ≠ τ`. Establish `h0 : tangent (γ b') c = 0` using `ht b' c (by rw [hc]; exact fun h => hb' h.symm)`.

Simplify using `[hx', hb', tmat, h0]`. Simplify using `[hx', hb']`. Establish `h0` using `hw c hc`. Simplify using `only [Matrix.vecMul, dotProduct] at h0`. Rewrite using `[← h0]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b' _`. Distinguish the cases in `hb' : ty b' ≠ τ`. Simplify using `[hx', hb']`. Establish `hb2 : ty b' = τ` using `not_not.mp hb'`.

Establish `h1 : tangent (γ b') c = 0` using `ht b' c (by rw [hb2]; exact hc)`. Simplify using `[hx', hb', tmat, h1]`. Establish `h3` using `congrFun (eq_zero_of_vecMul_tmat hdet hz) b`. Simplify `h3` using `[hx', hb]`.
-/
theorem vecMul_tmat_support {h : ℕ} (ty : Fin d → ZMod h) {γ : Fin d → Fin d → PowerSeries C}
    (hdet : v (tmat γ).det = 0) (ht : ∀ b c, ty c ≠ ty b → tangent (γ b) c = 0)
    (x : Fin d → C) (τ : ZMod h) (hw : ∀ c, ty c ≠ τ → Matrix.vecMul x (tmat γ) c = 0) :
    ∀ b, ty b ≠ τ → x b = 0 := by
  intro b hb
  set x' : Fin d → C := fun b => if ty b ≠ τ then x b else 0 with hx'
  have hz : Matrix.vecMul x' (tmat γ) = 0 := by
    funext c
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hc : ty c = τ
    · apply Finset.sum_eq_zero
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · have h0 : tangent (γ b') c = 0 := ht b' c (by rw [hc]; exact fun h => hb' h.symm)
        simp [hx', hb', tmat, h0]
      · simp [hx', hb']
    · have h0 := hw c hc
      simp only [Matrix.vecMul, dotProduct] at h0
      rw [← h0]
      apply Finset.sum_congr rfl
      intro b' _
      by_cases hb' : ty b' ≠ τ
      · simp [hx', hb']
      · have hb2 : ty b' = τ := not_not.mp hb'
        have h1 : tangent (γ b') c = 0 := ht b' c (by rw [hb2]; exact hc)
        simp [hx', hb', tmat, h1]
  have h3 := congrFun (eq_zero_of_vecMul_tmat hdet hz) b
  simpa [hx', hb] using h3

end

end ReciprocityTheory.ChartRestriction.G.Sh.PTb
