import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UMatUpper
import Lemmata.GeneralBFactForm.Imports

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI

open Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

noncomputable section

section Mat

variable {n : ℕ}

/- English proof (translation)
Use `haveI : Invertible M := M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)`. Conclude with `Matrix.blockTriangular_inv_of_blockTriangular hM`.
-/
lemma inv_blockTriangular {α : Type*} [LinearOrder α] {b : Fin n → α} {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.BlockTriangular b) (hd : M.det ≠ 0) : (M⁻¹).BlockTriangular b := by
  haveI : Invertible M := M.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)
  exact Matrix.blockTriangular_inv_of_blockTriangular hM

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular N hN]`. Simplify using `[h1]`.
-/
lemma det_lowerUni {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.BlockTriangular OrderDual.toDual)
    (h1 : ∀ a, N a a = 1) : N.det = 1 := by
  rw [Matrix.det_of_lowerTriangular N hN]
  simp [h1]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_form.goal1 .. | (apply Bl.general_b_fact_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_form.goal1 <;> assumption)`.
-/
theorem lu_unique {N N' U U' : Matrix (Fin n) (Fin n) ℂ}
    (hN : N.BlockTriangular OrderDual.toDual) (hN1 : ∀ a, N a a = 1)
    (hN' : N'.BlockTriangular OrderDual.toDual) (hN'1 : ∀ a, N' a a = 1)
    (hU : U.BlockTriangular id) (hU' : U'.BlockTriangular id) (hd : U'.det ≠ 0)
    (h : N * U = N' * U') : N = N' ∧ U = U' := by
  first | exact Bl.general_b_fact_form.goal1 .. | (apply Bl.general_b_fact_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_form.goal1 <;> assumption)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma lminor_last' (M : Matrix (Fin n) (Fin n) ℂ) : lminor M (Fin.last n) = M.det := by
  rfl

/- English proof (translation)
Set `A : ∀ r : Fin n, Matrix (Fin r) (Fin r) ℂ` to `fun r => M.submatrix (Fin.castLE r.isLt.le) (Fin.castLE r.isLt.le)`. Establish `hA : ∀ r : Fin n, IsUnit (A r).det` using `fun r => isUnit_iff_ne_zero.mpr (hM r.castSucc)`. Set `x : ∀ r : Fin n, Fin r → ℂ` to `fun r => -((fun j => M r (Fin.castLE r.isLt.le j)) ᵥ* (A r)⁻¹)`. Establish `hx : ∀ r : Fin n, ∀ j : Fin r, ∑ i : Fin r, x r i * M (Fin.castLE r.isLt.le i) (Fin.castLE r.isLt.le j) = -M r (Fin.castLE r.isLt.le j)`. Introduce `r j`.

Establish `hv : x r ᵥ* A r = -(fun j => M r (Fin.castLE r.isLt.le j))`. Simplify using `only [x, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hA r), Matrix.vecMul_one]`. Establish `h` using `congrFun hv j`. Simplify `h` using `[Matrix.vecMul, dotProduct, A]`. Set `L : Matrix (Fin n) (Fin n) ℂ` to `Matrix.of fun r c => if h : c < r then x r ⟨c, h⟩ else if c = r then 1 else 0`.

Establish `hLlow : L.BlockTriangular OrderDual.toDual`. Introduce `r c hrc`. Establish `hrc' : r < c` using `OrderDual.toDual_lt_toDual.mp hrc`. Simplify using `[L, not_lt.mpr hrc'.le, hrc'.ne']`. Establish `hL1 : ∀ a, L a a = 1` using `fun a => by simp [L]`.

Establish `hLdet : L.det = 1` using `det_lowerUni hLlow hL1`. Establish `hLu : IsUnit L.det` using `by rw [hLdet]; exact isUnit_one`. Establish `hrow : ∀ r c : Fin n, c < r → (L * M) r c = 0`. Introduce `r c hcr`. Establish `e1 : ∀ k, L r k * M k c = (if h : k < r then x r ⟨k, h⟩ * M k c else 0) + (if k = r then M k c else 0)`.

Introduce `k`. Distinguish the cases in `h : k < r`. Simplify using `[L, h, h.ne]`. Distinguish the cases in `h' : k = r`. Substitute `h'` using the available equality.

Simplify using `[L]`. Simplify using `[L, h, h']`. Establish `hsub : ∑ k : Fin n, (if h : k < r then x r ⟨k, h⟩ * M k c else 0) = ∑ j : Fin r, x r j * M (Fin.castLE r.isLt.le j) c`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb r.isLt.le)))]`. Rewrite using `[Finset.sum_map]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hj : (Fin.castLEEmb r.isLt.le j) < r` using `by show (j : ℕ) < r`. Conclude with `j.isLt`. Rewrite using `[dif_pos hj]`. Both sides reduce to the same expression.

Introduce `k _ hk`. Establish `hk' : ¬ k < r`. Introduce `h`. Apply `hk` to reduce the goal to its premises. Conclude with `Finset.mem_map.mpr ⟨⟨k, h⟩, Finset.mem_univ _, Fin.ext rfl⟩`.

Rewrite using `[dif_neg hk']`. Rewrite using `[Matrix.mul_apply, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ r (fun k => M k c), if_pos (Finset.mem_univ _), hsub]`. Establish `h` using `hx r ⟨c, hcr⟩`. Establish `hc : Fin.castLE r.isLt.le (⟨c, hcr⟩ : Fin r) = c` using `Fin.ext rfl`. Rewrite `h` using `[hc]`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨L⁻¹, L * M, inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Establish `h1 : (L * L⁻¹) a a = 1`.

Rewrite using `[Matrix.mul_nonsing_inv L hLu]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite `h1` using `[hL1, one_mul]`. Then use the resulting hypothesis. Introduce `k _ hka`.

Break down `lt_or_gt_of_ne hka with h | h` into its components or cases. Establish `h0 : L⁻¹ k a = 0` using `inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero) (OrderDual.toDual_lt_toDual.mpr h)`. Rewrite using `[h0, mul_zero]`. Establish `h0 : L a k = 0` using `hLlow (OrderDual.toDual_lt_toDual.mpr h)`. Rewrite using `[h0, zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ a) h`. Introduce `r c hcr`. Conclude with `hrow r c hcr`. Rewrite using `[Matrix.det_mul, hLdet, one_mul, ← lminor_last']`.

Conclude with `hM _`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.one_mul]`.
-/
theorem lu_exists {M : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i : Fin (n + 1), lminor M i ≠ 0) :
    ∃ N U : Matrix (Fin n) (Fin n) ℂ, N.BlockTriangular OrderDual.toDual ∧ (∀ a, N a a = 1) ∧
      U.BlockTriangular id ∧ U.det ≠ 0 ∧ N * U = M := by
  classical
  let A : ∀ r : Fin n, Matrix (Fin r) (Fin r) ℂ := fun r =>
    M.submatrix (Fin.castLE r.isLt.le) (Fin.castLE r.isLt.le)
  have hA : ∀ r : Fin n, IsUnit (A r).det := fun r => isUnit_iff_ne_zero.mpr (hM r.castSucc)
  let x : ∀ r : Fin n, Fin r → ℂ := fun r =>
    -((fun j => M r (Fin.castLE r.isLt.le j)) ᵥ* (A r)⁻¹)
  have hx : ∀ r : Fin n, ∀ j : Fin r,
      ∑ i : Fin r, x r i * M (Fin.castLE r.isLt.le i) (Fin.castLE r.isLt.le j) =
        -M r (Fin.castLE r.isLt.le j) := by
    intro r j
    have hv : x r ᵥ* A r = -(fun j => M r (Fin.castLE r.isLt.le j)) := by
      simp only [x, Matrix.neg_vecMul, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hA r),
        Matrix.vecMul_one]
    have h := congrFun hv j
    simpa [Matrix.vecMul, dotProduct, A] using h

  let L : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun r c =>
    if h : c < r then x r ⟨c, h⟩ else if c = r then 1 else 0
  have hLlow : L.BlockTriangular OrderDual.toDual := by
    intro r c hrc
    have hrc' : r < c := OrderDual.toDual_lt_toDual.mp hrc
    simp [L, not_lt.mpr hrc'.le, hrc'.ne']
  have hL1 : ∀ a, L a a = 1 := fun a => by simp [L]
  have hLdet : L.det = 1 := det_lowerUni hLlow hL1
  have hLu : IsUnit L.det := by rw [hLdet]; exact isUnit_one
  have hrow : ∀ r c : Fin n, c < r → (L * M) r c = 0 := by
    intro r c hcr
    have e1 : ∀ k, L r k * M k c =
        (if h : k < r then x r ⟨k, h⟩ * M k c else 0) + (if k = r then M k c else 0) := by
      intro k
      by_cases h : k < r
      · simp [L, h, h.ne]
      · by_cases h' : k = r
        · subst h'
          simp [L]
        · simp [L, h, h']
    have hsub : ∑ k : Fin n, (if h : k < r then x r ⟨k, h⟩ * M k c else 0) =
        ∑ j : Fin r, x r j * M (Fin.castLE r.isLt.le j) c := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map (Fin.castLEEmb r.isLt.le)))]
      · rw [Finset.sum_map]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hj : (Fin.castLEEmb r.isLt.le j) < r := by
          show (j : ℕ) < r
          exact j.isLt
        rw [dif_pos hj]
        rfl
      · intro k _ hk
        have hk' : ¬ k < r := by
          intro h
          apply hk
          exact Finset.mem_map.mpr ⟨⟨k, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
        rw [dif_neg hk']
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => e1 k, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ r (fun k => M k c), if_pos (Finset.mem_univ _), hsub]
    have h := hx r ⟨c, hcr⟩
    have hc : Fin.castLE r.isLt.le (⟨c, hcr⟩ : Fin r) = c := Fin.ext rfl
    rw [hc] at h
    rw [h]
    ring
  refine ⟨L⁻¹, L * M, inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero), ?_, ?_, ?_, ?_⟩
  · intro a
    have h1 : (L * L⁻¹) a a = 1 := by
      rw [Matrix.mul_nonsing_inv L hLu]
      simp
    rw [Matrix.mul_apply, Finset.sum_eq_single a] at h1
    · rwa [hL1, one_mul] at h1
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · have h0 : L⁻¹ k a = 0 := inv_blockTriangular hLlow (by rw [hLdet]; exact one_ne_zero)
          (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, mul_zero]
      · have h0 : L a k = 0 := hLlow (OrderDual.toDual_lt_toDual.mpr h)
        rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · intro r c hcr
    exact hrow r c hcr
  · rw [Matrix.det_mul, hLdet, one_mul, ← lminor_last']
    exact hM _
  · rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul L hLu, Matrix.one_mul]

end Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}

def Mt (v : Ix ι r → ℂ) (τ : ι) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => v (τ, a, b)

def BC (ι : Type*) [Fintype ι] (r : ℕ) : Set (Ix ι r → ℂ) := {v | ∀ τ, ∀ i : Fin (r + 1), lminor (Mt v τ) i ≠ 0}

def sS (ι : Type*) (r : ℕ) : Set (Ix ι r → ℂ) := {w | ∀ τ b, w (τ, b, b) ≠ 0}

/- English proof (translation)
Use extensionality with `a b`. Both sides reduce to the same expression.
-/
lemma Mt_lu (w : Ix ι r → ℂ) (τ : ι) : Mt (lu w) τ = (1 + sl w τ) * up w τ := by
  ext a b
  rfl

/- English proof (translation)
Introduce `i j hij`. Establish `hij' : i < j` using `OrderDual.toDual_lt_toDual.mp hij`. Simplify using `[sl, Matrix.one_apply_ne hij'.ne, not_lt.mpr hij'.le]`.
-/
lemma one_add_sl_low (w : Ix ι r → ℂ) (τ : ι) : (1 + sl w τ).BlockTriangular OrderDual.toDual := by
  intro i j hij
  have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
  simp [sl, Matrix.one_apply_ne hij'.ne, not_lt.mpr hij'.le]

/- English proof (translation)
Simplify using `[sl]`.
-/
lemma one_add_sl_diag (w : Ix ι r → ℂ) (τ : ι) (a : Fin r) : (1 + sl w τ) a a = 1 := by
  simp [sl]

/- English proof (translation)
Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Simplify using `[up, hij']`.
-/
lemma up_upper (w : Ix ι r → ℂ) (τ : ι) : (up w τ).BlockTriangular id := by
  intro i j hij
  have hij' : j < i := hij
  simp [up, hij']

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular (up_upper w τ)]`. Simplify using `[up]`.
-/
lemma det_up (w : Ix ι r → ℂ) (τ : ι) : (up w τ).det = ∏ b, w (τ, b, b) := by
  rw [Matrix.det_of_upperTriangular (up_upper w τ)]
  simp [up]

/- English proof (translation)
Rewrite using `[det_up]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun b _ => hw τ b`.
-/
lemma det_up_ne {w : Ix ι r → ℂ} (hw : w ∈ sS ι r) (τ : ι) : (up w τ).det ≠ 0 := by
  rw [det_up]
  exact Finset.prod_ne_zero_iff.mpr fun b _ => hw τ b

/- English proof (translation)
Use function extensionality and compare the values at `i`. Take `⟨τ, a, b⟩` from `i`. Distinguish the cases in `hba : b < a`. Establish `h` using `congrFun (congrFun (h1 τ) a) b`. Simplify `h` using `[sl, hba]`.

Establish `h` using `congrFun (congrFun (h2 τ) a) b`. Simplify `h` using `[up, hba]`.
-/
lemma eq_of_sl_up {w w' : Ix ι r → ℂ} (h1 : ∀ τ, sl w τ = sl w' τ) (h2 : ∀ τ, up w τ = up w' τ) : w = w' := by
  funext i
  obtain ⟨τ, a, b⟩ := i
  by_cases hba : b < a
  · have h := congrFun (congrFun (h1 τ) a) b
    simpa [sl, hba] using h
  · have h := congrFun (congrFun (h2 τ) a) b
    simpa [up, hba] using h

/- English proof (translation)
Introduce `w hw w' hw' h`. Establish `key : ∀ τ, (1 + sl w τ) = (1 + sl w' τ) ∧ up w τ = up w' τ`. Introduce `τ`. Establish `hM : (1 + sl w τ) * up w τ = (1 + sl w' τ) * up w' τ`. Rewrite using `[← Mt_lu, ← Mt_lu, h]`.

Conclude with `lu_unique (one_add_sl_low w τ) (one_add_sl_diag w τ) (one_add_sl_low w' τ) (one_add_sl_diag w' τ) (up_upper w τ) (up_upper w' τ) (det_up_ne hw' τ) hM`. Conclude with `eq_of_sl_up (fun τ => add_left_cancel (key τ).1) (fun τ => (key τ).2)`.
-/
theorem lu_injOn : Set.InjOn (lu (ι := ι) (r := r)) (sS ι r) := by
  intro w hw w' hw' h
  have key : ∀ τ, (1 + sl w τ) = (1 + sl w' τ) ∧ up w τ = up w' τ := by
    intro τ
    have hM : (1 + sl w τ) * up w τ = (1 + sl w' τ) * up w' τ := by
      rw [← Mt_lu, ← Mt_lu, h]
    exact lu_unique (one_add_sl_low w τ) (one_add_sl_diag w τ) (one_add_sl_low w' τ)
      (one_add_sl_diag w' τ) (up_upper w τ) (up_upper w' τ) (det_up_ne hw' τ) hM
  exact eq_of_sl_up (fun τ => add_left_cancel (key τ).1) (fun τ => (key τ).2)

/- English proof (translation)
Introduce `v hv`. Use `choose N U hN hN1 hU hUd hNU using fun τ => lu_exists (M := Mt v τ) (hv τ)`. Use `⟨fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ b show (if b < b then N τ b b else U τ b b) ≠ 0`. Rewrite using `[if_neg (lt_irrefl b)]`.

Introduce `h0`. Establish `hdet : (U τ).det = ∏ b, U τ b b` using `Matrix.det_of_upperTriangular (hU τ)`. Conclude with `hUd τ (hdet ▸ Finset.prod_eq_zero (Finset.mem_univ b) h0)`. Establish `hsl : ∀ τ, 1 + sl (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2) τ = N τ`. Introduce `τ`.

Use extensionality with `a b`. Break down `lt_trichotomy b a with h | h | h` into its components or cases. Simplify using `[sl, h, Matrix.one_apply_ne (ne_of_gt h)]`. Substitute `h` using the available equality. Simplify using `[sl, hN1]`.

Establish `h0 : N τ a b = 0` using `hN τ (OrderDual.toDual_lt_toDual.mpr h)`. Simplify using `[sl, not_lt.mpr h.le, Matrix.one_apply_ne (ne_of_lt h), h0]`. Establish `hup : ∀ τ, up (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2) τ = U τ`. Introduce `τ`. Use extensionality with `a b`.

Distinguish the cases in `h : b < a`. Establish `h0 : U τ a b = 0` using `hU τ h`. Simplify using `[up, h, h0]`. Simplify using `[up, h]`. Use function extensionality and compare the values at `i`.

Take `⟨τ, a, b⟩` from `i`. Use `show ((1 + sl _ τ) * up _ τ : Matrix (Fin r) (Fin r) ℂ) a b = v (τ, a, b)`. Rewrite using `[hsl, hup, hNU]`. Both sides reduce to the same expression.
-/
theorem BC_subset_image : BC ι r ⊆ lu '' sS ι r := by
  intro v hv
  choose N U hN hN1 hU hUd hNU using fun τ => lu_exists (M := Mt v τ) (hv τ)
  refine ⟨fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2 else U i.1 i.2.1 i.2.2, ?_, ?_⟩
  · intro τ b
    show (if b < b then N τ b b else U τ b b) ≠ 0
    rw [if_neg (lt_irrefl b)]
    intro h0
    have hdet : (U τ).det = ∏ b, U τ b b := Matrix.det_of_upperTriangular (hU τ)
    exact hUd τ (hdet ▸ Finset.prod_eq_zero (Finset.mem_univ b) h0)
  · have hsl : ∀ τ, 1 + sl (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = N τ := by
      intro τ
      ext a b
      rcases lt_trichotomy b a with h | h | h
      · simp [sl, h, Matrix.one_apply_ne (ne_of_gt h)]
      · subst h
        simp [sl, hN1]
      · have h0 : N τ a b = 0 := hN τ (OrderDual.toDual_lt_toDual.mpr h)
        simp [sl, not_lt.mpr h.le, Matrix.one_apply_ne (ne_of_lt h), h0]
    have hup : ∀ τ, up (fun i => if i.2.2 < i.2.1 then N i.1 i.2.1 i.2.2
        else U i.1 i.2.1 i.2.2) τ = U τ := by
      intro τ
      ext a b
      by_cases h : b < a
      · have h0 : U τ a b = 0 := hU τ h
        simp [up, h, h0]
      · simp [up, h]
    funext i
    obtain ⟨τ, a, b⟩ := i
    show ((1 + sl _ τ) * up _ τ : Matrix (Fin r) (Fin r) ℂ) a b = v (τ, a, b)
    rw [hsl, hup, hNU]
    rfl

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
