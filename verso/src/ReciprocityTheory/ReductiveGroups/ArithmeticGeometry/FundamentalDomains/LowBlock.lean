import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NsqMulVecLeOpN

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Use `set g : ℕ → ℂ := fun i => if h : i < r then f ⟨i, h⟩ else 0 with hg`. Establish `e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i`. Rewrite using `[Finset.sum_range]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [hg, dif_pos j.isLt]`.

Establish `e2 : ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range (X.p0 + (r - X.p0)), g i`. Rewrite using `[Nat.add_sub_cancel' X.p0_le]`. Rewrite using `[e1, e2, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Establish `ha : (a : ℕ) < r` using `lt_of_lt_of_le a.isLt X.p0_le`. Simplify using `only [hg, dif_pos ha]`. Both sides reduce to the same expression. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `hm : X.p0 + (m : ℕ) < r` using `by have := m.isLt; have := X.p0_le; omega`.

Simplify using `only [hg, dif_pos hm]`.
-/
lemma sum_split (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) +
      ∑ m : Fin (r - X.p0), f ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩ := by
  set g : ℕ → ℂ := fun i => if h : i < r then f ⟨i, h⟩ else 0 with hg
  have e1 : ∑ j, f j = ∑ i ∈ Finset.range r, g i := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hg, dif_pos j.isLt]
  have e2 : ∑ i ∈ Finset.range r, g i = ∑ i ∈ Finset.range (X.p0 + (r - X.p0)), g i := by
    rw [Nat.add_sub_cancel' X.p0_le]
  rw [e1, e2, Finset.sum_range_add, Finset.sum_range, Finset.sum_range]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    have ha : (a : ℕ) < r := lt_of_lt_of_le a.isLt X.p0_le
    simp only [hg, dif_pos ha]
    rfl
  · refine Finset.sum_congr rfl fun m _ => ?_
    have hm : X.p0 + (m : ℕ) < r := by have := m.isLt; have := X.p0_le; omega
    simp only [hg, dif_pos hm]

def nI (m : Fin (r - X.p0)) : Fin r := ⟨X.p0 + m, by have := m.isLt; have := X.p0_le; omega⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma nI_val_eq_p0_add (m : Fin (r - X.p0)) : ((nI X m : Fin r) : ℕ) = X.p0 + m := rfl

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0)`. Simplify using `only [Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]`.

Distinguish the cases in `h : a = c`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun e => h (Fin.castLE_injective X.p0_le e))]`.
-/
lemma L_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) = if a = c then 1 else 0 := by
  have ha := a.isLt
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0) := by
    simp only [Fin.val_castLE]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : a = c
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (Fin.castLE_injective X.p0_le e))]

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `h1 : (Fin.castLE X.p0_le a : Fin r) ≠ nI X m`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Rewrite `h'` using `[Fin.val_castLE, nI_val_eq_p0_add]`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((nI X m : Fin r) : ℕ) < X.p0)`. Rewrite using `[Fin.val_castLE, nI_val_eq_p0_add]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_neg h2, add_zero]`.
-/
lemma L_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    X.lowBlock Z τ (Fin.castLE X.p0_le a) (nI X m) = 0 := by
  have ha := a.isLt
  have h1 : (Fin.castLE X.p0_le a : Fin r) ≠ nI X m := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : ¬ (X.p0 ≤ ((Fin.castLE X.p0_le a : Fin r) : ℕ) ∧ ((nI X m : Fin r) : ℕ) < X.p0) := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_neg h2, add_zero]

/- English proof (translation)
Establish `hc` using `c.isLt`. Establish `h1 : nI X m ≠ (Fin.castLE X.p0_le c : Fin r)`. Introduce `h`. Establish `h'` using `congrArg Fin.val h`. Rewrite `h'` using `[Fin.val_castLE, nI_val_eq_p0_add]`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0`. Rewrite using `[Fin.val_castLE, nI_val_eq_p0_add]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_pos h2, zero_add]`.

Conclude with `congrArg₂ (Z τ) (Fin.ext (by simp [nI_val_eq_p0_add])) (Fin.ext (by simp))`.
-/
lemma L_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    X.lowBlock Z τ (nI X m) (Fin.castLE X.p0_le c) = Z τ m c := by
  have hc := c.isLt
  have h1 : nI X m ≠ (Fin.castLE X.p0_le c : Fin r) := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_castLE, nI_val_eq_p0_add] at h'
    omega
  have h2 : X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 := by
    rw [Fin.val_castLE, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, if_neg h1, dif_pos h2, zero_add]
  exact congrArg₂ (Z τ) (Fin.ext (by simp [nI_val_eq_p0_add])) (Fin.ext (by simp))

/- English proof (translation)
Establish `h2 : ¬ (X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((nI X m' : Fin r) : ℕ) < X.p0)`. Rewrite using `[nI_val_eq_p0_add, nI_val_eq_p0_add]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]`. Distinguish the cases in `h : m = m'`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `h1 : nI X m ≠ nI X m'`. Introduce `e`. Establish `h'` using `congrArg Fin.val e`.

Rewrite `h'` using `[nI_val_eq_p0_add, nI_val_eq_p0_add]`. Conclude with `h (Fin.ext (by omega))`. Rewrite using `[if_neg h, if_neg h1]`.
-/
lemma L_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    X.lowBlock Z τ (nI X m) (nI X m') = if m = m' then 1 else 0 := by
  have h2 : ¬ (X.p0 ≤ ((nI X m : Fin r) : ℕ) ∧ ((nI X m' : Fin r) : ℕ) < X.p0) := by
    rw [nI_val_eq_p0_add, nI_val_eq_p0_add]
    omega
  simp only [Data.lowBlock, Matrix.of_apply, dif_neg h2, add_zero]
  by_cases h : m = m'
  · subst h
    simp
  · have h1 : nI X m ≠ nI X m' := by
      intro e
      have h' := congrArg Fin.val e
      rw [nI_val_eq_p0_add, nI_val_eq_p0_add] at h'
      exact h (Fin.ext (by omega))
    rw [if_neg h, if_neg h1]

/- English proof (translation)
Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.sgn, a.isLt]`.
-/
lemma sgn_p (a : Fin X.p0) : sgn X.p0 ((Fin.castLE X.p0_le a : Fin r) : ℕ) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn, a.isLt]

/- English proof (translation)
Rewrite using `[nI_val_eq_p0_add]`. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.sgn]`.
-/
lemma sgn_n (m : Fin (r - X.p0)) : sgn X.p0 ((nI X m : Fin r) : ℕ) = -1 := by
  rw [nI_val_eq_p0_add]
  simp [ReciprocityTheory.ChartRestriction.G.FD.sgn]

def Gp (Z : X.Coord) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (X.lowBlock Z τ)ᵀ * Matrix.diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) *
    (X.lowBlock Z τ).map (starRingEnd ℂ)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
private lemma gram_eq_upper_bounds (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Establish `h` using `ho τ`. Rewrite `h` using `[gram_eq_upper_bounds]`. Establish `hm : mat (X.xZ x Z) τ = mat x τ * X.lowBlock Z τ` using `rfl`. Rewrite using `[gram_eq_upper_bounds, hm, Gp, ← h, Matrix.transpose_mul, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
lemma gram_xZ {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := by
  have h := ho τ
  rw [gram_eq_upper_bounds] at h
  have hm : mat (X.xZ x Z) τ = mat x τ * X.lowBlock Z τ := rfl
  rw [gram_eq_upper_bounds, hm, Gp, ← h, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Gp, Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]`.
-/
lemma Gp_apply (Z : X.Coord) (τ : X.Ψ) (a c : Fin r) :
    Gp X Z τ a c = ∑ j, X.lowBlock Z τ j a * ((sgn X.p0 (j : ℕ) : ℝ) : ℂ) * conj (X.lowBlock Z τ j c) := by
  rw [Gp, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]

/- English proof (translation)
The claim follows from `sum_split X f`.
-/
private lemma sum_eq_sum_castLE_add_sum_nI (f : Fin r → ℂ) :
    ∑ j, f j = ∑ a : Fin X.p0, f (Fin.castLE X.p0_le a) + ∑ m : Fin (r - X.p0), f (nI X m) :=
  sum_split X f

/- English proof (translation)
Rewrite using `[Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]`. Simplify using `only [L_pp X, L_np X, sgn_p X, sgn_n X]`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Simplify using `[sub_eq_add_neg]`.

Simplify using `[hac, Ne.symm hac, sub_eq_add_neg]`.
-/
lemma Gp_pp (Z : X.Coord) (τ : X.Ψ) (a c : Fin X.p0) :
    Gp X Z τ (Fin.castLE X.p0_le a) (Fin.castLE X.p0_le c) =
      (if a = c then 1 else 0) - ∑ m, Z τ m a * conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_np X, sgn_p X, sgn_n X]
  by_cases hac : a = c
  · subst hac
    simp [sub_eq_add_neg]
  · simp [hac, Ne.symm hac, sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]`. Simplify using `only [L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]`. Simplify using the standard rewrite rules.
-/
lemma Gp_np (Z : X.Coord) (τ : X.Ψ) (m : Fin (r - X.p0)) (c : Fin X.p0) :
    Gp X Z τ (nI X m) (Fin.castLE X.p0_le c) = -conj (Z τ m c) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

/- English proof (translation)
Rewrite using `[Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]`. Simplify using `only [L_pp X, L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]`. Simplify using the standard rewrite rules.
-/
lemma Gp_pn (Z : X.Coord) (τ : X.Ψ) (a : Fin X.p0) (m : Fin (r - X.p0)) :
    Gp X Z τ (Fin.castLE X.p0_le a) (nI X m) = -Z τ m a := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pp X, L_pn X, L_np X, L_nn X, sgn_p X, sgn_n X]
  simp

/- English proof (translation)
Rewrite using `[Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]`. Simplify using `only [L_pn X, L_nn X, sgn_p X, sgn_n X]`. Distinguish the cases in `h : m = m'`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`.
-/
lemma Gp_nn (Z : X.Coord) (τ : X.Ψ) (m m' : Fin (r - X.p0)) :
    Gp X Z τ (nI X m) (nI X m') = -(if m = m' then 1 else 0) := by
  rw [Gp_apply X, sum_eq_sum_castLE_add_sum_nI X]
  simp only [L_pn X, L_nn X, sgn_p X, sgn_n X]
  by_cases h : m = m'
  · subst h
    simp
  · simp [h, Ne.symm h]

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
