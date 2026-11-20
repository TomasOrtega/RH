import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.SmallRadAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.BallSub
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.ContractB

noncomputable section

open ValuativeRel Matrix GlobalTheory.SplitWeil UpperTheory.ConvolutionTheory.Loc UpperTheory.Gal.Join
open GlobalTheory.SmGL hiding iwahori

namespace UpperTheory.Gal.InertialTypesAlt.L

section Mat

variable {k : Type} [Field k] {n : ℕ}

private def colM (p : Fin n) (a : Fin n → k) : Matrix (Fin n) (Fin n) k := fun i j => if j = p then a i else 0

private def rowM (p : Fin n) (b : Fin n → k) : Matrix (Fin n) (Fin n) k := fun i j => if i = p then b j else 0

/- English proof (translation)
Simplify using `[Matrix.mul_apply, colM, ite_mul]`.
-/
private theorem colM_mul (p : Fin n) (a : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (colM p a * M) i j = a i * M p j := by
  simp [Matrix.mul_apply, colM, ite_mul]

/- English proof (translation)
Simplify using `[Matrix.mul_apply, rowM, mul_ite]`.
-/
private theorem mul_rowM (p : Fin n) (b : Fin n → k) (M : Matrix (Fin n) (Fin n) k) (i j : Fin n) :
    (M * rowM p b) i j = M i p * b j := by
  simp [Matrix.mul_apply, rowM, mul_ite]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[colM_mul]`. Simplify using `[colM, h]`.
-/
private theorem colM_sq {p : Fin n} {a : Fin n → k} (h : a p = 0) : colM p a * colM p a = 0 := by
  ext i j
  rw [colM_mul]
  simp [colM, h]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[mul_rowM]`. Simplify using `[rowM, h]`.
-/
private theorem rowM_sq {p : Fin n} {b : Fin n → k} (h : b p = 0) : rowM p b * rowM p b = 0 := by
  ext i j
  rw [mul_rowM]
  simp [rowM, h]

private def nilU (A : Matrix (Fin n) (Fin n) k) (h : A * A = 0) : GL (Fin n) k where
  val := 1 + A
  inv := 1 - A
  val_inv := by simp [add_mul, mul_sub, h]
  inv_val := by simp [sub_mul, mul_add, h]

/- English proof (translation)
Use `(mem_unipRad (e := opp (points (Fin n)))).trans (and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ _ => ?_⟩)` and prove the remaining obligations. Conclude with `(h i () ()).trans (by simp)`. Conclude with `(h i).trans (by simp)`.
-/
private theorem mem_low {g : GL (Fin n) k} :
    g ∈ unipBLower k (Fin n) ↔ (∀ i j, i < j → (g : Matrix (Fin n) (Fin n) k) i j = 0) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) k) i i = 1 := by
  refine (mem_unipRad (e := opp (points (Fin n)))).trans (and_congr Iff.rfl ⟨fun h i => ?_, fun h i _ _ => ?_⟩)
  · exact (h i () ()).trans (by simp)
  · exact (h i).trans (by simp)

/- English proof (translation)
Rewrite using `[← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify using the standard rewrite rules.
-/
private theorem conj_entry (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    ((diagT k (Fin n) t * u * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t i : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t j : k)⁻¹ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

/- English proof (translation)
Rewrite using `[← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem conj_entry' (t : Fin n → kˣ) (u : GL (Fin n) k) (i j : Fin n) :
    (((diagT k (Fin n) t)⁻¹ * u * diagT k (Fin n) t : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (t j : k) * (u : Matrix (Fin n) (Fin n) k) i j * (t i : k)⁻¹ := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp
  ring

end Mat

section Val

variable {k : Type} [Field k] [ValuativeRel k]

/- English proof (translation)
Establish `h1 : valuation k (x - 1) < valuation k (1 : k)` using `by simpa using h.trans_lt hr`. Establish `e` using `Valuation.map_add_eq_of_lt_left (valuation k) h1`. Simplify using `using e`.
-/
private theorem val_one_of {r : ValueGroupWithZero k} (hr : r < 1) {x : k} (h : valuation k (x - 1) ≤ r) :
    valuation k x = 1 := by
  have h1 : valuation k (x - 1) < valuation k (1 : k) := by simpa using h.trans_lt hr
  have e := Valuation.map_add_eq_of_lt_left (valuation k) h1
  simpa using e

/- English proof (translation)
Establish `hz : 0 < valuation k (z : k)` using `zero_lt_iff.2 (by simp)`. Rewrite using `[map_mul, map_mul, map_inv₀, mul_comm (valuation k (x : k)), mul_assoc]`. Use `mul_le_of_le_one_right' ?_` and prove the remaining obligations. Rewrite using `[← div_eq_mul_inv]`. Conclude with `(div_le_one₀ hz).2 h`.
-/
private theorem val_le {x z : kˣ} (h : valuation k (x : k) ≤ valuation k (z : k)) (y : k) :
    valuation k ((x : k) * y * (z : k)⁻¹) ≤ valuation k y := by
  have hz : 0 < valuation k (z : k) := zero_lt_iff.2 (by simp)
  rw [map_mul, map_mul, map_inv₀, mul_comm (valuation k (x : k)), mul_assoc]
  refine mul_le_of_le_one_right' ?_
  rw [← div_eq_mul_inv]
  exact (div_le_one₀ hz).2 h

end Val

section Fact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Establish `hmem : ∀ g, g ∈ K ↔ g ∈ ball n r` using `fun g => by rw [← SetLike.mem_coe, hK]`. Establish `hd1 : ∀ g ∈ K, ∀ i, valuation k ((g : Matrix (Fin n) (Fin n) k) i i) = 1` using `fun g hg i => val_one_of hr (by simpa using (hmem g).1 hg i i)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`.

Introduce `_ g hg hc`. Establish `h0 : ∀ i, (g : Matrix (Fin n) (Fin n) k) i i ≠ 0` using `fun i h => by`. Use `hd1 g hg i` as an intermediate fact. Simplify using `[h] at this`. Set `d : Fin n → kˣ` to `fun i => Units.mk0 _ (h0 i)`.

Establish `e : g = diagT k (Fin n) d`. Use extensionality with `i j`. Rewrite using `[val_diagT]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[d]`. Rewrite using `[diagonal_apply_ne _ h]`. Conclude with `hc i j h (Or.inl (Nat.zero_le _))`. Conclude with `⟨1, one_mem _, d, e ▸ hg, 1, one_mem _, by simpa using e⟩`. Consider the case `succ m ih`.

Introduce `hm g hg hc`. Set `p : Fin n` to `⟨m, hm⟩`. Establish `hgr : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r` using `(hmem g).1 hg`. Establish `hpp : valuation k ((g : Matrix (Fin n) (Fin n) k) p p) = 1` using `hd1 g hg p`. Establish `hp0 : (g : Matrix (Fin n) (Fin n) k) p p ≠ 0` using `fun h => by simp [h] at hpp`.

Set `a : Fin n → k` to `fun i => if i < p then (g : Matrix (Fin n) (Fin n) k) i p / (g : Matrix (Fin n) (Fin n) k) p p else 0`. Set `b : Fin n → k` to `fun j => if j < p then (g : Matrix (Fin n) (Fin n) k) p j / (g : Matrix (Fin n) (Fin n) k) p p else 0`. Establish `ap : a p = 0` using `by simp [a]`. Establish `bp : b p = 0` using `by simp [b]`. Establish `ha : ∀ i, valuation k (a i) ≤ r` using `fun i => by`.

Simplify using `only [a]`. Use `split_ifs with h`. Use `hgr i p` as an intermediate fact. Rewrite `this` using `[one_apply_ne h.ne, sub_zero]`. Rewrite using `[map_div₀, hpp, div_one]` and apply the resulting hypothesis.

Simplify using the standard rewrite rules. Establish `hb : ∀ j, valuation k (b j) ≤ r` using `fun j => by`. Simplify using `only [b]`. Use `split_ifs with h`. Use `hgr p j` as an intermediate fact.

Rewrite `this` using `[one_apply_ne h.ne', sub_zero]`. Rewrite using `[map_div₀, hpp, div_one]` and apply the resulting hypothesis. Simplify using the standard rewrite rules. Set `U : GL (Fin n) k` to `nilU (colM p a) (colM_sq ap)`. Set `L : GL (Fin n) k` to `nilU (rowM p b) (rowM_sq bp)`.

Establish `hUv : (U : Matrix (Fin n) (Fin n) k) = 1 + colM p a` using `rfl`. Establish `hLv : (L : Matrix (Fin n) (Fin n) k) = 1 + rowM p b` using `rfl`. Establish `hUi : ((U⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 - colM p a` using `rfl`. Establish `hLi : ((L⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 - rowM p b` using `rfl`. Establish `hU : U ∈ K ⊓ unipB k (Fin n)`.

Use `⟨(hmem U).2 fun i j => ?_, (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hUv, Matrix.add_apply, add_sub_cancel_left]`. Simplify using `only [colM]`. Use `split_ifs`. Conclude with `ha i`.

Simplify using the standard rewrite rules. Rewrite using `[hUv, Matrix.add_apply, one_apply_ne hji.ne', zero_add]`. Simplify using `only [colM]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify using `[a, hji.not_gt]`. Both sides reduce to the same expression. Rewrite using `[hUv, Matrix.add_apply, one_apply_eq]`. Simplify using `only [colM]`. Use `split_ifs with h`.

Substitute `h` using the available equality. Simplify using `[ap]`. Simplify using the standard rewrite rules. Establish `hL : L ∈ K ⊓ unipBLower k (Fin n)`. Use `⟨(hmem L).2 fun i j => ?_, mem_low.2 ⟨fun i j hij => ?_, fun i => ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hLv, Matrix.add_apply, add_sub_cancel_left]`. Simplify using `only [rowM]`. Use `split_ifs`. Conclude with `hb j`. Simplify using the standard rewrite rules.

Rewrite using `[hLv, Matrix.add_apply, one_apply_ne hij.ne, zero_add]`. Simplify using `only [rowM]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[b, hij.not_gt]`.

Both sides reduce to the same expression. Rewrite using `[hLv, Matrix.add_apply, one_apply_eq]`. Simplify using `only [rowM]`. Use `split_ifs with h`. Substitute `h` using the available equality.

Simplify using `[bp]`. Simplify using the standard rewrite rules. Establish `hH : ∀ i j, (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j = (g : Matrix (Fin n) (Fin n) k) i j - a i * (g : Matrix (Fin n) (Fin n) k) p j` using `fun i j => by`. Rewrite using `[Units.val_mul, hUi, sub_mul, one_mul, Matrix.sub_apply, colM_mul]`. Establish `hE : ∀ i j, (((U⁻¹ * g * L⁻¹ : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j = (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j - (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i p * b j` using `fun i j => by`.

Rewrite using `[Units.val_mul _ (L⁻¹), hLi, mul_sub, mul_one, Matrix.sub_apply, mul_rowM]`. Establish `hclean : ∀ i j : Fin n, i ≠ j → (m ≤ i.1 ∨ m ≤ j.1) → (((U⁻¹ * g * L⁻¹ : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j = 0`. Introduce `i j hij hor`. Rewrite using `[hE, hH, hH]`. Distinguish the cases in `hi : m + 1 ≤ i.1`.

Establish `hip : ¬ i < p` using `fun h => by`. Establish `: i.1 < m` using `h`. Use linear arithmetic over natural numbers and integers. Establish `hne : i ≠ p` using `fun h => by`. Establish `: i.1 = m` using `congrArg Fin.val h`.

Use linear arithmetic over natural numbers and integers. Establish `e1` using `hc i j hij (Or.inl hi)`. Establish `e2` using `hc i p hne (Or.inl hi)`. Simplify using `[a, hip, e1, e2]`. Distinguish the cases in `hj : m + 1 ≤ j.1`.

Establish `hjp : ¬ j < p` using `fun h => by`. Establish `: j.1 < m` using `h`. Use linear arithmetic over natural numbers and integers. Establish `hne : p ≠ j` using `fun h => by`. Establish `: m = j.1` using `congrArg Fin.val h`.

Use linear arithmetic over natural numbers and integers. Establish `e1` using `hc i j hij (Or.inr hj)`. Establish `e2` using `hc p j hne (Or.inr hj)`. Simplify using `[b, hjp, e1, e2]`. Break down `hor with h | h` into its components or cases.

Establish `hi' : i = p` using `Fin.ext (by simp only [p]; omega)`. Substitute `hi'` using the available equality. Establish `hjp : j < p` using `lt_of_le_of_ne (Fin.le_def.2 (by simp only [p]; omega)) (Ne.symm hij)`. Establish `e : (g : Matrix (Fin n) (Fin n) k) p p * ((g : Matrix (Fin n) (Fin n) k) p j / (g : Matrix (Fin n) (Fin n) k) p p) = (g : Matrix (Fin n) (Fin n) k) p j` using `by field_simp`. Simplify using `only [ap, zero_mul, sub_zero, b, if_pos hjp, e, sub_self]`.

Establish `hj' : j = p` using `Fin.ext (by simp only [p]; omega)`. Substitute `hj'` using the available equality. Establish `hip : i < p` using `lt_of_le_of_ne (Fin.le_def.2 (by simp only [p]; omega)) hij`. Establish `e : (g : Matrix (Fin n) (Fin n) k) i p / (g : Matrix (Fin n) (Fin n) k) p p * (g : Matrix (Fin n) (Fin n) k) p p = (g : Matrix (Fin n) (Fin n) k) i p` using `by field_simp`. Simplify using `only [bp, mul_zero, sub_zero, a, if_pos hip, e, sub_self]`.

Take `⟨u, hu, d, hd, c, hc', e⟩` from `ih (by omega) (U⁻¹ * g * L⁻¹) (K.mul_mem (K.mul_mem (K.inv_mem hU.1) hg) (K.inv_mem hL.1)) hclean`. Use `⟨U * u, (K ⊓ unipB k (Fin n)).mul_mem hU hu, d, hd, c * L, (K ⊓ unipBLower k (Fin n)).mul_mem hc' hL, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem nat_mul_factorial_bound {r : ValueGroupWithZero k} (hr : r < 1) (K : Subgroup (GL (Fin n) k))
    (hK : (K : Set (GL (Fin n) k)) = ball n r) :
    ∀ m, m ≤ n → ∀ g ∈ K,
      (∀ i j : Fin n, i ≠ j → (m ≤ i.1 ∨ m ≤ j.1) → (g : Matrix (Fin n) (Fin n) k) i j = 0) →
      ∃ u ∈ K ⊓ unipB k (Fin n), ∃ d, diagT k (Fin n) d ∈ K ∧ ∃ c ∈ K ⊓ unipBLower k (Fin n),
        g = u * diagT k (Fin n) d * c := by
  have hmem : ∀ g, g ∈ K ↔ g ∈ ball n r := fun g => by rw [← SetLike.mem_coe, hK]
  have hd1 : ∀ g ∈ K, ∀ i, valuation k ((g : Matrix (Fin n) (Fin n) k) i i) = 1 := fun g hg i =>
    val_one_of hr (by simpa using (hmem g).1 hg i i)
  intro m
  induction m with
  | zero =>
    intro _ g hg hc
    have h0 : ∀ i, (g : Matrix (Fin n) (Fin n) k) i i ≠ 0 := fun i h => by
      have := hd1 g hg i
      simp [h] at this
    let d : Fin n → kˣ := fun i => Units.mk0 _ (h0 i)
    have e : g = diagT k (Fin n) d := by
      ext i j
      rw [val_diagT]
      by_cases h : i = j
      · subst h
        simp [d]
      · rw [diagonal_apply_ne _ h]
        exact hc i j h (Or.inl (Nat.zero_le _))
    exact ⟨1, one_mem _, d, e ▸ hg, 1, one_mem _, by simpa using e⟩
  | succ m ih =>
    intro hm g hg hc
    let p : Fin n := ⟨m, hm⟩
    have hgr : ∀ i j, valuation k ((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j) ≤ r :=
      (hmem g).1 hg
    have hpp : valuation k ((g : Matrix (Fin n) (Fin n) k) p p) = 1 := hd1 g hg p
    have hp0 : (g : Matrix (Fin n) (Fin n) k) p p ≠ 0 := fun h => by simp [h] at hpp
    let a : Fin n → k := fun i => if i < p then (g : Matrix (Fin n) (Fin n) k) i p / (g : Matrix (Fin n) (Fin n) k) p p else 0
    let b : Fin n → k := fun j => if j < p then (g : Matrix (Fin n) (Fin n) k) p j / (g : Matrix (Fin n) (Fin n) k) p p else 0
    have ap : a p = 0 := by simp [a]
    have bp : b p = 0 := by simp [b]
    have ha : ∀ i, valuation k (a i) ≤ r := fun i => by
      simp only [a]
      split_ifs with h
      · have := hgr i p
        rw [one_apply_ne h.ne, sub_zero] at this
        rwa [map_div₀, hpp, div_one]
      · simp
    have hb : ∀ j, valuation k (b j) ≤ r := fun j => by
      simp only [b]
      split_ifs with h
      · have := hgr p j
        rw [one_apply_ne h.ne', sub_zero] at this
        rwa [map_div₀, hpp, div_one]
      · simp
    let U : GL (Fin n) k := nilU (colM p a) (colM_sq ap)
    let L : GL (Fin n) k := nilU (rowM p b) (rowM_sq bp)
    have hUv : (U : Matrix (Fin n) (Fin n) k) = 1 + colM p a := rfl
    have hLv : (L : Matrix (Fin n) (Fin n) k) = 1 + rowM p b := rfl
    have hUi : ((U⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 - colM p a := rfl
    have hLi : ((L⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 - rowM p b := rfl
    have hU : U ∈ K ⊓ unipB k (Fin n) := by
      refine ⟨(hmem U).2 fun i j => ?_, (mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩⟩
      · rw [hUv, Matrix.add_apply, add_sub_cancel_left]
        simp only [colM]
        split_ifs
        · exact ha i
        · simp
      · rw [hUv, Matrix.add_apply, one_apply_ne hji.ne', zero_add]
        simp only [colM]
        split_ifs with h
        · subst h
          simp [a, hji.not_gt]
        · rfl
      · rw [hUv, Matrix.add_apply, one_apply_eq]
        simp only [colM]
        split_ifs with h
        · subst h
          simp [ap]
        · simp
    have hL : L ∈ K ⊓ unipBLower k (Fin n) := by
      refine ⟨(hmem L).2 fun i j => ?_, mem_low.2 ⟨fun i j hij => ?_, fun i => ?_⟩⟩
      · rw [hLv, Matrix.add_apply, add_sub_cancel_left]
        simp only [rowM]
        split_ifs
        · exact hb j
        · simp
      · rw [hLv, Matrix.add_apply, one_apply_ne hij.ne, zero_add]
        simp only [rowM]
        split_ifs with h
        · subst h
          simp [b, hij.not_gt]
        · rfl
      · rw [hLv, Matrix.add_apply, one_apply_eq]
        simp only [rowM]
        split_ifs with h
        · subst h
          simp [bp]
        · simp
    have hH : ∀ i j, (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j =
        (g : Matrix (Fin n) (Fin n) k) i j - a i * (g : Matrix (Fin n) (Fin n) k) p j := fun i j => by
      rw [Units.val_mul, hUi, sub_mul, one_mul, Matrix.sub_apply, colM_mul]
    have hE : ∀ i j, (((U⁻¹ * g * L⁻¹ : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j =
        (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j -
          (((U⁻¹ * g : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i p * b j := fun i j => by
      rw [Units.val_mul _ (L⁻¹), hLi, mul_sub, mul_one, Matrix.sub_apply, mul_rowM]
    have hclean : ∀ i j : Fin n, i ≠ j → (m ≤ i.1 ∨ m ≤ j.1) →
        (((U⁻¹ * g * L⁻¹ : GL (Fin n) k)) : Matrix (Fin n) (Fin n) k) i j = 0 := by
      intro i j hij hor
      rw [hE, hH, hH]
      by_cases hi : m + 1 ≤ i.1
      · have hip : ¬ i < p := fun h => by
          have : i.1 < m := h
          omega
        have hne : i ≠ p := fun h => by
          have : i.1 = m := congrArg Fin.val h
          omega
        have e1 := hc i j hij (Or.inl hi)
        have e2 := hc i p hne (Or.inl hi)
        simp [a, hip, e1, e2]
      by_cases hj : m + 1 ≤ j.1
      · have hjp : ¬ j < p := fun h => by
          have : j.1 < m := h
          omega
        have hne : p ≠ j := fun h => by
          have : m = j.1 := congrArg Fin.val h
          omega
        have e1 := hc i j hij (Or.inr hj)
        have e2 := hc p j hne (Or.inr hj)
        simp [b, hjp, e1, e2]
      rcases hor with h | h
      · have hi' : i = p := Fin.ext (by simp only [p]; omega)
        subst hi'
        have hjp : j < p := lt_of_le_of_ne (Fin.le_def.2 (by simp only [p]; omega)) (Ne.symm hij)
        have e : (g : Matrix (Fin n) (Fin n) k) p p * ((g : Matrix (Fin n) (Fin n) k) p j / (g : Matrix (Fin n) (Fin n) k) p p) =
            (g : Matrix (Fin n) (Fin n) k) p j := by field_simp
        simp only [ap, zero_mul, sub_zero, b, if_pos hjp, e, sub_self]
      · have hj' : j = p := Fin.ext (by simp only [p]; omega)
        subst hj'
        have hip : i < p := lt_of_le_of_ne (Fin.le_def.2 (by simp only [p]; omega)) hij
        have e : (g : Matrix (Fin n) (Fin n) k) i p / (g : Matrix (Fin n) (Fin n) k) p p * (g : Matrix (Fin n) (Fin n) k) p p =
            (g : Matrix (Fin n) (Fin n) k) i p := by field_simp
        simp only [bp, mul_zero, sub_zero, a, if_pos hip, e, sub_self]
    obtain ⟨u, hu, d, hd, c, hc', e⟩ := ih (by omega) (U⁻¹ * g * L⁻¹)
      (K.mul_mem (K.mul_mem (K.inv_mem hU.1) hg) (K.inv_mem hL.1)) hclean
    refine ⟨U * u, (K ⊓ unipB k (Fin n)).mul_mem hU hu, d, hd, c * L,
      (K ⊓ unipBLower k (Fin n)).mul_mem hc' hL, ?_⟩
    calc g = U * (U⁻¹ * g * L⁻¹) * L := by group
      _ = U * u * diagT k (Fin n) d * (c * L) := by rw [e]; group

end Fact

end UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Introduce `k _ _ _ _ n r h0 h1 K hK`. Establish `hmem : ∀ g, g ∈ K ↔ g ∈ ball n r` using `fun g => by rw [← SetLike.mem_coe, hK]`. Take `⟨K₀, e₀, ho, hc⟩` from `UpperTheory.ConvolutionTheory.Loc.ballSub k n r h0 h1`. Establish `eK : (K : Set (GL (Fin n) k)) = K₀` using `hK.trans e₀.symm`. Use `⟨⟨⟨eK ▸ hc, eK ▸ ho⟩, ?_, ?_, ?_⟩, fun t => ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Conclude with `UpperTheory.Gal.InertialTypesAlt.L.nat_mul_factorial_bound h1 K hK n le_rfl g hg fun i j _ h => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Introduce `t ht u hu`. Take `⟨hu1, hu2⟩` from `(mem_unipB k).1 hu.2`. Establish `hur` using `(hmem u).1 hu.1`. Use `(hmem _).2 fun i j => ?_` and prove the remaining obligations. Rewrite using `[UpperTheory.Gal.InertialTypesAlt.L.conj_entry]`.

Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[one_apply_ne h.ne, sub_zero]`. Use `hur i j` as an intermediate fact. Rewrite `this` using `[one_apply_ne h.ne, sub_zero]`. Conclude with `(UpperTheory.Gal.InertialTypesAlt.L.val_le (ht i j h) _).trans this`.

Substitute `h` using the available equality. Rewrite using `[hu2 i, mul_one, mul_inv_cancel₀ (t i).ne_zero, one_apply_eq, sub_self, map_zero]`. Conclude with `zero_le`. Rewrite using `[hu1 i j h, one_apply_ne h.ne']`. Simplify using the standard rewrite rules.

Introduce `t ht c hc'`. Take `⟨hc1, hc2⟩` from `UpperTheory.Gal.InertialTypesAlt.L.mem_low.1 hc'.2`. Establish `hcr` using `(hmem c).1 hc'.1`. Use `(hmem _).2 fun i j => ?_` and prove the remaining obligations. Rewrite using `[UpperTheory.Gal.InertialTypesAlt.L.conj_entry']`.

Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[hc1 i j h, one_apply_ne h.ne]`. Simplify using the standard rewrite rules. Substitute `h` using the available equality. Rewrite using `[hc2 i, mul_one, mul_inv_cancel₀ (t i).ne_zero, one_apply_eq, sub_self, map_zero]`.

Conclude with `zero_le`. Rewrite using `[one_apply_ne h.ne', sub_zero]`. Use `hcr i j` as an intermediate fact. Rewrite `this` using `[one_apply_ne h.ne', sub_zero]`. Conclude with `(UpperTheory.Gal.InertialTypesAlt.L.val_le (ht j i h) _).trans this`.

Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, b, hb, e⟩`. Conclude with `⟨a, (hmem a).1 ha, b, (hmem b).1 hb, t, rfl, e⟩`. Introduce and unpack `⟨a, ha, b, hb, s, hs, e⟩`.

Take `rfl : s = t` from `hs`. Conclude with `⟨a, (hmem a).2 ha, b, (hmem b).2 hb, e⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.ballLev :
    UpperTheory.Gal.InertialTypesAlt.L.BallLev := by
  intro k _ _ _ _ n r h0 h1 K hK
  have hmem : ∀ g, g ∈ K ↔ g ∈ ball n r := fun g => by rw [← SetLike.mem_coe, hK]
  obtain ⟨K₀, e₀, ho, hc⟩ := UpperTheory.ConvolutionTheory.Loc.ballSub k n r h0 h1
  have eK : (K : Set (GL (Fin n) k)) = K₀ := hK.trans e₀.symm
  refine ⟨⟨⟨eK ▸ hc, eK ▸ ho⟩, ?_, ?_, ?_⟩, fun t => ?_⟩
  · intro g hg
    exact UpperTheory.Gal.InertialTypesAlt.L.nat_mul_factorial_bound h1 K hK n le_rfl g hg fun i j _ h => by
      have := i.2
      have := j.2
      omega
  · intro t ht u hu
    obtain ⟨hu1, hu2⟩ := (mem_unipB k).1 hu.2
    have hur := (hmem u).1 hu.1
    refine (hmem _).2 fun i j => ?_
    rw [UpperTheory.Gal.InertialTypesAlt.L.conj_entry]
    rcases lt_trichotomy i j with h | h | h
    · rw [one_apply_ne h.ne, sub_zero]
      have := hur i j
      rw [one_apply_ne h.ne, sub_zero] at this
      exact (UpperTheory.Gal.InertialTypesAlt.L.val_le (ht i j h) _).trans this
    · subst h
      rw [hu2 i, mul_one, mul_inv_cancel₀ (t i).ne_zero, one_apply_eq, sub_self, map_zero]
      exact zero_le
    · rw [hu1 i j h, one_apply_ne h.ne']
      simp
  · intro t ht c hc'
    obtain ⟨hc1, hc2⟩ := UpperTheory.Gal.InertialTypesAlt.L.mem_low.1 hc'.2
    have hcr := (hmem c).1 hc'.1
    refine (hmem _).2 fun i j => ?_
    rw [UpperTheory.Gal.InertialTypesAlt.L.conj_entry']
    rcases lt_trichotomy i j with h | h | h
    · rw [hc1 i j h, one_apply_ne h.ne]
      simp
    · subst h
      rw [hc2 i, mul_one, mul_inv_cancel₀ (t i).ne_zero, one_apply_eq, sub_self, map_zero]
      exact zero_le
    · rw [one_apply_ne h.ne', sub_zero]
      have := hcr i j
      rw [one_apply_ne h.ne', sub_zero] at this
      exact (UpperTheory.Gal.InertialTypesAlt.L.val_le (ht j i h) _).trans this
  · ext g
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, (hmem a).1 ha, b, (hmem b).1 hb, t, rfl, e⟩
    · rintro ⟨a, ha, b, hb, s, hs, e⟩
      obtain rfl : s = t := hs
      exact ⟨a, (hmem a).2 ha, b, (hmem b).2 hb, e⟩
