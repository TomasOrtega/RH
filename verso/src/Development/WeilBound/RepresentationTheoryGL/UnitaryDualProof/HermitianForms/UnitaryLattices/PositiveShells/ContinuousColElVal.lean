import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.U.Shell

open PositivityTheory.RgUd.Form PositivityTheory.RgUd.Form.U

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blkAt_val {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j =
      fromBlocks (g : Matrix (Fin n) (Fin n) k) 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k)
        (finSumFinEquiv.symm (Fin.cast (Nat.add_sub_cancel' h).symm i))
        (finSumFinEquiv.symm (Fin.cast (Nat.add_sub_cancel' h).symm j)) := by
  rfl

/- English proof (translation)
The claim follows from `Fin.ext rfl`.
-/
theorem cast_eq_castAdd {n N : ℕ} (h : n ≤ N) (i : Fin N) (hi : (i : ℕ) < n) :
    Fin.cast (Nat.add_sub_cancel' h).symm i = Fin.castAdd (N - n) (⟨i, hi⟩ : Fin n) := Fin.ext rfl

/- English proof (translation)
Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem cast_eq_natAdd {n N : ℕ} (h : n ≤ N) (i : Fin N) (hi : n ≤ (i : ℕ)) :
    Fin.cast (Nat.add_sub_cancel' h).symm i = Fin.natAdd n (⟨i - n, by omega⟩ : Fin (N - n)) := by
  ext; simp; omega

/- English proof (translation)
Rewrite using `[blkAt_val, cast_eq_castAdd h i hi, cast_eq_castAdd h j hj, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]`.
-/
theorem blkAt_val_lt {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) (hi : (i : ℕ) < n) (hj : (j : ℕ) < n) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j = (g : Matrix (Fin n) (Fin n) k) ⟨i, hi⟩ ⟨j, hj⟩ := by
  rw [blkAt_val, cast_eq_castAdd h i hi, cast_eq_castAdd h j hj, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁]

/- English proof (translation)
Rewrite using `[blkAt_val, cast_eq_natAdd h i hi, finSumFinEquiv_symm_apply_natAdd]`. Distinguish the cases in `hj : (j : ℕ) < n`. Rewrite using `[cast_eq_castAdd h j hj, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₂₁, one_apply_ne (fun e => by rw [e] at hi; omega)]`. Both sides reduce to the same expression. Rewrite using `[cast_eq_natAdd h j (by omega), finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂]`.

Simplify using `only [one_apply, Fin.ext_iff]`. Use `congr 1`. Apply `propext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
theorem blkAt_val_left {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) (hi : n ≤ (i : ℕ)) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [blkAt_val, cast_eq_natAdd h i hi, finSumFinEquiv_symm_apply_natAdd]
  by_cases hj : (j : ℕ) < n
  · rw [cast_eq_castAdd h j hj, finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₂₁,
      one_apply_ne (fun e => by rw [e] at hi; omega)]
    rfl
  · rw [cast_eq_natAdd h j (by omega), finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂]
    simp only [one_apply, Fin.ext_iff]
    congr 1
    apply propext; omega

/- English proof (translation)
Distinguish the cases in `hi : n ≤ (i : ℕ)`. Conclude with `blkAt_val_left h g i j hi`. Rewrite using `[blkAt_val, cast_eq_castAdd h i (by omega), finSumFinEquiv_symm_apply_castAdd, cast_eq_natAdd h j hj, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂, one_apply_ne (fun e => by rw [e] at hi; omega)]`. Both sides reduce to the same expression.
-/
theorem blkAt_val_right {n N : ℕ} (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) (hj : n ≤ (j : ℕ)) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  by_cases hi : n ≤ (i : ℕ)
  · exact blkAt_val_left h g i j hi
  rw [blkAt_val, cast_eq_castAdd h i (by omega), finSumFinEquiv_symm_apply_castAdd,
    cast_eq_natAdd h j hj, finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂,
    one_apply_ne (fun e => by rw [e] at hi; omega)]
  rfl

/- English proof (translation)
Use `show (1 + colMat k n x) i j = _`. Rewrite using `[Matrix.add_apply]`. Use `congr 1`. Distinguish the cases in `hj : j = Fin.last n`. Substitute `hj` using the available equality.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [colMat]`. Consider the case `cast i => simp [colMat]`. Establish `: ¬ ((j : ℕ) = n)` using `fun e => hj (Fin.ext (by simp [e]))`. Simplify using `[colMat, hj, this]`.
-/
theorem unip_val (n : ℕ) (x : Fin n → k) (i j : Fin (n + 1)) :
    ((unip k n (Multiplicative.ofAdd x) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j + if hij : (j : ℕ) = n ∧ (i : ℕ) < n then x ⟨i, hij.2⟩ else 0 := by
  show (1 + colMat k n x) i j = _
  rw [Matrix.add_apply]
  congr 1
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simp [colMat]
    | cast i => simp [colMat]
  · have : ¬ ((j : ℕ) = n) := fun e => hj (Fin.ext (by simp [e]))
    simp [colMat, hj, this]

/- English proof (translation)
Use `show (blkAt k (m + 2) N h (unip k (m + 1) (Multiplicative.ofAdd x)) : Matrix (Fin N) (Fin N) k) i j = _`. Distinguish the cases in `hi : (i : ℕ) < m + 2`. Distinguish the cases in `hj : (j : ℕ) < m + 2`. Rewrite using `[blkAt_val_lt h _ i j hi hj, unip_val]`. Use `congr 1`.

Simplify using `[one_apply, Fin.ext_iff]`. Distinguish the cases in `c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m`. Rewrite using `[dif_pos ⟨c.1, by simp only [Fin.val_mk]; omega⟩, dif_pos c]`. Rewrite using `[dif_neg (by simp only [Fin.val_mk]; omega), dif_neg c]`. Rewrite using `[blkAt_val_right h _ i j (by omega), dif_neg (by omega), add_zero]`.

Rewrite using `[blkAt_val_left h _ i j (by omega), dif_neg (by omega), add_zero]`.
-/
theorem colEl_val {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i j : Fin N) :
    (colEl k m N h x : Matrix (Fin N) (Fin N) k) i j =
      (1 : Matrix (Fin N) (Fin N) k) i j + if hij : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m then x ⟨i, by omega⟩ else 0 := by
  show (blkAt k (m + 2) N h (unip k (m + 1) (Multiplicative.ofAdd x)) : Matrix (Fin N) (Fin N) k) i j = _
  by_cases hi : (i : ℕ) < m + 2
  · by_cases hj : (j : ℕ) < m + 2
    · rw [blkAt_val_lt h _ i j hi hj, unip_val]
      congr 1
      · simp [one_apply, Fin.ext_iff]
      · by_cases c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m
        · rw [dif_pos ⟨c.1, by simp only [Fin.val_mk]; omega⟩, dif_pos c]
        · rw [dif_neg (by simp only [Fin.val_mk]; omega), dif_neg c]
    · rw [blkAt_val_right h _ i j (by omega), dif_neg (by omega), add_zero]
  · rw [blkAt_val_left h _ i j (by omega), dif_neg (by omega), add_zero]

/- English proof (translation)
Simplify using `only [colEl, ofAdd_add, map_mul]`.
-/
theorem colEl_add {m N : ℕ} (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  simp only [colEl, ofAdd_add, map_mul]

/- English proof (translation)
Simplify using `only [colEl, ofAdd_zero, map_one]`.
-/
theorem colEl_zero {m N : ℕ} (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  simp only [colEl, ofAdd_zero, map_one]

/- English proof (translation)
Rewrite using `[← colEl_add, add_neg_cancel, colEl_zero]`.
-/
theorem colEl_mul_neg {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    colEl k m N h x * colEl k m N h (-x) = 1 := by
  rw [← colEl_add, add_neg_cancel, colEl_zero]

/- English proof (translation)
The claim follows from `(eq_inv_of_mul_eq_one_right (colEl_mul_neg h x)).symm`.
-/
theorem colEl_inv {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    (colEl k m N h x)⁻¹ = colEl k m N h (-x) :=
  (eq_inv_of_mul_eq_one_right (colEl_mul_neg h x)).symm

/- English proof (translation)
Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Simplify using `only [colEl_val]`. Distinguish the cases in `c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m`. Simplify using `only [dif_pos c]`. Conclude with `continuous_const.add (continuous_apply _)`.

Simplify using `only [dif_neg c]`. Conclude with `continuous_const`.
-/
theorem continuous_colEl_val {m N : ℕ} (h : m + 2 ≤ N) :
    Continuous fun x => (colEl k m N h x : Matrix (Fin N) (Fin N) k) := by
  refine continuous_matrix fun i j => ?_
  simp only [colEl_val]
  by_cases c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m
  · simp only [dif_pos c]
    exact continuous_const.add (continuous_apply _)
  · simp only [dif_neg c]
    exact continuous_const

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨continuous_colEl_val h, ?_⟩` and prove the remaining obligations. Simplify using `only [colEl_inv]`. Conclude with `(continuous_colEl_val h).comp continuous_neg`.
-/
theorem continuous_colEl {m N : ℕ} (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  refine Units.continuous_iff.2 ⟨continuous_colEl_val h, ?_⟩
  simp only [colEl_inv]
  exact (continuous_colEl_val h).comp continuous_neg

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `e : ∀ i : Fin N, (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = fun r => (g : Matrix (Fin N) (Fin N) k) r i`. Introduce `i`. Use function extensionality and compare the values at `r`. Simplify using `[mulVec, dotProduct, Pi.single_apply]`. Establish `e1 : ∀ i : Fin N, (Pi.single i (1 : k) : Fin N → k) = fun r => (1 : Matrix (Fin N) (Fin N) k) r i`.

Introduce `i`. Use function extensionality and compare the values at `r`. Simplify using `[Pi.single_apply, one_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hg r i hi`.

Establish `hg' : ∀ i : Fin N, (i : ℕ) < n → (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1` using `hg`. Conclude with `congrFun ((e i).symm.trans ((hg' i hi).trans (e1 i))) r`. Introduce `hg i hi show (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1`. Rewrite using `[e i, e1 i]`. Use function extensionality and compare the values at `r`.

Conclude with `hg r i hi`.
-/
theorem mem_colFix_iff {N n : ℕ} (g : GL (Fin N) k) :
    g ∈ colFix k N n ↔ ∀ r i : Fin N, (i : ℕ) < n →
      (g : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i := by
  have e : ∀ i : Fin N, (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) =
      fun r => (g : Matrix (Fin N) (Fin N) k) r i := by
    intro i; funext r; simp [mulVec, dotProduct, Pi.single_apply]
  have e1 : ∀ i : Fin N, (Pi.single i (1 : k) : Fin N → k) = fun r => (1 : Matrix (Fin N) (Fin N) k) r i := by
    intro i; funext r; simp [Pi.single_apply, one_apply]
  constructor
  · intro hg r i hi
    have hg' : ∀ i : Fin N, (i : ℕ) < n →
        (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1 := hg
    exact congrFun ((e i).symm.trans ((hg' i hi).trans (e1 i))) r
  · intro hg i hi
    show (g : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) = Pi.single i 1
    rw [e i, e1 i]; funext r; exact hg r i hi

/- English proof (translation)
Rewrite using `[mem_unipB]`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Use `Fin.lt_def.1 hij` as an intermediate fact. Rewrite using `[colEl_val, one_apply_ne (fun e => by rw [e] at this; omega), dif_neg (by omega), add_zero]`. Rewrite using `[colEl_val, one_apply_eq, dif_neg (by omega), add_zero]`.
-/
theorem colEl_mem_unipB {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : colEl k m N h x ∈ unipB k (Fin N) := by
  rw [mem_unipB]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have := Fin.lt_def.1 hij
    rw [colEl_val, one_apply_ne (fun e => by rw [e] at this; omega), dif_neg (by omega), add_zero]
  · rw [colEl_val, one_apply_eq, dif_neg (by omega), add_zero]

/- English proof (translation)
The claim follows from `Subgroup.mem_inf.2 ⟨colEl_mem_unipB h x, (mem_colFix_iff _).2 fun r i hi => by rw [colEl_val, dif_neg (by omega), add_zero]⟩`.
-/
theorem colEl_mem_derUnip {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : colEl k m N h x ∈ derUnip k N (m + 1) :=
  Subgroup.mem_inf.2 ⟨colEl_mem_unipB h x, (mem_colFix_iff _).2 fun r i hi => by
    rw [colEl_val, dif_neg (by omega), add_zero]⟩

/- English proof (translation)
Use `show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), (colEl k m N h x : GL (Fin N) k).val p.1 p.2)) = 1`. Rewrite using `[Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]`. Introduce `p hp`. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hp).2`. Rewrite using `[colEl_val, one_apply_ne (fun e => by rw [e] at h1; omega), dif_neg (by omega), add_zero]`.
-/
theorem derChar_colEl (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    derChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip h x⟩ = 1 := by
  show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ),
    (colEl k m N h x : GL (Fin N) k).val p.1 p.2)) = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  rw [colEl_val, one_apply_ne (fun e => by rw [e] at h1; omega), dif_neg (by omega), add_zero]

/- English proof (translation)
Use extensionality with `i j`. Unfold `scalAt`. Distinguish the cases in `hi : (i : ℕ) < n`. Distinguish the cases in `hj : (j : ℕ) < n`. Rewrite using `[blkAt_val_lt hn _ i j hi hj]`.

Simplify using `[Matrix.algebraMap_matrix_apply, diagonal_apply, hi, Fin.ext_iff]`. Rewrite using `[blkAt_val_right hn _ i j (by omega)]`. Rewrite using `[one_apply_ne (fun e => by rw [e] at hi; omega), diagonal_apply_ne _ (fun e => by rw [e] at hi; omega)]`. Rewrite using `[blkAt_val_left hn _ i j (by omega)]`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Simplify using `[hi]`. Rewrite using `[one_apply_ne e, diagonal_apply_ne _ e]`.
-/
theorem scalAt_val {n N : ℕ} (hn : n ≤ N) (z : kˣ) :
    (scalAt k n N hn z : Matrix (Fin N) (Fin N) k) = diagonal fun i : Fin N => if (i : ℕ) < n then (z : k) else 1 := by
  ext i j
  unfold scalAt
  by_cases hi : (i : ℕ) < n
  · by_cases hj : (j : ℕ) < n
    · rw [blkAt_val_lt hn _ i j hi hj]
      simp [Matrix.algebraMap_matrix_apply, diagonal_apply, hi, Fin.ext_iff]
    · rw [blkAt_val_right hn _ i j (by omega)]
      rw [one_apply_ne (fun e => by rw [e] at hi; omega), diagonal_apply_ne _ (fun e => by rw [e] at hi; omega)]
  · rw [blkAt_val_left hn _ i j (by omega)]
    by_cases e : i = j
    · subst e; simp [hi]
    · rw [one_apply_ne e, diagonal_apply_ne _ e]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul]`. Use extensionality with `i j`. Rewrite using `[scalAt_val, diagonal_mul, mul_diagonal, colEl_val, colEl_val]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Distinguish the cases in `c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m`. Rewrite using `[dif_pos c, dif_pos c, one_apply_ne (fun e => by rw [e] at c; omega), if_pos (by omega), if_neg (by omega)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dif_neg c, dif_neg c]`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[one_apply_ne e]`.
-/
theorem scalAt_mul_colEl {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) (x : Fin (m + 1) → k) :
    scalAt k (m + 1) N (by omega) z * colEl k m N h x = colEl k m N h ((z : k) • x) * scalAt k (m + 1) N (by omega) z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  rw [scalAt_val, diagonal_mul, mul_diagonal, colEl_val, colEl_val]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases c : (j : ℕ) = m + 1 ∧ (i : ℕ) ≤ m
  · rw [dif_pos c, dif_pos c, one_apply_ne (fun e => by rw [e] at c; omega), if_pos (by omega), if_neg (by omega)]
    ring
  · rw [dif_neg c, dif_neg c]
    by_cases e : i = j
    · subst e; simp
    · simp [one_apply_ne e]

/- English proof (translation)
The claim follows from `MirU_le_Mir k n ⟨_, rfl⟩`.
-/
theorem unip_mem_Mir (n : ℕ) (x : Fin n → k) : unip k n (Multiplicative.ofAdd x) ∈ Mir k n :=
  MirU_le_Mir k n ⟨_, rfl⟩

/- English proof (translation)
Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, det_of_isUpperTriangular]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[unip_val, one_apply_eq, dif_neg (by omega), add_zero]`. Introduce `i j hij`.

Use `Fin.lt_def.1 hij` as an intermediate fact. Rewrite using `[unip_val, one_apply_ne (fun e => by rw [e] at this; simp at this), dif_neg (by simp at this; omega), add_zero]`.
-/
theorem det_unip (n : ℕ) (x : Fin n → k) : Matrix.GeneralLinearGroup.det (unip k n (Multiplicative.ofAdd x)) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, det_of_isUpperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    rw [unip_val, one_apply_eq, dif_neg (by omega), add_zero]
  · intro i j hij
    have := Fin.lt_def.1 hij
    rw [unip_val, one_apply_ne (fun e => by rw [e] at this; simp at this), dif_neg (by simp at this; omega), add_zero]

/- English proof (translation)
Simplify using `[nabs]`.
-/
theorem nabs_one' : nabs k 1 = 1 := by simp [nabs]

/- English proof (translation)
Simplify using `[nabs, map_pow]`.
-/
theorem nabs_pow' (z : kˣ) (n : ℕ) : nabs k (z ^ n) = nabs k z ^ n := by simp [nabs, map_pow]

/- English proof (translation)
Use `hB _ (unip_mem_Mir (m + 1) x) v w` as an intermediate fact. Rewrite `this` using `[det_unip, nabs_one', Real.one_rpow, Complex.ofReal_one, one_mul]`. Conclude with `this`.
-/
theorem B_colEl {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : MirEq π (m + 1) h s B)
    (x : Fin (m + 1) → k) (v w : V) : B (π (colEl k m N h x) v) (π (colEl k m N h x) w) = B v w := by
  have := hB _ (unip_mem_Mir (m + 1) x) v w
  rw [det_unip, nabs_one', Real.one_rpow, Complex.ofReal_one, one_mul] at this
  exact this

/- English proof (translation)
Use `show vecMul (eLast k (m + 1)) _ = _`. Rewrite using `[vecMul_eLast, scalAt_val]`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = Fin.last (m + 1)`. Substitute `hj` using the available equality.

Simplify using `[eLast]`. Rewrite using `[diagonal_apply_ne _ (Ne.symm hj)]`. Simplify using `[eLast, Pi.single_apply, hj]`.
-/
theorem scalAt_mem_Mir (m : ℕ) (z : kˣ) : scalAt k (m + 1) (m + 1 + 1) (by omega) z ∈ Mir k (m + 1) := by
  show vecMul (eLast k (m + 1)) _ = _
  rw [vecMul_eLast, scalAt_val]
  funext j
  by_cases hj : j = Fin.last (m + 1)
  · subst hj; simp [eLast]
  · rw [diagonal_apply_ne _ (Ne.symm hj)]
    simp [eLast, Pi.single_apply, hj]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[scalAt_val]`. Distinguish the cases in `hi : (i : ℕ) < m + 2`. Distinguish the cases in `hj : (j : ℕ) < m + 2`.

Rewrite using `[blkAt_val_lt h _ i j hi hj, scalAt_val]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[diagonal_apply_ne _ e, diagonal_apply_ne _ (fun e' => e (Fin.ext (by simpa using congrArg Fin.val e')))]`.

Rewrite using `[blkAt_val_right h _ i j (by omega)]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite using `[one_apply_ne e, diagonal_apply_ne _ e]`. Rewrite using `[blkAt_val_left h _ i j (by omega)]`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite using `[one_apply_ne e, diagonal_apply_ne _ e]`.
-/
theorem blkAt_scalAt {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) :
    blkAt k (m + 1 + 1) N h (scalAt k (m + 1) (m + 1 + 1) (by omega) z) = scalAt k (m + 1) N (by omega) z := by
  apply Units.ext
  ext i j
  rw [scalAt_val]
  by_cases hi : (i : ℕ) < m + 2
  · by_cases hj : (j : ℕ) < m + 2
    · rw [blkAt_val_lt h _ i j hi hj, scalAt_val]
      by_cases e : i = j
      · subst e; simp
      · rw [diagonal_apply_ne _ e, diagonal_apply_ne _ (fun e' => e (Fin.ext (by simpa using congrArg Fin.val e')))]
    · rw [blkAt_val_right h _ i j (by omega)]
      by_cases e : i = j
      · subst e; simp; omega
      · rw [one_apply_ne e, diagonal_apply_ne _ e]
  · rw [blkAt_val_left h _ i j (by omega)]
    by_cases e : i = j
    · subst e; simp; omega
    · rw [one_apply_ne e, diagonal_apply_ne _ e]

/- English proof (translation)
Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, scalAt_val, det_diagonal, Fin.prod_univ_castSucc]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.prod_congr rfl (fun x _ => if_pos (Nat.lt_succ_iff.1 x.isLt))]`. Simplify using the standard rewrite rules.
-/
theorem det_scalAt (m : ℕ) (z : kˣ) :
    Matrix.GeneralLinearGroup.det (scalAt k (m + 1) (m + 1 + 1) (by omega) z) = z ^ (m + 1) := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalAt_val, det_diagonal, Fin.prod_univ_castSucc]
  simp
  rw [Finset.prod_congr rfl (fun x _ => if_pos (Nat.lt_succ_iff.1 x.isLt))]
  simp

/- English proof (translation)
Use `hB _ (scalAt_mem_Mir m z) v w` as an intermediate fact. Rewrite `this` using `[blkAt_scalAt h z, det_scalAt, nabs_pow', ← Real.rpow_natCast_mul (show 0 ≤ nabs k z from NNReal.coe_nonneg _)]`. Rewrite using `[this]`. Use `push_cast`. Put the polynomial expressions in normal form.
-/
theorem B_scalAt {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} {s : ℝ} {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : MirEq π (m + 1) h s B)
    (z : kˣ) (v w : V) :
    B (π (scalAt k (m + 1) N (by omega) z) v) (π (scalAt k (m + 1) N (by omega) z) w) =
      ((nabs k z ^ (((m : ℝ) + 1) * s) : ℝ) : ℂ) * B v w := by
  have := hB _ (scalAt_mem_Mir m z) v w
  rw [blkAt_scalAt h z, det_scalAt, nabs_pow', ← Real.rpow_natCast_mul (show 0 ≤ nabs k z from NNReal.coe_nonneg _)] at this
  rw [this]
  push_cast
  ring_nf

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[mul_apply]`. Repeatedly rewrite using `[hA]`. Rewrite using `[← mul_apply, Matrix.one_mul]`.
-/
theorem row_one_mul {N : ℕ} (A M : Matrix (Fin N) (Fin N) k) (i j : Fin N)
    (hA : ∀ l, A i l = (1 : Matrix (Fin N) (Fin N) k) i l) : (A * M) i j = M i j := by
  rw [mul_apply]
  simp_rw [hA]
  rw [← mul_apply, Matrix.one_mul]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Rewrite using `[mul_apply]`. Repeatedly rewrite using `[hA]`. Rewrite using `[← mul_apply, Matrix.mul_one]`.
-/
theorem col_mul_one {N : ℕ} (A M : Matrix (Fin N) (Fin N) k) (i j : Fin N)
    (hA : ∀ l, A l j = (1 : Matrix (Fin N) (Fin N) k) l j) : (M * A) i j = M i j := by
  rw [mul_apply]
  simp_rw [hA]
  rw [← mul_apply, Matrix.mul_one]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `hg'` using `(mem_colFix_iff g).1 hg`. Use `conv_rhs => rw [← one_mulVec y]`. Use function extensionality and compare the values at `r`. Simplify using `only [mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hl : (l : ℕ) < n`. Rewrite using `[hg' r l hl]`. Rewrite using `[hy l (by omega), mul_zero, mul_zero]`.
-/
theorem colFix_mulVec {N n : ℕ} {g : GL (Fin N) k} (hg : g ∈ colFix k N n) (y : Fin N → k)
    (hy : ∀ r : Fin N, n ≤ (r : ℕ) → y r = 0) : (g : Matrix (Fin N) (Fin N) k).mulVec y = y := by
  have hg' := (mem_colFix_iff g).1 hg
  conv_rhs => rw [← one_mulVec y]
  funext r
  simp only [mulVec, dotProduct]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : (l : ℕ) < n
  · rw [hg' r l hl]
  · rw [hy l (by omega), mul_zero, mul_zero]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Simplify using `[mulVec, dotProduct, Pi.single_apply]`.
-/
theorem mulVec_single_apply {N : ℕ} (M : Matrix (Fin N) (Fin N) k) (i r : Fin N) :
    M.mulVec (Pi.single i 1) r = M r i := by
  simp [mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Rewrite using `[mul_apply]`. Repeatedly rewrite using `[colEl_val, add_mul, Finset.sum_add_distrib]`. Establish `e1 : ∑ l, (1 : Matrix (Fin N) (Fin N) k) i l * M l j = M i j` using `by rw [← mul_apply, Matrix.one_mul]`. Rewrite using `[e1]`. Use `congr 1`.

Distinguish the cases in `hi : (i : ℕ) ≤ m`. Rewrite using `[dif_pos hi, Finset.sum_eq_single ⟨m + 1, by omega⟩]`. Rewrite using `[dif_pos ⟨rfl, hi⟩]`. Introduce `l _ hl`. Rewrite using `[dif_neg (fun c => hl (Fin.ext c.1)), zero_mul]`.

Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`. Rewrite using `[dif_neg hi]`. Conclude with `Finset.sum_eq_zero fun l _ => by rw [dif_neg (fun c => hi c.2), zero_mul]`.
-/
theorem colEl_mul_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (M : Matrix (Fin N) (Fin N) k) (i j : Fin N) :
    ((colEl k m N h x : Matrix (Fin N) (Fin N) k) * M) i j =
      M i j + if hi : (i : ℕ) ≤ m then x ⟨i, by omega⟩ * M ⟨m + 1, by omega⟩ j else 0 := by
  rw [mul_apply]
  simp_rw [colEl_val, add_mul, Finset.sum_add_distrib]
  have e1 : ∑ l, (1 : Matrix (Fin N) (Fin N) k) i l * M l j = M i j := by rw [← mul_apply, Matrix.one_mul]
  rw [e1]
  congr 1
  by_cases hi : (i : ℕ) ≤ m
  · rw [dif_pos hi, Finset.sum_eq_single ⟨m + 1, by omega⟩]
    · rw [dif_pos ⟨rfl, hi⟩]
    · intro l _ hl
      rw [dif_neg (fun c => hl (Fin.ext c.1)), zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [dif_neg hi]
    exact Finset.sum_eq_zero fun l _ => by rw [dif_neg (fun c => hi c.2), zero_mul]

/- English proof (translation)
Take `⟨hu1, hu2⟩` from `Subgroup.mem_inf.1 u.2`. Establish `hrow : ∀ M : Matrix (Fin N) (Fin N) k, ∀ i j : Fin N, m + 1 ≤ (i : ℕ) → ((colEl k m N h x : Matrix (Fin N) (Fin N) k) * M) i j = M i j`. Introduce `M i j hi`. Conclude with `row_one_mul _ _ _ _ fun l => by rw [colEl_val, dif_neg (by omega), add_zero]`. Establish `hcol : ∀ M : Matrix (Fin N) (Fin N) k, ∀ i j : Fin N, m + 2 ≤ (j : ℕ) → (M * (((colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) i j = M i j`.

Introduce `M i j hj`. Conclude with `col_mul_one _ _ _ _ fun l => by rw [colEl_inv, colEl_val, dif_neg (by omega), add_zero]`. Establish `hmem : colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2)`. Use `Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (colEl_mem_unipB h x) hu1) (Subgroup.inv_mem _ (colEl_mem_unipB h x)), ?_⟩` and prove the remaining obligations. Use `show ∀ i : Fin N, (i : ℕ) < m + 2 → _`.

Introduce `i hi`. Establish `hy : ∀ r : Fin N, m + 2 ≤ (r : ℕ) → (((colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) r = 0`. Introduce `r hr`. Rewrite using `[mulVec_single_apply, colEl_inv, colEl_val, one_apply_ne (fun e => by rw [e] at hr; omega), dif_neg (by omega), add_zero]`. Rewrite using `[Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, colFix_mulVec hu2 _ hy, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]`.

Use `⟨hmem, ?_⟩` and prove the remaining obligations. Use `show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ), (colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ : GL (Fin N) k).val p.1 p.2)) = Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ), (u : …`. Use `congr 2`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hp).2`.

Rewrite using `[Units.val_mul, Units.val_mul, hcol _ _ _ (by omega), hrow _ _ _ (by omega)]`.
-/
theorem conj_colEl (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (u : derUnip k N (m + 2)) :
    ∃ hu : colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2),
      lvlChar k ψ N (m + 2) ⟨_, hu⟩ = lvlChar k ψ N (m + 2) u := by
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 u.2
  have hrow : ∀ M : Matrix (Fin N) (Fin N) k, ∀ i j : Fin N, m + 1 ≤ (i : ℕ) →
      ((colEl k m N h x : Matrix (Fin N) (Fin N) k) * M) i j = M i j := by
    intro M i j hi
    exact row_one_mul _ _ _ _ fun l => by rw [colEl_val, dif_neg (by omega), add_zero]
  have hcol : ∀ M : Matrix (Fin N) (Fin N) k, ∀ i j : Fin N, m + 2 ≤ (j : ℕ) →
      (M * (((colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)) i j = M i j := by
    intro M i j hj
    exact col_mul_one _ _ _ _ fun l => by rw [colEl_inv, colEl_val, dif_neg (by omega), add_zero]
  have hmem : colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ (colEl_mem_unipB h x) hu1)
      (Subgroup.inv_mem _ (colEl_mem_unipB h x)), ?_⟩
    show ∀ i : Fin N, (i : ℕ) < m + 2 → _
    intro i hi
    have hy : ∀ r : Fin N, m + 2 ≤ (r : ℕ) →
        (((colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec (Pi.single i 1) r = 0 := by
      intro r hr
      rw [mulVec_single_apply, colEl_inv, colEl_val, one_apply_ne (fun e => by rw [e] at hr; omega),
        dif_neg (by omega), add_zero]
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, colFix_mulVec hu2 _ hy, mulVec_mulVec,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  refine ⟨hmem, ?_⟩
  show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ),
      (colEl k m N h x * (u : GL (Fin N) k) * (colEl k m N h x)⁻¹ : GL (Fin N) k).val p.1 p.2)) =
    Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 2 - 1 ≤ (p.1 : ℕ),
      (u : GL (Fin N) k).val p.1 p.2))
  congr 2
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  rw [Units.val_mul, Units.val_mul, hcol _ _ _ (by omega), hrow _ _ _ (by omega)]

/- English proof (translation)
Establish `key : twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) ≤ (twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))).comap (π (colEl k m N h x))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, y, rfl⟩`. Take `⟨hm, hχ⟩` from `conj_colEl ψ h x u`. Use `Submodule.subset_span ⟨⟨_, hm⟩, π (colEl k m N h x) y, ?_⟩` and prove the remaining obligations.

Rewrite using `[hχ, map_sub, map_smul]`. Use `congr 1`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`. Use `congr 2`. Use `group`.

Conclude with `key hv`.
-/
theorem colEl_twKer (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (x : Fin (m + 1) → k) {v : V}
    (hv : v ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))) :
    π (colEl k m N h x) v ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := by
  have key : twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) ≤
      (twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))).comap (π (colEl k m N h x)) := by
    refine Submodule.span_le.2 ?_
    rintro w ⟨u, y, rfl⟩
    obtain ⟨hm, hχ⟩ := conj_colEl ψ h x u
    refine Submodule.subset_span ⟨⟨_, hm⟩, π (colEl k m N h x) y, ?_⟩
    rw [hχ, map_sub, map_smul]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  exact key hv

/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `w ⟨u, v, rfl⟩`. Take `⟨hu1, hu2⟩` from `Subgroup.mem_inf.1 u.2`. Take `⟨hl, hd⟩` from `(mem_unipB k).1 hu1`. Establish `hf` using `(mem_colFix_iff _).1 hu2`.

Use `set U : GL (Fin N) k := (u : GL (Fin N) k) with hU`. Set `j1 : Fin N` to `⟨m + 1, by omega⟩`. Set `a : Fin (m + 1) → k` to `fun r => (U : Matrix (Fin N) (Fin N) k) ⟨r, by omega⟩ j1`. Use `set u' : GL (Fin N) k := colEl k m N h (-a) * U with hu'`. Establish `hmem : u' ∈ derUnip k N (m + 2)`.

Use `Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (colEl_mem_unipB h (-a)) hu1, (mem_colFix_iff _).2 fun r i hi => ?_⟩` and prove the remaining obligations. Rewrite using `[hu', Units.val_mul, colEl_mul_apply]`. Distinguish the cases in `hi' : (i : ℕ) < m + 1`. Rewrite using `[hf r i hi', hf j1 i hi', one_apply_ne (show j1 ≠ i from fun e => by rw [← e] at hi'; simp [j1] at hi')]`. Simplify using the standard rewrite rules.

Establish `hi1 : i = j1` using `Fin.ext (by simp [j1]; omega)`. Substitute `hi1` using the available equality. Distinguish the cases in `hr : (r : ℕ) ≤ m`. Rewrite using `[dif_pos hr, hd, mul_one, one_apply_ne (fun e => by rw [e] at hr; simp [j1] at hr)]`. Simplify using `[a]`.

Rewrite using `[dif_neg hr, add_zero]`. Distinguish the cases in `e : r = j1`. Rewrite using `[e, hd, one_apply_eq]`. Rewrite using `[one_apply_ne e]`. Conclude with `hl r j1 (Fin.lt_def.2 (by have := Fin.val_ne_of_ne e; simp [j1] at this ⊢; omega))`.

Establish `hχ : derChar k ψ N (m + 1) u = lvlChar k ψ N (m + 2) ⟨u', hmem⟩` using `by show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), U.val p.1 p.2)) = Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), u'.val p.1 p.2))`. Use `congr 2`. Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Take `⟨h1, h2⟩` from `(Finset.mem_filter.1 hp).2`. Rewrite using `[hu', Units.val_mul, colEl_mul_apply, dif_neg (by omega), add_zero]`.

Establish `hUu : U = colEl k m N h a * u'`. Rewrite using `[hu', ← mul_assoc, colEl_mul_neg, one_mul]`. Establish `h1 : π u' v - ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • v ∈ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2))` using `Submodule.subset_span ⟨⟨u', hmem⟩, v, rfl⟩`. Establish `h2` using `colEl_twKer ψ h π a h1`. Establish `h3 : π (colEl k m N h a) v - v ∈ Submodule.span ℂ {w | ∃ (x : Fin (m + 1) → k) (v : V), w = π (colEl k m N h x) v - v}` using `Submodule.subset_span ⟨a, v, rfl⟩`.

Establish `e : π U v - ((derChar k ψ N (m + 1) u : ℂˣ) : ℂ) • v = π (colEl k m N h a) (π u' v - ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • v) + ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • (π (colEl k m N h a) v - v)`. Rewrite using `[hχ]`. Use `conv_lhs => rw [hUu, map_mul, Module.End.mul_apply]`. Rewrite using `[map_sub, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup h2 (Submodule.smul_mem _ _ h3)`.
-/
theorem derKer_le (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) :
    DerKer k ψ π m ≤ twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) ⊔
      Submodule.span ℂ {w | ∃ (x : Fin (m + 1) → k) (v : V), w = π (colEl k m N h x) v - v} := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨u, v, rfl⟩
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 u.2
  obtain ⟨hl, hd⟩ := (mem_unipB k).1 hu1
  have hf := (mem_colFix_iff _).1 hu2
  set U : GL (Fin N) k := (u : GL (Fin N) k) with hU
  let j1 : Fin N := ⟨m + 1, by omega⟩
  let a : Fin (m + 1) → k := fun r => (U : Matrix (Fin N) (Fin N) k) ⟨r, by omega⟩ j1
  set u' : GL (Fin N) k := colEl k m N h (-a) * U with hu'
  have hmem : u' ∈ derUnip k N (m + 2) := by
    refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (colEl_mem_unipB h (-a)) hu1, (mem_colFix_iff _).2 fun r i hi => ?_⟩
    rw [hu', Units.val_mul, colEl_mul_apply]
    by_cases hi' : (i : ℕ) < m + 1
    · rw [hf r i hi', hf j1 i hi', one_apply_ne (show j1 ≠ i from fun e => by rw [← e] at hi'; simp [j1] at hi')]
      simp
    · have hi1 : i = j1 := Fin.ext (by simp [j1]; omega)
      subst hi1
      by_cases hr : (r : ℕ) ≤ m
      · rw [dif_pos hr, hd, mul_one, one_apply_ne (fun e => by rw [e] at hr; simp [j1] at hr)]
        simp [a]
      · rw [dif_neg hr, add_zero]
        by_cases e : r = j1
        · rw [e, hd, one_apply_eq]
        · rw [one_apply_ne e]
          exact hl r j1 (Fin.lt_def.2 (by have := Fin.val_ne_of_ne e; simp [j1] at this ⊢; omega))
  have hχ : derChar k ψ N (m + 1) u = lvlChar k ψ N (m + 2) ⟨u', hmem⟩ := by
    show Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), U.val p.1 p.2)) =
      Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ m + 1 ≤ (p.1 : ℕ), u'.val p.1 p.2))
    congr 2
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    rw [hu', Units.val_mul, colEl_mul_apply, dif_neg (by omega), add_zero]
  have hUu : U = colEl k m N h a * u' := by
    rw [hu', ← mul_assoc, colEl_mul_neg, one_mul]
  have h1 : π u' v - ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • v ∈
      twKer π (derUnip k N (m + 2)) (lvlChar k ψ N (m + 2)) := Submodule.subset_span ⟨⟨u', hmem⟩, v, rfl⟩
  have h2 := colEl_twKer ψ h π a h1
  have h3 : π (colEl k m N h a) v - v ∈
      Submodule.span ℂ {w | ∃ (x : Fin (m + 1) → k) (v : V), w = π (colEl k m N h x) v - v} :=
    Submodule.subset_span ⟨a, v, rfl⟩
  have e : π U v - ((derChar k ψ N (m + 1) u : ℂˣ) : ℂ) • v =
      π (colEl k m N h a) (π u' v - ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • v) +
        ((lvlChar k ψ N (m + 2) ⟨u', hmem⟩ : ℂˣ) : ℂ) • (π (colEl k m N h a) v - v) := by
    rw [hχ]
    conv_lhs => rw [hUu, map_mul, Module.End.mul_apply]
    rw [map_sub, map_smul, smul_sub]
    abel
  rw [e]
  exact Submodule.add_mem_sup h2 (Submodule.smul_mem _ _ h3)

/- English proof (translation)
Establish `hm : π (colEl k m N h x) v - ((derChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip h x⟩ : ℂˣ) : ℂ) • v ∈ DerKer k ψ π m` using `Submodule.subset_span ⟨⟨_, colEl_mem_derUnip h x⟩, v, rfl⟩`. Rewrite `hm` using `[derChar_colEl, Units.val_one, one_smul]`. Rewrite using `[← neg_sub]`. Conclude with `neg_mem hm`.
-/
theorem sub_colEl_mem (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (x : Fin (m + 1) → k) (v : V) :
    v - π (colEl k m N h x) v ∈ DerKer k ψ π m := by
  have hm : π (colEl k m N h x) v - ((derChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip h x⟩ : ℂˣ) : ℂ) • v ∈
      DerKer k ψ π m := Submodule.subset_span ⟨⟨_, colEl_mem_derUnip h x⟩, v, rfl⟩
  rw [derChar_colEl, Units.val_one, one_smul] at hm
  rw [← neg_sub]
  exact neg_mem hm

end PositivityTheory.RgUd.Form.U.Shell
