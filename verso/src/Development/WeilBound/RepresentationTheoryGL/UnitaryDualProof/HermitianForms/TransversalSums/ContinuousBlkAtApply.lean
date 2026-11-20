import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.AvgData

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir

namespace PositivityTheory.RgUd.Form.ColumnElementGluing

open PositivityTheory.RgUd.Form

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Glue

/- English proof (translation)
Apply the tactic sequence `refine Fin.addCases (fun p => ?_) (fun q => ?_) y <;> simp`.
-/
private theorem blkAt_apply_lemma {a r : ℕ} (y : Fin (a + r)) :
    finSumFinEquiv.symm y =
      if hy : (y : ℕ) < a then Sum.inl ⟨y, hy⟩ else Sum.inr ⟨y - a, by have := y.2; omega⟩ := by
  refine Fin.addCases (fun p => ?_) (fun q => ?_) y <;> simp

/- English proof (translation)
Simplify using `only [blkAt, glCongr, blkGL, blkHom]`. Simplify using `[Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]`. Rewrite using `[blkAt_apply_lemma, blkAt_apply_lemma]`. Apply the tactic sequence `by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;>`. Simplify using `[hi, hj, Matrix.one_apply, Fin.ext_iff]`.

Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Establish `e : ((i : ℕ) - n = (j : ℕ) - n) ↔ (i : ℕ) = j` using `by omega`. Simplify using `only [e]`.
-/
theorem blkAt_apply (n N : ℕ) (h : n ≤ N) (g : GL (Fin n) k) (i j : Fin N) :
    (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j =
      if hij : (i : ℕ) < n ∧ (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin N) (Fin N) k) i j := by
  simp only [blkAt, glCongr, blkGL, blkHom]
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  rw [blkAt_apply_lemma, blkAt_apply_lemma]
  by_cases hi : (i : ℕ) < n <;> by_cases hj : (j : ℕ) < n <;>
    simp [hi, hj, Matrix.one_apply, Fin.ext_iff]
  · omega
  · omega
  · have e : ((i : ℕ) - n = (j : ℕ) - n) ↔ (i : ℕ) = j := by omega
    simp only [e]

/- English proof (translation)
Use `show (1 + colMat k n (Multiplicative.toAdd x)) i j = _`. Simplify using `only [Matrix.add_apply, colMat]`. Use `congr 1`. Distinguish the cases in `hj : (j : ℕ) = n`. Establish `e : j = Fin.last n` using `Fin.ext hj`.

Substitute `e` using the available equality. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp`. Establish `e : j ≠ Fin.last n` using `fun e => hj (by rw [e]; simp)`. Simplify using `[e, hj]`.
-/
theorem unip_apply (n : ℕ) (x : Multiplicative (Fin n → k)) (i j : Fin (n + 1)) :
    (unip k n x : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j +
        if hij : (j : ℕ) = n ∧ (i : ℕ) < n then x.toAdd ⟨i, hij.2⟩ else 0 := by
  show (1 + colMat k n (Multiplicative.toAdd x)) i j = _
  simp only [Matrix.add_apply, colMat]
  congr 1
  by_cases hj : (j : ℕ) = n
  · have e : j = Fin.last n := Fin.ext hj
    subst e
    refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp
  · have e : j ≠ Fin.last n := fun e => hj (by rw [e]; simp)
    simp [e, hj]

/- English proof (translation)
Use `show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i j = _`. Simplify using `only [glEmbMat]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>`. Simplify using `[Matrix.one_apply, Fin.ext_iff]`. Use `j'.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `i'.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem glEmb_apply (n : ℕ) (g : GL (Fin n) k) (i j : Fin (n + 1)) :
    (glEmb k n g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j =
      if hij : (i : ℕ) < n ∧ (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨i, hij.1⟩ ⟨j, hij.2⟩
      else (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) i j = _
  simp only [glEmbMat]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.one_apply, Fin.ext_iff]
  · have := j'.2
    omega
  · have := i'.2
    omega

def padV {m N : ℕ} (_h : m + 2 ≤ N) (x : Fin (m + 1) → k) : Fin N → k :=
  fun i => if hi : (i : ℕ) < m + 1 then x ⟨i, hi⟩ else 0

def cIdx {m N : ℕ} (h : m + 2 ≤ N) : Fin N := ⟨m + 1, by omega⟩

/- English proof (translation)
Simplify using `only [colEl, blkAt_apply, unip_apply, padV, cIdx, Fin.ext_iff, Matrix.one_apply, toAdd_ofAdd]`. Apply the tactic sequence `by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>`. Apply the tactic sequence `by_cases hc : (j : ℕ) = m + 1 <;> by_cases hi' : (i : ℕ) < m + 1 <;>`. Apply the tactic sequence `simp [hi, hj, hc, hi'] <;> omega`.
-/
theorem colEl_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i j : Fin N) :
    (colEl k m N h x : Matrix (Fin N) (Fin N) k) i j =
      (1 : Matrix (Fin N) (Fin N) k) i j + if j = cIdx h then padV h x i else 0 := by
  simp only [colEl, blkAt_apply, unip_apply, padV, cIdx, Fin.ext_iff, Matrix.one_apply,
    toAdd_ofAdd]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>
    by_cases hc : (j : ℕ) = m + 1 <;> by_cases hi' : (i : ℕ) < m + 1 <;>
    simp [hi, hj, hc, hi'] <;> omega

/- English proof (translation)
Simplify using `only [colEl, ofAdd_add, map_mul]`.
-/
theorem colEl_add' {m N : ℕ} (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  simp only [colEl, ofAdd_add, map_mul]

/- English proof (translation)
Simplify using `[colEl]`.
-/
theorem colEl_zero' {m N : ℕ} (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  simp [colEl]

/- English proof (translation)
Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_upperTriangular]`. Use `Finset.prod_eq_one (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[unip_apply]`. Simplify using `only [Matrix.one_apply_eq, add_eq_left]`.

Rewrite using `[dif_neg]`. Use linear arithmetic over natural numbers and integers. Introduce `i j hij`. Establish `hij' : j < i` using `hij`. Rewrite using `[unip_apply, Matrix.one_apply_ne (ne_of_lt hij').symm, zero_add, dif_neg]`.

Introduce `hc`. Use `Fin.lt_def.mp hij'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem det_unip' (n : ℕ) (x : Multiplicative (Fin n → k)) : Matrix.GeneralLinearGroup.det (unip k n x) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one (fun i _ => ?_)
    rw [unip_apply]
    simp only [Matrix.one_apply_eq, add_eq_left]
    rw [dif_neg]
    omega
  · intro i j hij
    have hij' : j < i := hij
    rw [unip_apply, Matrix.one_apply_ne (ne_of_lt hij').symm, zero_add, dif_neg]
    intro hc
    have := Fin.lt_def.mp hij'
    omega

/- English proof (translation)
Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]`. Use `show (glEmbMat k n (g : Matrix (Fin n) (Fin n) k)).det = _`. Rewrite using `[Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]`. Simplify using `[glEmbMat, Fin.succAbove_last]`.

Use `congr 1`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, glEmbMat, Fin.lastCases_castSucc]`.
-/
theorem det_glEmb' (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (glEmb k n g) = Matrix.GeneralLinearGroup.det g := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  show (glEmbMat k n (g : Matrix (Fin n) (Fin n) k)).det = _
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc]
  simp [glEmbMat, Fin.succAbove_last]
  congr 1
  ext a b
  simp only [Matrix.submatrix_apply, glEmbMat, Fin.lastCases_castSucc]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [blkAt_apply, glEmb_apply, Matrix.one_apply, Fin.ext_iff]`. Apply the tactic sequence `by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>`. Apply the tactic sequence `by_cases hi' : (i : ℕ) < m + 1 <;> by_cases hj' : (j : ℕ) < m + 1 <;>`. Apply the tactic sequence `simp [hi, hj, hi', hj'] <;> omega`.
-/
theorem blkAt_glEmb' {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) :
    blkAt k (m + 2) N h (glEmb k (m + 1) g) = blkAt k (m + 1) N (by omega) g := by
  ext i j
  simp only [blkAt_apply, glEmb_apply, Matrix.one_apply, Fin.ext_iff]
  by_cases hi : (i : ℕ) < m + 2 <;> by_cases hj : (j : ℕ) < m + 2 <;>
    by_cases hi' : (i : ℕ) < m + 1 <;> by_cases hj' : (j : ℕ) < m + 1 <;>
    simp [hi, hj, hi', hj'] <;> omega

/- English proof (translation)
Conclude with `(eq_inv_of_mul_eq_one_left (by rw [← colEl_add', neg_add_cancel, colEl_zero'])).symm`.
-/
theorem colEl_inv {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    (colEl k m N h x)⁻¹ = colEl k m N h (-x) := by
  exact (eq_inv_of_mul_eq_one_left (by rw [← colEl_add', neg_add_cancel, colEl_zero'])).symm

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [padV, Pi.neg_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem padV_neg {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : padV h (-x) = -padV h x := by
  funext i
  simp only [padV, Pi.neg_apply]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `only [padV]`. Rewrite using `[dif_neg (by omega)]`.
-/
theorem padV_of_ge {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (i : Fin N) (hi : m + 1 ≤ (i : ℕ)) :
    padV h x i = 0 := by
  simp only [padV]
  rw [dif_neg (by omega)]

/- English proof (translation)
Simplify using `only [blkAt_apply]`. Distinguish the cases in `hij : (i : ℕ) < n ∧ (j : ℕ) < n`. Simplify using `only [dif_pos hij]`. Conclude with `Units.continuous_val.matrix_elem _ _`. Simplify using `only [dif_neg hij]`.

Conclude with `continuous_const`.
-/
theorem continuous_blkAt_apply (n N : ℕ) (h : n ≤ N) (i j : Fin N) :
    Continuous fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k) i j := by
  simp only [blkAt_apply]
  by_cases hij : (i : ℕ) < n ∧ (j : ℕ) < n
  · simp only [dif_pos hij]
    exact Units.continuous_val.matrix_elem _ _
  · simp only [dif_neg hij]
    exact continuous_const

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Establish `hc : Continuous fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k)` using `continuous_pi fun i => continuous_pi fun j => continuous_blkAt_apply n N h i j`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Establish `e : (fun g : GL (Fin n) k => ((blkAt k n N h g)⁻¹ : GL (Fin N) k).val) = (fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k)) ∘ (fun g => g⁻¹)`. Use function extensionality and compare the values at `g`.

Simplify using `[map_inv]`. Rewrite using `[e]`. Conclude with `hc.comp continuous_inv`.
-/
theorem continuous_blkAt' (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  rw [Units.continuous_iff]
  have hc : Continuous fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k) :=
    continuous_pi fun i => continuous_pi fun j => continuous_blkAt_apply n N h i j
  refine ⟨hc, ?_⟩
  have e : (fun g : GL (Fin n) k => ((blkAt k n N h g)⁻¹ : GL (Fin N) k).val) =
      (fun g : GL (Fin n) k => (blkAt k n N h g : Matrix (Fin N) (Fin N) k)) ∘ (fun g => g⁻¹) := by
    funext g
    simp [map_inv]
  rw [e]
  exact hc.comp continuous_inv

/- English proof (translation)
Simplify using `only [colEl_apply]`. Use `continuous_const.add ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = cIdx h`. Simplify using `only [hj, if_true, padV]`. Distinguish the cases in `hi : (i : ℕ) < m + 1`.

Simplify using `only [dif_pos hi]`. Conclude with `continuous_apply _`. Simplify using `only [dif_neg hi]`. Conclude with `continuous_const`. Simplify using `only [hj, if_false]`.

Conclude with `continuous_const`.
-/
theorem continuous_colEl_apply {m N : ℕ} (h : m + 2 ≤ N) (i j : Fin N) :
    Continuous fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k) i j := by
  simp only [colEl_apply]
  refine continuous_const.add ?_
  by_cases hj : j = cIdx h
  · simp only [hj, if_true, padV]
    by_cases hi : (i : ℕ) < m + 1
    · simp only [dif_pos hi]
      exact continuous_apply _
    · simp only [dif_neg hi]
      exact continuous_const
  · simp only [hj, if_false]
    exact continuous_const

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Establish `hc : Continuous fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k)` using `continuous_pi fun i => continuous_pi fun j => continuous_colEl_apply h i j`. Use `⟨hc, ?_⟩` and prove the remaining obligations. Establish `e : (fun x : Fin (m + 1) → k => ((colEl k m N h x)⁻¹ : GL (Fin N) k).val) = (fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k)) ∘ (fun x => -x)`. Use function extensionality and compare the values at `x`.

Simplify using `[colEl_inv]`. Rewrite using `[e]`. Conclude with `hc.comp continuous_neg`.
-/
theorem continuous_colEl' {m N : ℕ} (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  rw [Units.continuous_iff]
  have hc : Continuous fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k) :=
    continuous_pi fun i => continuous_pi fun j => continuous_colEl_apply h i j
  refine ⟨hc, ?_⟩
  have e : (fun x : Fin (m + 1) → k => ((colEl k m N h x)⁻¹ : GL (Fin N) k).val) =
      (fun x : Fin (m + 1) → k => (colEl k m N h x : Matrix (Fin N) (Fin N) k)) ∘ (fun x => -x) := by
    funext x
    simp [colEl_inv]
  rw [e]
  exact hc.comp continuous_neg

/- English proof (translation)
Rewrite using `[derUnip, Subgroup.mem_inf, GlobalTheory.SmGL.mem_unipB]`. Apply `and_congr Iff.rfl` to reduce the goal to its premises. Use `show (∀ j : Fin N, (j : ℕ) < n → (u : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single j 1 = Pi.single j 1) ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `H i j hj`.

Use `congrFun (H j hj) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`. Simplify `this` using `[Matrix.one_apply, Pi.single_apply, Matrix.col]`. Introduce `H j hj`. Use function extensionality and compare the values at `i`.

Rewrite using `[Matrix.mulVec_single_one]`. Simplify using `[Matrix.col, H i j hj, Matrix.one_apply, Pi.single_apply]`.
-/
theorem mem_derUnip_iff {N n : ℕ} (u : GL (Fin N) k) : u ∈ derUnip k N n ↔
    ((∀ i j : Fin N, (j : ℕ) < i → (u : Matrix (Fin N) (Fin N) k) i j = 0) ∧
      ∀ i, (u : Matrix (Fin N) (Fin N) k) i i = 1) ∧
      ∀ i j : Fin N, (j : ℕ) < n → (u : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [derUnip, Subgroup.mem_inf, GlobalTheory.SmGL.mem_unipB]
  apply and_congr Iff.rfl
  show (∀ j : Fin N, (j : ℕ) < n → (u : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single j 1 = Pi.single j 1) ↔ _
  constructor
  · intro H i j hj
    have := congrFun (H j hj) i
    rw [Matrix.mulVec_single_one] at this
    simpa [Matrix.one_apply, Pi.single_apply, Matrix.col] using this
  · intro H j hj
    funext i
    rw [Matrix.mulVec_single_one]
    simp [Matrix.col, H i j hj, Matrix.one_apply, Pi.single_apply]

/- English proof (translation)
Introduce `u hu`. Rewrite `hu`, the goal using `[mem_derUnip_iff]`. Conclude with `⟨hu.1, fun i j hj => hu.2 i j (by omega)⟩`.
-/
theorem derUnip_anti {N n n' : ℕ} (hn : n ≤ n') : derUnip k N n' ≤ derUnip k N n := by
  intro u hu
  rw [mem_derUnip_iff] at hu ⊢
  exact ⟨hu.1, fun i j hj => hu.2 i j (by omega)⟩

/- English proof (translation)
Rewrite using `[mem_derUnip_iff]`. Use `⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hj => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff] split_ifs <;> first | omega | simp`. Apply the tactic sequence `simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff] split_ifs <;> first | omega | simp`. Apply the tactic sequence `simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff] split_ifs <;> first | omega | simp`.
-/
theorem colEl_mem_derUnip' {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    colEl k m N h x ∈ derUnip k N (m + 1) := by
  rw [mem_derUnip_iff]
  refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, fun i j hj => ?_⟩
  · simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp only [colEl_apply, padV, cIdx, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lvlChar_apply (ψ : AddChar k Circle) (N n : ℕ) (u : derUnip k N n) :
    lvlChar k ψ N n u = Circle.toUnits (ψ (∑ p : Fin N × Fin N with (p.2 : ℕ) = p.1 + 1 ∧ n - 1 ≤ (p.1 : ℕ),
      (u : GL (Fin N) k).val p.1 p.2)) := rfl

/- English proof (translation)
Rewrite using `[lvlChar_apply]`. Use `congr 2`. Rewrite using `[Finset.sum_eq_single ((⟨m, by omega⟩, ⟨m + 1, by omega⟩) : Fin N × Fin N)]`. Simplify using `[colEl_apply, cIdx, padV, xi0, Matrix.one_apply, Fin.ext_iff]`. Both sides reduce to the same expression.

Introduce and unpack `⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hp hne`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Simplify using `only [ne_eq, Prod.mk.injEq, Fin.mk.injEq, not_and] at hne`. Simplify using `only [colEl_apply, cIdx, padV, Matrix.one_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | omega | simp`.

Introduce `hnot`. It suffices to derive a contradiction. Apply `hnot` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem lvlChar_colEl' (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    lvlChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip' h x⟩ = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) := by
  rw [lvlChar_apply]
  congr 2
  rw [Finset.sum_eq_single ((⟨m, by omega⟩, ⟨m + 1, by omega⟩) : Fin N × Fin N)]
  · simp [colEl_apply, cIdx, padV, xi0, Matrix.one_apply, Fin.ext_iff]
    rfl
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ hp hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [ne_eq, Prod.mk.injEq, Fin.mk.injEq, not_and] at hne
    simp only [colEl_apply, cIdx, padV, Matrix.one_apply, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · intro hnot
    exfalso
    apply hnot
    simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_castSucc, glEmbMat, colMat]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem glEmbMat_mul_colMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (x : Fin n → k) :
    glEmbMat k n A * colMat k n x = colMat k n (A *ᵥ x) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, glEmbMat, colMat]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_castSucc, glEmbMat, colMat]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>`. Simplify using the standard rewrite rules.
-/
theorem colMat_mul_glEmbMat (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (y : Fin n → k) :
    colMat k n y * glEmbMat k n A = colMat k n y := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, glEmbMat, colMat]
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j <;>
    simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use `show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) * (1 + colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd x))) = (1 + colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) k) *ᵥ x)))) * glEmbMat k n (g : Matrix (Fin n) (Fin n) k)`. Simplify using `only [toAdd_ofAdd, mul_add, add_mul, mul_one, one_mul, glEmbMat_mul_colMat, colMat_mul_glEmbMat]`.
-/
theorem glEmb_mul_unip (n : ℕ) (g : GL (Fin n) k) (x : Fin n → k) :
    glEmb k n g * unip k n (Multiplicative.ofAdd x) =
      unip k n (Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) k) *ᵥ x)) * glEmb k n g := by
  apply Units.ext
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) *
      (1 + colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd x))) =
    (1 + colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd ((g : Matrix (Fin n) (Fin n) k) *ᵥ x)))) *
      glEmbMat k n (g : Matrix (Fin n) (Fin n) k)
  simp only [toAdd_ofAdd, mul_add, add_mul, mul_one, one_mul, glEmbMat_mul_colMat, colMat_mul_glEmbMat]

/- English proof (translation)
Rewrite using `[← blkAt_glEmb' h g]`. Simplify using `only [colEl]`. Rewrite using `[← map_mul, ← map_inv, ← map_mul, glEmb_mul_unip, mul_inv_cancel_right]`.
-/
theorem blkAt_conj_colEl' {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) :
    blkAt k (m + 1) N (by omega) g * colEl k m N h x * (blkAt k (m + 1) N (by omega) g)⁻¹ =
      colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) := by
  rw [← blkAt_glEmb' h g]
  simp only [colEl]
  rw [← map_mul, ← map_inv, ← map_mul, glEmb_mul_unip, mul_inv_cancel_right]

/- English proof (translation)
Simplify using `only [scalAt]`. Rewrite using `[blkAt_conj_colEl']`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.algebraMap_matrix_apply]`.
-/
theorem scalAt_conj_colEl' {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) (x : Fin (m + 1) → k) :
    scalAt k (m + 1) N (by omega) z * colEl k m N h x * (scalAt k (m + 1) N (by omega) z)⁻¹ =
      colEl k m N h ((z : k) • x) := by
  simp only [scalAt]
  rw [blkAt_conj_colEl']
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.algebraMap_matrix_apply]

/- English proof (translation)
Simplify using `only [scalAt]`. Rewrite using `[← map_mul, ← map_mul]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]`.

Conclude with `Algebra.commutes _ _`.
-/
theorem scalAt_comm_blkAt' {m N : ℕ} (h : m + 1 ≤ N) (z : kˣ) (g : GL (Fin (m + 1)) k) :
    scalAt k (m + 1) N h z * blkAt k (m + 1) N h g = blkAt k (m + 1) N h g * scalAt k (m + 1) N h z := by
  simp only [scalAt]
  rw [← map_mul, ← map_mul]
  congr 1
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  exact Algebra.commutes _ _

/- English proof (translation)
Simplify using `[Matrix.mul_apply, colEl_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]`.
-/
theorem colEl_mul_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (M : Matrix (Fin N) (Fin N) k)
    (i j : Fin N) : ((colEl k m N h x : Matrix (Fin N) (Fin N) k) * M) i j = M i j + padV h x i * M (cIdx h) j := by
  simp [Matrix.mul_apply, colEl_apply, add_mul, Finset.sum_add_distrib, Matrix.one_apply]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, colEl_apply, mul_add, Finset.sum_add_distrib]`. Rewrite using `[← Matrix.mul_apply, Matrix.mul_one]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp [Matrix.mulVec, dotProduct]`.
-/
theorem mul_colEl_apply {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) (M : Matrix (Fin N) (Fin N) k)
    (i j : Fin N) : (M * (colEl k m N h x : Matrix (Fin N) (Fin N) k)) i j =
      M i j + if j = cIdx h then (M *ᵥ padV h x) i else 0 := by
  simp only [Matrix.mul_apply, colEl_apply, mul_add, Finset.sum_add_distrib]
  rw [← Matrix.mul_apply, Matrix.mul_one]
  congr 1
  split_ifs <;> simp [Matrix.mulVec, dotProduct]

/- English proof (translation)
Rewrite using `[lvlChar_apply, lvlChar_apply]`. Use `congr 2`. Establish `B` using `(mem_derUnip_iff u).mp hu`. Use `symm`. Apply `Finset.sum_subset` to reduce the goal to its premises.

Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `p hp hnp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hnp`.

Establish `h2 : (p.2 : ℕ) < m + 2` using `by omega`. Use `show (u : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0`. Rewrite using `[B.2 p.1 p.2 h2, Matrix.one_apply_ne]`. Introduce `e`. Rewrite `hp` using `[e]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem lvlChar_succ (ψ : AddChar k Circle) {N m : ℕ} (u : GL (Fin N) k) (hu : u ∈ derUnip k N (m + 2))
    (hu' : u ∈ derUnip k N (m + 1)) : lvlChar k ψ N (m + 1) ⟨u, hu'⟩ = lvlChar k ψ N (m + 2) ⟨u, hu⟩ := by
  rw [lvlChar_apply, lvlChar_apply]
  congr 2
  have B := (mem_derUnip_iff u).mp hu
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    omega
  · intro p hp hnp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hnp
    have h2 : (p.2 : ℕ) < m + 2 := by omega
    show (u : Matrix (Fin N) (Fin N) k) p.1 p.2 = 0
    rw [B.2 p.1 p.2 h2, Matrix.one_apply_ne]
    intro e
    rw [e] at hp
    omega

/- English proof (translation)
Take `⟨u, hu⟩` from `u`. Establish `B` using `(mem_derUnip_iff u).mp hu`. Take `⟨x, hxd⟩ : ∃ x : Fin (m + 1) → k, ∀ i : Fin (m + 1), x i = (u : Matrix (Fin N) (Fin N) k) ⟨i, by have` from `i.2; omega⟩ (cIdx h) := ⟨_, fun _ => rfl⟩`. Establish `hv1 : colEl k m N h (-x) * u ∈ derUnip k N (m + 1)` using `Subgroup.mul_mem _ (colEl_mem_derUnip' h (-x)) hu`. Establish `hv2 : colEl k m N h (-x) * u ∈ derUnip k N (m + 2)`.

Establish `A` using `(mem_derUnip_iff _).mp hv1`. Rewrite using `[mem_derUnip_iff]`. Use `⟨A.1, fun i j hj => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hjm : (j : ℕ) < m + 1`. Conclude with `A.2 i j hjm`.

Establish `hjc : j = cIdx h` using `Fin.ext (by simp only [cIdx]; omega)`. Substitute `hjc` using the available equality. Rewrite using `[Units.val_mul, colEl_mul_apply, B.1.2 (cIdx h), mul_one]`. Distinguish the cases in `hi : (i : ℕ) < m + 1`. Establish `hne : i ≠ cIdx h` using `fun e => by rw [e] at hi; simp [cIdx] at hi`.

Rewrite using `[Matrix.one_apply_ne hne]`. Simplify using `only [padV, dif_pos hi, Pi.neg_apply, hxd]`. Simplify using the standard rewrite rules. Rewrite using `[padV_of_ge h _ i (by omega), add_zero]`. Distinguish the cases in `hie : (i : ℕ) = m + 1`.

Establish `e : i = cIdx h` using `Fin.ext (by simp [cIdx, hie])`. Rewrite using `[e, B.1.2, Matrix.one_apply_eq]`. Establish `hlt : ((cIdx h : Fin N) : ℕ) < i` using `by simp only [cIdx]; omega`. Rewrite using `[B.1.1 i (cIdx h) hlt, Matrix.one_apply_ne]`. Introduce `e`.

Apply `hie` to reduce the goal to its premises. Rewrite using `[e]`. Both sides reduce to the same expression. Establish `hu_eq : u = colEl k m N h x * (colEl k m N h (-x) * u)`. Rewrite using `[← colEl_inv, mul_inv_cancel_left]`.

Use `⟨x, ⟨_, hv2⟩, hu_eq, ?_⟩` and prove the remaining obligations. Establish `e : (⟨u, hu⟩ : derUnip k N (m + 1)) = ⟨colEl k m N h x, colEl_mem_derUnip' h x⟩ * ⟨_, hv1⟩` using `Subtype.ext hu_eq`. Rewrite using `[e, map_mul, lvlChar_colEl', lvlChar_succ ψ _ hv2 hv1]`.
-/
theorem derUnip_decomp' (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (u : derUnip k N (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (u' : derUnip k N (m + 2)), (u : GL (Fin N) k) = colEl k m N h x * u' ∧
      lvlChar k ψ N (m + 1) u = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) * lvlChar k ψ N (m + 2) u' := by
  obtain ⟨u, hu⟩ := u
  have B := (mem_derUnip_iff u).mp hu
  obtain ⟨x, hxd⟩ : ∃ x : Fin (m + 1) → k, ∀ i : Fin (m + 1),
      x i = (u : Matrix (Fin N) (Fin N) k) ⟨i, by have := i.2; omega⟩ (cIdx h) := ⟨_, fun _ => rfl⟩
  have hv1 : colEl k m N h (-x) * u ∈ derUnip k N (m + 1) :=
    Subgroup.mul_mem _ (colEl_mem_derUnip' h (-x)) hu
  have hv2 : colEl k m N h (-x) * u ∈ derUnip k N (m + 2) := by
    have A := (mem_derUnip_iff _).mp hv1
    rw [mem_derUnip_iff]
    refine ⟨A.1, fun i j hj => ?_⟩
    by_cases hjm : (j : ℕ) < m + 1
    · exact A.2 i j hjm
    · have hjc : j = cIdx h := Fin.ext (by simp only [cIdx]; omega)
      subst hjc
      rw [Units.val_mul, colEl_mul_apply, B.1.2 (cIdx h), mul_one]
      by_cases hi : (i : ℕ) < m + 1
      · have hne : i ≠ cIdx h := fun e => by rw [e] at hi; simp [cIdx] at hi
        rw [Matrix.one_apply_ne hne]
        simp only [padV, dif_pos hi, Pi.neg_apply, hxd]
        simp
      · rw [padV_of_ge h _ i (by omega), add_zero]
        by_cases hie : (i : ℕ) = m + 1
        · have e : i = cIdx h := Fin.ext (by simp [cIdx, hie])
          rw [e, B.1.2, Matrix.one_apply_eq]
        · have hlt : ((cIdx h : Fin N) : ℕ) < i := by simp only [cIdx]; omega
          rw [B.1.1 i (cIdx h) hlt, Matrix.one_apply_ne]
          intro e
          apply hie
          rw [e]
          rfl
  have hu_eq : u = colEl k m N h x * (colEl k m N h (-x) * u) := by
    rw [← colEl_inv, mul_inv_cancel_left]
  refine ⟨x, ⟨_, hv2⟩, hu_eq, ?_⟩
  have e : (⟨u, hu⟩ : derUnip k N (m + 1)) =
      ⟨colEl k m N h x, colEl_mem_derUnip' h x⟩ * ⟨_, hv1⟩ := Subtype.ext hu_eq
  rw [e, map_mul, lvlChar_colEl', lvlChar_succ ψ _ hv2 hv1]

/- English proof (translation)
Take `⟨u, hu⟩` from `u'`. Establish `B` using `(mem_derUnip_iff u).mp hu`. Establish `hu1 : u ∈ derUnip k N (m + 1)` using `derUnip_anti (by omega) hu`. Establish `hcne : ∀ l : Fin N, (l : ℕ) < m + 1 → cIdx h ≠ l` using `fun l hl e => by`. Use `congrArg Fin.val e` as an intermediate fact.

Simplify using `only [cIdx] at this`. Use linear arithmetic over natural numbers and integers. Establish `hA : ∀ i l : Fin N, (l : ℕ) < m + 2 → ((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i l = (1 : Matrix (Fin N) (Fin N) k) i l + padV h x i * (1 : Matrix (Fin N) (Fin N) k) (cIdx h) l`. Introduce `i l hl`. Rewrite using `[Units.val_mul, colEl_mul_apply, B.2 i l hl, B.2 (cIdx h) l hl]`.

Establish `hmv : ∀ i, (((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ padV h (-x)) i = padV h (-x) i`. Introduce `i`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single i]`. Distinguish the cases in `hi : (i : ℕ) < m + 1`.

Rewrite using `[hA i i (by omega), Matrix.one_apply_eq, Matrix.one_apply_ne (hcne i hi), mul_zero, add_zero, one_mul]`. Rewrite using `[padV_of_ge h _ i (by omega), mul_zero]`. Introduce `l _ hli`. Distinguish the cases in `hl : (l : ℕ) < m + 1`. Rewrite using `[hA i l (by omega), Matrix.one_apply_ne (Ne.symm hli), Matrix.one_apply_ne (hcne l hl), mul_zero, add_zero, zero_mul]`.

Rewrite using `[padV_of_ge h _ l (by omega), mul_zero]`. Simplify using the standard rewrite rules. Establish `hv : ∀ i j : Fin N, ((colEl k m N h x * u * (colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = ((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j + if j = cIdx h then padV h (-x) i else 0`. Introduce `i j`. Rewrite using `[colEl_inv, Units.val_mul, mul_colEl_apply, hmv]`.

Establish `hmem : colEl k m N h x * u * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2)`. Establish `hv1 : colEl k m N h x * u * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 1)` using `Subgroup.mul_mem _ (Subgroup.mul_mem _ (colEl_mem_derUnip' h x) hu1) (Subgroup.inv_mem _ (colEl_mem_derUnip' h x))`. Establish `A` using `(mem_derUnip_iff _).mp hv1`. Rewrite using `[mem_derUnip_iff]`. Use `⟨A.1, fun i j hj => ?_⟩` and prove the remaining obligations.

Rewrite using `[hv i j, hA i j hj]`. Distinguish the cases in `hjc : j = cIdx h`. Substitute `hjc` using the available equality. Rewrite using `[if_pos rfl, Matrix.one_apply_eq, mul_one, padV_neg, Pi.neg_apply, add_neg_cancel_right]`. Rewrite using `[if_neg hjc, Matrix.one_apply_ne (fun e => hjc e.symm), mul_zero, add_zero, add_zero]`.

Use `⟨hmem, ?_⟩` and prove the remaining obligations. Rewrite using `[lvlChar_apply, lvlChar_apply]`. Use `congr 2`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `p hp`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp`. Use `show ((colEl k m N h x * u * (colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 = (u : Matrix (Fin N) (Fin N) k) p.1 p.2`. Establish `hpc : p.2 ≠ cIdx h` using `fun e => by`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [cIdx] at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hv, if_neg hpc, add_zero, Units.val_mul, colEl_mul_apply, padV_of_ge h _ _ (by omega), zero_mul, add_zero]`.
-/
theorem colEl_conj_derUnip' (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k)
    (u' : derUnip k N (m + 2)) :
    ∃ hm : colEl k m N h x * (u' : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2),
      lvlChar k ψ N (m + 2) ⟨_, hm⟩ = lvlChar k ψ N (m + 2) u' := by
  obtain ⟨u, hu⟩ := u'
  have B := (mem_derUnip_iff u).mp hu
  have hu1 : u ∈ derUnip k N (m + 1) := derUnip_anti (by omega) hu
  have hcne : ∀ l : Fin N, (l : ℕ) < m + 1 → cIdx h ≠ l := fun l hl e => by
    have := congrArg Fin.val e
    simp only [cIdx] at this
    omega
  have hA : ∀ i l : Fin N, (l : ℕ) < m + 2 →
      ((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i l =
        (1 : Matrix (Fin N) (Fin N) k) i l + padV h x i * (1 : Matrix (Fin N) (Fin N) k) (cIdx h) l := by
    intro i l hl
    rw [Units.val_mul, colEl_mul_apply, B.2 i l hl, B.2 (cIdx h) l hl]
  have hmv : ∀ i, (((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) *ᵥ padV h (-x)) i =
      padV h (-x) i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · by_cases hi : (i : ℕ) < m + 1
      · rw [hA i i (by omega), Matrix.one_apply_eq, Matrix.one_apply_ne (hcne i hi), mul_zero, add_zero,
          one_mul]
      · rw [padV_of_ge h _ i (by omega), mul_zero]
    · intro l _ hli
      by_cases hl : (l : ℕ) < m + 1
      · rw [hA i l (by omega), Matrix.one_apply_ne (Ne.symm hli), Matrix.one_apply_ne (hcne l hl), mul_zero,
          add_zero, zero_mul]
      · rw [padV_of_ge h _ l (by omega), mul_zero]
    · simp
  have hv : ∀ i j : Fin N,
      ((colEl k m N h x * u * (colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
        ((colEl k m N h x * u : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j +
          if j = cIdx h then padV h (-x) i else 0 := by
    intro i j
    rw [colEl_inv, Units.val_mul, mul_colEl_apply, hmv]
  have hmem : colEl k m N h x * u * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2) := by
    have hv1 : colEl k m N h x * u * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 1) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (colEl_mem_derUnip' h x) hu1)
        (Subgroup.inv_mem _ (colEl_mem_derUnip' h x))
    have A := (mem_derUnip_iff _).mp hv1
    rw [mem_derUnip_iff]
    refine ⟨A.1, fun i j hj => ?_⟩
    rw [hv i j, hA i j hj]
    by_cases hjc : j = cIdx h
    · subst hjc
      rw [if_pos rfl, Matrix.one_apply_eq, mul_one, padV_neg, Pi.neg_apply, add_neg_cancel_right]
    · rw [if_neg hjc, Matrix.one_apply_ne (fun e => hjc e.symm), mul_zero, add_zero, add_zero]
  refine ⟨hmem, ?_⟩
  rw [lvlChar_apply, lvlChar_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  show ((colEl k m N h x * u * (colEl k m N h x)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) p.1 p.2 =
    (u : Matrix (Fin N) (Fin N) k) p.1 p.2
  have hpc : p.2 ≠ cIdx h := fun e => by
    have := congrArg Fin.val e
    simp only [cIdx] at this
    omega
  rw [hv, if_neg hpc, add_zero, Units.val_mul, colEl_mul_apply, padV_of_ge h _ _ (by omega), zero_mul,
    add_zero]

end Glue

open Glue

/- English proof (translation)
Conclude with `Glue.colEl_add' h x y`.
-/
theorem colEl_add {m N : ℕ} (h : m + 2 ≤ N) (x y : Fin (m + 1) → k) :
    colEl k m N h (x + y) = colEl k m N h x * colEl k m N h y := by
  exact Glue.colEl_add' h x y

/- English proof (translation)
Conclude with `Glue.colEl_zero' h`.
-/
theorem colEl_zero {m N : ℕ} (h : m + 2 ≤ N) : colEl k m N h 0 = 1 := by
  exact Glue.colEl_zero' h

/- English proof (translation)
Conclude with `Glue.continuous_colEl' h`.
-/
theorem continuous_colEl {m N : ℕ} (h : m + 2 ≤ N) : Continuous (colEl k m N h) := by
  exact Glue.continuous_colEl' h

/- English proof (translation)
Conclude with `Glue.continuous_blkAt' n N h`.
-/
theorem continuous_blkAt (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  exact Glue.continuous_blkAt' n N h

/- English proof (translation)
Conclude with `Glue.blkAt_glEmb' h g`.
-/
theorem blkAt_glEmb {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) :
    blkAt k (m + 2) N h (glEmb k (m + 1) g) = blkAt k (m + 1) N (by omega) g := by
  exact Glue.blkAt_glEmb' h g

/- English proof (translation)
Conclude with `Glue.det_glEmb' n g`.
-/
theorem det_glEmb (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (glEmb k n g) = Matrix.GeneralLinearGroup.det g := by
  exact Glue.det_glEmb' n g

/- English proof (translation)
Conclude with `Glue.det_unip' n x`.
-/
theorem det_unip (n : ℕ) (x : Multiplicative (Fin n → k)) : Matrix.GeneralLinearGroup.det (unip k n x) = 1 := by
  exact Glue.det_unip' n x

/- English proof (translation)
Conclude with `Glue.blkAt_conj_colEl' h g x`.
-/
theorem blkAt_conj_colEl {m N : ℕ} (h : m + 2 ≤ N) (g : GL (Fin (m + 1)) k) (x : Fin (m + 1) → k) :
    blkAt k (m + 1) N (by omega) g * colEl k m N h x * (blkAt k (m + 1) N (by omega) g)⁻¹ =
      colEl k m N h ((g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) *ᵥ x) := by
  exact Glue.blkAt_conj_colEl' h g x

/- English proof (translation)
Conclude with `Glue.scalAt_conj_colEl' h z x`.
-/
theorem scalAt_conj_colEl {m N : ℕ} (h : m + 2 ≤ N) (z : kˣ) (x : Fin (m + 1) → k) :
    scalAt k (m + 1) N (by omega) z * colEl k m N h x * (scalAt k (m + 1) N (by omega) z)⁻¹ =
      colEl k m N h ((z : k) • x) := by
  exact Glue.scalAt_conj_colEl' h z x

/- English proof (translation)
Conclude with `Glue.colEl_mem_derUnip' h x`.
-/
theorem colEl_mem_derUnip {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) : colEl k m N h x ∈ derUnip k N (m + 1) := by
  exact Glue.colEl_mem_derUnip' h x

/- English proof (translation)
Conclude with `Glue.lvlChar_colEl' ψ h x`.
-/
theorem lvlChar_colEl (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k) :
    lvlChar k ψ N (m + 1) ⟨colEl k m N h x, colEl_mem_derUnip h x⟩ = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) := by
  exact Glue.lvlChar_colEl' ψ h x

/- English proof (translation)
Conclude with `Glue.derUnip_decomp' ψ h u`.
-/
theorem derUnip_decomp (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (u : derUnip k N (m + 1)) :
    ∃ (x : Fin (m + 1) → k) (u' : derUnip k N (m + 2)), (u : GL (Fin N) k) = colEl k m N h x * u' ∧
      lvlChar k ψ N (m + 1) u = Circle.toUnits (ψ (xi0 k m ⬝ᵥ x)) * lvlChar k ψ N (m + 2) u' := by
  exact Glue.derUnip_decomp' ψ h u

/- English proof (translation)
Conclude with `Glue.colEl_conj_derUnip' ψ h x u'`.
-/
theorem colEl_conj_derUnip (ψ : AddChar k Circle) {m N : ℕ} (h : m + 2 ≤ N) (x : Fin (m + 1) → k)
    (u' : derUnip k N (m + 2)) :
    ∃ hm : colEl k m N h x * (u' : GL (Fin N) k) * (colEl k m N h x)⁻¹ ∈ derUnip k N (m + 2),
      lvlChar k ψ N (m + 2) ⟨_, hm⟩ = lvlChar k ψ N (m + 2) u' := by
  exact Glue.colEl_conj_derUnip' ψ h x u'

/- English proof (translation)
Conclude with `Glue.scalAt_comm_blkAt' h z g`.
-/
theorem scalAt_comm_blkAt {m N : ℕ} (h : m + 1 ≤ N) (z : kˣ) (g : GL (Fin (m + 1)) k) :
    scalAt k (m + 1) N h z * blkAt k (m + 1) N h g = blkAt k (m + 1) N h g * scalAt k (m + 1) N h z := by
  exact Glue.scalAt_comm_blkAt' h z g

end PositivityTheory.RgUd.Form.ColumnElementGluing
