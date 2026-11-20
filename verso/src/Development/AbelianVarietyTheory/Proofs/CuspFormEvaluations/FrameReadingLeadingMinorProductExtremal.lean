import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.TotalDegreeEqOfMemHarmA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameReadHw

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.FrameRead
open scoped Classical

section Alg

variable {R : Type} [CommRing R]

def PM (x y : R) : Prop := ∃ ε : ℤˣ, x = ((ε : ℤ) : R) * y

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, by simp⟩`.
-/
theorem PM.rfl' (x : R) : PM x x := ⟨1, by simp⟩

/- English proof (translation)
Take `⟨e, rfl⟩` from `h`. Take `⟨e', rfl⟩` from `h'`. Conclude with `⟨e * e', by push_cast; ring⟩`.
-/
theorem PM.mul {x y x' y' : R} (h : PM x y) (h' : PM x' y') : PM (x * x') (y * y') := by
  obtain ⟨e, rfl⟩ := h
  obtain ⟨e', rfl⟩ := h'
  exact ⟨e * e', by push_cast; ring⟩

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using PM.rfl' (1 : R)`. Consider the case `succ k ih => rw [pow_succ, pow_succ]`. Conclude with `ih.mul h`.
-/
theorem PM.pow {x y : R} (h : PM x y) (k : ℕ) : PM (x ^ k) (y ^ k) := by
  induction k with
  | zero => simpa using PM.rfl' (1 : R)
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul h

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using PM.rfl' (1 : R)`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `(h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))`.
-/
theorem PM.prod {ι : Type} (S : Finset ι) {f g : ι → R} (h : ∀ i ∈ S, PM (f i) (g i)) :
    PM (∏ i ∈ S, f i) (∏ i ∈ S, g i) := by
  induction S using Finset.induction_on with
  | empty => simpa using PM.rfl' (1 : R)
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

/- English proof (translation)
Establish `h` using `Matrix.mul_adjugate M`. Use `set Y := M.adjugate`. Establish `key : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 1 * Y = Matrix.fromBlocks (M.det • (1 : Matrix α α R)) 0 Y.toBlocks₂₁ Y.toBlocks₂₂`. Use extensionality with `i j`. Break down `i with i | i` into its components or cases.

Use `congrFun (congrFun h (.inl i)) j` as an intermediate fact. Rewrite `this`, the goal using `[Matrix.mul_apply]`. Rewrite `this`, the goal using `[Fintype.sum_sum_type]`. Apply the tactic sequence `rcases j with j | j <;>`. Simplify `this` using `[Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.one_apply]`.

Rewrite using `[Matrix.mul_apply, Fintype.sum_sum_type]`. Apply the tactic sequence `rcases j with j | j <;>`. Simplify using `[Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]`. Use `congrArg Matrix.det key` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul]`.

Simplify using `using this`.
-/
theorem jacobi_blocks {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Matrix (α ⊕ β) (α ⊕ β) R) :
    M.toBlocks₁₁.det * M.adjugate.det = M.det ^ Fintype.card α * M.adjugate.toBlocks₂₂.det := by
  have h := Matrix.mul_adjugate M
  set Y := M.adjugate
  have key : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 1 * Y =
      Matrix.fromBlocks (M.det • (1 : Matrix α α R)) 0 Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    ext i j
    rcases i with i | i
    · have := congrFun (congrFun h (.inl i)) j
      rw [Matrix.mul_apply] at this ⊢
      rw [Fintype.sum_sum_type] at this ⊢
      rcases j with j | j <;>
        simpa [Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.one_apply] using this
    · rw [Matrix.mul_apply, Fintype.sum_sum_type]
      rcases j with j | j <;>
        simp [Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.one_apply]
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_smul] at this
  simpa using this

def lead {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  if h : k ≤ n then (Matrix.of fun s b : Fin k => M (Fin.castLE h s) (Fin.castLE h b)).det else 0

/- English proof (translation)
Simplify using `[lead]`.
-/
theorem lead_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : lead M 0 = 1 := by simp [lead]

/- English proof (translation)
Simplify using `only [lead, le_refl, dif_pos]`. Both sides reduce to the same expression.
-/
theorem lead_self {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : lead M n = M.det := by
  simp only [lead, le_refl, dif_pos]; rfl

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, n = j + (k + 1)` from `⟨n - (k + 1), by omega⟩`. Establish `hj` using `jacobi_blocks (M.submatrix (finSumFinEquiv (m := j) (n := k + 1)) finSumFinEquiv)`. Rewrite `hj` using `[Matrix.adjugate_submatrix_equiv_self, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self, Matrix.det_adjugate]`. Establish `e1 : (M.submatrix (finSumFinEquiv (m` using `j) (n := k + 1)) finSumFinEquiv).toBlocks₁₁.det = lead M (j + (k + 1) - 1 - k) := by`. Establish `: j + (k + 1) - 1 - k = j` using `by omega`.

Rewrite using `[this, lead, dif_pos (by omega)]`. Both sides reduce to the same expression. Establish `e2 : (Matrix.of fun s b => M.adjugate (r s) (c b)) = ((M.adjugate.submatrix (finSumFinEquiv (m` using `j) (n := k + 1)) finSumFinEquiv).toBlocks₂₂).submatrix Fin.revPerm id := by`. Use extensionality with `s b`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.toBlocks₂₂, finSumFinEquiv_apply_right, id]`.

Apply the tactic sequence `congr 1 <;> apply Fin.ext`. Use `s.isLt` as an intermediate fact. Simplify using `[hr, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Simplify using `[hc]`.

Rewrite using `[e2, Matrix.det_permute]`. Use `⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (k + 1))), ?_⟩` and prove the remaining obligations. Use `congr 1`. Rewrite `hj` using `[e1]`. Simplify using `only [Fintype.card_fin] at hj`.

Apply `mul_left_cancel₀ (pow_ne_zero j hM)` to reduce the goal to its premises. Rewrite using `[← hj, show j + (k + 1) - 1 = j + k by omega, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacobi_rev [IsDomain R] {n k : ℕ} (h : k + 1 ≤ n) (M : Matrix (Fin n) (Fin n) R) (hM : M.det ≠ 0)
    (r c : Fin (k + 1) → Fin n) (hr : ∀ s, (r s : ℕ) = n - 1 - s) (hc : ∀ b, (c b : ℕ) = n - (k + 1) + b) :
    PM (Matrix.of fun s b => M.adjugate (r s) (c b)).det (M.det ^ k * lead M (n - 1 - k)) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + (k + 1) := ⟨n - (k + 1), by omega⟩
  have hj := jacobi_blocks (M.submatrix (finSumFinEquiv (m := j) (n := k + 1)) finSumFinEquiv)
  rw [Matrix.adjugate_submatrix_equiv_self, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self,
    Matrix.det_adjugate] at hj
  have e1 : (M.submatrix (finSumFinEquiv (m := j) (n := k + 1)) finSumFinEquiv).toBlocks₁₁.det =
      lead M (j + (k + 1) - 1 - k) := by
    have : j + (k + 1) - 1 - k = j := by omega
    rw [this, lead, dif_pos (by omega)]
    rfl
  have e2 : (Matrix.of fun s b => M.adjugate (r s) (c b)) =
      ((M.adjugate.submatrix (finSumFinEquiv (m := j) (n := k + 1)) finSumFinEquiv).toBlocks₂₂).submatrix
        Fin.revPerm id := by
    ext s b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.toBlocks₂₂, finSumFinEquiv_apply_right, id]
    congr 1 <;> apply Fin.ext
    · have := s.isLt
      simp [hr, Fin.val_rev]; omega
    · simp [hc]
  rw [e2, Matrix.det_permute]
  refine ⟨Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (k + 1))), ?_⟩
  congr 1
  rw [e1] at hj
  simp only [Fintype.card_fin] at hj
  apply mul_left_cancel₀ (pow_ne_zero j hM)
  rw [← hj, show j + (k + 1) - 1 = j + k by omega, pow_add]
  ring

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ _ (m + 1), ← ih]`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (hB (Nat.le_succ m))`.

Rewrite using `[hd, Nat.succ_eq_add_one, Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_mul_step (B : ℕ → ℕ) (hB : Antitone B) (m : ℕ) :
    ∑ i ∈ Finset.range m, i * (B i - B (i + 1)) + B 0 + m * B m = ∑ i ∈ Finset.range (m + 1), B i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ _ (m + 1), ← ih]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hB (Nat.le_succ m))
    rw [hd, Nat.succ_eq_add_one, Nat.add_sub_cancel_left]
    ring

/- English proof (translation)
Break down `n with _ | m` into its components or cases. Simplify using `[hL]`. Establish `hd : lam.detShift = s + A m - B 0`. Rewrite using `[DomWeight.detShift, dif_pos (Nat.succ_pos m), hw]`. Simplify using the standard rewrite rules.

Establish `hs` using `sum_mul_step B hB (m + 1)`. Rewrite `hs` using `[Finset.sum_range_succ _ (m + 1), hBn]`. Establish `he : (((∑ i ∈ Finset.range (m + 1), B i : ℕ) : ℤ) + lam.detShift - s).toNat = ∑ i ∈ Finset.range (m + 1), i * (B i - B (i + 1)) + A m`. Rewrite using `[hd]`. Use linear arithmetic over natural numbers and integers.

Establish `hlast : lam.natW (Fin.last m) - Formalism.GradedWeylDivisibility.nuNext lam.natW (Fin.last m) = 0`. Establish `: lam.natW (Fin.last m) = 0`. Rewrite using `[DomWeight.natW, hd, hw]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish `hstep : ∀ i : Fin m, lam.natW i.castSucc - Formalism.GradedWeylDivisibility.nuNext lam.natW i.castSucc = (A i - A (i + 1)) + (B (m - 1 - i) - B (m - 1 - i + 1))`. Introduce `i`. Establish `hi` using `i.isLt`. Rewrite using `[Formalism.GradedWeylDivisibility.nuNext, dif_pos (by simpa using hi)]`. Simplify using `only [DomWeight.natW, hd, hw, Fin.val_castSucc]`.

Establish `e1 : m + 1 - 1 - (i : ℕ) = m - 1 - i + 1` using `by omega`. Establish `e2 : m + 1 - 1 - ((i : ℕ) + 1) = m - 1 - i` using `by omega`. Rewrite using `[e1, e2]`. Establish `h1` using `hA (Nat.le_succ i)`. Establish `h2` using `hA (show (i : ℕ) + 1 ≤ m by omega)`.

Establish `h3` using `hB (Nat.le_succ (m - 1 - i))`. Establish `h4` using `hB (Nat.zero_le (m - 1 - i))`. Simplify using `only [Nat.succ_eq_add_one] at h1 h3`. Use linear arithmetic over natural numbers and integers. Rewrite using `[he, Fin.prod_univ_castSucc, hlast]`.

Simplify using `only [hstep, Fin.val_castSucc]`. Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => L (i + 1) ^ ((A i - A (i + 1)) + (B (m - 1 - i) - B (m - 1 - i + 1)))) m]`. Simplify using `only [mul_pow, pow_add, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]`. Rewrite using `[Finset.prod_range_succ (fun i => L (i + 1) ^ (A i - A (i + 1))), hAn, Finset.prod_range_succ (fun i => L (m + 1 - 1 - i) ^ (B i - B (i + 1))), show m + 1 - 1 - m = 0 by omega, hL, ← Finset.prod_range_reflect (fun i => L (m + 1 - 1 - i) ^ (B i - B (i + 1)))]`. Establish `: ∏ j ∈ Finset.range m, L (m + 1 - 1 - (m - 1 - j)) ^ (B (m - 1 - j) - B (m - 1 - j + 1)) = ∏ j ∈ Finset.range m, L (j + 1) ^ (B (m - 1 - j) - B (m - 1 - j + 1))`.

Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hj` as an intermediate fact. Rewrite using `[show m + 1 - 1 - (m - 1 - j) = j + 1 by omega]`. Rewrite using `[this]`. Simplify using `only [Nat.sub_zero, one_pow, pow_zero]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_steps {n : ℕ} (L : ℕ → R) (hL : L 0 = 1) (A B : ℕ → ℕ) (hA : Antitone A) (hB : Antitone B)
    (hAn : A n = 0) (hBn : B n = 0) (s : ℤ) (lam : DomWeight n)
    (hw : ∀ i : Fin n, lam.w i = s + A i - B (n - 1 - i)) :
    (∏ i ∈ Finset.range n, L (i + 1) ^ (A i - A (i + 1))) *
      ∏ i ∈ Finset.range n, (L n ^ i * L (n - 1 - i)) ^ (B i - B (i + 1)) =
    L n ^ (((∑ i ∈ Finset.range n, B i : ℕ) : ℤ) + lam.detShift - s).toNat *
      ∏ i : Fin n, L (i + 1) ^ (lam.natW i - Formalism.GradedWeylDivisibility.nuNext lam.natW i) := by
  rcases n with _ | m
  · simp [hL]
  have hd : lam.detShift = s + A m - B 0 := by
    rw [DomWeight.detShift, dif_pos (Nat.succ_pos m), hw]; simp
  have hs := sum_mul_step B hB (m + 1)
  rw [Finset.sum_range_succ _ (m + 1), hBn] at hs
  have he : (((∑ i ∈ Finset.range (m + 1), B i : ℕ) : ℤ) + lam.detShift - s).toNat =
      ∑ i ∈ Finset.range (m + 1), i * (B i - B (i + 1)) + A m := by
    rw [hd]; omega
  have hlast : lam.natW (Fin.last m) - Formalism.GradedWeylDivisibility.nuNext lam.natW (Fin.last m) = 0 := by
    have : lam.natW (Fin.last m) = 0 := by
      rw [DomWeight.natW, hd, hw]; simp
    omega
  have hstep : ∀ i : Fin m, lam.natW i.castSucc - Formalism.GradedWeylDivisibility.nuNext lam.natW i.castSucc =
      (A i - A (i + 1)) + (B (m - 1 - i) - B (m - 1 - i + 1)) := by
    intro i
    have hi := i.isLt
    rw [Formalism.GradedWeylDivisibility.nuNext, dif_pos (by simpa using hi)]
    simp only [DomWeight.natW, hd, hw, Fin.val_castSucc]
    have e1 : m + 1 - 1 - (i : ℕ) = m - 1 - i + 1 := by omega
    have e2 : m + 1 - 1 - ((i : ℕ) + 1) = m - 1 - i := by omega
    rw [e1, e2]
    have h1 := hA (Nat.le_succ i)
    have h2 := hA (show (i : ℕ) + 1 ≤ m by omega)
    have h3 := hB (Nat.le_succ (m - 1 - i))
    have h4 := hB (Nat.zero_le (m - 1 - i))
    simp only [Nat.succ_eq_add_one] at h1 h3
    omega
  rw [he, Fin.prod_univ_castSucc, hlast]
  simp only [hstep, Fin.val_castSucc]
  rw [Fin.prod_univ_eq_prod_range (fun i => L (i + 1) ^ ((A i - A (i + 1)) + (B (m - 1 - i) - B (m - 1 - i + 1)))) m]
  simp only [mul_pow, pow_add, Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_range_succ (fun i => L (i + 1) ^ (A i - A (i + 1))), hAn,
    Finset.prod_range_succ (fun i => L (m + 1 - 1 - i) ^ (B i - B (i + 1))),
    show m + 1 - 1 - m = 0 by omega, hL,
    ← Finset.prod_range_reflect (fun i => L (m + 1 - 1 - i) ^ (B i - B (i + 1)))]
  have : ∏ j ∈ Finset.range m, L (m + 1 - 1 - (m - 1 - j)) ^ (B (m - 1 - j) - B (m - 1 - j + 1)) =
      ∏ j ∈ Finset.range m, L (j + 1) ^ (B (m - 1 - j) - B (m - 1 - j + 1)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have := Finset.mem_range.1 hj
    rw [show m + 1 - 1 - (m - 1 - j) = j + 1 by omega]
  rw [this]
  simp only [Nat.sub_zero, one_pow, pow_zero]
  ring

end Alg

def cut (a : ℕ → ℕ) (m i : ℕ) : ℕ := if i < m then a i else 0

/- English proof (translation)
Introduce `i j hij`. Use `ha hij` as an intermediate fact. Simplify using `only [cut]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem cut_antitone {a : ℕ → ℕ} (ha : Antitone a) (m : ℕ) : Antitone (cut a m) := by
  intro i j hij
  have := ha hij
  simp only [cut]
  split_ifs <;> omega

/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun i => f i ^ (a i - if i + 1 < m then a (i + 1) else 0)) m, ← Finset.prod_subset (Finset.range_subset_range.2 h)]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [cut, Finset.mem_range.1 hi, if_true]`. Introduce `i _ hi`. Establish `: ¬ i < m` using `by simpa using hi`.

Simplify using `[cut, this]`.
-/
theorem prod_cut {R : Type} [CommRing R] (f : ℕ → R) (a : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    ∏ i : Fin m, f i ^ (a i - if (i : ℕ) + 1 < m then a (i + 1) else 0) =
      ∏ i ∈ Finset.range n, f i ^ (cut a m i - cut a m (i + 1)) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => f i ^ (a i - if i + 1 < m then a (i + 1) else 0)) m,
    ← Finset.prod_subset (Finset.range_subset_range.2 h)]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only [cut, Finset.mem_range.1 hi, if_true]
  · intro i _ hi
    have : ¬ i < m := by simpa using hi
    simp [cut, this]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range a m, ← Finset.sum_subset (Finset.range_subset_range.2 h)]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Simplify using `only [cut, Finset.mem_range.1 hi, if_true]`. Introduce `i _ hi`. Establish `: ¬ i < m` using `by simpa using hi`.

Simplify using `[cut, this]`.
-/
theorem sum_cut (a : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) : ∑ i : Fin m, a i = ∑ i ∈ Finset.range n, cut a m i := by
  rw [Fin.sum_univ_eq_sum_range a m, ← Finset.sum_subset (Finset.range_subset_range.2 h)]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [cut, Finset.mem_range.1 hi, if_true]
  · intro i _ hi
    have : ¬ i < m := by simpa using hi
    simp [cut, this]

/- English proof (translation)
Introduce `h`. Use `congrArg (MvPolynomial.eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2) h` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Establish `e : (MvPolynomial.eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2).mapMatrix (gen K n t) = 1`. Use extensionality with `i j`.

Simplify using `[gen]`. Rewrite `this` using `[e]`. Simplify using `at this`.
-/
theorem gen_det_ne_zero {Ix : Type} (K : Type) [Field K] (n : ℕ) (t : Ix) : (gen K n t).det ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval fun v : Ix × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2) h
  rw [RingHom.map_det] at this
  have e : (MvPolynomial.eval fun v : Ix × Fin n × Fin n =>
      (1 : Matrix (Fin n) (Fin n) K) v.2.1 v.2.2).mapMatrix (gen K n t) = 1 := by
    ext i j
    simp [gen]
  rw [e] at this
  simp at this

/- English proof (translation)
Rewrite using `[extremal, Formalism.GradedWeylDivisibility.hw, map_prod]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, lead, dif_pos (by omega)]`. Use `congr 2`. Use extensionality with `s b`.

Simplify using `[Formalism.GradedWeylDivisibility.blockEmb, gen]`.
-/
theorem blockEmb_extremal {Ix : Type} (K : Type) [Field K] {n : ℕ} (t : Ix) (lam : DomWeight n) :
    Formalism.GradedWeylDivisibility.blockEmb K t (extremal K n lam) =
      ∏ i : Fin n, lead (gen K n t) (i + 1) ^ (lam.natW i - Formalism.GradedWeylDivisibility.nuNext lam.natW i) := by
  rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, lead, dif_pos (by omega)]
  congr 2
  ext s b
  simp [Formalism.GradedWeylDivisibility.blockEmb, gen]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ} {Ix : Type} [Fintype Ix]
  {pl : Ix → (E →+* ℂ)}

/- English proof (translation)
Rewrite using `[GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff, not_not]`. Conclude with `(h.2 _).2 ⟨t, rfl⟩`.
-/
theorem not_inPsi_conj (h : IsEnum H pl) (t : Ix) : ¬ InPsi H (ComplexEmbedding.conjugate (pl t)) := by
  rw [GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff, not_not]
  exact (h.2 _).2 ⟨t, rfl⟩

/- English proof (translation)
Establish `cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ` using `fun τ => star_star τ`. Establish `hb : Function.Bijective (Sum.elim pl fun t => ComplexEmbedding.conjugate (pl t))`. Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab`. Rewrite using `[h.1 hab]`.

Conclude with `absurd (hab ▸ (h.2 _).2 ⟨a, rfl⟩) (not_inPsi_conj h b)`. Conclude with `absurd (hab ▸ (h.2 _).2 ⟨b, rfl⟩) (not_inPsi_conj h a)`. Use `congrArg ComplexEmbedding.conjugate hab` as an intermediate fact. Rewrite `this` using `[cc, cc]`. Rewrite using `[h.1 this]`.

Introduce `τ`. Distinguish the cases in `hτ : InPsi H τ`. Take `⟨t, rfl⟩` from `(h.2 τ).1 hτ`. Conclude with `⟨.inl t, rfl⟩`. Take `⟨t, ht⟩` from `(h.2 _).1 ((GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff τ).2 hτ)`.

Conclude with `⟨.inr t, by simp only [Sum.elim_inr]; rw [ht, cc]⟩`. Rewrite using `[← hb.prod_comp f, Fintype.prod_sum_type, Finset.prod_mul_distrib]`. Both sides reduce to the same expression.
-/
theorem prod_types {R : Type} [CommMonoid R] (h : IsEnum H pl) (f : (E →+* ℂ) → R) :
    ∏ σ, f σ = ∏ t, (f (pl t) * f (ComplexEmbedding.conjugate (pl t))) := by
  have cc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => star_star τ
  have hb : Function.Bijective (Sum.elim pl fun t => ComplexEmbedding.conjugate (pl t)) := by
    constructor
    · rintro (a | a) (b | b) hab <;> simp only [Sum.elim_inl, Sum.elim_inr] at hab
      · rw [h.1 hab]
      · exact absurd (hab ▸ (h.2 _).2 ⟨a, rfl⟩) (not_inPsi_conj h b)
      · exact absurd (hab ▸ (h.2 _).2 ⟨b, rfl⟩) (not_inPsi_conj h a)
      · have := congrArg ComplexEmbedding.conjugate hab
        rw [cc, cc] at this
        rw [h.1 this]
    · intro τ
      by_cases hτ : InPsi H τ
      · obtain ⟨t, rfl⟩ := (h.2 τ).1 hτ
        exact ⟨.inl t, rfl⟩
      · obtain ⟨t, ht⟩ := (h.2 _).1 ((GlobalTheory.ThetaRuleCheck.inPsi_conjugate_iff τ).2 hτ)
        exact ⟨.inr t, by simp only [Sum.elim_inr]; rw [ht, cc]⟩
  rw [← hb.prod_comp f, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  rfl

/- English proof (translation)
Establish `hex : ∃ t', pl t' = pl t` using `⟨t, rfl⟩`. Rewrite using `[cof, aeval_X, dif_pos hi, dif_pos hex, h.1 hex.choose_spec]`.
-/
theorem cof_X_type (h : IsEnum H pl) (R : Type) [CommRing R] (t : Ix) (i : Fin (Dw.mult (pl t))) (b : Fin n)
    (hi : (i : ℕ) < n) : cof Dw pl R n (X ⟨pl t, i, b⟩) = gen R n t b ⟨i, hi⟩ := by
  have hex : ∃ t', pl t' = pl t := ⟨t, rfl⟩
  rw [cof, aeval_X, dif_pos hi, dif_pos hex, h.1 hex.choose_spec]

/- English proof (translation)
Establish `hno : ¬ ∃ t', pl t' = ComplexEmbedding.conjugate (pl t)` using `fun hh => not_inPsi_conj h t ((h.2 _).2 hh)`. Establish `hex : ∃ t', ComplexEmbedding.conjugate (pl t') = ComplexEmbedding.conjugate (pl t)` using `⟨t, rfl⟩`. Establish `: hex.choose = t` using `h.1 ((ComplexEmbedding.involutive_conjugate E).injective hex.choose_spec)`. Rewrite using `[cof, aeval_X, dif_pos hi, dif_neg hno, dif_pos hex, this]`.
-/
theorem cof_X_conj (h : IsEnum H pl) (R : Type) [CommRing R] (t : Ix)
    (i : Fin (Dw.mult (ComplexEmbedding.conjugate (pl t)))) (b : Fin n) (hi : (i : ℕ) < n) :
    cof Dw pl R n (X ⟨ComplexEmbedding.conjugate (pl t), i, b⟩) = (gen R n t).adjugate (Fin.rev ⟨i, hi⟩) b := by
  have hno : ¬ ∃ t', pl t' = ComplexEmbedding.conjugate (pl t) := fun hh => not_inPsi_conj h t ((h.2 _).2 hh)
  have hex : ∃ t', ComplexEmbedding.conjugate (pl t') = ComplexEmbedding.conjugate (pl t) := ⟨t, rfl⟩
  have : hex.choose = t := h.1 ((ComplexEmbedding.involutive_conjugate E).injective hex.choose_spec)
  rw [cof, aeval_X, dif_pos hi, dif_neg hno, dif_pos hex, this]

/- English proof (translation)
Apply the tactic sequence `rw [Datum.mult]; split_ifs <;> omega`.
-/
theorem mult_le (hn : Dw.p + Dw.q ≤ n) (σ : E →+* ℂ) : Dw.mult σ ≤ n := by
  rw [Datum.mult]; split_ifs <;> omega

/- English proof (translation)
Introduce `E _ _ _ H Dw n Ix _ pl h hn l c a s lam ha hw`. It suffices to establish `hs : PM (cof Dw pl c.F n (pG (Dw` using `Dw) c a n)) (detFac Dw pl c.F a s lam * ten fun t => extremal c.F n (lam t)) by`. Take `⟨ε, hε⟩` from `hs`. Use `⟨ε, ?_⟩` and prove the remaining obligations. Rewrite using `[hε, smul_eq_C_mul, map_intCast]`.

Rewrite using `[pG, map_prod, prod_types h, detFac, ten, ← Finset.prod_mul_distrib]`. Use `PM.prod _ fun t _ => ?_` and prove the remaining obligations. Establish `hp` using `mult_le Dw hn (pl t)`. Establish `hq` using `mult_le Dw hn (ComplexEmbedding.conjugate (pl t))`. Establish `key` using `prod_steps (lead (gen c.F n t)) (lead_zero _) (cut (fun i => a (pl t, i)) (Dw.mult (pl t))) (cut (fun i => a (ComplexEmbedding.conjugate (pl t), i)) (Dw.mult (ComplexEmbedding.conjugate (pl t)))) (cut_antitone (ha _) _) (cut_antitone (ha _) _) (by simp [cut, hp]) (by simp [cut, h …`.

Introduce `i`. Rewrite using `[hw t i, Fin.val_rev, show n - (i + 1) = n - 1 - i by omega]`. Simplify using `only [cut]`. Use `push_cast`. Use the proof step `rfl)`.

Rewrite `key` using `[← sum_cut _ hq, ← prod_cut (fun i => lead (gen c.F n t) (i + 1)) _ hp, ← prod_cut (fun i => lead (gen c.F n t) n ^ i * lead (gen c.F n t) (n - 1 - i)) _ hq, lead_self]`. Rewrite using `[blockEmb_extremal, degC, ← key, map_prod, map_prod]`. Use `PM.mul (PM.prod _ fun i _ => ?_) (PM.prod _ fun i _ => ?_)` and prove the remaining obligations. Establish `hi : (i : ℕ) + 1 ≤ n` using `by have := i.isLt; omega`. Rewrite using `[map_pow, dif_pos hi, if_pos ((h.2 _).2 ⟨t, rfl⟩)]`.

Use `PM.pow ?_ _` and prove the remaining obligations. Rewrite using `[minorPolynomial, AlgHom.map_det, lead, dif_pos hi, ← Matrix.det_transpose]`. Use `PM.rfl' _ using 2` and compare the differences between its conclusion and the goal. Use extensionality with `u b : 2`. Simplify using `only [Matrix.of_apply, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]`.

Rewrite using `[cof_X_type Dw h _ _ _ _ (by have := b.isLt; simp only; omega)]`. Both sides reduce to the same expression. Establish `hi : (i : ℕ) + 1 ≤ n` using `by have := i.isLt; omega`. Rewrite using `[map_pow, dif_pos hi, if_neg (not_inPsi_conj h t)]`. Use `PM.pow ?_ _` and prove the remaining obligations.

Rewrite using `[minorPolynomial, AlgHom.map_det]`. Use `jacobi_rev hi (gen c.F n t) (gen_det_ne_zero _ _ _) (fun u => Fin.rev (Fin.castLE hi u)) (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)) (fun u => by simp [Fin.val_rev]; omega) (fun b => by simp) using 2` and compare the differences between its conclusion and the goal. Use extensionality with `u b : 2`. Simplify using `only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]`. Rewrite using `[cof_X_conj Dw h _ _ _ _ (by have := u.isLt; simp only; omega)]`.

Both sides reduce to the same expression.
-/
theorem cof_pG : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ) (s : Ix → ℤ) (lam : Ix → DomWeight n), (∀ τ, Antitone fun i => a (τ, i)) → WtIs Dw pl a s lam → ∃ ε : ℤˣ, cof Dw pl c.F n (pG (Dw := Dw) c a n) = ((ε : ℤ) : c.F) • (detFac Dw pl c.F a s lam * ten fun t => extremal c.F n (lam t)) := by
  intro E _ _ _ H Dw n Ix _ pl h hn l c a s lam ha hw
  suffices hs : PM (cof Dw pl c.F n (pG (Dw := Dw) c a n))
      (detFac Dw pl c.F a s lam * ten fun t => extremal c.F n (lam t)) by
    obtain ⟨ε, hε⟩ := hs
    refine ⟨ε, ?_⟩
    rw [hε, smul_eq_C_mul, map_intCast]
  rw [pG, map_prod, prod_types h, detFac, ten, ← Finset.prod_mul_distrib]
  refine PM.prod _ fun t _ => ?_
  have hp := mult_le Dw hn (pl t)
  have hq := mult_le Dw hn (ComplexEmbedding.conjugate (pl t))
  have key := prod_steps (lead (gen c.F n t)) (lead_zero _) (cut (fun i => a (pl t, i)) (Dw.mult (pl t)))
    (cut (fun i => a (ComplexEmbedding.conjugate (pl t), i)) (Dw.mult (ComplexEmbedding.conjugate (pl t))))
    (cut_antitone (ha _) _) (cut_antitone (ha _) _) (by simp [cut, hp]) (by simp [cut, hq]) (s t) (lam t) (by
      intro i
      rw [hw t i, Fin.val_rev, show n - (i + 1) = n - 1 - i by omega]
      simp only [cut]
      push_cast
      rfl)
  rw [← sum_cut _ hq, ← prod_cut (fun i => lead (gen c.F n t) (i + 1)) _ hp,
    ← prod_cut (fun i => lead (gen c.F n t) n ^ i * lead (gen c.F n t) (n - 1 - i)) _ hq, lead_self] at key
  rw [blockEmb_extremal, degC, ← key, map_prod, map_prod]
  refine PM.mul (PM.prod _ fun i _ => ?_) (PM.prod _ fun i _ => ?_)
  · have hi : (i : ℕ) + 1 ≤ n := by have := i.isLt; omega
    rw [map_pow, dif_pos hi, if_pos ((h.2 _).2 ⟨t, rfl⟩)]
    refine PM.pow ?_ _
    rw [minorPolynomial, AlgHom.map_det, lead, dif_pos hi, ← Matrix.det_transpose]
    convert PM.rfl' _ using 2
    ext u b : 2
    simp only [Matrix.of_apply, Matrix.transpose_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    rw [cof_X_type Dw h _ _ _ _ (by have := b.isLt; simp only; omega)]
    rfl
  · have hi : (i : ℕ) + 1 ≤ n := by have := i.isLt; omega
    rw [map_pow, dif_pos hi, if_neg (not_inPsi_conj h t)]
    refine PM.pow ?_ _
    rw [minorPolynomial, AlgHom.map_det]
    convert jacobi_rev hi (gen c.F n t) (gen_det_ne_zero _ _ _) (fun u => Fin.rev (Fin.castLE hi u))
      (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b))
      (fun u => by simp [Fin.val_rev]; omega) (fun b => by simp) using 2
    ext u b : 2
    simp only [Matrix.of_apply, AlgHom.mapMatrix_apply, Matrix.map_apply]
    rw [cof_X_conj Dw h _ _ _ _ (by have := u.isLt; simp only; omega)]
    rfl

end GlobalTheory.FrameReadHw
