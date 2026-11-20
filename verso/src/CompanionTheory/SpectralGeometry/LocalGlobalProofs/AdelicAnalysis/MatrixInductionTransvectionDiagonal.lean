import Mathlib

open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.StableRangeOne

def elem (R : Type) [CommRing R] (ι : Type) [Fintype ι] [DecidableEq ι] :
    Submonoid (Matrix ι ι R) :=
  Submonoid.closure ({T | ∃ i j c, i ≠ j ∧ T = Matrix.transvection i j c} ∪
    {T | ∃ D : ι → R, (∀ i, IsUnit (D i)) ∧ T = Matrix.diagonal D})

def rowOp {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ι) (c : ι → R) : Matrix ι ι R :=
  1 + Matrix.of fun i j => if i = k then c j else 0

def colOp {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (k : ι) (c : ι → R) : Matrix ι ι R :=
  1 + Matrix.of fun i j => if j = k then c i else 0

def Fixed {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (A : Matrix ι ι R) : Prop :=
  ∀ i j, (i ∉ s ∨ j ∉ s) → A i j = (1 : Matrix ι ι R) i j

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
The claim follows from `Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)`.
-/
lemma transvection_mem {i j : ι} (h : i ≠ j) (c : R) :
    Matrix.transvection i j c ∈ elem R ι :=
  Submonoid.subset_closure (Or.inl ⟨i, j, c, h, rfl⟩)

/- English proof (translation)
The claim follows from `Submonoid.subset_closure (Or.inr ⟨D, h, rfl⟩)`.
-/
lemma diagonal_mem {D : ι → R} (h : ∀ i, IsUnit (D i)) : Matrix.diagonal D ∈ elem R ι :=
  Submonoid.subset_closure (Or.inr ⟨D, h, rfl⟩)

/- English proof (translation)
Proceed by induction on `hA using Submonoid.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩` into its components or cases. Use `⟨Matrix.transvection i j (-c), transvection_mem h _, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.transvection_mul_transvection_same _ _ h]`.

Simplify using the standard rewrite rules. Use `⟨Matrix.diagonal (fun i => (((hD i).unit⁻¹ : Rˣ) : R)), diagonal_mem (fun i => Units.isUnit _), ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `(hD i).val_inv_mul`. Consider the case `one => exact ⟨1, one_mem _, one_mul _⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, ha, ha'⟩` from `hx`. Take `⟨b, hb, hb'⟩` from `hy`.

Conclude with `⟨b * a, mul_mem hb ha, by rw [mul_assoc, ← mul_assoc a, ha', one_mul, hb']⟩`.
-/
lemma exists_left_inv {A : Matrix ι ι R} (hA : A ∈ elem R ι) :
    ∃ B ∈ elem R ι, B * A = 1 := by
  induction hA using Submonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩
    · refine ⟨Matrix.transvection i j (-c), transvection_mem h _, ?_⟩
      rw [Matrix.transvection_mul_transvection_same _ _ h]
      simp
    · refine ⟨Matrix.diagonal (fun i => (((hD i).unit⁻¹ : Rˣ) : R)),
        diagonal_mem (fun i => Units.isUnit _), ?_⟩
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      exact (hD i).val_inv_mul
  | one => exact ⟨1, one_mem _, one_mul _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha'⟩ := hx
    obtain ⟨b, hb, hb'⟩ := hy
    exact ⟨b * a, mul_mem hb ha, by rw [mul_assoc, ← mul_assoc a, ha', one_mul, hb']⟩

/- English proof (translation)
Take `⟨B, hB, hBT⟩` from `exists_left_inv hT`. Establish `: A = B * (T * A)` using `by rw [← mul_assoc, hBT, one_mul]`. Rewrite using `[this]`. Conclude with `mul_mem hB h`.
-/
lemma mem_of_mul_left {T A : Matrix ι ι R} (hT : T ∈ elem R ι) (h : T * A ∈ elem R ι) :
    A ∈ elem R ι := by
  obtain ⟨B, hB, hBT⟩ := exists_left_inv hT
  have : A = B * (T * A) := by rw [← mul_assoc, hBT, one_mul]
  rw [this]
  exact mul_mem hB h

/- English proof (translation)
Take `⟨B, hB, hBT⟩` from `exists_left_inv hT`. Establish `hTB : T * B = 1` using `mul_eq_one_comm.mp hBT`. Establish `: A = (A * T) * B` using `by rw [mul_assoc, hTB, mul_one]`. Rewrite using `[this]`. Conclude with `mul_mem h hB`.
-/
lemma mem_of_mul_right {T A : Matrix ι ι R} (hT : T ∈ elem R ι) (h : A * T ∈ elem R ι) :
    A ∈ elem R ι := by
  obtain ⟨B, hB, hBT⟩ := exists_left_inv hT
  have hTB : T * B = 1 := mul_eq_one_comm.mp hBT
  have : A = (A * T) * B := by rw [mul_assoc, hTB, mul_one]
  rw [this]
  exact mul_mem h hB

/- English proof (translation)
Take `⟨B, _, hBA⟩` from `exists_left_inv hA`. Establish `: B.det * A.det = 1` using `by rw [← Matrix.det_mul, hBA, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)`.
-/
lemma isUnit_det_of_mem {A : Matrix ι ι R} (hA : A ∈ elem R ι) : IsUnit A.det := by
  obtain ⟨B, _, hBA⟩ := exists_left_inv hA
  have : B.det * A.det = 1 := by rw [← Matrix.det_mul, hBA, Matrix.det_one]
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact this)

/- English proof (translation)
Establish `key : ∀ t : Finset ι, k ∉ t → rowOp k (fun j => if j ∈ t then c j else 0) ∈ elem R ι`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `_`.

Establish `: rowOp k (fun j => if j ∈ (∅ : Finset ι) then c j else 0) = (1 : Matrix ι ι R)`. Use extensionality with `a b`. Simplify using `[rowOp]`. Rewrite using `[this]`. Conclude with `one_mem _`.

Consider the case `insert i t hi ih`. Introduce `hk`. Establish `hki : k ≠ i` using `fun h => hk (h ▸ Finset.mem_insert_self _ _)`. Establish `hkt : k ∉ t` using `fun h => hk (Finset.mem_insert_of_mem h)`. Establish `: rowOp k (fun j => if j ∈ insert i t then c j else 0) = rowOp k (fun j => if j ∈ t then c j else 0) * Matrix.transvection k i (c i)`.

Use extensionality with `a b`. Distinguish the cases in `hb : b = i`. Substitute `hb` using the available equality. Rewrite using `[Matrix.mul_transvection_apply_same]`. Distinguish the cases in `ha : a = k`.

Substitute `ha` using the available equality. Simplify using `[rowOp, Matrix.one_apply, hi, hki, hkt]`. Simplify using `[rowOp, Matrix.one_apply, ha]`. Rewrite using `[Matrix.mul_transvection_apply_of_ne _ _ _ _ hb]`. Simplify using `[rowOp, Finset.mem_insert, hb]`.

Rewrite using `[this]`. Conclude with `mul_mem (ih hkt) (transvection_mem hki _)`. Use `key (Finset.univ.erase k) (by simp)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using `[hc]`. Simplify using `[h]`.
-/
lemma rowOp_mem (k : ι) (c : ι → R) (hc : c k = 0) : rowOp k c ∈ elem R ι := by
  have key : ∀ t : Finset ι, k ∉ t → rowOp k (fun j => if j ∈ t then c j else 0) ∈ elem R ι := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have : rowOp k (fun j => if j ∈ (∅ : Finset ι) then c j else 0) = (1 : Matrix ι ι R) := by
        ext a b
        simp [rowOp]
      rw [this]
      exact one_mem _
    | insert i t hi ih =>
      intro hk
      have hki : k ≠ i := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkt : k ∉ t := fun h => hk (Finset.mem_insert_of_mem h)
      have : rowOp k (fun j => if j ∈ insert i t then c j else 0) =
          rowOp k (fun j => if j ∈ t then c j else 0) * Matrix.transvection k i (c i) := by
        ext a b
        by_cases hb : b = i
        · subst hb
          rw [Matrix.mul_transvection_apply_same]
          by_cases ha : a = k
          · subst ha
            simp [rowOp, Matrix.one_apply, hi, hki, hkt]
          · simp [rowOp, Matrix.one_apply, ha]
        · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hb]
          simp [rowOp, Finset.mem_insert, hb]
      rw [this]
      exact mul_mem (ih hkt) (transvection_mem hki _)
  have := key (Finset.univ.erase k) (by simp)
  convert this using 2
  funext j
  by_cases h : j = k
  · subst h; simp [hc]
  · simp [h]

/- English proof (translation)
Establish `key : ∀ t : Finset ι, k ∉ t → colOp k (fun j => if j ∈ t then c j else 0) ∈ elem R ι`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Introduce `_`.

Establish `: colOp k (fun j => if j ∈ (∅ : Finset ι) then c j else 0) = (1 : Matrix ι ι R)`. Use extensionality with `a b`. Simplify using `[colOp]`. Rewrite using `[this]`. Conclude with `one_mem _`.

Consider the case `insert i t hi ih`. Introduce `hk`. Establish `hki : k ≠ i` using `fun h => hk (h ▸ Finset.mem_insert_self _ _)`. Establish `hkt : k ∉ t` using `fun h => hk (Finset.mem_insert_of_mem h)`. Establish `: colOp k (fun j => if j ∈ insert i t then c j else 0) = Matrix.transvection i k (c i) * colOp k (fun j => if j ∈ t then c j else 0)`.

Use extensionality with `a b`. Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality. Rewrite using `[Matrix.transvection_mul_apply_same]`. Distinguish the cases in `hb : b = k`.

Substitute `hb` using the available equality. Simplify using `[colOp, Matrix.one_apply, hi, hki.symm, hkt]`. Simplify using `[colOp, Matrix.one_apply, hb, Ne.symm hb]`. Rewrite using `[Matrix.transvection_mul_apply_of_ne _ _ _ _ ha]`. Simplify using `[colOp, Finset.mem_insert, ha]`.

Rewrite using `[this]`. Conclude with `mul_mem (transvection_mem hki.symm _) (ih hkt)`. Use `key (Finset.univ.erase k) (by simp)` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j`.

Distinguish the cases in `h : j = k`. Substitute `h` using the available equality. Simplify using `[hc]`. Simplify using `[h]`.
-/
lemma colOp_mem (k : ι) (c : ι → R) (hc : c k = 0) : colOp k c ∈ elem R ι := by
  have key : ∀ t : Finset ι, k ∉ t → colOp k (fun j => if j ∈ t then c j else 0) ∈ elem R ι := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have : colOp k (fun j => if j ∈ (∅ : Finset ι) then c j else 0) = (1 : Matrix ι ι R) := by
        ext a b
        simp [colOp]
      rw [this]
      exact one_mem _
    | insert i t hi ih =>
      intro hk
      have hki : k ≠ i := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkt : k ∉ t := fun h => hk (Finset.mem_insert_of_mem h)
      have : colOp k (fun j => if j ∈ insert i t then c j else 0) =
          Matrix.transvection i k (c i) * colOp k (fun j => if j ∈ t then c j else 0) := by
        ext a b
        by_cases ha : a = i
        · subst ha
          rw [Matrix.transvection_mul_apply_same]
          by_cases hb : b = k
          · subst hb
            simp [colOp, Matrix.one_apply, hi, hki.symm, hkt]
          · simp [colOp, Matrix.one_apply, hb, Ne.symm hb]
        · rw [Matrix.transvection_mul_apply_of_ne _ _ _ _ ha]
          simp [colOp, Finset.mem_insert, ha]
      rw [this]
      exact mul_mem (transvection_mem hki.symm _) (ih hkt)
  have := key (Finset.univ.erase k) (by simp)
  convert this using 2
  funext j
  by_cases h : j = k
  · subst h; simp [hc]
  · simp [h]

/- English proof (translation)
Rewrite using `[rowOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]`. Use `congr 1`. Apply the tactic sequence `by_cases h : i = k <;> simp [h]`.
-/
lemma rowOp_mul_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (rowOp k c * A) i j = A i j + if i = k then ∑ l, c l * A l j else 0 := by
  rw [rowOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  by_cases h : i = k <;> simp [h]

/- English proof (translation)
Rewrite using `[colOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
lemma colOp_mul_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (colOp k c * A) i j = A i j + c i * A k j := by
  rw [colOp, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp

/- English proof (translation)
Rewrite using `[rowOp, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
lemma mul_rowOp_apply (k : ι) (c : ι → R) (A : Matrix ι ι R) (i j : ι) :
    (A * rowOp k c) i j = A i j + A i k * c j := by
  rw [rowOp, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp

/- English proof (translation)
Take `⟨ui, hui⟩` from `hu.exists_right_inv`. Use `set v : ι → R := fun i => if i = k then 0 else -(A i k * ui) with hv`. Use `set x : ι → R := fun j => if j = k then 0 else -(ui * A k j) with hx`. Use `set D : ι → R := Function.update (fun _ => 1) k ui with hD`. Establish `hDu : ∀ i, IsUnit (D i)`.

Introduce `i`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Simplify using `only [hD, Function.update_self]`. Conclude with `IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hui)`.

Simplify using `[hD, Function.update_of_ne h]`. Establish `hCm` using `colOp_mem k v (by simp [hv])`. Establish `hRm` using `rowOp_mem k x (by simp [hx])`. Establish `hDm` using `diagonal_mem hDu`. Use `set A4 : Matrix ι ι R := Matrix.diagonal D * ((colOp k v * A) * rowOp k x) with hA4`.

Apply the tactic sequence `have entry : ∀ i j, A4 i j = D i * ((A i j + v i * A k j) + (A i k + v i * A k k) * x j) := by`. Introduce `i j`. Rewrite using `[hA4, Matrix.diagonal_mul, mul_rowOp_apply, colOp_mul_apply, colOp_mul_apply]`. Establish `hF4 : Fixed s A4`. Introduce `i j hij`.

Rewrite using `[entry]`. Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[hv, hx, hD, Matrix.one_apply]`. Rewrite using `[mul_comm]`. Conclude with `hui`. Establish `: A i i * ui = 1` using `hui`. Simplify using `only [hv, hx, if_true, hj, if_false, hD, Function.update_self, Matrix.one_apply, Ne.symm hj]`.

Take the linear combination `(-(ui * A i j)) * this`. Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using `[hv, hx, hi, hD, Function.update_of_ne hi, Matrix.one_apply]`. Establish `: A j j * ui = 1` using `hui`.

Take the linear combination `(-A i j) * this`. Establish `hDi : D i = 1` using `by simp [hD, Function.update_of_ne hi]`. Establish `hvx : (A i k + v i * A k k) = 0`. Establish `: A k k * ui = 1` using `hui`. Simplify using `only [hv, hi, if_false]`.

Take the linear combination `(-A i k) * this`. Rewrite using `[hDi, hvx, zero_mul, add_zero, one_mul]`. Break down `hij with h | h` into its components or cases. Establish `hi' : i ∉ insert k s` using `by simp [hi, h]`. Establish `h0 : A i k = 0`.

Rewrite using `[hF i k (Or.inl hi'), Matrix.one_apply_ne hi]`. Rewrite using `[hF i j (Or.inl hi')]`. Simplify using `[hv, hi, h0]`. Establish `hj' : j ∉ insert k s` using `by simp [hj, h]`. Establish `h0 : A k j = 0`.

Rewrite using `[hF k j (Or.inr hj'), Matrix.one_apply_ne (Ne.symm hj)]`. Rewrite using `[hF i j (Or.inr hj'), h0, mul_zero, add_zero]`. Establish `hdet : IsUnit A4.det`. Rewrite using `[hA4, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]`. Conclude with `(isUnit_det_of_mem hDm).mul (((isUnit_det_of_mem hCm).mul hA).mul (isUnit_det_of_mem hRm))`.

Establish `h4` using `ih A4 hdet hF4`. Conclude with `mem_of_mul_left hCm (mem_of_mul_right hRm (mem_of_mul_left hDm h4))`.
-/
lemma mem_of_unit_pivot {s : Finset ι} {k : ι}
    (ih : ∀ A : Matrix ι ι R, IsUnit A.det → Fixed s A → A ∈ elem R ι)
    {A : Matrix ι ι R} (hA : IsUnit A.det) (hF : Fixed (insert k s) A)
    (hk : k ∉ s) (hu : IsUnit (A k k)) : A ∈ elem R ι := by
  obtain ⟨ui, hui⟩ := hu.exists_right_inv
  set v : ι → R := fun i => if i = k then 0 else -(A i k * ui) with hv
  set x : ι → R := fun j => if j = k then 0 else -(ui * A k j) with hx
  set D : ι → R := Function.update (fun _ => 1) k ui with hD
  have hDu : ∀ i, IsUnit (D i) := by
    intro i
    by_cases h : i = k
    · subst h
      simp only [hD, Function.update_self]
      exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hui)
    · simp [hD, Function.update_of_ne h]
  have hCm := colOp_mem k v (by simp [hv])
  have hRm := rowOp_mem k x (by simp [hx])
  have hDm := diagonal_mem hDu
  set A4 : Matrix ι ι R := Matrix.diagonal D * ((colOp k v * A) * rowOp k x) with hA4
  have entry : ∀ i j, A4 i j = D i * ((A i j + v i * A k j) +
      (A i k + v i * A k k) * x j) := by
    intro i j
    rw [hA4, Matrix.diagonal_mul, mul_rowOp_apply, colOp_mul_apply, colOp_mul_apply]
  have hF4 : Fixed s A4 := by
    intro i j hij
    rw [entry]
    by_cases hi : i = k
    · subst hi
      by_cases hj : j = i
      · subst hj
        simp [hv, hx, hD, Matrix.one_apply]
        rw [mul_comm]; exact hui
      · have : A i i * ui = 1 := hui
        simp only [hv, hx, if_true, hj, if_false, hD, Function.update_self,
          Matrix.one_apply, Ne.symm hj]
        linear_combination (-(ui * A i j)) * this
    · by_cases hj : j = k
      · subst hj
        simp [hv, hx, hi, hD, Function.update_of_ne hi, Matrix.one_apply]
        have : A j j * ui = 1 := hui
        linear_combination (-A i j) * this
      · have hDi : D i = 1 := by simp [hD, Function.update_of_ne hi]
        have hvx : (A i k + v i * A k k) = 0 := by
          have : A k k * ui = 1 := hui
          simp only [hv, hi, if_false]
          linear_combination (-A i k) * this
        rw [hDi, hvx, zero_mul, add_zero, one_mul]
        rcases hij with h | h
        · have hi' : i ∉ insert k s := by simp [hi, h]
          have h0 : A i k = 0 := by
            rw [hF i k (Or.inl hi'), Matrix.one_apply_ne hi]
          rw [hF i j (Or.inl hi')]
          simp [hv, hi, h0]
        · have hj' : j ∉ insert k s := by simp [hj, h]
          have h0 : A k j = 0 := by
            rw [hF k j (Or.inr hj'), Matrix.one_apply_ne (Ne.symm hj)]
          rw [hF i j (Or.inr hj'), h0, mul_zero, add_zero]
  have hdet : IsUnit A4.det := by
    rw [hA4, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    exact (isUnit_det_of_mem hDm).mul
      (((isUnit_det_of_mem hCm).mul hA).mul (isUnit_det_of_mem hRm))
  have h4 := ih A4 hdet hF4
  exact mem_of_mul_left hCm (mem_of_mul_right hRm (mem_of_mul_left hDm h4))

/- English proof (translation)
Use `set B := A⁻¹ with hB`. Establish `hBA : B * A = 1` using `Matrix.nonsing_inv_mul A hA`. Establish `hsum : ∑ l, B k l * A l k = 1`. Use `congrFun (congrFun hBA k) k` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply]`.

Establish `hzero : ∀ l, l ∉ insert k s → A l k = 0`. Introduce `l hl`. Establish `hlk : l ≠ k` using `fun h => hl (h ▸ Finset.mem_insert_self _ _)`. Rewrite using `[hF l k (Or.inl hl), Matrix.one_apply_ne hlk]`. Establish `hsplit : ∑ l, B k l * A l k = B k k * A k k + ∑ l ∈ s, B k l * A l k`.

Rewrite using `[← Finset.sum_insert (f := fun l => B k l * A l k) hk]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `l _ hl`. Rewrite using `[hzero l hl, mul_zero]`.

Use `set b := ∑ l ∈ s, B k l * A l k with hb`. Establish `hcop : IsCoprime (A k k) b` using `⟨B k k, 1, by rw [one_mul, ← hsplit, hsum]⟩`. Take `⟨t, ht⟩` from `hR _ _ hcop`. Use `set w : ι → R := fun l => if l ∈ s then t * B k l else 0 with hw`. Establish `hwsum : ∀ j, ∑ l, w l * A l j = t * ∑ l ∈ s, B k l * A l j`.

Introduce `j`. Rewrite using `[Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ s)]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l hl`. Simplify using `[hw, hl, mul_assoc]`.

Introduce `l _ hl`. Simplify using `[hw, hl]`. Use `⟨w, by simp [hw, hk], ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Rewrite using `[rowOp_mul_apply]`.

Distinguish the cases in `hi : i = k`. Substitute `hi` using the available equality. Establish `hj : j ∉ insert i s`. Break down `hij with h | h` into its components or cases. Conclude with `absurd (Finset.mem_insert_self _ _) h`.

Conclude with `h`. Establish `hji : i ≠ j` using `fun h => hj (h ▸ Finset.mem_insert_self _ _)`. Rewrite using `[if_pos rfl, hwsum, hF i j (Or.inr hj), Finset.sum_eq_zero, mul_zero, add_zero]`. Introduce `l hl`. Establish `hlj : l ≠ j` using `fun h => hj (h ▸ Finset.mem_insert_of_mem hl)`.

Rewrite using `[hF l j (Or.inr hj), Matrix.one_apply_ne hlj, mul_zero]`. Rewrite using `[if_neg hi, add_zero]`. Conclude with `hF i j hij`. Rewrite using `[rowOp_mul_apply, if_pos rfl, hwsum]`. Conclude with `ht`.
-/
lemma exists_unit_pivot (hR : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    {s : Finset ι} {k : ι} {A : Matrix ι ι R} (hA : IsUnit A.det)
    (hF : Fixed (insert k s) A) (hk : k ∉ s) :
    ∃ w : ι → R, w k = 0 ∧ Fixed (insert k s) (rowOp k w * A) ∧
      IsUnit ((rowOp k w * A) k k) := by
  set B := A⁻¹ with hB
  have hBA : B * A = 1 := Matrix.nonsing_inv_mul A hA
  have hsum : ∑ l, B k l * A l k = 1 := by
    have := congrFun (congrFun hBA k) k
    simpa [Matrix.mul_apply] using this
  have hzero : ∀ l, l ∉ insert k s → A l k = 0 := by
    intro l hl
    have hlk : l ≠ k := fun h => hl (h ▸ Finset.mem_insert_self _ _)
    rw [hF l k (Or.inl hl), Matrix.one_apply_ne hlk]
  have hsplit : ∑ l, B k l * A l k = B k k * A k k + ∑ l ∈ s, B k l * A l k := by
    rw [← Finset.sum_insert (f := fun l => B k l * A l k) hk]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro l _ hl
    rw [hzero l hl, mul_zero]
  set b := ∑ l ∈ s, B k l * A l k with hb
  have hcop : IsCoprime (A k k) b := ⟨B k k, 1, by rw [one_mul, ← hsplit, hsum]⟩
  obtain ⟨t, ht⟩ := hR _ _ hcop
  set w : ι → R := fun l => if l ∈ s then t * B k l else 0 with hw
  have hwsum : ∀ j, ∑ l, w l * A l j = t * ∑ l ∈ s, B k l * A l j := by
    intro j
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ s)]
    · apply Finset.sum_congr rfl
      intro l hl
      simp [hw, hl, mul_assoc]
    · intro l _ hl
      simp [hw, hl]
  refine ⟨w, by simp [hw, hk], ?_, ?_⟩
  · intro i j hij
    rw [rowOp_mul_apply]
    by_cases hi : i = k
    · subst hi
      have hj : j ∉ insert i s := by
        rcases hij with h | h
        · exact absurd (Finset.mem_insert_self _ _) h
        · exact h
      have hji : i ≠ j := fun h => hj (h ▸ Finset.mem_insert_self _ _)
      rw [if_pos rfl, hwsum, hF i j (Or.inr hj), Finset.sum_eq_zero, mul_zero, add_zero]
      intro l hl
      have hlj : l ≠ j := fun h => hj (h ▸ Finset.mem_insert_of_mem hl)
      rw [hF l j (Or.inr hj), Matrix.one_apply_ne hlj, mul_zero]
    · rw [if_neg hi, add_zero]
      exact hF i j hij
  · rw [rowOp_mul_apply, if_pos rfl, hwsum]
    exact ht

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Introduce `A _ hF`. Establish `: A = 1`. Use extensionality with `i j`.

Conclude with `hF i j (Or.inl (by simp))`. Rewrite using `[this]`. Conclude with `one_mem _`. Consider the case `insert k s hk ih`. Introduce `A hA hF`.

Take `⟨w, hw0, hwF, hwu⟩` from `exists_unit_pivot hR hA hF hk`. Establish `hm` using `rowOp_mem k w hw0`. Establish `hdet : IsUnit (rowOp k w * A).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `(isUnit_det_of_mem hm).mul hA`.

Conclude with `mem_of_mul_left hm (mem_of_unit_pivot ih hdet hwF hk hwu)`.
-/
lemma mem_of_fixed (hR : ∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b))
    (s : Finset ι) : ∀ A : Matrix ι ι R, IsUnit A.det → Fixed s A → A ∈ elem R ι := by
  induction s using Finset.induction_on with
  | empty =>
    intro A _ hF
    have : A = 1 := by
      ext i j
      exact hF i j (Or.inl (by simp))
    rw [this]
    exact one_mem _
  | insert k s hk ih =>
    intro A hA hF
    obtain ⟨w, hw0, hwF, hwu⟩ := exists_unit_pivot hR hA hF hk
    have hm := rowOp_mem k w hw0
    have hdet : IsUnit (rowOp k w * A).det := by
      rw [Matrix.det_mul]
      exact (isUnit_det_of_mem hm).mul hA
    exact mem_of_mul_left hm (mem_of_unit_pivot ih hdet hwF hk hwu)

/- English proof (translation)
Introduce `R _ hR ι _ _ p ht hd hm A hA`. Establish `hmem : A ∈ elem R ι` using `mem_of_fixed hR Finset.univ A hA (fun i j h => by simp at h)`. Establish `key : ∀ B ∈ elem R ι, p B`. Introduce `B hB`. Proceed by induction on `hB using Submonoid.closure_induction with`.

Consider the case `mem x hx`. Break down `hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩` into its components or cases. Conclude with `ht i j c h`. Conclude with `hd D hD`. Consider the case `one`.

Use `hd (fun _ => 1) (fun _ => isUnit_one)` as an intermediate fact. Simplify using `using this`. Consider the case `mul x y hx hy px py`. Conclude with `hm x y (isUnit_det_of_mem hx) (isUnit_det_of_mem hy) px py`. Conclude with `key A hmem`.
-/
theorem matrix_induction :
    ∀ (R : Type) [CommRing R], (∀ a b : R, IsCoprime a b → ∃ t, IsUnit (a + t * b)) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : Matrix ι ι R → Prop),
        (∀ (i j : ι) (c : R), i ≠ j → p (Matrix.transvection i j c)) →
        (∀ D : ι → R, (∀ i, IsUnit (D i)) → p (Matrix.diagonal D)) →
        (∀ A B, IsUnit A.det → IsUnit B.det → p A → p B → p (A * B)) →
        ∀ A : Matrix ι ι R, IsUnit A.det → p A := by
  intro R _ hR ι _ _ p ht hd hm A hA
  have hmem : A ∈ elem R ι :=
    mem_of_fixed hR Finset.univ A hA (fun i j h => by simp at h)
  have key : ∀ B ∈ elem R ι, p B := by
    intro B hB
    induction hB using Submonoid.closure_induction with
    | mem x hx =>
      rcases hx with ⟨i, j, c, h, rfl⟩ | ⟨D, hD, rfl⟩
      · exact ht i j c h
      · exact hd D hD
    | one =>
      have := hd (fun _ => 1) (fun _ => isUnit_one)
      simpa using this
    | mul x y hx hy px py =>
      exact hm x y (isUnit_det_of_mem hx) (isUnit_det_of_mem hy) px py
  exact key A hmem

end GlobalTheory.CompanionTheory.Adelic.StableRangeOne
