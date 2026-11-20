import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSquaresConeOfCompactPosDefStatement

open Matrix GlobalTheory.RedTh

noncomputable section

namespace GlobalTheory.SiegelCone

abbrev Tail {n : ℕ} (k : Fin n) : Type := {i : Fin n // k ≤ i}

def unip (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  Set.pi Set.univ fun i => Set.pi Set.univ fun j =>
    if i = j then {1} else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)

/- English proof (translation)
Use `isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `isCompact_singleton`. Conclude with `isCompact_singleton`. Conclude with `isCompact_Icc`.
-/
theorem isCompact_unip (n : ℕ) : IsCompact (unip n) := by
  refine isCompact_univ_pi fun i => isCompact_univ_pi fun j => ?_
  split_ifs
  · exact isCompact_singleton
  · exact isCompact_singleton
  · exact isCompact_Icc

/- English proof (translation)
Introduce `i _ j _`. Simplify using `only`. Use `split_ifs with h1 h2`. Substitute `h1` using the available equality. Simplify using `[h.diag]`.

Simplify using `[h.lower i j h2]`. Establish `: i < j` using `lt_of_le_of_ne (not_lt.1 h2) h1`. Conclude with `abs_le.1 (h.upper i j this)`.
-/
theorem mem_unip {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (h : GlobalTheory.RedTh.IsSiegel d u) :
    u ∈ unip n := by
  intro i _ j _
  simp only
  split_ifs with h1 h2
  · subst h1; simp [h.diag]
  · simp [h.lower i j h2]
  · have : i < j := lt_of_le_of_ne (not_lt.1 h2) h1
    exact abs_le.1 (h.upper i j this)

def tailForm {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) : Matrix (Tail k) (Tail k) ℝ :=
  (u.submatrix Subtype.val Subtype.val)ᵀ * diagonal (fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹) *
    u.submatrix Subtype.val Subtype.val

/- English proof (translation)
Unfold `tailForm`. Conclude with `((continuous_id.matrix_submatrix _ _).matrix_transpose.matrix_mul continuous_const).matrix_mul (continuous_id.matrix_submatrix _ _)`.
-/
theorem continuous_tailForm {n : ℕ} (k : Fin n) : Continuous (tailForm k) := by
  unfold tailForm
  exact ((continuous_id.matrix_submatrix _ _).matrix_transpose.matrix_mul continuous_const).matrix_mul
    (continuous_id.matrix_submatrix _ _)

/- English proof (translation)
Establish `hu' : ∀ i j, u i j ∈ (if i = j then ({1} : Set ℝ) else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2))` using `fun i j => hu i trivial j trivial`. Use `set v := u.submatrix (Subtype.val : Tail k → Fin n) Subtype.val`. Establish `htri : v.BlockTriangular id`. Introduce `a b hab`. Use `hu' a.1 b.1` as an intermediate fact.

Establish `hne : a.1 ≠ b.1` using `fun h => (ne_of_lt hab) (Subtype.ext h).symm`. Simplify using `only [hne, if_false, show b.1 < a.1 from hab, if_true, Set.mem_singleton_iff] at this`. Conclude with `this`. Establish `hdet : v.det = 1`. Rewrite using `[det_of_upperTriangular htri]`.

Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Use `hu' a.1 a.1` as an intermediate fact. Simplify `this` using `[v]`. Establish `hunit : IsUnit v` using `(isUnit_iff_isUnit_det v).2 (by rw [hdet]; exact isUnit_one)`. Establish `hD : (diagonal fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹).PosDef` using `posDef_diagonal_iff.2 fun a => by positivity`.

Use `hD.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hunit)` as an intermediate fact. Rewrite `this` using `[conjTranspose_eq_transpose_of_trivial]`. Conclude with `this`.
-/
theorem tailForm_posDef {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) :
    (tailForm k u).PosDef := by
  have hu' : ∀ i j, u i j ∈ (if i = j then ({1} : Set ℝ) else if j < i then {0} else Set.Icc (-(1 / 2)) (1 / 2)) :=
    fun i j => hu i trivial j trivial
  set v := u.submatrix (Subtype.val : Tail k → Fin n) Subtype.val
  have htri : v.BlockTriangular id := by
    intro a b hab
    have := hu' a.1 b.1
    have hne : a.1 ≠ b.1 := fun h => (ne_of_lt hab) (Subtype.ext h).symm
    simp only [hne, if_false, show b.1 < a.1 from hab, if_true, Set.mem_singleton_iff] at this
    exact this
  have hdet : v.det = 1 := by
    rw [det_of_upperTriangular htri]
    refine Finset.prod_eq_one fun a _ => ?_
    have := hu' a.1 a.1
    simpa [v] using this
  have hunit : IsUnit v := (isUnit_iff_isUnit_det v).2 (by rw [hdet]; exact isUnit_one)
  have hD : (diagonal fun a : Tail k => ((4 : ℝ) ^ (a.1 : ℕ))⁻¹).PosDef :=
    posDef_diagonal_iff.2 fun a => by positivity
  have := hD.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hunit)
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this

/- English proof (translation)
Rewrite using `[tailForm, mul_apply]`. Simplify using `only [mul_diagonal, transpose_apply, submatrix_apply]`. Rewrite using `[← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (k ≤ ·)) (p := (k ≤ ·)) (by simp)]`. Use `Finset.sum_congr rfl fun c _ => by ring` and prove the remaining obligations.
-/
theorem tailForm_apply {n : ℕ} (k : Fin n) (u : Matrix (Fin n) (Fin n) ℝ) (a b : Tail k) :
    tailForm k u a b = ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m a.1 * u m b.1 else 0 := by
  rw [tailForm, mul_apply]
  simp only [mul_diagonal, transpose_apply, submatrix_apply]
  rw [← Finset.sum_filter, Finset.sum_subtype (Finset.univ.filter (k ≤ ·)) (p := (k ≤ ·)) (by simp)]
  refine Finset.sum_congr rfl fun c _ => by ring

end GlobalTheory.SiegelCone

namespace GlobalTheory.SiegelCone

def extZ {n : ℕ} (k : Fin n) (l : Tail k → ℤ) : Fin n → ℤ := fun i => if h : k ≤ i then l ⟨i, h⟩ else 0

/- English proof (translation)
Set `F : ℕ → ℝ` to `fun m => if h : m < n then d ⟨m, h⟩ * 4 ^ m else 0`. Set `G : ℕ → ℝ` to `fun k => if k = 0 then F 0 else F k - F (k - 1)`. Establish `htel : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), G k = F m`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp [G]`. Consider the case `succ m ih => rw [Finset.sum_range_succ, ih]`. Simplify using `only [G, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun k => G k, fun k => ?_, fun m => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `h0 : (k : ℕ) = 0`. Use `hs.nonneg k` as an intermediate fact. Simplify using `only [G, h0, if_true, F, dif_pos (show 0 < n from lt_of_le_of_lt (Nat.zero_le _) k.2)]`. Establish `e : (⟨0, lt_of_le_of_lt (Nat.zero_le _) k.2⟩ : Fin n) = k` using `Fin.ext h0.symm`. Rewrite using `[e]`.

Check the signs of the components of the expression. Take `⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1` from `⟨(k : ℕ) - 1, by omega⟩`. Establish `hjn : j < n` using `by omega`. Establish `hstep` using `hs.step ⟨j, hjn⟩ k (by simp [hj])`. Establish `hnn` using `hs.nonneg ⟨j, hjn⟩`.

Establish `hdk : ∀ h, d ⟨j + 1, h⟩ = d k` using `fun h => congrArg d (Fin.ext hj.symm)`. Establish `hFk : F (j + 1) = d k * 4 ^ (j + 1)`. Simplify using `only [F, dif_pos (show j + 1 < n by omega), hdk]`. Establish `hFj : F j = d ⟨j, hjn⟩ * 4 ^ j` using `by simp only [F, dif_pos hjn]`. Use `show 0 ≤ G (k : ℕ)`.

Rewrite using `[hj]`. Simplify using `only [G, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hFk, hFj, pow_succ]`. Establish `: (0 : ℝ) ≤ 4 ^ j` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hsum : ∑ k : Fin n, (if k ≤ m then G k else 0) = F m`.

Establish `h1 : ∀ k : Fin n, (if k ≤ m then G k else 0) = (fun x : ℕ => if x ≤ (m : ℕ) then G x else 0) k` using `fun k => by simp only [Fin.le_iff_val_le_val]`. Rewrite using `[Finset.sum_congr rfl (fun k _ => h1 k), Fin.sum_univ_eq_sum_range (fun x => if x ≤ (m : ℕ) then G x else 0) n, ← Finset.sum_filter]`. Establish `h2 : (Finset.range n).filter (· ≤ (m : ℕ)) = Finset.range ((m : ℕ) + 1)`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Rewrite using `[h2, htel]`. Rewrite using `[hsum]`. Simplify using `only [F, dif_pos m.2, Fin.eta]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_increments {n : ℕ} {d : Fin n → ℝ} {u : Matrix (Fin n) (Fin n) ℝ} (hs : GlobalTheory.RedTh.IsSiegel d u) :
    ∃ G : Fin n → ℝ, (∀ k, 0 ≤ G k) ∧ ∀ m, d m = ((4 : ℝ) ^ (m : ℕ))⁻¹ * ∑ k, if k ≤ m then G k else 0 := by
  let F : ℕ → ℝ := fun m => if h : m < n then d ⟨m, h⟩ * 4 ^ m else 0
  let G : ℕ → ℝ := fun k => if k = 0 then F 0 else F k - F (k - 1)
  have htel : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), G k = F m := by
    intro m
    induction m with
    | zero => simp [G]
    | succ m ih => rw [Finset.sum_range_succ, ih]; simp only [G, if_neg (Nat.succ_ne_zero m), Nat.add_sub_cancel]; ring
  refine ⟨fun k => G k, fun k => ?_, fun m => ?_⟩
  · by_cases h0 : (k : ℕ) = 0
    · have := hs.nonneg k
      simp only [G, h0, if_true, F, dif_pos (show 0 < n from lt_of_le_of_lt (Nat.zero_le _) k.2)]
      have e : (⟨0, lt_of_le_of_lt (Nat.zero_le _) k.2⟩ : Fin n) = k := Fin.ext h0.symm
      rw [e]; positivity
    · obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨(k : ℕ) - 1, by omega⟩
      have hjn : j < n := by omega
      have hstep := hs.step ⟨j, hjn⟩ k (by simp [hj])
      have hnn := hs.nonneg ⟨j, hjn⟩
      have hdk : ∀ h, d ⟨j + 1, h⟩ = d k := fun h => congrArg d (Fin.ext hj.symm)
      have hFk : F (j + 1) = d k * 4 ^ (j + 1) := by
        simp only [F, dif_pos (show j + 1 < n by omega), hdk]
      have hFj : F j = d ⟨j, hjn⟩ * 4 ^ j := by simp only [F, dif_pos hjn]
      show 0 ≤ G (k : ℕ)
      rw [hj]
      simp only [G, if_neg (Nat.succ_ne_zero j), Nat.add_sub_cancel, hFk, hFj, pow_succ]
      have : (0 : ℝ) ≤ 4 ^ j := by positivity
      nlinarith
  · have hsum : ∑ k : Fin n, (if k ≤ m then G k else 0) = F m := by
      have h1 : ∀ k : Fin n, (if k ≤ m then G k else 0) = (fun x : ℕ => if x ≤ (m : ℕ) then G x else 0) k :=
        fun k => by simp only [Fin.le_iff_val_le_val]
      rw [Finset.sum_congr rfl (fun k _ => h1 k), Fin.sum_univ_eq_sum_range (fun x => if x ≤ (m : ℕ) then G x else 0) n,
        ← Finset.sum_filter]
      have h2 : (Finset.range n).filter (· ≤ (m : ℕ)) = Finset.range ((m : ℕ) + 1) := by
        ext x; simp; omega
      rw [h2, htel]
    rw [hsum]
    simp only [F, dif_pos m.2, Fin.eta]
    field_simp

/- English proof (translation)
Establish `hlow : ∀ m i, k ≤ m → ¬ k ≤ i → u m i = 0`. Introduce `m i hm hi`. Use `hu m trivial i trivial` as an intermediate fact. Establish `hlt : i < m` using `lt_of_lt_of_le (not_le.1 hi) hm`. Simplify `this` using `[hlt.ne', hlt]`.

Distinguish the cases in `hi : k ≤ i`. Distinguish the cases in `hj : k ≤ j`. Use `congrFun (congrFun hC ⟨i, hi⟩) ⟨j, hj⟩` as an intermediate fact. Rewrite `this` using `[tailForm_apply]`. Rewrite using `[this]`.

Simplify using `[Matrix.sum_apply, vecMulVec_apply, extZ, hi, hj]`. Simplify using `only [extZ, dif_neg hj, Int.cast_zero, mul_zero]`. Simplify using `only [Finset.sum_const_zero]`. Use `(Finset.sum_eq_zero fun m _ => ?_).symm` and prove the remaining obligations. Use `split_ifs with hm`.

Rewrite using `[hlow m j hm hj, mul_zero]`. Both sides reduce to the same expression. Simplify using `only [extZ, dif_neg hi, Int.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero]`. Use `(Finset.sum_eq_zero fun m _ => ?_).symm` and prove the remaining obligations. Use `split_ifs with hm`.

Rewrite using `[hlow m i hm hi, mul_zero, zero_mul]`. Both sides reduce to the same expression.
-/
theorem tail_sum {n : ℕ} (k : Fin n) {u : Matrix (Fin n) (Fin n) ℝ} (hu : u ∈ unip n) (T : Finset (Tail k → ℤ))
    (C : (Tail k → ℤ) → ℝ)
    (hC : tailForm k u = ∑ l ∈ T, C l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))) (i j : Fin n) :
    ∑ l ∈ T, C l * ((extZ k l i : ℝ) * (extZ k l j : ℝ)) =
      ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
  have hlow : ∀ m i, k ≤ m → ¬ k ≤ i → u m i = 0 := by
    intro m i hm hi
    have := hu m trivial i trivial
    have hlt : i < m := lt_of_lt_of_le (not_le.1 hi) hm
    simpa [hlt.ne', hlt] using this
  by_cases hi : k ≤ i
  · by_cases hj : k ≤ j
    · have := congrFun (congrFun hC ⟨i, hi⟩) ⟨j, hj⟩
      rw [tailForm_apply] at this
      rw [this]
      simp [Matrix.sum_apply, vecMulVec_apply, extZ, hi, hj]
    · simp only [extZ, dif_neg hj, Int.cast_zero, mul_zero]
      simp only [Finset.sum_const_zero]
      refine (Finset.sum_eq_zero fun m _ => ?_).symm
      split_ifs with hm
      · rw [hlow m j hm hj, mul_zero]
      · rfl
  · simp only [extZ, dif_neg hi, Int.cast_zero, zero_mul, mul_zero, Finset.sum_const_zero]
    refine (Finset.sum_eq_zero fun m _ => ?_).symm
    split_ifs with hm
    · rw [hlow m i hm hi, mul_zero, zero_mul]
    · rfl

/- English proof (translation)
Introduce `n`. Establish `hK : ∀ k : Fin n, ∃ T : Finset (Tail k → ℤ), ∀ P ∈ tailForm k '' unip n, ∃ c : (Tail k → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ T, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ))` using `fun k => GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef (Tail k) (tailForm k '' unip n) ((isCompact_unip n).image (continuous_tailForm k)) (by rintro _ ⟨u, hu, rfl⟩; exact tailForm_posDef k hu)`. Use `choose T hT using hK`. Use `⟨Finset.univ.biUnion fun k => (T k).image (extZ k), ?_⟩` and prove the remaining obligations. Introduce `d u hs`.

Establish `hu` using `mem_unip hs`. Use `choose C hC0 hC using fun k => hT k _ ⟨u, hu, rfl⟩`. Take `⟨G, hG0, hd⟩` from `exists_increments hs`. Use `⟨fun l => ∑ k : Fin n, G k * ∑ l' ∈ T k, if extZ k l' = l then C k l' else 0, fun l => ?_, ?_⟩` and prove the remaining obligations. Use `Finset.sum_nonneg fun k _ => mul_nonneg (hG0 k) (Finset.sum_nonneg fun l' _ => ?_) split_ifs` and prove the remaining obligations.

Conclude with `hC0 k l'`. Conclude with `le_rfl`. Use extensionality with `i j`. Establish `hL : GlobalTheory.RedTh.gram d u i j = ∑ k, G k * ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[GlobalTheory.RedTh.gram, mul_apply]`. Simplify using `only [mul_diagonal, transpose_apply]`. Use `_ = ∑ m : Fin n, ∑ k : Fin n, if k ≤ m then G k * (((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j) else 0 := by`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hd m, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`. Use `_ = _ := by`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[hL]`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]`.

Repeatedly rewrite using `[← tail_sum _ hu _ _ (hC _)]`. Repeatedly rewrite using `[Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l' hl' => ?_` and prove the remaining obligations. Establish `hmem : extZ k l' ∈ Finset.univ.biUnion fun k => (T k).image (extZ k)` using `Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hl'⟩`. Repeatedly rewrite using `[mul_ite, mul_zero, ite_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq, if_pos hmem]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_mem_cone : ∀ n : ℕ, ∃ S : Finset (Fin n → ℤ), ∀ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ),
    GlobalTheory.RedTh.IsSiegel d u → ∃ c : (Fin n → ℤ) → ℝ, (∀ l, 0 ≤ c l) ∧
      GlobalTheory.RedTh.gram d u = ∑ l ∈ S, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := by
  intro n
  have hK : ∀ k : Fin n, ∃ T : Finset (Tail k → ℤ), ∀ P ∈ tailForm k '' unip n, ∃ c : (Tail k → ℤ) → ℝ,
      (∀ l, 0 ≤ c l) ∧ P = ∑ l ∈ T, c l • vecMulVec (fun i => (l i : ℝ)) (fun i => (l i : ℝ)) := fun k =>
    GlobalTheory.T.exists_finset_squares_cone_of_compact_posDef (Tail k) (tailForm k '' unip n) ((isCompact_unip n).image (continuous_tailForm k))
      (by rintro _ ⟨u, hu, rfl⟩; exact tailForm_posDef k hu)
  choose T hT using hK
  refine ⟨Finset.univ.biUnion fun k => (T k).image (extZ k), ?_⟩
  intro d u hs
  have hu := mem_unip hs
  choose C hC0 hC using fun k => hT k _ ⟨u, hu, rfl⟩
  obtain ⟨G, hG0, hd⟩ := exists_increments hs
  refine ⟨fun l => ∑ k : Fin n, G k * ∑ l' ∈ T k, if extZ k l' = l then C k l' else 0, fun l => ?_, ?_⟩
  · refine Finset.sum_nonneg fun k _ => mul_nonneg (hG0 k) (Finset.sum_nonneg fun l' _ => ?_)
    split_ifs
    · exact hC0 k l'
    · exact le_rfl
  ext i j
  have hL : GlobalTheory.RedTh.gram d u i j = ∑ k, G k * ∑ m : Fin n, if k ≤ m then ((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j else 0 := by
    calc GlobalTheory.RedTh.gram d u i j = ∑ m, u m i * d m * u m j := by
          rw [GlobalTheory.RedTh.gram, mul_apply]; simp only [mul_diagonal, transpose_apply]
      _ = ∑ m : Fin n, ∑ k : Fin n, if k ≤ m then G k * (((4 : ℝ) ^ (m : ℕ))⁻¹ * u m i * u m j) else 0 := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hd m, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          split_ifs <;> ring
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          split_ifs <;> ring
  rw [hL]
  simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  simp_rw [← tail_sum _ hu _ _ (hC _)]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' hl' => ?_
  have hmem : extZ k l' ∈ Finset.univ.biUnion fun k => (T k).image (extZ k) :=
    Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, Finset.mem_image_of_mem _ hl'⟩
  simp_rw [mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos hmem]
  ring

end GlobalTheory.SiegelCone
