import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrbitDenom

section General
variable {E : Type} [CommRing E]

/- English proof (translation)
Use `symm`. Use `Finset.sum_of_injOn (Fin.castLE h) (fun a _ b _ hab => Fin.castLE_injective h hab) (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `k _ hk`. Use `hg k ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Conclude with `hk ⟨⟨k, by omega⟩, by simp, Fin.ext rfl⟩`.
-/
theorem sum_castLE {n l : ℕ} (h : l ≤ n) (g : Fin n → E) (hg : ∀ k : Fin n, l ≤ (k : ℕ) → g k = 0) :
    ∑ k, g k = ∑ k : Fin l, g (Fin.castLE h k) := by
  symm
  refine Finset.sum_of_injOn (Fin.castLE h) (fun a _ b _ hab => Fin.castLE_injective h hab)
    (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
  intro k _ hk
  refine hg k ?_
  by_contra hlt
  exact hk ⟨⟨k, by omega⟩, by simp, Fin.ext rfl⟩

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `sum_castLE h (fun k => M (p a) k * N k (Fin.castLE h b)) ?_` and prove the remaining obligations. Introduce `k hk`. Rewrite using `[hN k _ hk (by simp), mul_zero]`.
-/
theorem sub_mul_right {n l : ℕ} (h : l ≤ n) {α : Type} (p : α → Fin n) (M N : Matrix (Fin n) (Fin n) E)
    (hN : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → N k b = 0) :
    (M * N).submatrix p (Fin.castLE h) =
      M.submatrix p (Fin.castLE h) * N.submatrix (Fin.castLE h) (Fin.castLE h) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_castLE h (fun k => M (p a) k * N k (Fin.castLE h b)) ?_
  intro k hk
  rw [hN k _ hk (by simp), mul_zero]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Use `sum_castLE h (fun k => M (Fin.castLE h a) k * N k (p b)) ?_` and prove the remaining obligations. Introduce `k hk`. Rewrite using `[hM _ k (by rw [Fin.lt_def]; have := a.2; simp; omega), zero_mul]`.
-/
theorem sub_mul_left {n l : ℕ} (h : l ≤ n) {α : Type} (p : α → Fin n) (M N : Matrix (Fin n) (Fin n) E)
    (hM : ∀ a k : Fin n, a < k → M a k = 0) :
    (M * N).submatrix (Fin.castLE h) p =
      M.submatrix (Fin.castLE h) (Fin.castLE h) * N.submatrix (Fin.castLE h) p := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  refine sum_castLE h (fun k => M (Fin.castLE h a) k * N k (p b)) ?_
  intro k hk
  rw [hM _ k (by rw [Fin.lt_def]; have := a.2; simp; omega), zero_mul]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => hM _ _)`.
-/
theorem det_mem (O : Subring E) {l : ℕ} (M : Matrix (Fin l) (Fin l) E) (hM : ∀ a b, M a b ∈ O) :
    M.det ∈ O := by
  rw [Matrix.det_apply']
  exact O.sum_mem fun σ _ => O.mul_mem (intCast_mem O _) (O.prod_mem fun i _ => hM _ _)

/- English proof (translation)
Rewrite using `[Matrix.adjugate_apply]`. Use `det_mem O _ fun i j => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`. Rewrite using `[Pi.single_apply]`.

Use `split_ifs`. Conclude with `O.one_mem`. Conclude with `O.zero_mem`. Conclude with `hM _ _`.
-/
theorem adj_mem (O : Subring E) {l : ℕ} (M : Matrix (Fin l) (Fin l) E) (hM : ∀ a b, M a b ∈ O)
    (a b : Fin l) : M.adjugate a b ∈ O := by
  rw [Matrix.adjugate_apply]
  refine det_mem O _ fun i j => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · exact hM _ _

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular]`. Simplify using `[hA1]`. Introduce `i j hij`. Conclude with `hA _ _ hij`.
-/
theorem det_low {n l : ℕ} (h : l ≤ n) (A : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1) :
    (A.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular]
  · simp [hA1]
  · intro i j hij
    exact hA _ _ hij

/- English proof (translation)
Rewrite using `[Matrix.det_of_isUpperTriangular]`. Simplify using `[hB1]`. Introduce `i j hij`. Conclude with `hB _ _ hij`.
-/
theorem det_up {n l : ℕ} (h : l ≤ n) (B : Matrix (Fin n) (Fin n) E)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1) :
    (B.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [hB1]
  · intro i j hij
    exact hB _ _ hij

/- English proof (translation)
Rewrite using `[sub_mul_right h _ _ B (fun k b hk hb => hB _ _ (by rw [Fin.lt_def]; omega)), sub_mul_left h _ A W hA]`.
-/
theorem sub_three {n l : ℕ} (h : l ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hB : ∀ a k : Fin n, k < a → B a k = 0) :
    (A * W * B).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE h) (Fin.castLE h) * W.submatrix (Fin.castLE h) (Fin.castLE h) *
        B.submatrix (Fin.castLE h) (Fin.castLE h) := by
  rw [sub_mul_right h _ _ B (fun k b hk hb => hB _ _ (by rw [Fin.lt_def]; omega)), sub_mul_left h _ A W hA]

/- English proof (translation)
Rewrite using `[sub_three h A W B hA hB, Matrix.det_mul, Matrix.det_mul, det_low h A hA hA1, det_up h B hB hB1, one_mul, mul_one]`.
-/
theorem det_three {n l : ℕ} (h : l ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1) :
    ((A * W * B).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (W.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [sub_three h A W B hA hB, Matrix.det_mul, Matrix.det_mul, det_low h A hA hA1, det_up h B hB hB1,
    one_mul, mul_one]

/- English proof (translation)
Rewrite `hW` using `[Matrix.twoBlockTriangular_det W (fun i => (i : ℕ) < l) (fun i hi j hj => hc i j (by omega) hj)]`. Establish `h1` using `isUnit_of_mul_isUnit_left hW`. Set `e : Fin l ≃ {i : Fin n // (i : ℕ) < l}` to `{ toFun := fun a => ⟨Fin.castLE h a, a.2⟩ invFun := fun a => ⟨a.1, a.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`. Rewrite `h1` using `[← Matrix.det_submatrix_equiv_self e]`. Conclude with `h1`.
-/
theorem unit_cut {n l : ℕ} (h : l ≤ n) (W : Matrix (Fin n) (Fin n) E) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0) :
    IsUnit (W.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  rw [Matrix.twoBlockTriangular_det W (fun i => (i : ℕ) < l)
    (fun i hi j hj => hc i j (by omega) hj)] at hW
  have h1 := isUnit_of_mul_isUnit_left hW
  let e : Fin l ≃ {i : Fin n // (i : ℕ) < l} :=
    { toFun := fun a => ⟨Fin.castLE h a, a.2⟩
      invFun := fun a => ⟨a.1, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1

/- English proof (translation)
Use `set f := Fin.castLE h with hf`. Use `⟨(A * W * B).submatrix id f * ((A * W * B).submatrix f f).adjugate, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Rewrite using `[Matrix.mul_apply]`. Conclude with `O.sum_mem fun k _ => O.mul_mem (hZ _ _) (adj_mem O _ (fun _ _ => hZ _ _) _ _)`.

Establish `hu : IsUnit (W.submatrix f f * B.submatrix f f).det`. Rewrite using `[Matrix.det_mul, det_up h B hB hB1, mul_one]`. Conclude with `unit_cut h W hW hc`. Establish `h1 : (A * W * B).submatrix id f = A.submatrix id f * (W.submatrix f f * B.submatrix f f)`. Rewrite using `[sub_mul_right h _ _ B (fun k b hk hb => hB _ _ (by rw [Fin.lt_def]; omega)), sub_mul_right h _ A W hc, Matrix.mul_assoc]`.

Establish `h2 : (A * W * B).submatrix id f * ((A * W * B).submatrix f f).adjugate * A.submatrix f f * (W.submatrix f f * B.submatrix f f) = ((W.submatrix f f).det • A.submatrix id f) * (W.submatrix f f * B.submatrix f f)`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (A.submatrix f f), ← sub_three h A W B hA hB, Matrix.mul_assoc, Matrix.adjugate_mul, det_three h A W B hA hA1 hB hB1, Matrix.smul_mul, ← h1, Matrix.mul_smul, Matrix.mul_one]`. Establish `h3` using `congrArg (· * (W.submatrix f f * B.submatrix f f)⁻¹) h2`. Simplify `h3` using `only [Matrix.mul_nonsing_inv_cancel_right _ _ hu]`.
-/
theorem col_lemma (O : Subring E) {n l : ℕ} (h : l ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0) :
    ∃ G : Matrix (Fin n) (Fin l) E, (∀ a b, G a b ∈ O) ∧
      G * A.submatrix (Fin.castLE h) (Fin.castLE h) =
        (W.submatrix (Fin.castLE h) (Fin.castLE h)).det • A.submatrix id (Fin.castLE h) := by
  set f := Fin.castLE h with hf
  refine ⟨(A * W * B).submatrix id f * ((A * W * B).submatrix f f).adjugate, ?_, ?_⟩
  · intro a b
    rw [Matrix.mul_apply]
    exact O.sum_mem fun k _ => O.mul_mem (hZ _ _) (adj_mem O _ (fun _ _ => hZ _ _) _ _)
  · have hu : IsUnit (W.submatrix f f * B.submatrix f f).det := by
      rw [Matrix.det_mul, det_up h B hB hB1, mul_one]
      exact unit_cut h W hW hc
    have h1 : (A * W * B).submatrix id f = A.submatrix id f * (W.submatrix f f * B.submatrix f f) := by
      rw [sub_mul_right h _ _ B (fun k b hk hb => hB _ _ (by rw [Fin.lt_def]; omega)),
        sub_mul_right h _ A W hc, Matrix.mul_assoc]
    have h2 : (A * W * B).submatrix id f * ((A * W * B).submatrix f f).adjugate * A.submatrix f f *
        (W.submatrix f f * B.submatrix f f) =
        ((W.submatrix f f).det • A.submatrix id f) * (W.submatrix f f * B.submatrix f f) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A.submatrix f f), ← sub_three h A W B hA hB,
        Matrix.mul_assoc, Matrix.adjugate_mul, det_three h A W B hA hA1 hB hB1, Matrix.smul_mul, ← h1,
        Matrix.mul_smul, Matrix.mul_one]
    have h3 := congrArg (· * (W.submatrix f f * B.submatrix f f)⁻¹) h2
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hu] using h3

end General

section Block
variable {E : Type} [CommRing E]

/- English proof (translation)
Take `⟨G, hG, hGA⟩` from `col_lemma O h A W B hA hA1 hB hB1 hZ hW hc`. Establish `h1` using `congrFun (congrFun hGA j) ⟨i, hi⟩`. Rewrite `h1` using `[Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]`. Express the relevant statement in the definitionally equal form `_ = _ * A j i at h1`. Rewrite using `[← h1]`.

Conclude with `O.sum_mem fun k _ => O.mul_mem (hG _ _) (hAO _ _ k.2 hi')`.
-/
theorem low_mem (O : Subring E) {n l' l : ℕ} (h : l ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l ≤ (k : ℕ) → (b : ℕ) < l → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O)
    (i : Fin n) (hi' : l' ≤ (i : ℕ)) (hi : (i : ℕ) < l) (j : Fin n) :
    (W.submatrix (Fin.castLE h) (Fin.castLE h)).det * A j i ∈ O := by
  obtain ⟨G, hG, hGA⟩ := col_lemma O h A W B hA hA1 hB hB1 hZ hW hc
  have h1 := congrFun (congrFun hGA j) ⟨i, hi⟩
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at h1
  change _ = _ * A j i at h1
  rw [← h1]
  exact O.sum_mem fun k _ => O.mul_mem (hG _ _) (hAO _ _ k.2 hi')

/- English proof (translation)
Take `⟨G, hG, hGA⟩` from `col_lemma O h' A W B hA hA1 hB hB1 hZ hW hc`. Use `set D := (W.submatrix (Fin.castLE h') (Fin.castLE h')).det with hD`. Establish `hDO : D ∈ O`. Rewrite using `[hD, ← det_three h' A W B hA hA1 hB hB1]`. Conclude with `det_mem O _ fun _ _ => hZ _ _`.

Use `set C := W * B with hC`. Establish `hZ' : ∀ a b, (A * C) a b ∈ O` using `by rw [hC, ← Matrix.mul_assoc]; exact hZ`. Establish `key : ∀ a : Fin n, ∑ k : Fin n, (if l' ≤ (k : ℕ) then A a k * (D * C k j) else 0) ∈ O`. Introduce `a`. Establish `h1 : G * (A * C).submatrix (Fin.castLE h') id = D • (A.submatrix id (Fin.castLE h') * C.submatrix (Fin.castLE h') id)`.

Rewrite using `[sub_mul_left h' _ A C hA, ← Matrix.mul_assoc, hGA, Matrix.smul_mul]`. Establish `h2 : D * ∑ k : Fin l', A a (Fin.castLE h' k) * C (Fin.castLE h' k) j ∈ O`. Establish `h3` using `congrFun (congrFun h1 a) j`. Rewrite `h3` using `[Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.submatrix_apply, id] at h3`.

Rewrite using `[← h3]`. Conclude with `O.sum_mem fun k _ => O.mul_mem (hG _ _) (hZ' _ _)`. Establish `h4 : ∑ k : Fin n, (if l' ≤ (k : ℕ) then 0 else A a k * C k j) = ∑ k : Fin l', A a (Fin.castLE h' k) * C (Fin.castLE h' k) j`. Rewrite using `[sum_castLE h' _ (fun k hk => if_pos hk)]`. Use `Finset.sum_congr rfl fun k _ => if_neg ?_` and prove the remaining obligations.

Use `k.2` as an intermediate fact. Simplify using `only [Fin.val_castLE]`. Use linear arithmetic over natural numbers and integers. Establish `h5` using `O.sub_mem (O.mul_mem hDO (hZ' a j)) h2`. Rewrite `h5` using `[← h4, Matrix.mul_apply, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]`.

Use `h5 using 2 with k` and compare the differences between its conclusion and the goal. Apply the tactic sequence `split_ifs <;> ring`. Proceed by induction on `a using WellFoundedLT.induction with`. Consider the case `ind a ih`. Introduce `ha' ha`.

Establish `h1` using `key a`. Rewrite `h1` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos ha', hA1, one_mul]`. Use `(O.add_mem_cancel_right ?_).1 h1` and prove the remaining obligations. Use `O.sum_mem fun k hk => ?_` and prove the remaining obligations. Establish `hka : k ≠ a` using `(Finset.mem_erase.1 hk).1`.

Use `split_ifs with hk'`. Break down `lt_or_gt_of_ne hka with h2 | h2` into its components or cases. Conclude with `O.mul_mem (hAO _ _ ha hk') (ih k h2 hk' (lt_trans h2 ha))`. Rewrite using `[hA _ _ h2, zero_mul]`. Conclude with `O.zero_mem`.

Conclude with `O.zero_mem`.
-/
theorem schur_mem (O : Subring E) {n l' l : ℕ} (h' : l' ≤ n) (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O) (j : Fin n)
    (a : Fin n) : l' ≤ (a : ℕ) → (a : ℕ) < l →
    (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * (W * B) a j ∈ O := by
  obtain ⟨G, hG, hGA⟩ := col_lemma O h' A W B hA hA1 hB hB1 hZ hW hc
  set D := (W.submatrix (Fin.castLE h') (Fin.castLE h')).det with hD
  have hDO : D ∈ O := by
    rw [hD, ← det_three h' A W B hA hA1 hB hB1]
    exact det_mem O _ fun _ _ => hZ _ _
  set C := W * B with hC
  have hZ' : ∀ a b, (A * C) a b ∈ O := by rw [hC, ← Matrix.mul_assoc]; exact hZ
  have key : ∀ a : Fin n, ∑ k : Fin n, (if l' ≤ (k : ℕ) then A a k * (D * C k j) else 0) ∈ O := by
    intro a
    have h1 : G * (A * C).submatrix (Fin.castLE h') id =
        D • (A.submatrix id (Fin.castLE h') * C.submatrix (Fin.castLE h') id) := by
      rw [sub_mul_left h' _ A C hA, ← Matrix.mul_assoc, hGA, Matrix.smul_mul]
    have h2 : D * ∑ k : Fin l', A a (Fin.castLE h' k) * C (Fin.castLE h' k) j ∈ O := by
      have h3 := congrFun (congrFun h1 a) j
      rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.mul_apply] at h3
      simp only [Matrix.submatrix_apply, id] at h3
      rw [← h3]
      exact O.sum_mem fun k _ => O.mul_mem (hG _ _) (hZ' _ _)
    have h4 : ∑ k : Fin n, (if l' ≤ (k : ℕ) then 0 else A a k * C k j) =
        ∑ k : Fin l', A a (Fin.castLE h' k) * C (Fin.castLE h' k) j := by
      rw [sum_castLE h' _ (fun k hk => if_pos hk)]
      refine Finset.sum_congr rfl fun k _ => if_neg ?_
      have := k.2
      simp only [Fin.val_castLE]; omega
    have h5 := O.sub_mem (O.mul_mem hDO (hZ' a j)) h2
    rw [← h4, Matrix.mul_apply, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum] at h5
    convert h5 using 2 with k
    split_ifs <;> ring
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro ha' ha
    have h1 := key a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), if_pos ha', hA1, one_mul] at h1
    refine (O.add_mem_cancel_right ?_).1 h1
    refine O.sum_mem fun k hk => ?_
    have hka : k ≠ a := (Finset.mem_erase.1 hk).1
    split_ifs with hk'
    · rcases lt_or_gt_of_ne hka with h2 | h2
      · exact O.mul_mem (hAO _ _ ha hk') (ih k h2 hk' (lt_trans h2 ha))
      · rw [hA _ _ h2, zero_mul]; exact O.zero_mem
    · exact O.zero_mem

/- English proof (translation)
Use `set f := Fin.castLE h with hf`. Use `set D := (W.submatrix f f).det with hD`. Use `set Y := ((A * W * B).submatrix f f).adjugate * A.submatrix f f with hY`. Establish `hu : IsUnit (B.submatrix f f).det` using `by rw [det_up h B hB hB1]; exact isUnit_one`. Establish `h1 : Y * W.submatrix f f * B.submatrix f f = D • (1 : Matrix (Fin l) (Fin l) E)`.

Rewrite using `[hY, Matrix.mul_assoc _ (A.submatrix f f), Matrix.mul_assoc, ← sub_three h A W B hA hB, Matrix.adjugate_mul, det_three h A W B hA hA1 hB hB1]`. Establish `h2 : B.submatrix f f * (Y * W.submatrix f f) = D • (1 : Matrix (Fin l) (Fin l) E)`. Establish `h3 : B.submatrix f f * (Y * W.submatrix f f) * B.submatrix f f = D • (1 : Matrix (Fin l) (Fin l) E) * B.submatrix f f`. Rewrite using `[Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]`. Establish `h4` using `congrArg (· * (B.submatrix f f)⁻¹) h3`.

Simplify `h4` using `only [Matrix.mul_nonsing_inv_cancel_right _ _ hu]`. Set `p : Fin l` to `⟨l - 1, by omega⟩`. Set `q : Fin l` to `⟨l', hl⟩`. Establish `h5` using `congrFun (congrFun h2 p) p`. Rewrite `h5` using `[Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply, Finset.sum_eq_single p, Matrix.submatrix_apply, hB1, one_mul, Matrix.mul_apply, Finset.sum_eq_single q, Matrix.submatrix_apply, hcol _ _ (by simp [f, p]; omega) (by simp [f, p]; omega), if_pos (by si …`.

Use `⟨Y p q * ε (f p), O.mul_mem ?_ (hε _), by rw [← h5]; ring⟩` and prove the remaining obligations. Rewrite using `[hY, Matrix.mul_apply]`. Conclude with `O.sum_mem fun k _ => O.mul_mem (adj_mem O _ (fun _ _ => hZ _ _) _ _) (hAO _ _ k.2 le_rfl)`. Introduce `b _ hb`. Establish `: (b : ℕ) ≠ l'` using `fun e => hb (Fin.ext e)`.

Rewrite using `[Matrix.submatrix_apply, hcol _ _ (by simp [f, p]; omega) (by simp [f, p]; omega), if_neg (by simp [f, p]; omega), zero_mul, mul_zero]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Establish `: (b : ℕ) ≠ l - 1` using `fun e => hb (Fin.ext e)`. Use `b.2` as an intermediate fact.

Rewrite using `[Matrix.submatrix_apply, hB _ _ (by rw [Fin.lt_def]; simp [f, p]; omega), zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem scal_dvd (O : Subring E) {n l' l : ℕ} (h : l ≤ n) (hl : l' < l)
    (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O)
    (t : E) (ε : Fin n → E) (hε : ∀ b, ε b ∈ O)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b) :
    ∃ y ∈ O, (W.submatrix (Fin.castLE h) (Fin.castLE h)).det = y * t := by
  set f := Fin.castLE h with hf
  set D := (W.submatrix f f).det with hD
  set Y := ((A * W * B).submatrix f f).adjugate * A.submatrix f f with hY
  have hu : IsUnit (B.submatrix f f).det := by rw [det_up h B hB hB1]; exact isUnit_one
  have h1 : Y * W.submatrix f f * B.submatrix f f = D • (1 : Matrix (Fin l) (Fin l) E) := by
    rw [hY, Matrix.mul_assoc _ (A.submatrix f f), Matrix.mul_assoc, ← sub_three h A W B hA hB,
      Matrix.adjugate_mul, det_three h A W B hA hA1 hB hB1]
  have h2 : B.submatrix f f * (Y * W.submatrix f f) = D • (1 : Matrix (Fin l) (Fin l) E) := by
    have h3 : B.submatrix f f * (Y * W.submatrix f f) * B.submatrix f f =
        D • (1 : Matrix (Fin l) (Fin l) E) * B.submatrix f f := by
      rw [Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have h4 := congrArg (· * (B.submatrix f f)⁻¹) h3
    simpa only [Matrix.mul_nonsing_inv_cancel_right _ _ hu] using h4
  let p : Fin l := ⟨l - 1, by omega⟩
  let q : Fin l := ⟨l', hl⟩
  have h5 := congrFun (congrFun h2 p) p
  rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Matrix.mul_apply,
    Finset.sum_eq_single p, Matrix.submatrix_apply, hB1, one_mul, Matrix.mul_apply,
    Finset.sum_eq_single q, Matrix.submatrix_apply,
    hcol _ _ (by simp [f, p]; omega) (by simp [f, p]; omega), if_pos (by simp [f, p, q]; omega)] at h5
  · refine ⟨Y p q * ε (f p), O.mul_mem ?_ (hε _), by rw [← h5]; ring⟩
    rw [hY, Matrix.mul_apply]
    exact O.sum_mem fun k _ => O.mul_mem (adj_mem O _ (fun _ _ => hZ _ _) _ _) (hAO _ _ k.2 le_rfl)
  · intro b _ hb
    have : (b : ℕ) ≠ l' := fun e => hb (Fin.ext e)
    rw [Matrix.submatrix_apply, hcol _ _ (by simp [f, p]; omega) (by simp [f, p]; omega),
      if_neg (by simp [f, p]; omega), zero_mul, mul_zero]
  · simp
  · intro b _ hb
    have : (b : ℕ) ≠ l - 1 := fun e => hb (Fin.ext e)
    have := b.2
    rw [Matrix.submatrix_apply, hB _ _ (by rw [Fin.lt_def]; simp [f, p]; omega), zero_mul]
  · simp

/- English proof (translation)
Take `⟨y, hy, hD⟩` from `scal_dvd O h (by omega) A W B hA hA1 hB hB1 hZ hAO t ε hε hcol`. Set `a : Fin n` to `⟨l + l' - 1 - i, by omega⟩`. Establish `ha' : l' ≤ (a : ℕ)` using `by simp only [a]; omega`. Establish `ha : (a : ℕ) < l` using `by simp only [a]; omega`. Establish `h1` using `schur_mem O h' A W B hA hA1 hB hB1 hZ hW hc hAO j a ha' ha`.

Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i, hrow _ _ ha' ha, if_pos (by simp only [a]; omega)]`. Establish `h2` using `O.mul_mem (O.mul_mem hy (hε i)) h1`. Rewrite using `[hD]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-(y * t * (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * B i j)) * hε2 i`.

Introduce `b _ hb`. Establish `: (b : ℕ) ≠ i` using `fun e => hb (Fin.ext e)`. Rewrite using `[hrow _ _ ha' ha, if_neg (by simp only [a]; omega), zero_mul, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem up_mem (O : Subring E) {n l' l : ℕ} (h : l ≤ n) (h' : l' ≤ n)
    (A W B : Matrix (Fin n) (Fin n) E)
    (hA : ∀ a k : Fin n, a < k → A a k = 0) (hA1 : ∀ a, A a a = 1)
    (hB : ∀ a k : Fin n, k < a → B a k = 0) (hB1 : ∀ a, B a a = 1)
    (hZ : ∀ a b, (A * W * B) a b ∈ O) (hW : IsUnit W.det)
    (hc : ∀ k b : Fin n, l' ≤ (k : ℕ) → (b : ℕ) < l' → W k b = 0)
    (hAO : ∀ a b : Fin n, (a : ℕ) < l → l' ≤ (b : ℕ) → A a b ∈ O)
    (t : E) (ε : Fin n → E) (hε : ∀ b, ε b ∈ O) (hε2 : ∀ b, ε b * ε b = 1)
    (hcol : ∀ a b : Fin n, l' ≤ (b : ℕ) → (b : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (hrow : ∀ a b : Fin n, l' ≤ (a : ℕ) → (a : ℕ) < l →
      W a b = (if (a : ℕ) + b + 1 = l + l' then t else 0) * ε b)
    (i : Fin n) (hi' : l' ≤ (i : ℕ)) (hi : (i : ℕ) < l) (j : Fin n) :
    (W.submatrix (Fin.castLE h) (Fin.castLE h)).det *
      (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * B i j ∈ O := by
  obtain ⟨y, hy, hD⟩ := scal_dvd O h (by omega) A W B hA hA1 hB hB1 hZ hAO t ε hε hcol
  let a : Fin n := ⟨l + l' - 1 - i, by omega⟩
  have ha' : l' ≤ (a : ℕ) := by simp only [a]; omega
  have ha : (a : ℕ) < l := by simp only [a]; omega
  have h1 := schur_mem O h' A W B hA hA1 hB hB1 hZ hW hc hAO j a ha' ha
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hrow _ _ ha' ha,
    if_pos (by simp only [a]; omega)] at h1
  · have h2 := O.mul_mem (O.mul_mem hy (hε i)) h1
    rw [hD]
    convert h2 using 1
    linear_combination (-(y * t * (W.submatrix (Fin.castLE h') (Fin.castLE h')).det * B i j)) * hε2 i
  · intro b _ hb
    have : (b : ℕ) ≠ i := fun e => hb (Fin.ext e)
    rw [hrow _ _ ha' ha, if_neg (by simp only [a]; omega), zero_mul, zero_mul]
  · simp

/- English proof (translation)
The claim follows from `| [], _, _ => rfl | (t, s) :: bs, a, b => by simp only [ptEntryL, entry_symm bs (a - s), and_comm (a := a < s), and_comm (a := (s : ℕ) ≤ a), add_comm a b]`.
-/
theorem entry_symm : ∀ (bs : List (Eˣ × ℕ+)) (a b : ℕ), ptEntryL bs a b = ptEntryL bs b a
  | [], _, _ => rfl
  | (t, s) :: bs, a, b => by
    simp only [ptEntryL, entry_symm bs (a - s), and_comm (a := a < s), and_comm (a := (s : ℕ) ≤ a),
      add_comm a b]

/- English proof (translation)
The claim follows from `| [], i, h => by simp at h | (t, s) :: bs, i, h => by simp only [List.map_cons, List.sum_cons] at h ⊢ by_cases h1 : i < s · refine ⟨0, s, t, by omega, h1, by omega, ?_, ?_, ?_, ?_⟩ · intro a b _ ha _ hb simp [sameBlock, ha, hb] · intro a b _ ha simp only [ptEntryL] split_ifs <;> …`.
-/
theorem block_of : ∀ (bs : List (Eˣ × ℕ+)) (i : ℕ), i < (bs.map (fun b => (b.2 : ℕ))).sum →
    ∃ (l' l : ℕ) (t : E), l' ≤ i ∧ i < l ∧ l ≤ (bs.map (fun b => (b.2 : ℕ))).sum ∧
      (∀ a b, l' ≤ a → a < l → l' ≤ b → b < l → sameBlock bs a b = true) ∧
      (∀ a b, l' ≤ a → a < l → ptEntryL bs a b = if a + b + 1 = l + l' then t else 0) ∧
      (∀ a b, l ≤ a → b < l → ptEntryL bs a b = 0) ∧ (∀ a b, l' ≤ a → b < l' → ptEntryL bs a b = 0)
  | [], i, h => by simp at h
  | (t, s) :: bs, i, h => by
    simp only [List.map_cons, List.sum_cons] at h ⊢
    by_cases h1 : i < s
    · refine ⟨0, s, t, by omega, h1, by omega, ?_, ?_, ?_, ?_⟩
      · intro a b _ ha _ hb
        simp [sameBlock, ha, hb]
      · intro a b _ ha
        simp only [ptEntryL]
        split_ifs <;> first | rfl | omega
      · intro a b ha hb
        simp only [ptEntryL]
        split_ifs <;> first | rfl | omega
      · intro a b ha hb
        omega
    · obtain ⟨l', l, t', e1, e2, e3, e4, e5, e6, e7⟩ := block_of bs (i - s) (by omega)
      refine ⟨s + l', s + l, t', by omega, by omega, by omega, ?_, ?_, ?_, ?_⟩
      · intro a b ha' ha hb' hb
        have := e4 (a - s) (b - s) (by omega) (by omega) (by omega) (by omega)
        simp only [sameBlock, this, Bool.and_true, Bool.or_eq_true, decide_eq_true_eq]
        omega
      · intro a b ha' ha
        simp only [ptEntryL, e5 (a - s) (b - s) (by omega) (by omega)]
        split_ifs <;> first | rfl | omega
      · intro a b ha hb
        simp only [ptEntryL]
        split_ifs
        · omega
        · omega
        · exact e6 _ _ (by omega) (by omega)
        · rfl
      · intro a b ha hb
        simp only [ptEntryL]
        split_ifs
        · omega
        · omega
        · exact e7 _ _ (by omega) (by omega)
        · rfl

end Block

section Main
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

/- English proof (translation)
Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)`. Establish `hadd` using `(GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1`. Establish `hn : ∀ y : E, IsUnit y → ∃ c : F, c ≠ 0 ∧ algebraMap F E c = y * L.cj y`. Introduce `y hy`. Take `⟨c, hc⟩` from `(L.cj_fix (y * L.cj y)).1 (by rw [map_mul, L.cj_cj, mul_comm])`.

Use `⟨c, ?_, hc⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `(hy.mul (hy.map L.cj)).ne_zero (by rw [← hc, map_zero])`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Use `hadd 1 1 one_ne_zero one_ne_zero` as an intermediate fact. Simplify using `only [mul_one, map_one, Finset.prod_empty, Finset.sum_empty] at this ⊢`. Use linear arithmetic over natural numbers and integers. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha, ← ih]`.

Take `⟨c, hc0, hc⟩` from `hn _ (hx a)`. Take `⟨d, hd0, hd⟩` from `hn (∏ i ∈ s, x i) (IsUnit.prod_iff.2 fun i _ => hx i)`. Rewrite using `[← hc, ← hd, ← hadd c d hc0 hd0, map_mul (algebraMap F E), hc, hd, map_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vE_norm_prod (L : LocE F E) (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) {ι : Type} (x : ι → E)
    (hx : ∀ i, IsUnit (x i)) (s : Finset ι) :
    vE L ϖ ((∏ i ∈ s, x i) * L.cj (∏ i ∈ s, x i)) = ∑ i ∈ s, vE L ϖ (x i * L.cj (x i)) := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hadd := (GlobalTheory.UnramVal.vE_valuation L ϖ hϖ).1
  have hn : ∀ y : E, IsUnit y → ∃ c : F, c ≠ 0 ∧ algebraMap F E c = y * L.cj y := by
    intro y hy
    obtain ⟨c, hc⟩ := (L.cj_fix (y * L.cj y)).1 (by rw [map_mul, L.cj_cj, mul_comm])
    refine ⟨c, ?_, hc⟩
    rintro rfl
    exact (hy.mul (hy.map L.cj)).ne_zero (by rw [← hc, map_zero])
  induction s using Finset.induction_on with
  | empty =>
    have := hadd 1 1 one_ne_zero one_ne_zero
    simp only [mul_one, map_one, Finset.prod_empty, Finset.sum_empty] at this ⊢
    omega
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    obtain ⟨c, hc0, hc⟩ := hn _ (hx a)
    obtain ⟨d, hd0, hd⟩ := hn (∏ i ∈ s, x i) (IsUnit.prod_iff.2 fun i _ => hx i)
    rw [← hc, ← hd, ← hadd c d hc0 hd0, map_mul (algebraMap F E), hc, hd, map_mul]
    congr 1
    ring

end Main

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S u u' hu hu' huO hZ Δ hΔ`. Establish `: Nontrivial E` using `Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)`. Establish `hcj : ∀ x ∈ L.O, L.cj x ∈ L.O` using `fun x hx => ((GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 x hx).1`. Take `⟨-, -, -, hW, hun, -⟩` from `GlobalTheory.FrameBasic.main L r k S`. Establish `hW' : IsUnit S.Zh.det` using `hW`.

Establish `hA : ∀ a b : Fin (r + 1), a < b → cT L u a b = 0` using `fun a b h => by`. Rewrite using `[cT, hu.1 _ _ h, map_zero]`. Establish `hA1 : ∀ a : Fin (r + 1), cT L u a a = 1` using `fun a => by rw [cT, hu.2, map_one]`. Establish `hB : ∀ a b : Fin (r + 1), b < a → u' a b = 0` using `hu'.1`. Establish `hDO : ∀ l, S.D l ∈ L.O` using `fun l => by`.

Unfold `Frames.D lead`. Rewrite using `[← det_three _ _ _ _ hA hA1 hB hu'.2]`. Conclude with `det_mem _ _ fun _ _ => hZ _ _`. Use `set x : Fin (r + 2) → E := fun l => if S.D l ≠ 0 then S.D l else 1 with hx`. Establish `hxO : ∀ l, x l ∈ L.O` using `fun l => by`.

Simplify using `only [hx]`. Use `split_ifs`. Conclude with `hDO l`. Conclude with `L.O.one_mem`. Establish `hxu : ∀ l, IsUnit (x l)` using `fun l => by`.

Simplify using `only [hx]`. Use `split_ifs with h`. Conclude with `hun l h`. Conclude with `isUnit_one`. Establish `h10 : vE L S.ϖ 1 = 0`.

Simplify using `using vE_norm_prod L S.ϖ S.ϖ_irr x hxu ∅`. Use `⟨hΔ ▸ L.O.prod_mem fun l _ => hxO l, hΔ ▸ IsUnit.prod_iff.2 fun l _ => hxu l, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hΔ, vE_norm_prod L S.ϖ S.ϖ_irr x hxu, Frames.vD]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : S.D l = 0`.

Simplify using `[hx, h0, h10]`. Distinguish the cases in `h1 : l = 0`. Establish `: S.D 0 = 1` using `Matrix.det_isEmpty (n := Fin 0)`. Simplify using `[hx, h1, this, h10]`. Simplify using `[hx, h0, h1]`.

Introduce `i j`. Take `⟨l', l, t, e1, e2, e3, e4, e5, e6, e7⟩` from `block_of S.w.blocks i (by rw [S.w.size]; exact i.2)`. Rewrite `e3` using `[S.w.size]`. Establish `e3' : l' ≤ r + 1` using `by omega`. Establish `hZh : ∀ a b : Fin (r + 1), S.Zh a b = ptEntryL S.w.blocks a b * (-1) ^ (r - (b : ℕ))` using `fun a b => S.relevant a b`.

Establish `hc : ∀ a b : Fin (r + 1), l ≤ (a : ℕ) → (b : ℕ) < l → S.Zh a b = 0` using `fun a b ha hb => by`. Rewrite using `[hZh, e6 _ _ ha hb, zero_mul]`. Establish `hc' : ∀ a b : Fin (r + 1), l' ≤ (a : ℕ) → (b : ℕ) < l' → S.Zh a b = 0` using `fun a b ha hb => by`. Rewrite using `[hZh, e7 _ _ ha hb, zero_mul]`. Establish `hAO : ∀ a b : Fin (r + 1), (a : ℕ) < l → l' ≤ (b : ℕ) → cT L u a b ∈ L.O`.

Introduce `a b ha hb`. Distinguish the cases in `hab : a < b`. Rewrite using `[hA _ _ hab]`. Conclude with `L.O.zero_mem`. Rewrite `hab` using `[Fin.lt_def]`.

Conclude with `hcj _ (huO _ _ (e4 _ _ hb (by omega) (by omega) ha))`. Establish `g1` using `low_mem L.O e3 _ _ _ hA hA1 hB hu'.2 hZ hW' hc hAO i e1 e2 j`. Establish `g2` using `up_mem L.O e3 e3' _ _ _ hA hA1 hB hu'.2 hZ hW' hc' hAO t (fun b => (-1) ^ (r - (b : ℕ))) (fun b => L.O.pow_mem (L.O.neg_mem L.O.one_mem) _) (fun b => by rw [← mul_pow]; simp) (fun a b hb' hb => by rw [hZh, entry_symm, e5 _ _ hb' hb, add_comm (b : ℕ) a]) (fun a b ha' ha => by rw [ …`. Set `p : Fin (r + 2)` to `⟨l, by omega⟩`. Set `p' : Fin (r + 2)` to `⟨l', by omega⟩`.

Establish `hp : x p = (S.Zh.submatrix (Fin.castLE e3) (Fin.castLE e3)).det` using `if_pos (unit_cut e3 _ hW' hc).ne_zero`. Establish `hp' : x p' = (S.Zh.submatrix (Fin.castLE e3') (Fin.castLE e3')).det` using `if_pos (unit_cut e3' _ hW' hc').ne_zero`. Establish `hne : p' ≠ p` using `fun e => by`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [p, p'] at this`.

Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨y, hy, hΔy⟩ : ∃ y ∈ L.O, Δ = x p * (x p' * y) := by`. Use `⟨∏ m ∈ (Finset.univ.erase p).erase p', x m, L.O.prod_mem fun m _ => hxO m, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩), Finset.mul_prod_erase _ _ (Finset.mem_univ _), hΔ]`. Rewrite `g1` using `[← hp]`.

Rewrite `g2` using `[← hp, ← hp']`. Prove the components needed by the constructor for the conclusion. Establish `g3` using `hcj _ (L.O.mul_mem (L.O.mul_mem (hxO p') hy) g1)`. Rewrite using `[hΔy]`. Use `g3 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [cT, map_mul, L.cj_cj]`. Expand and normalize the polynomial expressions, which then agree. Establish `g3` using `L.O.mul_mem hy g2`. Rewrite using `[hΔy]`. Use `g3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, IsUni u → IsUni u' → (∀ i j : Fin (r + 1), sameBlock S.w.blocks i j = true → u i j ∈ L.O) → IsIntM L (cT L u * S.Zh * u') → ∀ Δ : E, Δ = ∏ l : Fin (r + 2), (if S.D l ≠ 0 then S.D l else 1) → Δ ∈ L.O ∧ IsUnit Δ ∧ vE L S.ϖ (Δ * L.cj Δ) = S.vD ∧ ∀ i j, L.cj Δ * u i j ∈ L.O ∧ Δ * u' i j ∈ L.O := by
  intro F _ _ _ _ _ E _ _ _ L r k S u u' hu hu' huO hZ Δ hΔ
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; norm_num)
  have hcj : ∀ x ∈ L.O, L.cj x ∈ L.O := fun x hx =>
    ((GlobalTheory.UnramOrder.order_facts L S.ϖ S.ϖ_irr).2.1 x hx).1
  obtain ⟨-, -, -, hW, hun, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hW' : IsUnit S.Zh.det := hW
  have hA : ∀ a b : Fin (r + 1), a < b → cT L u a b = 0 := fun a b h => by
    rw [cT, hu.1 _ _ h, map_zero]
  have hA1 : ∀ a : Fin (r + 1), cT L u a a = 1 := fun a => by rw [cT, hu.2, map_one]
  have hB : ∀ a b : Fin (r + 1), b < a → u' a b = 0 := hu'.1
  have hDO : ∀ l, S.D l ∈ L.O := fun l => by
    unfold Frames.D lead
    rw [← det_three _ _ _ _ hA hA1 hB hu'.2]
    exact det_mem _ _ fun _ _ => hZ _ _
  set x : Fin (r + 2) → E := fun l => if S.D l ≠ 0 then S.D l else 1 with hx
  have hxO : ∀ l, x l ∈ L.O := fun l => by
    simp only [hx]; split_ifs
    · exact hDO l
    · exact L.O.one_mem
  have hxu : ∀ l, IsUnit (x l) := fun l => by
    simp only [hx]; split_ifs with h
    · exact hun l h
    · exact isUnit_one
  have h10 : vE L S.ϖ 1 = 0 := by
    simpa using vE_norm_prod L S.ϖ S.ϖ_irr x hxu ∅
  refine ⟨hΔ ▸ L.O.prod_mem fun l _ => hxO l, hΔ ▸ IsUnit.prod_iff.2 fun l _ => hxu l, ?_, ?_⟩
  · rw [hΔ, vE_norm_prod L S.ϖ S.ϖ_irr x hxu, Frames.vD]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases h0 : S.D l = 0
    · simp [hx, h0, h10]
    · by_cases h1 : l = 0
      · have : S.D 0 = 1 := Matrix.det_isEmpty (n := Fin 0)
        simp [hx, h1, this, h10]
      · simp [hx, h0, h1]
  · intro i j
    obtain ⟨l', l, t, e1, e2, e3, e4, e5, e6, e7⟩ :=
      block_of S.w.blocks i (by rw [S.w.size]; exact i.2)
    rw [S.w.size] at e3
    have e3' : l' ≤ r + 1 := by omega
    have hZh : ∀ a b : Fin (r + 1), S.Zh a b = ptEntryL S.w.blocks a b * (-1) ^ (r - (b : ℕ)) :=
      fun a b => S.relevant a b
    have hc : ∀ a b : Fin (r + 1), l ≤ (a : ℕ) → (b : ℕ) < l → S.Zh a b = 0 := fun a b ha hb => by
      rw [hZh, e6 _ _ ha hb, zero_mul]
    have hc' : ∀ a b : Fin (r + 1), l' ≤ (a : ℕ) → (b : ℕ) < l' → S.Zh a b = 0 := fun a b ha hb => by
      rw [hZh, e7 _ _ ha hb, zero_mul]
    have hAO : ∀ a b : Fin (r + 1), (a : ℕ) < l → l' ≤ (b : ℕ) → cT L u a b ∈ L.O := by
      intro a b ha hb
      by_cases hab : a < b
      · rw [hA _ _ hab]; exact L.O.zero_mem
      · rw [Fin.lt_def] at hab
        exact hcj _ (huO _ _ (e4 _ _ hb (by omega) (by omega) ha))
    have g1 := low_mem L.O e3 _ _ _ hA hA1 hB hu'.2 hZ hW' hc hAO i e1 e2 j
    have g2 := up_mem L.O e3 e3' _ _ _ hA hA1 hB hu'.2 hZ hW' hc' hAO t
      (fun b => (-1) ^ (r - (b : ℕ))) (fun b => L.O.pow_mem (L.O.neg_mem L.O.one_mem) _)
      (fun b => by rw [← mul_pow]; simp)
      (fun a b hb' hb => by rw [hZh, entry_symm, e5 _ _ hb' hb, add_comm (b : ℕ) a])
      (fun a b ha' ha => by rw [hZh, e5 _ _ ha' ha]) i e1 e2 j
    let p : Fin (r + 2) := ⟨l, by omega⟩
    let p' : Fin (r + 2) := ⟨l', by omega⟩
    have hp : x p = (S.Zh.submatrix (Fin.castLE e3) (Fin.castLE e3)).det :=
      if_pos (unit_cut e3 _ hW' hc).ne_zero
    have hp' : x p' = (S.Zh.submatrix (Fin.castLE e3') (Fin.castLE e3')).det :=
      if_pos (unit_cut e3' _ hW' hc').ne_zero
    have hne : p' ≠ p := fun e => by
      have := congrArg Fin.val e
      simp only [p, p'] at this
      omega
    obtain ⟨y, hy, hΔy⟩ : ∃ y ∈ L.O, Δ = x p * (x p' * y) := by
      refine ⟨∏ m ∈ (Finset.univ.erase p).erase p', x m, L.O.prod_mem fun m _ => hxO m, ?_⟩
      rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩),
        Finset.mul_prod_erase _ _ (Finset.mem_univ _), hΔ]
    rw [← hp] at g1
    rw [← hp, ← hp'] at g2
    constructor
    · have g3 := hcj _ (L.O.mul_mem (L.O.mul_mem (hxO p') hy) g1)
      rw [hΔy]
      convert g3 using 1
      simp only [cT, map_mul, L.cj_cj]
      ring
    · have g3 := L.O.mul_mem hy g2
      rw [hΔy]
      convert g3 using 1
      ring

end GlobalTheory.OrbitDenom
