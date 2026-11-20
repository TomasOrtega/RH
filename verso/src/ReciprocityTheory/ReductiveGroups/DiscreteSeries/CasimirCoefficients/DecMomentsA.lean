import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def dmW (U : Matrix (Fin n) (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) (J : {J : Finset (Fin n) // J.card = i}) : ℝ :=
  ‖(U.submatrix (Fin.castLE hi) (J.1.orderEmbOfFin J.2)).det‖ ^ 2

def dmChi (i : ℕ) (a : Fin n) : ℂ := if (a : ℕ) < i then 1 else 0

def dmK (U : Matrix (Fin n) (Fin n) ℂ) (i : ℕ) (k l : Fin n) : ℂ :=
  ∑ a, dmChi i a * (star (U a k) * U a l)

def dmInd (J : Finset (Fin n)) (k : Fin n) : ℂ := if k ∈ J then 1 else 0

/- English proof (translation)
Simplify using `only [dmChi, ite_mul, one_mul, zero_mul]`. Rewrite using `[← Finset.sum_filter]`. Use `Finset.sum_bij (fun a _ => Fin.castLE hi a) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a _`. Simplify using `[Finset.mem_filter, a.isLt]`.

Introduce `a _ b _ h`. Conclude with `Fin.castLE_injective hi h`. Introduce `b hb`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hb`. Conclude with `⟨⟨b, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩`.

Introduce `a _`. Both sides reduce to the same expression.
-/
lemma dm_sum_castLE {i : ℕ} (hi : i ≤ n) (f : Fin n → ℂ) :
    ∑ a : Fin i, f (Fin.castLE hi a) = ∑ a : Fin n, dmChi i a * f a := by
  simp only [dmChi, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun a _ => Fin.castLE hi a) ?_ ?_ ?_ ?_
  · intro a _
    simp [Finset.mem_filter, a.isLt]
  · intro a _ b _ h
    exact Fin.castLE_injective hi h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, hb⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro a _
    rfl

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]`.
-/
lemma dm_entry (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) (a b : Fin n) :
    (U * Matrix.diagonal d * Uᴴ) a b = ∑ j, U a j * d j * star (U b j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

/- English proof (translation)
Simplify `Matrix.mem_unitaryGroup_iff.mp hU` using `[Matrix.star_eq_conjTranspose]`.
-/
lemma dm_UUh {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : U * Uᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hU

/- English proof (translation)
Simplify `Matrix.mem_unitaryGroup_iff'.mp hU` using `[Matrix.star_eq_conjTranspose]`.
-/
lemma dm_UhU {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) : Uᴴ * U = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hU

/- English proof (translation)
Establish `h` using `congrFun (congrFun (dm_UUh hU) a) b`. Rewrite `h` using `[Matrix.mul_apply]`. Simplify `h` using `only [Matrix.conjTranspose_apply]`.
-/
lemma dm_unit {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    ∑ j, U a j * star (U b j) = (1 : Matrix (Fin n) (Fin n) ℂ) a b := by
  have h := congrFun (congrFun (dm_UUh hU) a) b
  rw [Matrix.mul_apply] at h
  simpa only [Matrix.conjTranspose_apply] using h

/- English proof (translation)
Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne]`. Conclude with `fun e => h (Fin.castLE_injective hi e)`.
-/
lemma dm_one_sub {i : ℕ} (hi : i ≤ n) (a b : Fin i) :
    (1 : Matrix (Fin n) (Fin n) ℂ) (Fin.castLE hi a) (Fin.castLE hi b) = (1 : Matrix (Fin i) (Fin i) ℂ) a b := by
  by_cases h : a = b
  · subst h
    simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]
    exact fun e => h (Fin.castLE_injective hi e)

/- English proof (translation)
Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.
-/
lemma dm_normsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Establish `h` using `lead_unitary_diag (U := U) (fun _ => (1 : ℂ)) i hi`. Simplify using `only [Finset.prod_const_one, mul_one] at h`. Simplify using `only [dmW]`. Rewrite using `[← h, lead, dif_pos hi, Matrix.diagonal_one, Matrix.mul_one, dm_UUh hU]`. Establish `h2 : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1`.

Use extensionality with `a b`. Rewrite using `[Matrix.submatrix_apply, dm_one_sub]`. Rewrite using `[h2, Matrix.det_one]`.
-/
lemma dm_mass {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) = 1 := by
  have h := lead_unitary_diag (U := U) (fun _ => (1 : ℂ)) i hi
  simp only [Finset.prod_const_one, mul_one] at h
  simp only [dmW]
  rw [← h, lead, dif_pos hi, Matrix.diagonal_one, Matrix.mul_one, dm_UUh hU]
  have h2 : (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 := by
    ext a b; rw [Matrix.submatrix_apply, dm_one_sub]
  rw [h2, Matrix.det_one]

/- English proof (translation)
Establish `h` using `lead_unitary_diag (U := U) (fun j => if j = k then (2 : ℂ) else 1) i hi`. Establish `hprod : ∀ J : Finset (Fin n), ∏ j ∈ J, (if j = k then (2 : ℂ) else 1) = 1 + dmInd J k`. Apply the tactic sequence `intro J; rw [Finset.prod_ite_eq']; unfold dmInd; split_ifs <;> norm_num`. Simplify using `only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h`. Establish `hm` using `dm_mass hU hi`.

Simplify using `only [dmW] at hm ⊢`. Rewrite `h` using `[hm]`. Set `v : Fin i → ℂ` to `fun a => U (Fin.castLE hi a) k`. Establish `hsub : (U * Matrix.diagonal (fun j => if j = k then (2 : ℂ) else 1) * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit (star v)`. Use extensionality with `a b`.

Rewrite using `[Matrix.submatrix_apply, dm_entry]`. Establish `hj : ∀ j, U (Fin.castLE hi a) j * (if j = k then (2 : ℂ) else 1) * star (U (Fin.castLE hi b) j) = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) + if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0`. Introduce `j`. Distinguish the cases in `hjk : j = k`. Substitute `hjk` using the available equality.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hjk, if_neg (Ne.symm hjk)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU, dm_one_sub]`.

Simplify using `[Matrix.mul_apply, v]`. Rewrite `h` using `[lead, dif_pos hi, hsub, Matrix.det_one_add_replicateCol_mul_replicateRow]`. Establish `hdot : star v ⬝ᵥ v = dmK U i k k`. Rewrite using `[dotProduct, dmK, ← dm_sum_castLE hi (fun a => star (U a k) * U a k)]`. Both sides reduce to the same expression.

Rewrite `h` using `[hdot]`. Take the linear combination `-h`.
-/
lemma sum_minorWeights_indicator {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k : Fin n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * dmInd J.1 k = dmK U i k k := by
  have h := lead_unitary_diag (U := U) (fun j => if j = k then (2 : ℂ) else 1) i hi
  have hprod : ∀ J : Finset (Fin n), ∏ j ∈ J, (if j = k then (2 : ℂ) else 1) = 1 + dmInd J k := by
    intro J; rw [Finset.prod_ite_eq']; unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  simp only [dmW] at hm ⊢
  rw [hm] at h
  let v : Fin i → ℂ := fun a => U (Fin.castLE hi a) k
  have hsub : (U * Matrix.diagonal (fun j => if j = k then (2 : ℂ) else 1) * Uᴴ).submatrix
      (Fin.castLE hi) (Fin.castLE hi) = 1 + Matrix.replicateCol Unit v * Matrix.replicateRow Unit (star v) := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * (if j = k then (2 : ℂ) else 1) * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0 := by
      intro j
      by_cases hjk : j = k
      · subst hjk; simp; ring
      · rw [if_neg hjk, if_neg (Ne.symm hjk)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU, dm_one_sub]
    simp [Matrix.mul_apply, v]
  rw [lead, dif_pos hi, hsub, Matrix.det_one_add_replicateCol_mul_replicateRow] at h
  have hdot : star v ⬝ᵥ v = dmK U i k k := by
    rw [dotProduct, dmK, ← dm_sum_castLE hi (fun a => star (U a k) * U a k)]
    rfl
  rw [hdot] at h
  linear_combination -h

/- English proof (translation)
Establish `h` using `lead_unitary_diag (U := U) (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) i hi`. Establish `hprod : ∀ J : Finset (Fin n), ∏ j ∈ J, ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) = 1 + dmInd J k + dmInd J l + dmInd J k * dmInd J l`. Introduce `J`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']`. Apply the tactic sequence `unfold dmInd; split_ifs <;> norm_num`.

Simplify using `only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h`. Establish `hm` using `dm_mass hU hi`. Establish `h1` using `sum_minorWeights_indicator hU hi k`. Establish `h2` using `sum_minorWeights_indicator hU hi l`. Simplify using `only [dmW] at hm h1 h2 ⊢`.

Rewrite `h` using `[hm, h1, h2]`. Set `W : Matrix (Fin i) (Fin 2) ℂ` to `Matrix.of fun a c => if c = 0 then U (Fin.castLE hi a) k else U (Fin.castLE hi a) l`. Establish `hsub : (U * Matrix.diagonal (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 + W * Wᴴ`. Use extensionality with `a b`. Rewrite using `[Matrix.submatrix_apply, dm_entry]`.

Establish `hj : ∀ j, U (Fin.castLE hi a) j * ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) * star (U (Fin.castLE hi b) j) = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) + ((if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0) + (if l = j the …`. Introduce `j`. Distinguish the cases in `hjk : j = k`. Establish `hjl : j ≠ l` using `hjk ▸ hkl`. Rewrite using `[if_pos hjk, if_neg hjl, if_pos hjk.symm, if_neg (Ne.symm hjl), hjk]`.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hjl : j = l`. Rewrite using `[if_neg hjk, if_pos hjl, if_neg (Ne.symm hjk), if_pos hjl.symm, hjl]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg hjk, if_neg hjl, if_neg (Ne.symm hjk), if_neg (Ne.symm hjl)]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU, dm_one_sub]`. Simplify using `[Matrix.mul_apply, W, Fin.sum_univ_two]`. Establish `hK : ∀ c c' : Fin 2, (Wᴴ * W) c c' = dmK U i (![k, l] c) (![k, l] c')`. Introduce `c c'`.

Rewrite using `[Matrix.mul_apply, dmK, ← dm_sum_castLE hi (fun a => star (U a (![k, l] c)) * U a (![k, l] c'))]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases c <;> fin_cases c' <;> simp [W]`. Rewrite `h` using `[lead, dif_pos hi, hsub, Matrix.det_one_add_mul_comm, Matrix.det_fin_two]`. Simplify using `only [Matrix.add_apply, hK, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide), Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one, zero_add] at h`.

Take the linear combination `-h`.
-/
lemma sum_minorWeights_indicator_pair {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k l : Fin n) (hkl : k ≠ l) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) =
      dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k := by
  have h := lead_unitary_diag (U := U)
    (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) i hi
  have hprod : ∀ J : Finset (Fin n),
      ∏ j ∈ J, ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1)) =
        1 + dmInd J k + dmInd J l + dmInd J k * dmInd J l := by
    intro J
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    unfold dmInd; split_ifs <;> norm_num
  simp only [hprod, mul_add, mul_one, Finset.sum_add_distrib] at h
  have hm := dm_mass hU hi
  have h1 := sum_minorWeights_indicator hU hi k
  have h2 := sum_minorWeights_indicator hU hi l
  simp only [dmW] at hm h1 h2 ⊢
  rw [hm, h1, h2] at h
  let W : Matrix (Fin i) (Fin 2) ℂ :=
    Matrix.of fun a c => if c = 0 then U (Fin.castLE hi a) k else U (Fin.castLE hi a) l
  have hsub : (U * Matrix.diagonal (fun j => (if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
      * Uᴴ).submatrix (Fin.castLE hi) (Fin.castLE hi) = 1 + W * Wᴴ := by
    ext a b
    rw [Matrix.submatrix_apply, dm_entry]
    have hj : ∀ j, U (Fin.castLE hi a) j * ((if j = k then (2 : ℂ) else 1) * (if j = l then (2 : ℂ) else 1))
        * star (U (Fin.castLE hi b) j)
        = U (Fin.castLE hi a) j * star (U (Fin.castLE hi b) j) +
          ((if k = j then U (Fin.castLE hi a) k * star (U (Fin.castLE hi b) k) else 0) +
          (if l = j then U (Fin.castLE hi a) l * star (U (Fin.castLE hi b) l) else 0)) := by
      intro j
      by_cases hjk : j = k
      · have hjl : j ≠ l := hjk ▸ hkl
        rw [if_pos hjk, if_neg hjl, if_pos hjk.symm, if_neg (Ne.symm hjl), hjk]; ring
      · by_cases hjl : j = l
        · rw [if_neg hjk, if_pos hjl, if_neg (Ne.symm hjk), if_pos hjl.symm, hjl]; ring
        · rw [if_neg hjk, if_neg hjl, if_neg (Ne.symm hjk), if_neg (Ne.symm hjl)]; ring
    simp only [hj, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, dm_unit hU,
      dm_one_sub]
    simp [Matrix.mul_apply, W, Fin.sum_univ_two]
  have hK : ∀ c c' : Fin 2, (Wᴴ * W) c c' = dmK U i (![k, l] c) (![k, l] c') := by
    intro c c'
    rw [Matrix.mul_apply, dmK, ← dm_sum_castLE hi (fun a => star (U a (![k, l] c)) * U a (![k, l] c'))]
    refine Finset.sum_congr rfl fun a _ => ?_
    fin_cases c <;> fin_cases c' <;> simp [W]
  rw [lead, dif_pos hi, hsub, Matrix.det_one_add_mul_comm, Matrix.det_fin_two] at h
  simp only [Matrix.add_apply, hK, Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_add] at h
  linear_combination -h

/- English proof (translation)
Distinguish the cases in `hkl : k = l`. Substitute `hkl` using the available equality. Establish `hsq : ∀ (m : Fin n) (J : Finset (Fin n)), dmInd J m * dmInd J m = dmInd J m`. Introduce `m J`. Unfold `dmInd`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[if_pos rfl]`. Simplify using `only [hsq, sum_minorWeights_indicator hU hi]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sum_minorWeights_indicator_pair hU hi k l hkl, if_neg hkl, add_zero]`.
-/
lemma dm_m {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) {i : ℕ} (hi : i ≤ n)
    (k l : Fin n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * dmInd J.1 l) =
      dmK U i k k * dmK U i l l - dmK U i k l * dmK U i l k + if k = l then dmK U i k k else 0 := by
  by_cases hkl : k = l
  · subst hkl
    have hsq : ∀ (m : Fin n) (J : Finset (Fin n)), dmInd J m * dmInd J m = dmInd J m := by
      intro m J
      unfold dmInd
      split_ifs <;> simp
    rw [if_pos rfl]
    simp only [hsq, sum_minorWeights_indicator hU hi]
    ring
  · rw [sum_minorWeights_indicator_pair hU hi k l hkl, if_neg hkl, add_zero]

end ReciprocityTheory.ChartRestriction.DS.S7
