import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply

open Matrix

noncomputable section

namespace PI.HwUniqW

open PI.UpqRep

variable {k r : ℕ}

def InB (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance instDecInB (i : Fin (2 * r + k + 1)) : Decidable (InB k r i) := by unfold InB; infer_instance

def bl (k r : ℕ) (a : Fin k) : Fin (2 * r + k + 1) := ⟨r + a.val, by omega⟩

def sub (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun a b => m (bl k r a) (bl k r b)

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `show r ≤ (bl k r a).val ∧ (bl k r a).val < r + k`. Use `show r ≤ r + a.val ∧ r + a.val < r + k`. Use linear arithmetic over natural numbers and integers.
-/
lemma inB_bl (a : Fin k) : InB k r (bl k r a) := by
  have := a.isLt
  show r ≤ (bl k r a).val ∧ (bl k r a).val < r + k
  show r ≤ r + a.val ∧ r + a.val < r + k
  omega

/- English proof (translation)
Introduce `a b h`. Establish `h'` using `congrArg Fin.val h`. Express the relevant statement in the definitionally equal form `r + a.val = r + b.val at h'`. Conclude with `Fin.ext (by omega)`.
-/
lemma blockIndex_injective : Function.Injective (bl k r) := by
  intro a b h
  have h' := congrArg Fin.val h
  change r + a.val = r + b.val at h'
  exact Fin.ext (by omega)

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Use `show r + c.val - r = c.val`. Use linear arithmetic over natural numbers and integers.
-/
lemma mk_bl (c : Fin k) (p : (bl k r c).val - r < k) : (⟨(bl k r c).val - r, p⟩ : Fin k) = c := by
  apply Fin.ext
  show r + c.val - r = c.val
  omega

/- English proof (translation)
Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`. Apply `Fin.ext` to reduce the goal to its premises. Use `show r + (i.val - r) = i.val`. Use linear arithmetic over natural numbers and integers.
-/
lemma block_mk {i : Fin (2 * r + k + 1)} (hi : InB k r i) (p : i.val - r < k) : bl k r ⟨i.val - r, p⟩ = i := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  apply Fin.ext
  show r + (i.val - r) = i.val
  omega

/- English proof (translation)
Introduce `h`. Substitute `h` using the available equality. Conclude with `hj hi`.
-/
lemma ne_of_inB {i j : Fin (2 * r + k + 1)} (hi : InB k r i) (hj : ¬ InB k r j) : i ≠ j := by
  intro h
  subst h
  exact hj hi

/- English proof (translation)
Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`. Establish `hj' : r ≤ j.val ∧ j.val < r + k` using `hj`. Simplify using `only [blockW]`. Rewrite using `[dif_pos hi', dif_pos hj']`.
-/
lemma blockW_in (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)} (hi : InB k r i)
    (hj : InB k r j) :
    blockW k r h i j = h ⟨i.val - r, by unfold InB at hi; omega⟩ ⟨j.val - r, by unfold InB at hj; omega⟩ := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  simp only [blockW]
  rw [dif_pos hi', dif_pos hj']

/- English proof (translation)
Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`. Establish `hj' : ¬ (r ≤ j.val ∧ j.val < r + k)` using `hj`. Simplify using `only [blockW]`. Rewrite using `[dif_pos hi', dif_neg hj']`.
-/
lemma blockW_in_out (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)} (hi : InB k r i)
    (hj : ¬ InB k r j) : blockW k r h i j = 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  simp only [blockW]
  rw [dif_pos hi', dif_neg hj']

/- English proof (translation)
Establish `hi' : ¬ (r ≤ i.val ∧ i.val < r + k)` using `hi`. Simplify using `only [blockW]`. Rewrite using `[dif_neg hi']`.
-/
lemma blockW_out (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)} (hi : ¬ InB k r i) :
    blockW k r h i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  simp only [blockW]
  rw [dif_neg hi']

/- English proof (translation)
Rewrite using `[blockW_in h (inB_bl a) (inB_bl b)]`. Simplify using `only [mk_bl]`.
-/
lemma blockW_bl (h : Matrix (Fin k) (Fin k) ℂ) (a b : Fin k) :
    blockW k r h (bl k r a) (bl k r b) = h a b := by
  rw [blockW_in h (inB_bl a) (inB_bl b)]
  simp only [mk_bl]

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Conclude with `blockW_bl h a b`.
-/
lemma sub_blockW (h : Matrix (Fin k) (Fin k) ℂ) : sub k r (blockW k r h) = h := by
  funext a b
  exact blockW_bl h a b

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : InB k r i`. Establish `key : ∑ l, blockW k r a i l * blockW k r b l j = ∑ c : Fin k, blockW k r a i (bl k r c) * blockW k r b (bl k r c) j`. Establish `hm` using `Finset.sum_map (Finset.univ : Finset (Fin k)) ⟨bl k r, blockIndex_injective⟩ (fun l => blockW k r a i l * blockW k r b l j)`.

Simplify using `only [Function.Embedding.coeFn_mk] at hm`. Rewrite using `[← hm]`. Use `symm`. Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `l _ hl`.

Establish `hl' : ¬ InB k r l`. Introduce `h'`. Apply `hl` to reduce the goal to its premises. Establish `h'' : r ≤ l.val ∧ l.val < r + k` using `h'`. Simplify using `only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]`.

Conclude with `⟨⟨l.val - r, by omega⟩, block_mk h' _⟩`. Rewrite using `[blockW_in_out a hi hl', zero_mul]`. Rewrite using `[key]`. Distinguish the cases in `hj : InB k r j`. Rewrite using `[blockW_in (a * b) hi hj, Matrix.mul_apply]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `c _`. Rewrite using `[blockW_in a hi (inB_bl c), blockW_in b (inB_bl c) hj]`. Simplify using `only [mk_bl]`. Rewrite using `[blockW_in_out (a * b) hi hj]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `c _`. Rewrite using `[blockW_in_out b (inB_bl c) hj, mul_zero]`. Rewrite using `[blockW_out (a * b) hi, Finset.sum_eq_single i]`. Rewrite using `[blockW_out a hi, if_pos rfl, one_mul]`.

Conclude with `blockW_out b hi`. Introduce `l _ hl`. Rewrite using `[blockW_out a hi, if_neg (Ne.symm hl), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
lemma blockW_mul (a b : Matrix (Fin k) (Fin k) ℂ) :
    blockW k r a * blockW k r b = blockW k r (a * b) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : InB k r i
  · have key : ∑ l, blockW k r a i l * blockW k r b l j
        = ∑ c : Fin k, blockW k r a i (bl k r c) * blockW k r b (bl k r c) j := by
      have hm := Finset.sum_map (Finset.univ : Finset (Fin k)) ⟨bl k r, blockIndex_injective⟩
        (fun l => blockW k r a i l * blockW k r b l j)
      simp only [Function.Embedding.coeFn_mk] at hm
      rw [← hm]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro l _ hl
      have hl' : ¬ InB k r l := by
        intro h'
        apply hl
        have h'' : r ≤ l.val ∧ l.val < r + k := h'
        simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
        exact ⟨⟨l.val - r, by omega⟩, block_mk h' _⟩
      rw [blockW_in_out a hi hl', zero_mul]
    rw [key]
    by_cases hj : InB k r j
    · rw [blockW_in (a * b) hi hj, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro c _
      rw [blockW_in a hi (inB_bl c), blockW_in b (inB_bl c) hj]
      simp only [mk_bl]
    · rw [blockW_in_out (a * b) hi hj]
      apply Finset.sum_eq_zero
      intro c _
      rw [blockW_in_out b (inB_bl c) hj, mul_zero]
  · rw [blockW_out (a * b) hi, Finset.sum_eq_single i]
    · rw [blockW_out a hi, if_pos rfl, one_mul]
      exact blockW_out b hi
    · intro l _ hl
      rw [blockW_out a hi, if_neg (Ne.symm hl), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hi : InB k r i`. Distinguish the cases in `hj : InB k r j`. Rewrite using `[blockW_in _ hi hj, Matrix.one_apply, Matrix.one_apply]`. Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`.

Establish `hj' : r ≤ j.val ∧ j.val < r + k` using `hj`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hij, if_neg]`.

Introduce `h`. Apply `hij` to reduce the goal to its premises. Establish `h2` using `congrArg Fin.val h`. Express the relevant statement in the definitionally equal form `i.val - r = j.val - r at h2`. Conclude with `Fin.ext (by omega)`.

Rewrite using `[blockW_in_out _ hi hj, Matrix.one_apply, if_neg (ne_of_inB hi hj)]`. Rewrite using `[blockW_out _ hi, Matrix.one_apply]`.
-/
lemma blockW_one : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  by_cases hi : InB k r i
  · by_cases hj : InB k r j
    · rw [blockW_in _ hi hj, Matrix.one_apply, Matrix.one_apply]
      have hi' : r ≤ i.val ∧ i.val < r + k := hi
      have hj' : r ≤ j.val ∧ j.val < r + k := hj
      by_cases hij : i = j
      · subst hij
        simp
      · rw [if_neg hij, if_neg]
        intro h
        apply hij
        have h2 := congrArg Fin.val h
        change i.val - r = j.val - r at h2
        exact Fin.ext (by omega)
    · rw [blockW_in_out _ hi hj, Matrix.one_apply, if_neg (ne_of_inB hi hj)]
  · rw [blockW_out _ hi, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply]`. Apply the tactic sequence `by_cases hi : InB k r i <;> by_cases hj : InB k r j`. Rewrite using `[blockW_in a hj hi, blockW_in _ hi hj, Matrix.conjTranspose_apply]`. Rewrite using `[blockW_out a hj, blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj).symm, star_zero]`.

Rewrite using `[blockW_in_out a hj hi, blockW_out _ hi, if_neg (fun h => ne_of_inB hj hi h.symm), star_zero]`. Rewrite using `[blockW_out a hj, blockW_out _ hi]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hij, if_neg (Ne.symm hij), star_zero]`.
-/
lemma blockW_conjTranspose (a : Matrix (Fin k) (Fin k) ℂ) : (blockW k r a)ᴴ = blockW k r aᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : InB k r i <;> by_cases hj : InB k r j
  · rw [blockW_in a hj hi, blockW_in _ hi hj, Matrix.conjTranspose_apply]
  · rw [blockW_out a hj, blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj).symm, star_zero]
  · rw [blockW_in_out a hj hi, blockW_out _ hi, if_neg (fun h => ne_of_inB hj hi h.symm), star_zero]
  · rw [blockW_out a hj, blockW_out _ hi]
    by_cases hij : i = j
    · subst hij
      simp
    · rw [if_neg hij, if_neg (Ne.symm hij), star_zero]

/- English proof (translation)
Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`. Unfold `piI`. Rewrite using `[if_pos (by omega)]`.
-/
lemma piI_in {i : Fin (2 * r + k + 1)} (hi : InB k r i) : piI k r i = i := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  unfold piI
  rw [if_pos (by omega)]

/- English proof (translation)
Establish `hi' : r ≤ i.val ∧ i.val < r + k` using `hi`. Unfold `epsI`. Rewrite using `[if_neg (by omega)]`.
-/
lemma epsI_in {i : Fin (2 * r + k + 1)} (hi : InB k r i) : epsI k r i = 1 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  unfold epsI
  rw [if_neg (by omega)]

/- English proof (translation)
Establish `hi' : ¬ (r ≤ i.val ∧ i.val < r + k)` using `hi`. Establish `h0` using `i.isLt`. Unfold `piI InB`. Use `split_ifs with h`. Conclude with `hi'`.

Use `show ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val < r + k)`. Use linear arithmetic over natural numbers and integers.
-/
lemma piI_out {i : Fin (2 * r + k + 1)} (hi : ¬ InB k r i) : ¬ InB k r (piI k r i) := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  have h0 := i.isLt
  unfold piI InB
  split_ifs with h
  · exact hi'
  · show ¬ (r ≤ 2 * r + k - i.val ∧ 2 * r + k - i.val < r + k)
    omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hl` using `l.isLt`. Simplify using `only [Hpk, piI, epsI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num`.
-/
private lemma Hpk_apply_wp_eq_ite (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l = piI k r i then epsI k r i else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, piI, epsI, Fin.ext_iff]
  split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num

/- English proof (translation)
Establish `hj` using `j.isLt`. Establish `hl` using `l.isLt`. Simplify using `only [Hpk, piI, epsI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num`.
-/
private lemma Hpk_apply_eq_ite_piI (l j : Fin (2 * r + k + 1)) :
    Hpk k r l j = if l = piI k r j then epsI k r j else 0 := by
  have hj := j.isLt
  have hl := l.isLt
  simp only [Hpk, piI, epsI, Fin.ext_iff]
  split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (piI k r j)]`. Rewrite using `[Hpk_apply_eq_ite_piI, if_pos rfl]`. Introduce `l _ hl`. Rewrite using `[Hpk_apply_eq_ite_piI, if_neg hl, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma mul_Hpk_apply_highest_weight_uniqueness (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (M * Hpk k r) i j = M i (piI k r j) * epsI k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r j)]
  · rw [Hpk_apply_eq_ite_piI, if_pos rfl]
  · intro l _ hl
    rw [Hpk_apply_eq_ite_piI, if_neg hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]`. Rewrite using `[Hpk_apply_wp_eq_ite, if_pos rfl]`. Introduce `l _ hl`. Rewrite using `[Hpk_apply_wp_eq_ite, if_neg hl, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma Hpk_mul_applyHighestWeightUniqueness (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * M) i j = epsI k r i * M (piI k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]
  · rw [Hpk_apply_wp_eq_ite, if_pos rfl]
  · intro l _ hl
    rw [Hpk_apply_wp_eq_ite, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Hpk_mul_applyHighestWeightUniqueness, mul_Hpk_apply_highest_weight_uniqueness]`. Distinguish the cases in `hi : InB k r i`. Rewrite using `[piI_in hi, epsI_in hi, one_mul]`. Distinguish the cases in `hj : InB k r j`.

Rewrite using `[piI_in hj, epsI_in hj, mul_one]`. Rewrite using `[blockW_in_out a hi hj, blockW_in_out a hi (piI_out hj), zero_mul]`. Rewrite using `[blockW_out a hi, blockW_out a (piI_out hi)]`. Establish `hi' : ¬ (r ≤ i.val ∧ i.val < r + k)` using `hi`. Establish `h1` using `i.isLt`.

Establish `h2` using `j.isLt`. Simplify using `only [piI, epsI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num`.
-/
lemma Hpk_blockW_comm (a : Matrix (Fin k) (Fin k) ℂ) :
    Hpk k r * blockW k r a = blockW k r a * Hpk k r := by
  ext i j
  rw [Hpk_mul_applyHighestWeightUniqueness, mul_Hpk_apply_highest_weight_uniqueness]
  by_cases hi : InB k r i
  · rw [piI_in hi, epsI_in hi, one_mul]
    by_cases hj : InB k r j
    · rw [piI_in hj, epsI_in hj, mul_one]
    · rw [blockW_in_out a hi hj, blockW_in_out a hi (piI_out hj), zero_mul]
  · rw [blockW_out a hi, blockW_out a (piI_out hi)]
    have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
    have h1 := i.isLt
    have h2 := j.isLt
    simp only [piI, epsI, Fin.ext_iff]
    split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num

/- English proof (translation)
Simplify using `[Jm, allPos]`.
-/
lemma Jm_allPos : Jm (allPos k) = 1 := by
  simp [Jm, allPos]

/- English proof (translation)
Use `show inUJ (allPos k) h ↔ hᴴ * h = 1`. Unfold `inUJ`. Rewrite using `[Jm_allPos, mul_one]`.
-/
lemma mem_UJset_allPos {h : Matrix (Fin k) (Fin k) ℂ} : h ∈ UJset (allPos k) ↔ hᴴ * h = 1 := by
  show inUJ (allPos k) h ↔ hᴴ * h = 1
  unfold inUJ
  rw [Jm_allPos, mul_one]

/- English proof (translation)
Establish `h0 : (blockW k r h)ᴴ * Hpk k r * blockW k r h = Hpk k r` using `hm`. Rewrite `h0` using `[mul_assoc, Hpk_blockW_comm, ← mul_assoc, blockW_conjTranspose, blockW_mul]`. Use extensionality with `a b`. Establish `e` using `congrFun (congrFun h0 (bl k r a)) (bl k r b)`. Rewrite `e` using `[mul_Hpk_apply_highest_weight_uniqueness, Hpk_apply_wp_eq_ite, piI_in (inB_bl b), epsI_in (inB_bl b), mul_one, blockW_bl, piI_in (inB_bl a), epsI_in (inB_bl a)]`.

Rewrite using `[e, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hab, if_neg (fun e' => hab (blockIndex_injective e').symm)]`.
-/
lemma unitary_of_blockW_mem {h : Matrix (Fin k) (Fin k) ℂ} (hm : blockW k r h ∈ UH (Hpk k r)) :
    hᴴ * h = 1 := by
  have h0 : (blockW k r h)ᴴ * Hpk k r * blockW k r h = Hpk k r := hm
  rw [mul_assoc, Hpk_blockW_comm, ← mul_assoc, blockW_conjTranspose, blockW_mul] at h0
  ext a b
  have e := congrFun (congrFun h0 (bl k r a)) (bl k r b)
  rw [mul_Hpk_apply_highest_weight_uniqueness, Hpk_apply_wp_eq_ite, piI_in (inB_bl b), epsI_in (inB_bl b), mul_one, blockW_bl,
    piI_in (inB_bl a), epsI_in (inB_bl a)] at e
  rw [e, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [if_neg hab, if_neg (fun e' => hab (blockIndex_injective e').symm)]

/- English proof (translation)
Simplify using `[bvec, Matrix.mulVec]`.
-/
lemma mulVec_bvec_apply (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (g *ᵥ bvec j) i = g i j := by
  simp [bvec, Matrix.mulVec]

/- English proof (translation)
Simplify using `only [bvec, Pi.single_apply]`.
-/
lemma bvec_apply (i j : Fin (2 * r + k + 1)) : bvec j i = if i = j then 1 else 0 := by
  simp only [bvec, Pi.single_apply]

def FixEW (k r : ℕ) (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ a : Fin r, m *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ m *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    m *ᵥ bvec (wI k r (Fin.last k)) = bvec (wI k r (Fin.last k))

/- English proof (translation)
Establish `hcol : m *ᵥ bvec j = bvec j`. Establish `hj' : ¬ (r ≤ j.val ∧ j.val < r + k)` using `hj`. Establish `h0` using `j.isLt`. Take `⟨h1, h2⟩` from `hm`. Distinguish the cases in `c1 : j.val < r`.

Establish `e : j = eI k r ⟨j.val, c1⟩` using `Fin.ext rfl`. Rewrite using `[e]`. Conclude with `(h1 _).1`. Distinguish the cases in `c2 : j.val = r + k`. Establish `e : j = wI k r (Fin.last k)`.

Apply `Fin.ext` to reduce the goal to its premises. Use `show j.val = r + (Fin.last k).val`. Rewrite using `[Fin.val_last]`. Conclude with `c2`. Rewrite using `[e]`.

Conclude with `h2`. Establish `e : j = esI k r ⟨2 * r + k - j.val, by omega⟩`. Apply `Fin.ext` to reduce the goal to its premises. Use `show j.val = 2 * r + k - (2 * r + k - j.val)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e]`. Conclude with `(h1 _).2`. Establish `e` using `congrFun hcol i`. Rewrite `e` using `[mulVec_bvec_apply, bvec_apply]`. Conclude with `e`.
-/
lemma fix_col {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : FixEW k r m)
    (j : Fin (2 * r + k + 1)) (hj : ¬ InB k r j) (i : Fin (2 * r + k + 1)) :
    m i j = if i = j then 1 else 0 := by
  have hcol : m *ᵥ bvec j = bvec j := by
    have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
    have h0 := j.isLt
    obtain ⟨h1, h2⟩ := hm
    by_cases c1 : j.val < r
    · have e : j = eI k r ⟨j.val, c1⟩ := Fin.ext rfl
      rw [e]
      exact (h1 _).1
    · by_cases c2 : j.val = r + k
      · have e : j = wI k r (Fin.last k) := by
          apply Fin.ext
          show j.val = r + (Fin.last k).val
          rw [Fin.val_last]
          exact c2
        rw [e]
        exact h2
      · have e : j = esI k r ⟨2 * r + k - j.val, by omega⟩ := by
          apply Fin.ext
          show j.val = 2 * r + k - (2 * r + k - j.val)
          omega
        rw [e]
        exact (h1 _).2
  have e := congrFun hcol i
  rw [mulVec_bvec_apply, bvec_apply] at e
  exact e

/- English proof (translation)
Establish `hi` using `i.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [piI]`. Apply the tactic sequence `split_ifs <;> (try dsimp only at *) <;> omega`.
-/
private lemma piI_piI_highest_weight_uniqueness (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [piI]
  split_ifs <;> (try dsimp only at *) <;> omega

/- English proof (translation)
Establish `hU' : mᴴ * Hpk k r * m = Hpk k r` using `hU`. Establish `hpo : ¬ InB k r (piI k r i)` using `piI_out hi`. Establish `e` using `congrFun (congrFun hU' (piI k r i)) j`. Rewrite `e` using `[mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]`. Rewrite `e` using `[Matrix.conjTranspose_apply, fix_col hm _ hpo, if_pos rfl, star_one, one_mul, Hpk_mul_applyHighestWeightUniqueness, Hpk_apply_wp_eq_ite, piI_piI_highest_weight_uniqueness, if_neg (ne_of_inB hj hi)]`.

Establish `hne : epsI k r (piI k r i) ≠ 0`. Unfold `epsI`. Apply the tactic sequence `split_ifs <;> norm_num`. Conclude with `(mul_eq_zero.mp e).resolve_left hne`. Introduce `l _ hl`.

Rewrite using `[Matrix.conjTranspose_apply, fix_col hm _ hpo, if_neg hl, star_zero, zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma fix_row {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : m ∈ UH (Hpk k r))
    (hm : FixEW k r m) (i j : Fin (2 * r + k + 1)) (hi : ¬ InB k r i) (hj : InB k r j) : m i j = 0 := by
  have hU' : mᴴ * Hpk k r * m = Hpk k r := hU
  have hpo : ¬ InB k r (piI k r i) := piI_out hi
  have e := congrFun (congrFun hU' (piI k r i)) j
  rw [mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (piI k r i)] at e
  · rw [Matrix.conjTranspose_apply, fix_col hm _ hpo, if_pos rfl, star_one, one_mul, Hpk_mul_applyHighestWeightUniqueness,
      Hpk_apply_wp_eq_ite, piI_piI_highest_weight_uniqueness, if_neg (ne_of_inB hj hi)] at e
    have hne : epsI k r (piI k r i) ≠ 0 := by
      unfold epsI
      split_ifs <;> norm_num
    exact (mul_eq_zero.mp e).resolve_left hne
  · intro l _ hl
    rw [Matrix.conjTranspose_apply, fix_col hm _ hpo, if_neg hl, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hb : m = blockW k r (sub k r m)`. Use extensionality with `i j`. Distinguish the cases in `hj : InB k r j`. Distinguish the cases in `hi : InB k r i`. Rewrite using `[blockW_in _ hi hj] show m i j = m (bl k r _) (bl k r _)`.

Rewrite using `[block_mk hi, block_mk hj]`. Rewrite using `[fix_row hU hm i j hi hj, blockW_out _ hi, if_neg (ne_of_inB hj hi).symm]`. Rewrite using `[fix_col hm j hj i]`. Distinguish the cases in `hi : InB k r i`. Rewrite using `[blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]`.

Rewrite using `[blockW_out _ hi]`. Use `⟨?_, hb⟩` and prove the remaining obligations. Rewrite using `[mem_UJset_allPos]`. Rewrite `hU` using `[hb]`. Conclude with `unitary_of_blockW_mem hU`.
-/
theorem fix_block {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : m ∈ UH (Hpk k r))
    (hm : FixEW k r m) : sub k r m ∈ UJset (allPos k) ∧ m = blockW k r (sub k r m) := by
  have hb : m = blockW k r (sub k r m) := by
    ext i j
    by_cases hj : InB k r j
    · by_cases hi : InB k r i
      · rw [blockW_in _ hi hj]
        show m i j = m (bl k r _) (bl k r _)
        rw [block_mk hi, block_mk hj]
      · rw [fix_row hU hm i j hi hj, blockW_out _ hi, if_neg (ne_of_inB hj hi).symm]
    · rw [fix_col hm j hj i]
      by_cases hi : InB k r i
      · rw [blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]
      · rw [blockW_out _ hi]
  refine ⟨?_, hb⟩
  rw [mem_UJset_allPos]
  rw [hb] at hU
  exact unitary_of_blockW_mem hU

end PI.HwUniqW

end
