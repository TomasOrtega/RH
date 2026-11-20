import Formalism.ResultantValuation.ResultantConjugate

open Finset Equiv

noncomputable section

namespace Formalism.ResultantValuation

namespace LaplaceProof

/- English proof (translation)
Use `Perm.swap_induction_on f ?_ ?_` and prove the remaining obligations. Rewrite using `[map_one, Perm.signAux_one]`. Introduce `g x y hxy ih`. Rewrite using `[Perm.sign_mul, Perm.signAux_mul, ih, Perm.sign_swap hxy, Perm.signAux_swap hxy]`.
-/
theorem perm_sign_eq_inversion_sign {n : ℕ} (f : Perm (Fin n)) : Perm.sign f = Perm.signAux f := by
  refine Perm.swap_induction_on f ?_ ?_
  · rw [map_one, Perm.signAux_one]
  · intro g x y hxy ih
    rw [Perm.sign_mul, Perm.signAux_mul, ih, Perm.sign_swap hxy, Perm.signAux_swap hxy]

/- English proof (translation)
Establish `hs : Perm.finPairsLT n = univ.sigma (fun x : Fin n => univ.filter (· < x))`. Use extensionality with `⟨x, y⟩`. Simplify using `[Perm.mem_finPairsLT]`. Rewrite using `[hs, Finset.prod_sigma]`. Use `Finset.prod_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_filter]`.
-/
theorem prod_finPairsLT {n : ℕ} (f : (Σ _ : Fin n, Fin n) → ℤˣ) :
    ∏ p ∈ Perm.finPairsLT n, f p = ∏ x : Fin n, ∏ y : Fin n, if y < x then f ⟨x, y⟩ else 1 := by
  have hs : Perm.finPairsLT n = univ.sigma (fun x : Fin n => univ.filter (· < x)) := by
    ext ⟨x, y⟩
    simp [Perm.mem_finPairsLT]
  rw [hs, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_filter]

variable {a b : ℕ}

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨?_, by simp⟩` and prove the remaining obligations. Introduce and unpack `(i | i) (j | j) hij`. Simplify using `only [Sum.elim_inl] at hij`. Rewrite using `[(J.orderEmbOfFin h).injective hij]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr] at hij`. Establish `h1` using `J.orderEmbOfFin_mem h i`. Rewrite `h1` using `[hij]`. Conclude with `absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc j))`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at hij`.

Establish `h1` using `J.orderEmbOfFin_mem h j`. Rewrite `h1` using `[← hij]`. Conclude with `absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc i))`. Simplify using `only [Sum.elim_inr] at hij`. Rewrite using `[(Jᶜ.orderEmbOfFin hc).injective hij]`.
-/
theorem shuffle_bijective (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) :
    Function.Bijective (Sum.elim (J.orderEmbOfFin h) (Jᶜ.orderEmbOfFin hc)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp⟩
  rintro (i | i) (j | j) hij
  · simp only [Sum.elim_inl] at hij
    rw [(J.orderEmbOfFin h).injective hij]
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    have h1 := J.orderEmbOfFin_mem h i
    rw [hij] at h1
    exact absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc j))
  · simp only [Sum.elim_inl, Sum.elim_inr] at hij
    have h1 := J.orderEmbOfFin_mem h j
    rw [← hij] at h1
    exact absurd h1 (Finset.mem_compl.mp (Jᶜ.orderEmbOfFin_mem hc i))
  · simp only [Sum.elim_inr] at hij
    rw [(Jᶜ.orderEmbOfFin hc).injective hij]

def shuffle (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) : Perm (Fin (a + b)) :=
  finSumFinEquiv.symm.trans (Equiv.ofBijective _ (shuffle_bijective J h hc))

/- English proof (translation)
Simplify using `[shuffle]`.
-/
@[simp] theorem shuffle_castAdd (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b)
    (i : Fin a) : shuffle J h hc (Fin.castAdd b i) = J.orderEmbOfFin h i := by
  simp [shuffle]

/- English proof (translation)
Simplify using `[shuffle]`.
-/
@[simp] theorem shuffle_natAdd (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b)
    (j : Fin b) : shuffle J h hc (Fin.natAdd a j) = Jᶜ.orderEmbOfFin hc j := by
  simp [shuffle]

/- English proof (translation)
Establish `hm : J.filter (· ≤ J.orderEmbOfFin h i) = (Finset.Iic i).map (J.orderEmbOfFin h).toEmbedding`. Use extensionality with `y`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_Iic]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hy, hyt⟩`.

Establish `hr : y ∈ Set.range (J.orderEmbOfFin h)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `Finset.mem_coe.mpr hy`. Take `⟨k, rfl⟩` from `hr`. Conclude with `⟨k, (J.orderEmbOfFin h).le_iff_le.mp hyt, rfl⟩`.

Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨Finset.orderEmbOfFin_mem _ _ _, (J.orderEmbOfFin h).le_iff_le.mpr hk⟩`. Rewrite using `[hm, Finset.card_map, Fin.card_Iic]`.
-/
private lemma card_filter_le_orderEmbOfFin (J : Finset (Fin (a + b))) (h : J.card = a) (i : Fin a) :
    (J.filter (· ≤ J.orderEmbOfFin h i)).card = (i : ℕ) + 1 := by
  have hm : J.filter (· ≤ J.orderEmbOfFin h i) = (Finset.Iic i).map (J.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_Iic]
    constructor
    · rintro ⟨hy, hyt⟩
      have hr : y ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hy
      obtain ⟨k, rfl⟩ := hr
      exact ⟨k, (J.orderEmbOfFin h).le_iff_le.mp hyt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (J.orderEmbOfFin h).le_iff_le.mpr hk⟩
  rw [hm, Finset.card_map, Fin.card_Iic]

/- English proof (translation)
Establish `h1` using `card_filter_le_orderEmbOfFin J h i`. Establish `h2 : (J.filter (· ≤ J.orderEmbOfFin h i)).card + (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card = (Finset.Iic (J.orderEmbOfFin h i)).card`. Rewrite using `[← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter disjoint_compl_right), ← Finset.filter_union, Finset.union_compl]`. Use `congr 1`. Use extensionality with `y`.

Simplify using the standard rewrite rules. Rewrite `h2` using `[Fin.card_Iic]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_compl_le (J : Finset (Fin (a + b))) (h : J.card = a) (i : Fin a) :
    (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + (i : ℕ) = (J.orderEmbOfFin h i : ℕ) := by
  have h1 := card_filter_le_orderEmbOfFin J h i
  have h2 : (J.filter (· ≤ J.orderEmbOfFin h i)).card + (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card
      = (Finset.Iic (J.orderEmbOfFin h i)).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter disjoint_compl_right),
      ← Finset.filter_union, Finset.union_compl]
    congr 1
    ext y
    simp
  rw [Fin.card_Iic] at h2
  omega

/- English proof (translation)
Rewrite using `[Perm.signAux.eq_1, prod_finPairsLT]`. Apply the tactic sequence `all_goals rfl`.
-/
private theorem perm_inversion_sign_eq_prod {n : ℕ} (g : Perm (Fin n)) :
    Perm.signAux g = ∏ x : Fin n, ∏ y : Fin n,
      if y < x then (if g x ≤ g y then (-1 : ℤˣ) else 1) else 1 := by
  rw [Perm.signAux.eq_1, prod_finPairsLT]
  all_goals rfl

/- English proof (translation)
Establish `hlt : ∀ (i : Fin a) (j : Fin b), (i : ℕ) < a + (j : ℕ)` using `fun i j => by`. Use `i.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hnlt : ∀ (i : Fin a) (j : Fin b), ¬ (a + (j : ℕ) < (i : ℕ))` using `fun i j => by`. Use `i.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.prod_univ_add, Finset.prod_mul_distrib, Fin.lt_iff_val_lt_val, Fin.coe_castAdd, Fin.coe_natAdd, add_lt_add_iff_left, hlt, hnlt, ↓reduceIte, Finset.prod_const_one, mul_one, one_mul, mul_assoc]`.
-/
private lemma prod_fin_add_lt_split (F : Fin (a + b) → Fin (a + b) → ℤˣ) :
    ∏ x : Fin (a + b), ∏ y : Fin (a + b), (if y < x then F x y else 1) =
      (∏ i : Fin a, ∏ i' : Fin a, if i' < i then F (Fin.castAdd b i) (Fin.castAdd b i') else 1) *
      ((∏ j : Fin b, ∏ i : Fin a, F (Fin.natAdd a j) (Fin.castAdd b i)) *
       (∏ j : Fin b, ∏ j' : Fin b, if j' < j then F (Fin.natAdd a j) (Fin.natAdd a j') else 1)) := by
  have hlt : ∀ (i : Fin a) (j : Fin b), (i : ℕ) < a + (j : ℕ) := fun i j => by
    have := i.isLt
    omega
  have hnlt : ∀ (i : Fin a) (j : Fin b), ¬ (a + (j : ℕ) < (i : ℕ)) := fun i j => by
    have := i.isLt
    omega
  simp only [Fin.prod_univ_add, Finset.prod_mul_distrib, Fin.lt_iff_val_lt_val, Fin.coe_castAdd,
    Fin.coe_natAdd, add_lt_add_iff_left, hlt, hnlt, ↓reduceIte, Finset.prod_const_one, mul_one, one_mul,
    mul_assoc]

/- English proof (translation)
Rewrite using `[← Finset.card_map (Jᶜ.orderEmbOfFin hc).toEmbedding]`. Use `congr 1`. Use extensionality with `y`. Simplify using `only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨j, hj, rfl⟩`. Conclude with `⟨Finset.orderEmbOfFin_mem _ _ _, hj⟩`. Introduce and unpack `⟨hy, hyt⟩`. Establish `hr : y ∈ Set.range (Jᶜ.orderEmbOfFin hc)`. Rewrite using `[Finset.range_orderEmbOfFin]`.

Conclude with `Finset.mem_coe.mpr hy`. Take `⟨j, rfl⟩` from `hr`. Conclude with `⟨j, hyt, rfl⟩`.
-/
private lemma card_filter_compl_orderEmbOfFin_le (J : Finset (Fin (a + b))) (hc : Jᶜ.card = b) (t : Fin (a + b)) :
    (univ.filter (fun j : Fin b => Jᶜ.orderEmbOfFin hc j ≤ t)).card = (Jᶜ.filter (· ≤ t)).card := by
  rw [← Finset.card_map (Jᶜ.orderEmbOfFin hc).toEmbedding]
  congr 1
  ext y
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Finset.orderEmbOfFin_mem _ _ _, hj⟩
  · rintro ⟨hy, hyt⟩
    have hr : y ∈ Set.range (Jᶜ.orderEmbOfFin hc) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hy
    obtain ⟨j, rfl⟩ := hr
    exact ⟨j, hyt, rfl⟩

/- English proof (translation)
Establish `hJ : J = Finset.univ.map (J.orderEmbOfFin h).toEmbedding`. Use extensionality with `y`. Simplify using `only [Finset.mem_map, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hr : y ∈ Set.range (J.orderEmbOfFin h)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `Finset.mem_coe.mpr hy`. Take `⟨k, rfl⟩` from `hr`. Conclude with `⟨k, rfl⟩`.

Introduce and unpack `⟨k, rfl⟩`. Conclude with `Finset.orderEmbOfFin_mem _ _ _`. Use `conv_lhs => rw [hJ]`. Conclude with `Finset.sum_map _ _ _`.
-/
private lemma sum_val_eq_sum_orderEmbOfFin (J : Finset (Fin (a + b))) (h : J.card = a) :
    ∑ j ∈ J, (j : ℕ) = ∑ i : Fin a, (J.orderEmbOfFin h i : ℕ) := by
  have hJ : J = Finset.univ.map (J.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hy
      have hr : y ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hy
      obtain ⟨k, rfl⟩ := hr
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact Finset.orderEmbOfFin_mem _ _ _
  conv_lhs => rw [hJ]
  exact Finset.sum_map _ _ _

/- English proof (translation)
Rewrite using `[perm_sign_eq_inversion_sign, perm_inversion_sign_eq_prod, prod_fin_add_lt_split]`. Establish `hA : (∏ i : Fin a, ∏ i' : Fin a, if i' < i then (if shuffle J h hc (Fin.castAdd b i) ≤ shuffle J h hc (Fin.castAdd b i') then (-1 : ℤˣ) else 1) else 1) = 1`. Use `Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun i' _ => ?_` and prove the remaining obligations. Use `split_ifs with h1 h2`. Rewrite `h2` using `[shuffle_castAdd, shuffle_castAdd, OrderEmbedding.le_iff_le]`.

Conclude with `absurd h2 (not_le.mpr h1)`. Both sides reduce to the same expression. Both sides reduce to the same expression. Establish `hD : (∏ j : Fin b, ∏ j' : Fin b, if j' < j then (if shuffle J h hc (Fin.natAdd a j) ≤ shuffle J h hc (Fin.natAdd a j') then (-1 : ℤˣ) else 1) else 1) = 1`. Use `Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun j' _ => ?_` and prove the remaining obligations.

Use `split_ifs with h1 h2`. Rewrite `h2` using `[shuffle_natAdd, shuffle_natAdd, OrderEmbedding.le_iff_le]`. Conclude with `absurd h2 (not_le.mpr h1)`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Rewrite using `[hA, hD, one_mul, mul_one]`. Simplify using `only [shuffle_castAdd, shuffle_natAdd]`. Rewrite using `[Finset.prod_comm]`. Establish `hrow : ∀ i : Fin a, (∏ j : Fin b, if Jᶜ.orderEmbOfFin hc j ≤ J.orderEmbOfFin h i then (-1 : ℤˣ) else 1) = (-1) ^ (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card`. Introduce `i`.

Rewrite using `[Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_filter_compl_orderEmbOfFin_le]`. Use `(Finset.prod_congr rfl fun i _ => hrow i).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_pow_eq_pow_sum, sum_val_eq_sum_orderEmbOfFin J h]`. Establish `hsum : ∑ i : Fin a, (J.orderEmbOfFin h i : ℕ) = ∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + a * (a - 1) / 2`. Rewrite using `[← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) a, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => (card_compl_le J h i).symm`. Rewrite using `[hsum]`. Generalize the expression as in `(∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card) = C`. Generalize the expression as in `a * (a - 1) / 2 = T`. Rewrite using `[show T + (C + T) = C + 2 * T by ring, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]`.
-/
theorem sign_shuffle (J : Finset (Fin (a + b))) (h : J.card = a) (hc : Jᶜ.card = b) :
    Perm.sign (shuffle J h hc) = (-1) ^ (a * (a - 1) / 2 + ∑ j ∈ J, (j : ℕ)) := by
  rw [perm_sign_eq_inversion_sign, perm_inversion_sign_eq_prod, prod_fin_add_lt_split]
  have hA : (∏ i : Fin a, ∏ i' : Fin a, if i' < i then (if shuffle J h hc (Fin.castAdd b i) ≤
      shuffle J h hc (Fin.castAdd b i') then (-1 : ℤˣ) else 1) else 1) = 1 := by
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun i' _ => ?_
    split_ifs with h1 h2
    · rw [shuffle_castAdd, shuffle_castAdd, OrderEmbedding.le_iff_le] at h2
      exact absurd h2 (not_le.mpr h1)
    · rfl
    · rfl
  have hD : (∏ j : Fin b, ∏ j' : Fin b, if j' < j then (if shuffle J h hc (Fin.natAdd a j) ≤
      shuffle J h hc (Fin.natAdd a j') then (-1 : ℤˣ) else 1) else 1) = 1 := by
    refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun j' _ => ?_
    split_ifs with h1 h2
    · rw [shuffle_natAdd, shuffle_natAdd, OrderEmbedding.le_iff_le] at h2
      exact absurd h2 (not_le.mpr h1)
    · rfl
    · rfl
  rw [hA, hD, one_mul, mul_one]
  simp only [shuffle_castAdd, shuffle_natAdd]
  rw [Finset.prod_comm]
  have hrow : ∀ i : Fin a, (∏ j : Fin b, if Jᶜ.orderEmbOfFin hc j ≤ J.orderEmbOfFin h i then
      (-1 : ℤˣ) else 1) = (-1) ^ (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card := by
    intro i
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, card_filter_compl_orderEmbOfFin_le]
  refine (Finset.prod_congr rfl fun i _ => hrow i).trans ?_
  rw [Finset.prod_pow_eq_pow_sum, sum_val_eq_sum_orderEmbOfFin J h]
  have hsum : ∑ i : Fin a, (J.orderEmbOfFin h i : ℕ) =
      ∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + a * (a - 1) / 2 := by
    rw [← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range (fun i => i) a, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (card_compl_le J h i).symm
  rw [hsum]
  generalize (∑ i : Fin a, (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card) = C
  generalize a * (a - 1) / 2 = T
  rw [show T + (C + T) = C + 2 * T by ring, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/- English proof (translation)
Rewrite using `[← M.det_transpose, Matrix.det_apply']`. Simplify using `only [Matrix.transpose_apply]`.
-/
theorem det_rows {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M : Matrix n n R) : M.det = ∑ σ : Perm n, ((Perm.sign σ : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← M.det_transpose, Matrix.det_apply']
  simp only [Matrix.transpose_apply]

/- English proof (translation)
Rewrite using `[Finset.card_compl, Fintype.card_fin, J.2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem compl_card (J : {J : Finset (Fin (a + b)) // J.card = a}) : (J.1ᶜ).card = b := by
  rw [Finset.card_compl, Fintype.card_fin, J.2]
  omega

def glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a}, Perm (Fin a) × Perm (Fin b)) :
    Perm (Fin (a + b)) :=
  shuffle x.1.1 x.1.2 (compl_card x.1) * finSumFinEquiv.permCongr (Perm.sumCongr x.2.1 x.2.2)

/- English proof (translation)
Simplify using `[glue, Equiv.permCongr_apply]`.
-/
@[simp] theorem glue_castAdd (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) (i : Fin a) :
    glue x (Fin.castAdd b i) = x.1.1.orderEmbOfFin x.1.2 (x.2.1 i) := by
  simp [glue, Equiv.permCongr_apply]

/- English proof (translation)
Simplify using `[glue, Equiv.permCongr_apply]`.
-/
@[simp] theorem glue_natAdd (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) (j : Fin b) :
    glue x (Fin.natAdd a j) = (x.1.1ᶜ).orderEmbOfFin (compl_card x.1) (x.2.2 j) := by
  simp [glue, Equiv.permCongr_apply]

/- English proof (translation)
Simplify using `only [glue, Perm.sign_mul, sign_shuffle, Perm.sign_permCongr, Perm.sign_sumCongr, mul_assoc]`.
-/
theorem sign_glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) :
    Perm.sign (glue x) = (-1) ^ (a * (a - 1) / 2 + ∑ j ∈ x.1.1, (j : ℕ)) *
      Perm.sign x.2.1 * Perm.sign x.2.2 := by
  simp only [glue, Perm.sign_mul, sign_shuffle, Perm.sign_permCongr, Perm.sign_sumCongr, mul_assoc]

/- English proof (translation)
Simplify using `only [glue_castAdd]`. Use extensionality with `y`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `Finset.orderEmbOfFin_mem _ _ _`. Introduce `hy`. Establish `hr : y ∈ Set.range (x.1.1.orderEmbOfFin x.1.2)`. Rewrite using `[Finset.range_orderEmbOfFin]`. Conclude with `Finset.mem_coe.mpr hy`.

Take `⟨k, rfl⟩` from `hr`. Conclude with `⟨x.2.1.symm k, by simp⟩`.
-/
theorem image_glue (x : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
    Perm (Fin a) × Perm (Fin b)) :
    univ.image (fun i => glue x (Fin.castAdd b i)) = x.1.1 := by
  simp only [glue_castAdd]
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.orderEmbOfFin_mem _ _ _
  · intro hy
    have hr : y ∈ Set.range (x.1.1.orderEmbOfFin x.1.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.mpr hy
    obtain ⟨k, rfl⟩ := hr
    exact ⟨x.2.1.symm k, by simp⟩

/- English proof (translation)
Introduce and unpack `⟨⟨J, hJ⟩, σ, τ⟩ ⟨⟨J', hJ'⟩, σ', τ'⟩ heq`. Establish `hJJ : J = J'`. Establish `h1` using `image_glue (⟨⟨J, hJ⟩, σ, τ⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a}, Perm (Fin a) × Perm (Fin b))`. Establish `h2` using `image_glue (⟨⟨J', hJ'⟩, σ', τ'⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a}, Perm (Fin a) × Perm (Fin b))`. Rewrite `h1` using `[heq]`.

Conclude with `h1.symm.trans h2`. Substitute `hJJ` using the available equality. Establish `hσ : σ = σ'`. Use `Equiv.ext fun i => ?_` and prove the remaining obligations. Establish `hi` using `congrArg (fun g : Perm (Fin (a + b)) => g (Fin.castAdd b i)) heq`.

Simplify using `only [glue_castAdd] at hi`. Conclude with `(J.orderEmbOfFin hJ).injective hi`. Establish `hτ : τ = τ'`. Use `Equiv.ext fun j => ?_` and prove the remaining obligations. Establish `hj` using `congrArg (fun g : Perm (Fin (a + b)) => g (Fin.natAdd a j)) heq`.

Simplify using `only [glue_natAdd] at hj`. Conclude with `(Jᶜ.orderEmbOfFin (compl_card ⟨J, hJ⟩)).injective hj`. Substitute `hσ` using the available equality. Substitute `hτ` using the available equality. Both sides reduce to the same expression.
-/
theorem glue_injective : Function.Injective (glue (a := a) (b := b)) := by
  rintro ⟨⟨J, hJ⟩, σ, τ⟩ ⟨⟨J', hJ'⟩, σ', τ'⟩ heq
  have hJJ : J = J' := by
    have h1 := image_glue (⟨⟨J, hJ⟩, σ, τ⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
      Perm (Fin a) × Perm (Fin b))
    have h2 := image_glue (⟨⟨J', hJ'⟩, σ', τ'⟩ : Σ _ : {J : Finset (Fin (a + b)) // J.card = a},
      Perm (Fin a) × Perm (Fin b))
    rw [heq] at h1
    exact h1.symm.trans h2
  subst hJJ
  have hσ : σ = σ' := by
    refine Equiv.ext fun i => ?_
    have hi := congrArg (fun g : Perm (Fin (a + b)) => g (Fin.castAdd b i)) heq
    simp only [glue_castAdd] at hi
    exact (J.orderEmbOfFin hJ).injective hi
  have hτ : τ = τ' := by
    refine Equiv.ext fun j => ?_
    have hj := congrArg (fun g : Perm (Fin (a + b)) => g (Fin.natAdd a j)) heq
    simp only [glue_natAdd] at hj
    exact (Jᶜ.orderEmbOfFin (compl_card ⟨J, hJ⟩)).injective hj
  subst hσ
  subst hτ
  rfl

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨glue_injective, ?_⟩` and prove the remaining obligations. Simplify using `only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_finset_len]`. Establish `key` using `Nat.add_choose_mul_factorial_mul_factorial b a`. Rewrite `key` using `[add_comm b a]`.

Rewrite using `[← key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem glue_bijective : Function.Bijective (glue (a := a) (b := b)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨glue_injective, ?_⟩
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_finset_len]
  have key := Nat.add_choose_mul_factorial_mul_factorial b a
  rw [add_comm b a] at key
  rw [← key]
  ring

end LaplaceProof

open LaplaceProof in
/- English proof (translation)
Introduce `R _ a b M`. Rewrite using `[det_rows M, ← (glue_bijective (a := a) (b := b)).sum_comp, Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[det_rows, det_rows, mul_assoc, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[sign_glue, Fin.prod_univ_add]`. Simplify using `only [glue_castAdd, glue_natAdd, Matrix.submatrix_apply]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem laplaceExpansionRows : LaplaceRows := by
  intro R _ a b M
  rw [det_rows M, ← (glue_bijective (a := a) (b := b)).sum_comp, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [det_rows, det_rows, mul_assoc, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [sign_glue, Fin.prod_univ_add]
  simp only [glue_castAdd, glue_natAdd, Matrix.submatrix_apply]
  push_cast
  ring

end Formalism.ResultantValuation
