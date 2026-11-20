import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ColOfLeftInv

open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace WlocSk.NB

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

variable {k r : ℕ}

abbrev Ix (k r : ℕ) := Fin r ⊕ (Fin (k + 1) ⊕ Fin r)

def pos (k r : ℕ) : Ix k r → Fin (2 * r + k + 1)
  | Sum.inl a => eI k r a
  | Sum.inr (Sum.inl j) => wI k r j
  | Sum.inr (Sum.inr a) => esI k r a

/- English proof (translation)
Introduce `p q h`. Apply the tactic sequence `rcases p with a | j | a <;> rcases q with b | j' | b <;>`. Apply the tactic sequence `simp only [pos, eI, wI, esI, Fin.ext_iff] at h <;>`. Use `first`. Consider the case `(congr 1; exact Fin.ext (by omega))`.

Consider the case `(congr 2; exact Fin.ext (by omega))`. Consider the case `(exfalso; omega)`. Consider the case `skip`. Apply the tactic sequence `all_goals (first | (exfalso; have := a.isLt; have := b.isLt; omega) | skip)`.
-/
theorem pos_inj : Function.Injective (pos k r) := by
  intro p q h
  rcases p with a | j | a <;> rcases q with b | j' | b <;>
    simp only [pos, eI, wI, esI, Fin.ext_iff] at h <;>
    first
    | (congr 1; exact Fin.ext (by omega))
    | (congr 2; exact Fin.ext (by omega))
    | (exfalso; omega)
    | skip
  all_goals (first | (exfalso; have := a.isLt; have := b.isLt; omega) | skip)

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨pos_inj, ?_⟩` and prove the remaining obligations. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem pos_bij : Function.Bijective (pos k r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨pos_inj, ?_⟩
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

def posE (k r : ℕ) : Ix k r ≃ Fin (2 * r + k + 1) := Equiv.ofBijective _ pos_bij

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem posE_apply (p : Ix k r) : posE k r p = pos k r p := rfl

/- English proof (translation)
Rewrite using `[← Equiv.sum_comp (posE k r) f, Fintype.sum_sum_type, Fintype.sum_sum_type]`. Conclude with `(add_assoc _ _ _).symm`.
-/
theorem sum_split {β : Type*} [AddCommMonoid β] (f : Fin (2 * r + k + 1) → β) :
    ∑ l, f l = ∑ a, f (eI k r a) + ∑ j, f (wI k r j) + ∑ a, f (esI k r a) := by
  rw [← Equiv.sum_comp (posE k r) f, Fintype.sum_sum_type, Fintype.sum_sum_type]
  exact (add_assoc _ _ _).symm

def dD (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j.val = k then -1 else 1

/- English proof (translation)
Apply the tactic sequence `unfold UnitaryGroupBasics.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega`.
-/
theorem tau_eI (a : Fin r) : UnitaryGroupBasics.tau k r (eI k r a) = esI k r a := by
  unfold UnitaryGroupBasics.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `unfold UnitaryGroupBasics.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega`.
-/
theorem tau_esI (a : Fin r) : UnitaryGroupBasics.tau k r (esI k r a) = eI k r a := by
  unfold UnitaryGroupBasics.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `unfold UnitaryGroupBasics.tau wI; apply Fin.ext; simp only; split_ifs <;> omega`.
-/
theorem tau_wI (j : Fin (k + 1)) : UnitaryGroupBasics.tau k r (wI k r j) = wI k r j := by
  unfold UnitaryGroupBasics.tau wI; apply Fin.ext; simp only; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `unfold UnitaryGroupBasics.sgn eI; simp only; split_ifs <;> first | rfl | omega`.
-/
theorem sgn_eI (a : Fin r) : UnitaryGroupBasics.sgn k r (eI k r a) = 1 := by
  unfold UnitaryGroupBasics.sgn eI; simp only; split_ifs <;> first | rfl | omega

/- English proof (translation)
Apply the tactic sequence `unfold UnitaryGroupBasics.sgn esI; simp only; split_ifs <;> first | rfl | omega`.
-/
theorem sgn_esI (a : Fin r) : UnitaryGroupBasics.sgn k r (esI k r a) = 1 := by
  unfold UnitaryGroupBasics.sgn esI; simp only; split_ifs <;> first | rfl | omega

/- English proof (translation)
Unfold `UnitaryGroupBasics.sgn wI dD`. Simplify using `only [Matrix.diagonal_apply_eq]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem sgn_wI (j : Fin (k + 1)) : UnitaryGroupBasics.sgn k r (wI k r j) = dD k j j := by
  unfold UnitaryGroupBasics.sgn wI dD
  simp only [Matrix.diagonal_apply_eq]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using @pos_inj k r (Sum.inl a) (Sum.inl b) h, fun h => h ▸ rfl⟩`.
-/
theorem eI_inj {a b : Fin r} : eI k r a = eI k r b ↔ a = b :=
  ⟨fun h => by simpa using @pos_inj k r (Sum.inl a) (Sum.inl b) h,
    fun h => h ▸ rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using @pos_inj k r (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) h, fun h => h ▸ rfl⟩`.
-/
theorem esI_inj {a b : Fin r} : esI k r a = esI k r b ↔ a = b :=
  ⟨fun h => by
    simpa using @pos_inj k r (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b)) h,
    fun h => h ▸ rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using @pos_inj k r (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) h, fun h => h ▸ rfl⟩`.
-/
theorem wI_inj {a b : Fin (k + 1)} : wI k r a = wI k r b ↔ a = b :=
  ⟨fun h => by
    simpa using @pos_inj k r (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b)) h,
    fun h => h ▸ rfl⟩

/- English proof (translation)
Introduce `h` and use `by have := @pos_inj k r (Sum.inl a) (Sum.inr (Sum.inr b)) h; simp at this`.
-/
theorem eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := fun h => by
  have := @pos_inj k r (Sum.inl a) (Sum.inr (Sum.inr b)) h; simp at this

/- English proof (translation)
Introduce `h` and use `by have := @pos_inj k r (Sum.inl a) (Sum.inr (Sum.inl j)) h; simp at this`.
-/
theorem eI_ne_wI (a : Fin r) (j : Fin (k + 1)) : eI k r a ≠ wI k r j := fun h => by
  have := @pos_inj k r (Sum.inl a) (Sum.inr (Sum.inl j)) h; simp at this

/- English proof (translation)
Introduce `h` and use `by have := @pos_inj k r (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr a)) h simp at this`.
-/
theorem wI_ne_esI (j : Fin (k + 1)) (a : Fin r) : wI k r j ≠ esI k r a := fun h => by
  have := @pos_inj k r (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr a)) h
  simp at this

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply, sum_split]`. Simplify using `only [UnitaryGroupBasics.hpk_mul_apply, tau_eI, tau_esI, tau_wI, sgn_eI, sgn_esI, sgn_wI, conjTranspose_apply, one_mul, mul_assoc]`.
-/
theorem form_apply (g : Mx k r) (i j : Fin (2 * r + k + 1)) :
    (gᴴ * Hpk k r * g) i j =
      ∑ a, star (g (eI k r a) i) * g (esI k r a) j +
      ∑ c, star (g (wI k r c) i) * dD k c c * g (wI k r c) j +
      ∑ a, star (g (esI k r a) i) * g (eI k r a) j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, sum_split]
  simp only [UnitaryGroupBasics.hpk_mul_apply, tau_eI, tau_esI, tau_wI, sgn_eI, sgn_esI, sgn_wI,
    conjTranspose_apply, one_mul, mul_assoc]

/- English proof (translation)
Rewrite using `[UnitaryGroupBasics.hpk_row, tau_esI, sgn_esI]`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun e => h (eI_inj.1 e).symm), if_neg h]`.
-/
theorem hpk_esI_eI (a b : Fin r) :
    Hpk k r (esI k r a) (eI k r b) = if a = b then 1 else 0 := by
  rw [UnitaryGroupBasics.hpk_row, tau_esI, sgn_esI]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg (fun e => h (eI_inj.1 e).symm), if_neg h]

def bA (g : Mx k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => g (eI k r a) (eI k r b)

def bB (g : Mx k r) : Matrix (Fin r) (Fin (k + 1)) ℂ := fun a j => g (eI k r a) (wI k r j)

def bC (g : Mx k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => g (eI k r a) (esI k r b)

def bE (g : Mx k r) : Matrix (Fin (k + 1)) (Fin r) ℂ := fun j b => g (wI k r j) (esI k r b)

def bF (g : Mx k r) : Matrix (Fin r) (Fin r) ℂ := fun a b => g (esI k r a) (esI k r b)

structure ColB (g : Mx k r) : Prop where
  aa : ∀ a b : Fin r, b ≤ a → g (eI k r a) (eI k r b) = if a = b then 1 else 0
  wa : ∀ (j : Fin (k + 1)) (b : Fin r), g (wI k r j) (eI k r b) = 0
  sa : ∀ a b : Fin r, g (esI k r a) (eI k r b) = 0
  ww : ∀ j c : Fin (k + 1), g (wI k r j) (wI k r c) = if j = c then 1 else 0
  sw : ∀ (a : Fin r) (j : Fin (k + 1)), g (esI k r a) (wI k r j) = 0

/- English proof (translation)
Rewrite using `[h _ _ (by simp only [eI]; omega) (Or.inl (by simp only [eI]; exact hab))]`. Simplify using `only [eI_inj]`. Use `wa j b := by`. Rewrite using `[h _ _ (by simp only [eI]; omega) (Or.inr (by simp only [wI]; omega)), if_neg (eI_ne_wI b j).symm]`. Use `sa a b := by`.

Rewrite using `[h _ _ (by simp only [eI]; omega) (Or.inr (by simp only [esI]; omega)), if_neg (eI_ne_esI b a).symm]`. Use `ww j c := by`. Rewrite using `[h _ _ (by simp only [wI]; omega) (Or.inr (by simp only [wI]; omega))]`. Simplify using `only [wI_inj]`. Use `sw a j := by`.

Rewrite using `[h _ _ (by simp only [wI]; omega) (Or.inr (by simp only [esI]; omega)), if_neg (wI_ne_esI j a).symm]`.
-/
theorem colB_of {g : Mx k r} (h : UnitaryGroupBasics.col k r g) : ColB g where
  aa a b hab := by
    rw [h _ _ (by simp only [eI]; omega) (Or.inl (by simp only [eI]; exact hab))]
    simp only [eI_inj]
  wa j b := by
    rw [h _ _ (by simp only [eI]; omega) (Or.inr (by simp only [wI]; omega)),
      if_neg (eI_ne_wI b j).symm]
  sa a b := by
    rw [h _ _ (by simp only [eI]; omega) (Or.inr (by simp only [esI]; omega)),
      if_neg (eI_ne_esI b a).symm]
  ww j c := by
    rw [h _ _ (by simp only [wI]; omega) (Or.inr (by simp only [wI]; omega))]
    simp only [wI_inj]
  sw a j := by
    rw [h _ _ (by simp only [wI]; omega) (Or.inr (by simp only [esI]; omega)),
      if_neg (wI_ne_esI j a).symm]

/- English proof (translation)
Introduce `a b hab`. Use `show g _ _ = 0`. Rewrite using `[h.aa a b (le_of_lt hab), if_neg (ne_of_gt (show b < a from hab))]`.
-/
theorem bA_upper {g : Mx k r} (h : ColB g) : (bA g).IsUpperTriangular := by
  intro a b hab
  show g _ _ = 0
  rw [h.aa a b (le_of_lt hab), if_neg (ne_of_gt (show b < a from hab))]

/- English proof (translation)
Rewrite using `[det_of_isUpperTriangular (bA_upper h)]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Use `show g _ _ = 1`. Rewrite using `[h.aa a a le_rfl, if_pos rfl]`.
-/
theorem bA_det {g : Mx k r} (h : ColB g) : (bA g).det = 1 := by
  rw [det_of_isUpperTriangular (bA_upper h)]
  refine Finset.prod_eq_one fun a _ => ?_
  show g _ _ = 1
  rw [h.aa a a le_rfl, if_pos rfl]

/- English proof (translation)
Use extensionality with `a b`. Establish `e` using `congrFun (congrFun (show gᴴ * Hpk k r * g = Hpk k r from hu) (esI k r a)) (eI k r b)`. Rewrite `e` using `[form_apply, hpk_esI_eI]`. Simplify using `only [hc.sa, hc.wa, mul_zero, Finset.sum_const_zero, zero_add] at e`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`.

Simplify `e` using `[bF, bA, conjTranspose_apply]`.
-/
theorem rel_F {g : Mx k r} (hc : ColB g) (hu : g ∈ UH (Hpk k r)) : (bF g)ᴴ * bA g = 1 := by
  ext a b
  have e := congrFun (congrFun (show gᴴ * Hpk k r * g = Hpk k r from hu) (esI k r a)) (eI k r b)
  rw [form_apply, hpk_esI_eI] at e
  simp only [hc.sa, hc.wa, mul_zero, Finset.sum_const_zero, zero_add] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simpa [bF, bA, conjTranspose_apply] using e

/- English proof (translation)
Simplify using `only [dD, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]`.
-/
theorem dD_mul_apply {m : Type*} (X : Matrix (Fin (k + 1)) m ℂ) (j : Fin (k + 1)) (b : m) :
    (dD k * X) j b = dD k j j * X j b := by
  simp only [dD, Matrix.diagonal_mul, Matrix.diagonal_apply_eq]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [bA, Matrix.mul_apply]`. Rewrite using `[sum_split]`. Simplify using `[hh.wa, hh.sa]`.
-/
theorem bA_mul {g h : Mx k r} (hh : ColB h) : bA (g * h) = bA g * bA h := by
  ext a b
  simp only [bA, Matrix.mul_apply]
  rw [sum_split]
  simp [hh.wa, hh.sa]

/- English proof (translation)
Use extensionality with `a j`. Simplify using `only [bA, bB, Matrix.mul_apply, Matrix.add_apply]`. Rewrite using `[sum_split]`. Simplify using `[hh.ww, hh.sw]`.
-/
theorem bB_mul {g h : Mx k r} (hh : ColB h) : bB (g * h) = bA g * bB h + bB g := by
  ext a j
  simp only [bA, bB, Matrix.mul_apply, Matrix.add_apply]
  rw [sum_split]
  simp [hh.ww, hh.sw]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [bF, Matrix.mul_apply]`. Rewrite using `[sum_split]`. Simplify using `[hg.sa, hg.sw]`.
-/
theorem bF_mul {g h : Mx k r} (hg : ColB g) : bF (g * h) = bF g * bF h := by
  ext a b
  simp only [bF, Matrix.mul_apply]
  rw [sum_split]
  simp [hg.sa, hg.sw]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [bA, bB, bC, bE, bF, Matrix.mul_apply, Matrix.add_apply]`. Rewrite using `[sum_split]`.
-/
theorem bC_mul (g h : Mx k r) : bC (g * h) = bA g * bC h + bB g * bE h + bC g * bF h := by
  ext a b
  simp only [bA, bB, bC, bE, bF, Matrix.mul_apply, Matrix.add_apply]
  rw [sum_split]

/- English proof (translation)
The claim follows from `colB_of ((UnitaryGroupBasics.nset_iff g).1 hg).2`.
-/
theorem colB_of_mem {g : Mx k r} (hg : g ∈ Nset k r) : ColB g :=
  colB_of ((UnitaryGroupBasics.nset_iff g).1 hg).2

/- English proof (translation)
Establish `hFA` using `rel_F hc hu`. Use `letI : Invertible (bA g).det := by rw [bA_det hc]; exact invertibleOne`. Use `letI : Invertible (bA g) := Matrix.invertibleOfDetInvertible (bA g)`. Establish `hinv : (bA g)⁻¹ = (bF g)ᴴ` using `Matrix.inv_eq_left_inv hFA`. Establish `hT : ((bF g)ᴴ).BlockTriangular id` using `hinv ▸ blockTriangular_inv_of_blockTriangular (bA_upper hc)`.

Introduce `a b hab`. Break down `lt_or_eq_of_le hab with h | rfl` into its components or cases. Rewrite using `[if_neg (ne_of_lt h)]`. Use `hT (show id a < id b from h)` as an intermediate fact. Rewrite `this` using `[conjTranspose_apply, star_eq_zero]`.

Conclude with `this`. Rewrite using `[if_pos rfl]`. Establish `e` using `congrFun (congrFun hFA a) a`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq]`. Establish `h1 : bA g a a = 1` using `by show g _ _ = 1; rw [hc.aa a a le_rfl, if_pos rfl]`.

Rewrite `e` using `[h1, mul_one, conjTranspose_apply]`. Use `congrArg star e` as an intermediate fact. Rewrite `this` using `[star_star, star_one]`. Then use the resulting hypothesis. Introduce `c _ hca`. Break down `lt_or_gt_of_ne hca with h | h` into its components or cases.

Rewrite using `[hT (show id c < id a from h), zero_mul]`. Establish `: bA g c a = 0` using `by show g _ _ = 0; rw [hc.aa c a (le_of_lt h), if_neg (ne_of_gt h)]`. Rewrite using `[this, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem bF_lowId {g : Mx k r} (hc : ColB g) (hu : g ∈ UH (Hpk k r)) :
    ∀ a b : Fin r, a ≤ b → bF g a b = if a = b then 1 else 0 := by
  have hFA := rel_F hc hu
  letI : Invertible (bA g).det := by rw [bA_det hc]; exact invertibleOne
  letI : Invertible (bA g) := Matrix.invertibleOfDetInvertible (bA g)
  have hinv : (bA g)⁻¹ = (bF g)ᴴ := Matrix.inv_eq_left_inv hFA
  have hT : ((bF g)ᴴ).BlockTriangular id := hinv ▸ blockTriangular_inv_of_blockTriangular (bA_upper hc)
  intro a b hab
  rcases lt_or_eq_of_le hab with h | rfl
  · rw [if_neg (ne_of_lt h)]
    have := hT (show id a < id b from h)
    rw [conjTranspose_apply, star_eq_zero] at this
    exact this
  · rw [if_pos rfl]
    have e := congrFun (congrFun hFA a) a
    rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq] at e
    · have h1 : bA g a a = 1 := by
        show g _ _ = 1; rw [hc.aa a a le_rfl, if_pos rfl]
      rw [h1, mul_one, conjTranspose_apply] at e
      have := congrArg star e
      rwa [star_star, star_one] at this
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hT (show id c < id a from h), zero_mul]
      · have : bA g c a = 0 := by
          show g _ _ = 0; rw [hc.aa c a (le_of_lt h), if_neg (ne_of_gt h)]
        rw [this, mul_zero]
    · simp

def wt (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℤ :=
  if i.val < r then (r : ℤ) - i.val else if i.val ≤ r + k then 0 else (r + k : ℤ) - i.val

/- English proof (translation)
Establish `hc` using `colB_of_mem hg`. Establish `hu : g ∈ UH (Hpk k r)` using `hg.1`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]`. Take `⟨p, rfl⟩` from `(posE k r).surjective i`. Take `⟨q, rfl⟩` from `(posE k r).surjective j`.

Simplify using `only [(posE k r).injective.eq_iff]`. Apply the tactic sequence `rcases p with a | c | a <;> rcases q with b | c' | b <;>`. Simplify using `only [posE_apply, pos, wt, eI, wI, esI, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] at h ⊢`. Establish `hb` using `b.isLt`. Establish `ha` using `a.isLt`.

Apply the tactic sequence `have hba : (b : ℕ) ≤ a := by split_ifs at h <;> omega`. Conclude with `hc.aa a b (Fin.le_iff_val_le_val.2 hba)`. Apply the tactic sequence `all_goals first`. Consider the case `(exfalso; have := a.isLt; have := b.isLt; split_ifs at h <;> omega)`. Consider the case `(exfalso; have := a.isLt; split_ifs at h <;> omega)`.

Consider the case `(exfalso; have := b.isLt; split_ifs at h <;> omega)`. Consider the case `skip`. Conclude with `hc.wa c b`. Conclude with `hc.ww c c'`. Conclude with `hc.sa a b`.

Conclude with `hc.sw a c'`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Apply the tactic sequence `split_ifs at h with h1 h2 h3 <;> first | (exfalso; omega) | skip`. Conclude with `bF_lowId hc hu a b (Fin.le_iff_val_le_val.2 (by omega))`.
-/
theorem nset_upper {g : Mx k r} (hg : g ∈ Nset k r) (i j : Fin (2 * r + k + 1))
    (h : ¬ wt k r j < wt k r i) : (g - 1) i j = 0 := by
  have hc := colB_of_mem hg
  have hu : g ∈ UH (Hpk k r) := hg.1
  rw [Matrix.sub_apply, Matrix.one_apply, sub_eq_zero]
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  simp only [(posE k r).injective.eq_iff]
  rcases p with a | c | a <;> rcases q with b | c' | b <;>
    simp only [posE_apply, pos, wt, eI, wI, esI, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
      if_false] at h ⊢
  · have hb := b.isLt
    have ha := a.isLt
    have hba : (b : ℕ) ≤ a := by split_ifs at h <;> omega
    exact hc.aa a b (Fin.le_iff_val_le_val.2 hba)
  all_goals first
    | (exfalso; have := a.isLt; have := b.isLt; split_ifs at h <;> omega)
    | (exfalso; have := a.isLt; split_ifs at h <;> omega)
    | (exfalso; have := b.isLt; split_ifs at h <;> omega)
    | skip
  · exact hc.wa c b
  · exact hc.ww c c'
  · exact hc.sa a b
  · exact hc.sw a c'
  · have ha := a.isLt
    have hb := b.isLt
    split_ifs at h with h1 h2 h3 <;> first | (exfalso; omega) | skip
    exact bF_lowId hc hu a b (Fin.le_iff_val_le_val.2 (by omega))

end WlocSk.NB
