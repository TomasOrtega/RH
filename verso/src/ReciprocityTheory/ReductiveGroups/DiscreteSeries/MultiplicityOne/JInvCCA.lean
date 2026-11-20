import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StDiagExists

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

/- English proof (translation)
Unfold `Hpk tau sgn`. Simplify using `only [Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_row (i m : Fin (2 * r + k + 1)) :
    Hpk k r i m = if m = tau k r i then sgn k r i else 0 := by
  unfold Hpk tau sgn
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]`. Rewrite using `[hpk_row, if_pos rfl]`. Introduce `m _ hm`. Rewrite using `[hpk_row, if_neg hm, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem hpk_mul_apply (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm
    rw [hpk_row, if_neg hm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Unfold `tau`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only`. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem tau_tau (i : Fin (2 * r + k + 1)) : tau k r (tau k r i) = i := by
  unfold tau
  apply Fin.ext
  simp only
  split_ifs <;> omega

/- English proof (translation)
Unfold `sgn tau`. Simplify using `only`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem sgn_tau (i : Fin (2 * r + k + 1)) : sgn k r (tau k r i) = sgn k r i := by
  unfold sgn tau
  simp only
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
theorem sgn_mul_self (i : Fin (2 * r + k + 1)) : sgn k r i * sgn k r i = 1 := by
  unfold sgn
  split_ifs <;> norm_num

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]`. Distinguish the cases in `h : j = i`. Rewrite using `[if_pos h, if_pos h.symm, sgn_mul_self]`. Rewrite using `[if_neg h, if_neg (Ne.symm h), mul_zero]`.
-/
theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [hpk_mul_apply, hpk_row, tau_tau, sgn_tau, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm, sgn_mul_self]
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.conjTranspose_apply, hpk_row, hpk_row]`. Distinguish the cases in `h : j = tau k r i`. Establish `h' : i = tau k r j` using `by rw [h, tau_tau]`. Rewrite using `[if_pos h', if_pos h, h, sgn_tau]`.

Apply the tactic sequence `unfold sgn; split_ifs <;> simp`. Establish `h' : ¬ i = tau k r j` using `fun h' => h (by rw [h', tau_tau])`. Rewrite using `[if_neg h', if_neg h, star_zero]`.
-/
theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, hpk_row, hpk_row]
  by_cases h : j = tau k r i
  · have h' : i = tau k r j := by rw [h, tau_tau]
    rw [if_pos h', if_pos h, h, sgn_tau]
    unfold sgn; split_ifs <;> simp
  · have h' : ¬ i = tau k r j := fun h' => h (by rw [h', tau_tau])
    rw [if_neg h', if_neg h, star_zero]

/- English proof (translation)
Apply `Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)` to reduce the goal to its premises. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hg', hpk_sq]`.
-/
theorem isUnit_of_uh {g : Mat k r} (hg : g ∈ GV k r) : IsUnit g.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * gᴴ * Hpk k r)
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq]

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hh' : hᴴ * Hpk k r * h = Hpk k r` using `hh`. Use `show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hg', hh']`.
-/
theorem uh_mul {g h : Mat k r} (hg : g ∈ GV k r) (hh : h ∈ GV k r) : g * h ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hu` using `isUnit_of_uh hg`. Use `show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by`. Rewrite using `[Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem uh_inv {g : Mat k r} (hg : g ∈ GV k r) : g⁻¹ ∈ GV k r := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hu := isUnit_of_uh hg
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [hg']
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by
        rw [Matrix.mul_nonsing_inv _ hu, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

def midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : Fin (k + 1) := ⟨i.val - r, by have := hi; omega⟩

/- English proof (translation)
Use `hi` as an intermediate fact. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [wI, midx]`. Use linear arithmetic over natural numbers and integers.
-/
lemma wI_midx {i : Fin (2 * r + k + 1)} (hi : mid k r i) : wI k r (midx hi) = i := by
  have := hi
  apply Fin.ext
  simp only [wI, midx]
  omega

/- English proof (translation)
Use `m.isLt` as an intermediate fact. Apply the tactic sequence `constructor <;> simp only [wI] <;> omega`.
-/
lemma mid_wI (m : Fin (k + 1)) : mid k r (wI k r m) := by
  have := m.isLt
  constructor <;> simp only [wI] <;> omega

/- English proof (translation)
Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [wI] at this`. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers.
-/
lemma wI_inj {a b : Fin (k + 1)} (h : wI k r a = wI k r b) : a = b := by
  have := congrArg Fin.val h
  simp only [wI] at this
  apply Fin.ext; omega

/- English proof (translation)
Unfold `embWb`. Rewrite using `[dif_neg (fun h => hj h.2)]`. Distinguish the cases in `h : q = j`. Substitute `h` using the available equality. Rewrite using `[if_pos ⟨rfl, hj⟩, if_pos rfl]`.

Rewrite using `[if_neg (fun h' => h h'.1), if_neg h]`.
-/
lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hj h.2)]
  by_cases h : q = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/- English proof (translation)
Unfold `embWb`. Rewrite using `[dif_neg (fun h => hq h.1)]`. Distinguish the cases in `h : q = j`. Rewrite using `[if_pos ⟨h, hq⟩, if_pos h]`. Rewrite using `[if_neg (fun h' => h h'.1), if_neg h]`.
-/
lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hq h.1)]
  by_cases h : q = j
  · rw [if_pos ⟨h, hq⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

/- English proof (translation)
Unfold `embWb`. Rewrite using `[dif_pos ⟨hq, hj⟩]`. Both sides reduce to the same expression.
-/
lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q)
    (hj : mid k r j) : embWb k r μ q j = μ (midx hq) (midx hj) := by
  unfold embWb
  rw [dif_pos ⟨hq, hj⟩]
  rfl

def Em (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) ℂ := fun i m => if i = wI k r m then 1 else 0

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (midx hi)]`. Rewrite using `[Em, if_pos (wI_midx hi).symm, one_mul]`. Introduce `b _ hb`. Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Apply `wI_inj (r := r)` to reduce the goal to its premises. Rewrite using `[wI_midx hi, h]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma Em_mul_mid {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : mid k r i) :
    (Em k r * A) i x = A (midx hi) x := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hi)]
  · rw [Em, if_pos (wI_midx hi).symm, one_mul]
  · intro b _ hb
    rw [Em, if_neg, zero_mul]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hi, h]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`.

Conclude with `hi (h ▸ mid_wI b)`.
-/
lemma Em_mul_out {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X)
    (hi : ¬ mid k r i) : (Em k r * A) i x = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Em, if_neg, zero_mul]
  intro h
  exact hi (h ▸ mid_wI b)

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (midx hj)]`. Rewrite using `[Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]`. Introduce `b _ hb`. Rewrite using `[Matrix.transpose_apply, Em, if_neg, mul_zero]`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Apply `wI_inj (r := r)` to reduce the goal to its premises. Rewrite using `[wI_midx hj, h]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma mul_EmT_mid {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X)
    (hj : mid k r j) : (A * (Em k r)ᵀ) x j = A x (midx hj) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hj)]
  · rw [Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hj, h]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Matrix.transpose_apply, Em, if_neg, mul_zero]`. Introduce `h`.

Conclude with `hj (h ▸ mid_wI b)`.
-/
lemma mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X)
    (hj : ¬ mid k r j) : (A * (Em k r)ᵀ) x j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
  intro h
  exact hj (h ▸ mid_wI b)

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]`. Simplify using `only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]`. Introduce `i _ hi`. Simplify using `only [Matrix.transpose_apply, Em]`. Rewrite using `[if_neg hi (c := i = wI k r a), zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma EmT_Em : (Em k r)ᵀ * Em k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]
  · simp only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]
  · intro i _ hi
    simp only [Matrix.transpose_apply, Em]
    rw [if_neg hi (c := i = wI k r a), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma Em_conjT : (Em k r)ᴴ = (Em k r)ᵀ := by
  ext a b
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Em]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← Em_conjT, Matrix.conjTranspose_conjTranspose]`.
-/
lemma EmT_conjT : ((Em k r)ᵀ)ᴴ = Em k r := by
  rw [← Em_conjT, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]`. Distinguish the cases in `hj : mid k r j`. Rewrite using `[mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]`. Distinguish the cases in `hi : mid k r i`.

Rewrite using `[Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]`. Establish `: Em k r i (midx hj) = if i = j then 1 else 0` using `by rw [Em, wI_midx hj]`. Rewrite using `[this, sub_self, add_zero]`. Rewrite using `[Em_mul_out _ i _ hi, emb_out_row μ i j hi]`. Establish `: Em k r i (midx hj) = if i = j then 1 else 0` using `by rw [Em, wI_midx hj]`.

Rewrite using `[this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]`. Rewrite using `[mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma emb_eq (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ = Em k r * μ * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply]
  by_cases hj : mid k r j
  · rw [mul_EmT_mid _ j i hj, mul_EmT_mid _ j i hj]
    by_cases hi : mid k r i
    · rw [Em_mul_mid _ i _ hi, emb_mid μ i j hi hj]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero]
    · rw [Em_mul_out _ i _ hi, emb_out_row μ i j hi]
      have : Em k r i (midx hj) = if i = j then 1 else 0 := by rw [Em, wI_midx hj]
      rw [this, sub_self, add_zero, if_neg (fun h => hi (by rw [h]; exact hj))]
  · rw [mul_EmT_out _ j i hj, mul_EmT_out _ j i hj, emb_out_col μ i j hj]
    ring

/- English proof (translation)
Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]`.
-/
lemma EmT_Q : (Em k r)ᵀ * (1 - Em k r * (Em k r)ᵀ) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, EmT_Em, Matrix.one_mul, sub_self]

/- English proof (translation)
Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]`.
-/
lemma Q_Em : (1 - Em k r * (Em k r)ᵀ) * Em k r = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, EmT_Em, Matrix.mul_one, sub_self]

/- English proof (translation)
Rewrite using `[emb_eq, emb_eq]`. Use `set E := Em k r with hE`. Use `set Q := 1 - E * Eᵀ with hQ`. Establish `t1 : E * a * Eᵀ * M * (E * b * Eᵀ) = E * (a * N * b) * Eᵀ`. Combine the equalities or inequalities in the displayed calculation.

Establish `t2 : E * a * Eᵀ * M * Q = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `t3 : Q * M * (E * b * Eᵀ) = 0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, add_zero, zero_add]`.
-/
lemma sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mat k r)
    (h1 : M * Em k r = Em k r * N) (h2 : (Em k r)ᵀ * M = N * (Em k r)ᵀ) :
    embWb k r a * M * embWb k r b =
      Em k r * (a * N * b) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * M * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_eq, emb_eq]
  set E := Em k r with hE
  set Q := 1 - E * Eᵀ with hQ
  have t1 : E * a * Eᵀ * M * (E * b * Eᵀ) = E * (a * N * b) * Eᵀ := by
    calc E * a * Eᵀ * M * (E * b * Eᵀ) = E * a * (Eᵀ * M) * E * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * E) * b * Eᵀ := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = E * (a * N * b) * Eᵀ := by rw [EmT_Em]; simp only [Matrix.mul_assoc, Matrix.one_mul]
  have t2 : E * a * Eᵀ * M * Q = 0 := by
    calc E * a * Eᵀ * M * Q = E * a * (Eᵀ * M) * Q := by simp only [Matrix.mul_assoc]
      _ = E * a * N * (Eᵀ * Q) := by rw [h2]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [EmT_Q, Matrix.mul_zero]
  have t3 : Q * M * (E * b * Eᵀ) = 0 := by
    calc Q * M * (E * b * Eᵀ) = Q * (M * E) * b * Eᵀ := by simp only [Matrix.mul_assoc]
      _ = (Q * E) * N * b * Eᵀ := by rw [h1]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [Q_Em]; simp only [Matrix.zero_mul]
  rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, t1, t2, t3, add_zero, zero_add]

/- English proof (translation)
Rewrite using `[emb_eq, Matrix.mul_one, add_sub_cancel]`.
-/
lemma emb_one : embWb k r 1 = 1 := by
  rw [emb_eq, Matrix.mul_one, add_sub_cancel]

/- English proof (translation)
Rewrite using `[emb_eq, emb_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, EmT_conjT, Em_conjT, Matrix.mul_assoc]`.
-/
lemma emb_conjT (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (embWb k r a)ᴴ = embWb k r aᴴ := by
  rw [emb_eq, emb_eq, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, EmT_conjT, Em_conjT,
    Matrix.mul_assoc]

/- English proof (translation)
Unfold `Hb`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `by_cases h : j = Fin.last k <;> simp [h]`.
-/
lemma Hb_conjT : (Hb k)ᴴ = Hb k := by
  unfold Hb
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  by_cases h : j = Fin.last k <;> simp [h]

/- English proof (translation)
Use extensionality with `i m`. Establish `h1 : (Hpk k r * Em k r) i m = Hpk k r i (wI k r m)`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (wI k r m)]`. Rewrite using `[Em, if_pos rfl, mul_one]`. Introduce `b _ hb`.

Rewrite using `[Em, if_neg hb, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[h1]`. Establish `hm` using `m.isLt`.

Establish `hil` using `i.isLt`. Distinguish the cases in `hi : mid k r i`. Rewrite using `[Em_mul_mid _ i _ hi]`. Establish `h0` using `hi`. Unfold `Hpk Hb`.

Rewrite using `[Matrix.diagonal_apply]`. Simplify using `only [wI, midx, Fin.ext_iff, Fin.val_last]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[Em_mul_out _ i _ hi]`. Unfold `Hpk`.

Simplify using `only [wI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
lemma Hpk_Em : Hpk k r * Em k r = Em k r * Hb k := by
  ext i m
  have h1 : (Hpk k r * Em k r) i m = Hpk k r i (wI k r m) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r m)]
    · rw [Em, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Em, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  have hm := m.isLt
  have hil := i.isLt
  by_cases hi : mid k r i
  · rw [Em_mul_mid _ i _ hi]
    have h0 := hi
    unfold Hpk Hb
    rw [Matrix.diagonal_apply]
    simp only [wI, midx, Fin.ext_iff, Fin.val_last]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [Em_mul_out _ i _ hi]
    unfold Hpk
    simp only [wI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Establish `h` using `congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))`. Rewrite `h` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, hpk_conjT, Hb_conjT]`. Conclude with `h`.
-/
lemma EmT_Hpk : (Em k r)ᵀ * Hpk k r = Hb k * (Em k r)ᵀ := by
  have h := congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, hpk_conjT, Hb_conjT] at h
  exact h

/- English proof (translation)
Rewrite using `[emb_conjT]`. Conclude with `sandwich _ _ _ _ Hpk_Em EmT_Hpk`.
-/
lemma emb_form (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (embWb k r a)ᴴ * Hpk k r * embWb k r a =
      Em k r * (aᴴ * Hb k * a) * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * Hpk k r * (1 - Em k r * (Em k r)ᵀ) := by
  rw [emb_conjT]
  exact sandwich _ _ _ _ Hpk_Em EmT_Hpk

/- English proof (translation)
Use `show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r`. Establish `h1` using `emb_form (k := k) (r := r) 1`. Rewrite `h1` using `[emb_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Rewrite using `[emb_form, h, ← h1]`.
-/
lemma emb_mem {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : aᴴ * Hb k * a = Hb k) : embWb k r a ∈ GV k r := by
  show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r
  have h1 := emb_form (k := k) (r := r) 1
  rw [emb_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one] at h1
  rw [emb_form, h, ← h1]

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvCC
