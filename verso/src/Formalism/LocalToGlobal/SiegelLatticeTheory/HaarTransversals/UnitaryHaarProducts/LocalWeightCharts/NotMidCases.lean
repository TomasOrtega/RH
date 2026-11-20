import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace

noncomputable section

open Matrix MeasureTheory Topology
open scoped ComplexConjugate ENNReal NNReal

namespace WlocSk.HM

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

def Hb (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then -1 else 1

def embWb (k r : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Mx k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩
  else if i = j ∧ ¬ (r ≤ i.val ∧ i.val ≤ r + k) then 1 else 0

def UWb (k r : ℕ) : Set (Mx k r) :=
  {g | g ∈ UH (Hpk k r) ∧ ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | simp | norm_num`.
-/
theorem hpk_herm : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp | norm_num

/- English proof (translation)
Use `⟨⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, ?_, ?_, fun a ha => isUnit_of_uh ha.1, ?_⟩` and prove the remaining obligations. Introduce `a ha b hb`. Use `⟨uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]`. Rewrite using `[← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]`.

Rewrite using `[← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]`. Introduce `a ha`. Establish `hu` using `isUnit_of_uh ha.1`. Establish `fix : ∀ v, a *ᵥ v = v → a⁻¹ *ᵥ v = v`. Introduce `v hv`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨uh_inv ha.1, fun c => ⟨fix _ (ha.2.1 c).1, fix _ (ha.2.1 c).2⟩, fix _ ha.2.2⟩`. Establish `hv : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {g : Mx k r | g *ᵥ v = v}` using `fun v => isClosed_eq (Continuous.matrix_mulVec continuous_id continuous_const) continuous_const`. Establish `e : (UWset k r z : Set (Mx k r)) = UH (Hpk k r) ∩ ((⋂ a : Fin r, ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g : Mx k r | g *ᵥ z = z})`. Use extensionality with `g`.

Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]`. Conclude with `Iff.rfl`. Rewrite using `[e]`. Conclude with `uh_closed.inter ((isClosed_iInter fun a => (hv _).inter (hv _)).inter (hv z))`.
-/
theorem uw_clsub (z : Fin (2 * r + k + 1) → ℂ) : ClSub (UWset k r z : Set (Mx k r)) := by
  refine ⟨⟨uh_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, ?_, ?_,
    fun a ha => isUnit_of_uh ha.1, ?_⟩
  · intro a ha b hb
    refine ⟨uh_mul ha.1 hb.1, fun c => ⟨?_, ?_⟩, ?_⟩
    · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).1, (ha.2.1 c).1]
    · rw [← Matrix.mulVec_mulVec, (hb.2.1 c).2, (ha.2.1 c).2]
    · rw [← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]
  · intro a ha
    have hu := isUnit_of_uh ha.1
    have fix : ∀ v, a *ᵥ v = v → a⁻¹ *ᵥ v = v := by
      intro v hv
      calc a⁻¹ *ᵥ v = a⁻¹ *ᵥ (a *ᵥ v) := by rw [hv]
        _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
    exact ⟨uh_inv ha.1, fun c => ⟨fix _ (ha.2.1 c).1, fix _ (ha.2.1 c).2⟩, fix _ ha.2.2⟩
  · have hv : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {g : Mx k r | g *ᵥ v = v} := fun v =>
      isClosed_eq (Continuous.matrix_mulVec continuous_id continuous_const) continuous_const
    have e : (UWset k r z : Set (Mx k r)) = UH (Hpk k r) ∩
        ((⋂ a : Fin r, ({g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g : Mx k r | g *ᵥ z = z}) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      exact Iff.rfl
    rw [e]
    exact uh_closed.inter ((isClosed_iInter fun a => (hv _).inter (hv _)).inter (hv z))

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
lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ (midx hq) (midx hj) := by
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
lemma Em_mul_out {X : Type*} (A : Matrix (Fin (k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (x : X) (hi : ¬ mid k r i) :
    (Em k r * A) i x = 0 := by
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
lemma mul_EmT_mid {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : mid k r j) :
    (A * (Em k r)ᵀ) x j = A x (midx hj) := by
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
lemma mul_EmT_out {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : ¬ mid k r j) :
    (A * (Em k r)ᵀ) x j = 0 := by
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
lemma sandwich (a b N : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (M : Mx k r)
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
    Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_one, EmT_conjT, Em_conjT, Matrix.mul_assoc]

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
Establish `h` using `congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))`. Rewrite `h` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, hpk_herm, Hb_conjT]`. Conclude with `h`.
-/
lemma EmT_Hpk : (Em k r)ᵀ * Hpk k r = Hb k * (Em k r)ᵀ := by
  have h := congrArg Matrix.conjTranspose (Hpk_Em (k := k) (r := r))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Em_conjT, hpk_herm, Hb_conjT] at h
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
Establish `h` using `emb_form (k := k) (r := r) 1`. Rewrite `h` using `[emb_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Conclude with `h`.
-/
lemma Hpk_eq : Hpk k r =
      Em k r * Hb k * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) * Hpk k r * (1 - Em k r * (Em k r)ᵀ) := by
  have h := emb_form (k := k) (r := r) 1
  rw [emb_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one] at h
  exact h

/- English proof (translation)
Establish `h2 : (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = (Em k r)ᵀ * (Em k r * b * (Em k r)ᵀ) * Em k r` using `by rw [h]`. Establish `e : ∀ c : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = c`. Introduce `c`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = c := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]`. Rewrite `h2` using `[e, e]`. Then use the resulting hypothesis.
-/
lemma sand_inj {a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : Em k r * a * (Em k r)ᵀ = Em k r * b * (Em k r)ᵀ) :
    a = b := by
  have h2 : (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = (Em k r)ᵀ * (Em k r * b * (Em k r)ᵀ) * Em k r := by rw [h]
  have e : ∀ c : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = c := by
    intro c
    calc (Em k r)ᵀ * (Em k r * c * (Em k r)ᵀ) * Em k r = ((Em k r)ᵀ * Em k r) * c * ((Em k r)ᵀ * Em k r) := by
          simp only [Matrix.mul_assoc]
      _ = c := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]
  rwa [e, e] at h2

/- English proof (translation)
Use `show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r ↔ _`. Rewrite using `[emb_form]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `sand_inj (add_right_cancel (h.trans (Hpk_eq (k := k) (r := r))))`.

Introduce `h`. Rewrite using `[h]`. Conclude with `Hpk_eq.symm`.
-/
lemma emb_mem (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r a ∈ UH (Hpk k r) ↔ aᴴ * Hb k * a = Hb k := by
  show (embWb k r a)ᴴ * Hpk k r * embWb k r a = Hpk k r ↔ _
  rw [emb_form]
  constructor
  · intro h
    exact sand_inj (add_right_cancel (h.trans (Hpk_eq (k := k) (r := r))))
  · intro h
    rw [h]
    exact Hpk_eq.symm

/- English proof (translation)
Rewrite using `[emb_eq, Matrix.mul_add, Matrix.add_mul, EmT_Q, Matrix.zero_mul, add_zero]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = a := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]`.
-/
lemma emb_linv (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (Em k r)ᵀ * embWb k r a * Em k r = a := by
  rw [emb_eq, Matrix.mul_add, Matrix.add_mul, EmT_Q, Matrix.zero_mul, add_zero]
  calc (Em k r)ᵀ * (Em k r * a * (Em k r)ᵀ) * Em k r = ((Em k r)ᵀ * Em k r) * a * ((Em k r)ᵀ * Em k r) := by
        simp only [Matrix.mul_assoc]
    _ = a := by rw [EmT_Em, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
lemma mulVec_bvec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (j l : Fin n) : (A *ᵥ bvec j) l = A l j := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Simplify using `[bvec, Pi.single_apply]`.
-/
lemma bvec_apply {n : ℕ} (j l : Fin n) : bvec j l = if l = j then 1 else 0 := by
  simp [bvec, Pi.single_apply]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[mulVec_bvec]`. Simplify using `only [Hpk, bvec, Pi.single_apply, eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | norm_num`.
-/
lemma hpk_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  funext i
  rw [mulVec_bvec]
  simp only [Hpk, bvec, Pi.single_apply, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | norm_num

/- English proof (translation)
Use function extensionality and compare the values at `i`. Rewrite using `[mulVec_bvec]`. Simplify using `only [Hpk, bvec, Pi.single_apply, eI, esI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega) | norm_num`.
-/
lemma hpk_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  funext i
  rw [mulVec_bvec]
  simp only [Hpk, bvec, Pi.single_apply, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega) | norm_num

/- English proof (translation)
Use `i.isLt` as an intermediate fact. Distinguish the cases in `h : i.val < r`. Conclude with `⟨⟨i.val, h⟩, Or.inl rfl⟩`. Use `⟨⟨2 * r + k - i.val, by omega⟩, Or.inr ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `only [esI]`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_mid_cases (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) : ∃ a : Fin r, i = eI k r a ∨ i = esI k r a := by
  have := i.isLt
  by_cases h : i.val < r
  · exact ⟨⟨i.val, h⟩, Or.inl rfl⟩
  · refine ⟨⟨2 * r + k - i.val, by omega⟩, Or.inr ?_⟩
    apply Fin.ext
    simp only [esI]
    omega

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `show ¬ (r ≤ a.val ∧ a.val ≤ r + k)`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_mid_e (a : Fin r) : ¬ mid k r (eI k r a) := by
  have := a.isLt
  show ¬ (r ≤ a.val ∧ a.val ≤ r + k)
  omega

/- English proof (translation)
Use `a.isLt` as an intermediate fact. Use `show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val ≤ r + k)`. Use linear arithmetic over natural numbers and integers.
-/
lemma not_mid_es (a : Fin r) : ¬ mid k r (esI k r a) := by
  have := a.isLt
  show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val ≤ r + k)
  omega

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Use `conv_lhs => rw [← hf]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']`.
-/
lemma fix_dual {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {f : Fin (2 * r + k + 1) → ℂ} (hf : g *ᵥ f = f) :
    gᴴ *ᵥ (Hpk k r *ᵥ f) = Hpk k r *ᵥ f := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  conv_lhs => rw [← hf]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

/- English proof (translation)
Take `⟨a, rfl | rfl⟩` from `not_mid_cases i hi`. Rewrite using `[← mulVec_bvec g (eI k r a) l, (hg.2 a).1, bvec_apply]`. Rewrite using `[← mulVec_bvec g (esI k r a) l, (hg.2 a).2, bvec_apply]`.
-/
lemma uwb_col {g : Mx k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g l i = if l = i then 1 else 0 := by
  obtain ⟨a, rfl | rfl⟩ := not_mid_cases i hi
  · rw [← mulVec_bvec g (eI k r a) l, (hg.2 a).1, bvec_apply]
  · rw [← mulVec_bvec g (esI k r a) l, (hg.2 a).2, bvec_apply]

/- English proof (translation)
Establish `key : ∀ j : Fin (2 * r + k + 1), gᴴ *ᵥ bvec j = bvec j → g j l = if j = l then 1 else 0`. Introduce `j hj`. Establish `h` using `congrFun hj l`. Rewrite `h` using `[mulVec_bvec, bvec_apply, Matrix.conjTranspose_apply]`. Establish `h2` using `congrArg star h`.

Rewrite `h2` using `[star_star]`. Rewrite using `[h2]`. Distinguish the cases in `e : l = j`. Rewrite using `[if_pos e, if_pos e.symm, star_one]`. Rewrite using `[if_neg e, if_neg (fun e' => e e'.symm), star_zero]`.

Take `⟨a, rfl | rfl⟩` from `not_mid_cases i hi`. Apply `key` to reduce the goal to its premises. Use `fix_dual hg.1 (hg.2 a).2` as an intermediate fact. Rewrite `this` using `[hpk_es]`. Then use the resulting hypothesis. Apply `key` to reduce the goal to its premises.

Use `fix_dual hg.1 (hg.2 a).1` as an intermediate fact. Rewrite `this` using `[hpk_e]`. Then use the resulting hypothesis.
-/
lemma uwb_row {g : Mx k r} (hg : g ∈ UWb k r) (i l : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    g i l = if i = l then 1 else 0 := by
  have key : ∀ j : Fin (2 * r + k + 1), gᴴ *ᵥ bvec j = bvec j → g j l = if j = l then 1 else 0 := by
    intro j hj
    have h := congrFun hj l
    rw [mulVec_bvec, bvec_apply, Matrix.conjTranspose_apply] at h
    have h2 := congrArg star h
    rw [star_star] at h2
    rw [h2]
    by_cases e : l = j
    · rw [if_pos e, if_pos e.symm, star_one]
    · rw [if_neg e, if_neg (fun e' => e e'.symm), star_zero]
  obtain ⟨a, rfl | rfl⟩ := not_mid_cases i hi
  · apply key
    have := fix_dual hg.1 (hg.2 a).2
    rwa [hpk_es] at this
  · apply key
    have := fix_dual hg.1 (hg.2 a).1
    rwa [hpk_e] at this

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hj : mid k r j`. Distinguish the cases in `hi : mid k r i`. Rewrite using `[emb_mid _ i j hi hj, Matrix.submatrix_apply, wI_midx, wI_midx]`. Rewrite using `[emb_out_row _ i j hi, uwb_row hg i j hi]`.

Rewrite using `[emb_out_col _ i j hj, uwb_col hg j i hj]`.
-/
lemma uwb_eq_emb {g : Mx k r} (hg : g ∈ UWb k r) : g = embWb k r (g.submatrix (wI k r) (wI k r)) := by
  ext i j
  by_cases hj : mid k r j
  · by_cases hi : mid k r i
    · rw [emb_mid _ i j hi hj, Matrix.submatrix_apply, wI_midx, wI_midx]
    · rw [emb_out_row _ i j hi, uwb_row hg i j hi]
  · rw [emb_out_col _ i j hj, uwb_col hg j i hj]

/- English proof (translation)
Use extensionality with `l`. Rewrite using `[mulVec_bvec, bvec_apply, emb_out_col _ l i hi]`.
-/
lemma emb_fix (a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1)) (hi : ¬ mid k r i) :
    embWb k r a *ᵥ bvec i = bvec i := by
  ext l
  rw [mulVec_bvec, bvec_apply, emb_out_col _ l i hi]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Establish `h` using `uwb_eq_emb hg`. Use `⟨_, ?_, h.symm⟩` and prove the remaining obligations. Rewrite using `[← emb_mem (r := r), ← h]`.

Conclude with `hg.1`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨(emb_mem a).mpr ha, fun b => ⟨emb_fix a _ (not_mid_e b), emb_fix a _ (not_mid_es b)⟩⟩`.
-/
lemma uwb_iff (g : Mx k r) : g ∈ UWb k r ↔ ∃ a, aᴴ * Hb k * a = Hb k ∧ embWb k r a = g := by
  constructor
  · intro hg
    have h := uwb_eq_emb hg
    refine ⟨_, ?_, h.symm⟩
    rw [← emb_mem (r := r), ← h]
    exact hg.1
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(emb_mem a).mpr ha, fun b => ⟨emb_fix a _ (not_mid_e b), emb_fix a _ (not_mid_es b)⟩⟩

/- English proof (translation)
Establish `: (fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) = fun x => (Em k r * Matrix.of x * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) : Mx k r)`. Use function extensionality and compare the values at `x`. Rewrite using `[emb_eq]`. Rewrite using `[this]`. Conclude with `(Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const).add continuous_const`.
-/
lemma emb_cont : Continuous fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r) := by
  have : (fun x : Fin (k + 1) → Fin (k + 1) → ℂ => (embWb k r (Matrix.of x) : Mt k r)) =
      fun x => (Em k r * Matrix.of x * (Em k r)ᵀ + (1 - Em k r * (Em k r)ᵀ) : Mx k r) := by
    funext x
    rw [emb_eq]
  rw [this]
  exact (Continuous.matrix_mul (Continuous.matrix_mul continuous_const continuous_id) continuous_const).add
    continuous_const

/- English proof (translation)
Unfold `Hb`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply, if_true]`. Establish `h : ∀ i : Fin k, (if i.castSucc = Fin.last k then (-1 : ℂ) else 1) = 1` using `fun i => if_neg (Fin.castSucc_lt_last i).ne`. Simplify using `only [h, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma hb_form (v w : Fin (k + 1) → ℂ) :
    star w ⬝ᵥ (Hb k *ᵥ v) =
      (∑ i : Fin k, star (w i.castSucc) * v i.castSucc) - star (w (Fin.last k)) * v (Fin.last k) := by
  unfold Hb
  simp only [dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_castSucc, Pi.star_apply, if_true]
  have h : ∀ i : Fin k, (if i.castSucc = Fin.last k then (-1 : ℂ) else 1) = 1 := fun i =>
    if_neg (Fin.castSucc_lt_last i).ne
  simp only [h, one_mul]
  ring

/- English proof (translation)
Use `set X := ∑ i : Fin k, ‖u i.castSucc‖ ^ 2 with hX`. Use `set Y := ∑ i : Fin k, ‖z i.castSucc‖ ^ 2 with hY`. Use `set A := ‖u (Fin.last k)‖ with hA`. Use `set B := ‖z (Fin.last k)‖ with hB`. Establish `hA0 : 0 ≤ A` using `norm_nonneg _`.

Establish `hB0 : 0 ≤ B` using `norm_nonneg _`. Establish `hY0 : 0 ≤ Y` using `Finset.sum_nonneg fun i _ => by positivity`. Establish `hX0 : 0 ≤ X` using `Finset.sum_nonneg fun i _ => by positivity`. Establish `hBpos : 0 < B`. Break down `hB0.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. Rewrite `hT` using `[← h]`. Evaluate the numerical expressions using `at hT`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hy : √Y < B` using `(Real.sqrt_lt' hBpos).mpr hT`.

Establish `hy0 : 0 ≤ √Y` using `Real.sqrt_nonneg _`. Establish `hx : √X ≤ 1 + A`. Rewrite using `[Real.sqrt_le_iff]`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.

Use the polynomial consequences of the given equalities and inequalities. Establish `hS : ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ √Y * √X`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_star]`.

Use `_ ≤ √Y * √X := Real.sum_mul_le_sqrt_mul_sqrt _ _ _`. Establish `hBA : B * A ≤ τ + √Y * √X`. Establish `e : B * A = ‖star (z (Fin.last k)) * u (Fin.last k)‖` using `by rw [norm_mul, norm_star]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ + ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ := norm_sub_le _ _`. Use `_ ≤ τ + √Y * √X := by linarith`. Establish `hd : 0 < B - √Y` using `by linarith`.

Establish `hAle : A ≤ (τ + √Y) / (B - √Y)`. Rewrite using `[le_div_iff₀ hd]`. Establish `: √Y * √X ≤ √Y * (1 + A)` using `mul_le_mul_of_nonneg_left hx hy0`. Use the polynomial consequences of the given equalities and inequalities. Use `Fin.lastCases ?_ (fun j => ?_) i` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj : ‖u j.castSucc‖ ^ 2 ≤ X` using `Finset.single_le_sum (f := fun i : Fin k => ‖u i.castSucc‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)`. Establish `: ‖u j.castSucc‖ ≤ √X` using `Real.le_sqrt_of_sq_le hj`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma real_bound (u z : Fin (k + 1) → ℂ) (τ : ℝ)
    (h1 : (∑ i : Fin k, ‖u i.castSucc‖ ^ 2) - ‖u (Fin.last k)‖ ^ 2 ≤ 1)
    (h2 : ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ ≤ τ)
    (hT : (∑ i : Fin k, ‖z i.castSucc‖ ^ 2) < ‖z (Fin.last k)‖ ^ 2) (i : Fin (k + 1)) :
    ‖u i‖ ≤ 1 + (τ + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) / (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) := by
  set X := ∑ i : Fin k, ‖u i.castSucc‖ ^ 2 with hX
  set Y := ∑ i : Fin k, ‖z i.castSucc‖ ^ 2 with hY
  set A := ‖u (Fin.last k)‖ with hA
  set B := ‖z (Fin.last k)‖ with hB
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => by positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => by positivity
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hT; norm_num at hT; linarith
  have hy : √Y < B := (Real.sqrt_lt' hBpos).mpr hT
  have hy0 : 0 ≤ √Y := Real.sqrt_nonneg _
  have hx : √X ≤ 1 + A := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hS : ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ √Y * √X := by
    calc ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ ∑ i : Fin k, ‖star (z i.castSucc) * u i.castSucc‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin k, ‖z i.castSucc‖ * ‖u i.castSucc‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_star]
      _ ≤ √Y * √X := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hBA : B * A ≤ τ + √Y * √X := by
    have e : B * A = ‖star (z (Fin.last k)) * u (Fin.last k)‖ := by rw [norm_mul, norm_star]
    rw [e]
    calc ‖star (z (Fin.last k)) * u (Fin.last k)‖
        = ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) -
            ((∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k))‖ := by
          congr 1; ring
      _ ≤ ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ +
            ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ :=
          norm_sub_le _ _
      _ ≤ τ + √Y * √X := by linarith
  have hd : 0 < B - √Y := by linarith
  have hAle : A ≤ (τ + √Y) / (B - √Y) := by
    rw [le_div_iff₀ hd]
    have : √Y * √X ≤ √Y * (1 + A) := mul_le_mul_of_nonneg_left hx hy0
    nlinarith
  refine Fin.lastCases ?_ (fun j => ?_) i
  · linarith
  · have hj : ‖u j.castSucc‖ ^ 2 ≤ X :=
      Finset.single_le_sum (f := fun i : Fin k => ‖u i.castSucc‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)
    have : ‖u j.castSucc‖ ≤ √X := Real.le_sqrt_of_sq_le hj
    linarith

/- English proof (translation)
Rewrite using `[Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]`.
-/
lemma normsq_eq (x : ℂ) : star x * x = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Rewrite using `[hb_form]`. Simplify using `only [normsq_eq]`. Rewrite using `[← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]`.
-/
lemma hb_self_re (v : Fin (k + 1) → ℂ) :
    (star v ⬝ᵥ (Hb k *ᵥ v)).re = (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) - ‖v (Fin.last k)‖ ^ 2 := by
  rw [hb_form]
  simp only [normsq_eq]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.ofReal_re]

/- English proof (translation)
Rewrite `hT` using `[hb_self_re]`. Use `⟨1 + ((∑ j, ‖z j‖) + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) / (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)), fun μ hμ hz i j => ?_⟩` and prove the remaining obligations. Establish `hu : ∀ l, (μ *ᵥ Pi.single j 1) l = μ l j` using `fun l => by`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hHb : ∀ l, (Hb k *ᵥ Pi.single j 1) l = Hb k l j` using `fun l => by`.

Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `key : ∀ w : Fin (k + 1) → ℂ, star (μ *ᵥ w) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1)) = star w ⬝ᵥ (Hb k *ᵥ Pi.single j 1)`. Introduce `w`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hμ]`. Establish `hHbn : ∀ l, ‖Hb k l j‖ ≤ 1`.

Introduce `l`. Unfold `Hb`. Rewrite using `[Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `a1` using `key (Pi.single j 1)`.

Establish `a2` using `key z`. Rewrite `a2` using `[hz]`. Establish `b1 : (star (μ *ᵥ Pi.single j 1) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))).re ≤ 1`. Rewrite using `[a1]`. Establish `: star (Pi.single j 1 : Fin (k + 1) → ℂ) ⬝ᵥ (Hb k *ᵥ Pi.single j 1) = Hb k j j`.

Rewrite using `[← hHb j]`. Simplify using `[dotProduct, Pi.single_apply]`. Rewrite using `[this]`. Conclude with `(Complex.re_le_norm _).trans (hHbn j)`. Rewrite `b1` using `[hb_self_re]`.

Establish `b2 : ‖star z ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))‖ ≤ ∑ j, ‖z j‖`. Rewrite using `[a2, dotProduct]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[hHb, norm_mul, Pi.star_apply, norm_star]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hHbn l)`.

Rewrite `b2` using `[hb_form]`. Use `real_bound (μ *ᵥ Pi.single j 1) z _ b1 b2 (by linarith) i` as an intermediate fact. Rewrite `this` using `[hu]`. Then use the resulting hypothesis.
-/
lemma col_bound (z : Fin (k + 1) → ℂ) (hT : (star z ⬝ᵥ (Hb k *ᵥ z)).re < 0) :
    ∃ R : ℝ, ∀ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, μᴴ * Hb k * μ = Hb k → μ *ᵥ z = z → ∀ i j, ‖μ i j‖ ≤ R := by
  rw [hb_self_re] at hT
  refine ⟨1 + ((∑ j, ‖z j‖) + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) /
    (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)), fun μ hμ hz i j => ?_⟩
  have hu : ∀ l, (μ *ᵥ Pi.single j 1) l = μ l j := fun l => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hHb : ∀ l, (Hb k *ᵥ Pi.single j 1) l = Hb k l j := fun l => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have key : ∀ w : Fin (k + 1) → ℂ, star (μ *ᵥ w) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1)) = star w ⬝ᵥ (Hb k *ᵥ Pi.single j 1) := by
    intro w
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hμ]
  have hHbn : ∀ l, ‖Hb k l j‖ ≤ 1 := by
    intro l
    unfold Hb
    rw [Matrix.diagonal_apply]
    split_ifs <;> simp
  have a1 := key (Pi.single j 1)
  have a2 := key z
  rw [hz] at a2
  have b1 : (star (μ *ᵥ Pi.single j 1) ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))).re ≤ 1 := by
    rw [a1]
    have : star (Pi.single j 1 : Fin (k + 1) → ℂ) ⬝ᵥ (Hb k *ᵥ Pi.single j 1) = Hb k j j := by
      rw [← hHb j]
      simp [dotProduct, Pi.single_apply]
    rw [this]
    exact (Complex.re_le_norm _).trans (hHbn j)
  rw [hb_self_re] at b1
  have b2 : ‖star z ⬝ᵥ (Hb k *ᵥ (μ *ᵥ Pi.single j 1))‖ ≤ ∑ j, ‖z j‖ := by
    rw [a2, dotProduct]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [hHb, norm_mul, Pi.star_apply, norm_star]
    exact mul_le_of_le_one_right (norm_nonneg _) (hHbn l)
  rw [hb_form] at b2
  have := real_bound (μ *ᵥ Pi.single j 1) z _ b1 b2 (by linarith) i
  rwa [hu] at this

/- English proof (translation)
Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (wI k r m)]`. Rewrite using `[Matrix.transpose_apply, Em, if_pos rfl, one_mul]`. Introduce `b _ hb`. Rewrite using `[Matrix.transpose_apply, Em, if_neg hb, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma EmT_mulVec (z : Fin (2 * r + k + 1) → ℂ) (m : Fin (k + 1)) : ((Em k r)ᵀ *ᵥ z) m = z (wI k r m) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (wI k r m)]
  · rw [Matrix.transpose_apply, Em, if_pos rfl, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `i`. Distinguish the cases in `hi : mid k r i`. Rewrite using `[Matrix.mulVec, dotProduct, Finset.sum_eq_single (midx hi)]`. Rewrite using `[Em, if_pos (wI_midx hi).symm, one_mul, EmT_mulVec, wI_midx]`. Introduce `b _ hb`.

Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`. Apply `hb` to reduce the goal to its premises. Apply `wI_inj (r := r)` to reduce the goal to its premises. Rewrite using `[wI_midx hi, h]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hz i (by omega)]`. Rewrite using `[Matrix.mulVec, dotProduct]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `b _`. Rewrite using `[Em, if_neg, zero_mul]`. Introduce `h`. Conclude with `hi (h ▸ mid_wI b)`.
-/
lemma Em_EmT_mulVec (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) : Em k r *ᵥ ((Em k r)ᵀ *ᵥ z) = z := by
  ext i
  by_cases hi : mid k r i
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (midx hi)]
    · rw [Em, if_pos (wI_midx hi).symm, one_mul, EmT_mulVec, wI_midx]
    · intro b _ hb
      rw [Em, if_neg, zero_mul]
      intro h
      apply hb
      apply wI_inj (r := r)
      rw [wI_midx hi, h]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [hz i (by omega)]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro b _
    rw [Em, if_neg, zero_mul]
    intro h
    exact hi (h ▸ mid_wI b)

/- English proof (translation)
Establish `key : ∀ w : Fin (k + 1) → ℂ, herm (Hpk k r) (Em k r *ᵥ w) (Em k r *ᵥ w) = star w ⬝ᵥ (Hb k *ᵥ w)`. Introduce `w`. Unfold `herm`. Rewrite using `[Matrix.mulVec_mulVec, Hpk_Em, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Em_conjT, EmT_Em, Matrix.one_mulVec]`. Rewrite using `[← key, Em_EmT_mulVec z hz]`.
-/
lemma herm_wb (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) z z = star ((Em k r)ᵀ *ᵥ z) ⬝ᵥ (Hb k *ᵥ ((Em k r)ᵀ *ᵥ z)) := by
  have key : ∀ w : Fin (k + 1) → ℂ, herm (Hpk k r) (Em k r *ᵥ w) (Em k r *ᵥ w) = star w ⬝ᵥ (Hb k *ᵥ w) := by
    intro w
    unfold herm
    rw [Matrix.mulVec_mulVec, Hpk_Em, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Em_conjT, EmT_Em, Matrix.one_mulVec]
  rw [← key, Em_EmT_mulVec z hz]

/- English proof (translation)
Use `set zb := (Em k r)ᵀ *ᵥ z with hzb`. Establish `hT' : (star zb ⬝ᵥ (Hb k *ᵥ zb)).re < 0`. Rewrite using `[hzb, ← herm_wb z hz]`. Unfold `Tz at hT`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨R, hR⟩` from `col_bound zb hT'`. Establish `hK0 : IsCompact (Set.pi Set.univ fun _ : Fin (k + 1) => Set.pi Set.univ fun _ : Fin (k + 1) => Metric.closedBall (0 : ℂ) R)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Establish `hK` using `hK0.image (emb_cont (k := k) (r := r))`. Use `IsCompact.of_isClosed_subset hK (uw_clsub z).closed ?_` and prove the remaining obligations. Introduce `g hg`.

Take `⟨a, ha, hag⟩` from `(uwb_iff g).mp ⟨hg.1, hg.2.1⟩`. Establish `hfix : a *ᵥ zb = zb`. Establish `e : a = (Em k r)ᵀ * g * Em k r` using `by rw [← hag, emb_linv]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzb, Em_EmT_mulVec z hz, hg.2.2]`. Use `⟨a, ?_, hag⟩` and prove the remaining obligations.

Introduce `i _ j _`. Rewrite using `[mem_closedBall_zero_iff]`. Conclude with `hR a ha hfix i j`.
-/
theorem compactW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    IsCompact (UWset k r z : Set (Mx k r)) := by
  set zb := (Em k r)ᵀ *ᵥ z with hzb
  have hT' : (star zb ⬝ᵥ (Hb k *ᵥ zb)).re < 0 := by
    rw [hzb, ← herm_wb z hz]
    unfold Tz at hT
    linarith
  obtain ⟨R, hR⟩ := col_bound zb hT'
  have hK0 : IsCompact (Set.pi Set.univ fun _ : Fin (k + 1) => Set.pi Set.univ fun _ : Fin (k + 1) =>
      Metric.closedBall (0 : ℂ) R) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK := hK0.image (emb_cont (k := k) (r := r))
  refine IsCompact.of_isClosed_subset hK (uw_clsub z).closed ?_
  intro g hg
  obtain ⟨a, ha, hag⟩ := (uwb_iff g).mp ⟨hg.1, hg.2.1⟩
  have hfix : a *ᵥ zb = zb := by
    have e : a = (Em k r)ᵀ * g * Em k r := by rw [← hag, emb_linv]
    rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hzb, Em_EmT_mulVec z hz, hg.2.2]
  refine ⟨a, ?_, hag⟩
  intro i _ j _
  rw [mem_closedBall_zero_iff]
  exact hR a ha hfix i j

end WlocSk.HM
