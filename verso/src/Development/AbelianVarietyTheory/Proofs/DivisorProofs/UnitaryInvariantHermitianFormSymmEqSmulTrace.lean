import Mathlib

open Matrix

namespace GlobalTheory
namespace SymSqForm

variable {n : ℕ}

def Q (x y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := vecMulVec x y + vecMulVec y x

def e (i : Fin n) : Fin n → ℂ := Pi.single i 1

/- English proof (translation)
Unfold `Q`. Rewrite using `[add_comm]`.
-/
lemma Q_comm (x y : Fin n → ℂ) : Q x y = Q y x := by unfold Q; rw [add_comm]

/- English proof (translation)
Unfold `Q IsSymm`. Rewrite using `[transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]`.
-/
lemma Q_isSymm (x y : Fin n → ℂ) : (Q x y).IsSymm := by
  unfold Q IsSymm; rw [transpose_add, transpose_vecMulVec, transpose_vecMulVec, add_comm]

/- English proof (translation)
Unfold `Q`. Rewrite using `[add_vecMulVec, vecMulVec_add]`. Normalize the expressions using the abelian group laws.
-/
lemma Q_add_left (x x' y : Fin n → ℂ) : Q (x + x') y = Q x y + Q x' y := by
  unfold Q; rw [add_vecMulVec, vecMulVec_add]; abel

/- English proof (translation)
Unfold `Q`. Rewrite using `[smul_vecMulVec, vecMulVec_smul, smul_add]`.
-/
lemma Q_smul_left (a : ℂ) (x y : Fin n → ℂ) : Q (a • x) y = a • Q x y := by
  unfold Q; rw [smul_vecMulVec, vecMulVec_smul, smul_add]

/- English proof (translation)
Rewrite using `[Q_comm, Q_add_left, Q_comm y, Q_comm y']`.
-/
lemma Q_add_right (x y y' : Fin n → ℂ) : Q x (y + y') = Q x y + Q x y' := by
  rw [Q_comm, Q_add_left, Q_comm y, Q_comm y']

/- English proof (translation)
Rewrite using `[Q_comm, Q_smul_left, Q_comm]`.
-/
lemma Q_smul_right (a : ℂ) (x y : Fin n → ℂ) : Q x (a • y) = a • Q x y := by
  rw [Q_comm, Q_smul_left, Q_comm]

/- English proof (translation)
Unfold `Q`. Rewrite using `[mul_add, add_mul, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul, vecMulVec_mul, vecMul_transpose, vecMul_transpose]`.
-/
lemma conj_Q (k : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    k * Q x y * kᵀ = Q (k *ᵥ x) (k *ᵥ y) := by
  unfold Q
  rw [mul_add, add_mul, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul, vecMulVec_mul,
    vecMul_transpose, vecMul_transpose]

def Good (f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  (∀ (a : ℂ) Z Z' W, f (a • Z + Z') W = a * f Z W + f Z' W) ∧ (∀ Z W, f W Z = star (f Z W)) ∧
    (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) Z W, Z.IsSymm → W.IsSymm →
      f (k.1 * Z * k.1ᵀ) (k.1 * W * k.1ᵀ) = f Z W)

variable {f : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ}

/- English proof (translation)
Simplify using `using hf.1 1 Z Z' W`.
-/
lemma Good.add_left (hf : Good f) (Z Z' W) : f (Z + Z') W = f Z W + f Z' W := by
  simpa using hf.1 1 Z Z' W

/- English proof (translation)
Use `hf.add_left 0 0 W` as an intermediate fact. Simplify using `using this`.
-/
lemma Good.zero_left (hf : Good f) (W) : f 0 W = 0 := by
  have := hf.add_left 0 0 W
  simpa using this

/- English proof (translation)
Simplify `hf.1 a Z 0 W` using `[hf.zero_left]`.
-/
lemma Good.smul_left (hf : Good f) (a : ℂ) (Z W) : f (a • Z) W = a * f Z W := by
  simpa [hf.zero_left] using hf.1 a Z 0 W

/- English proof (translation)
Rewrite using `[hf.2.1 (a • W) Z, hf.smul_left, star_mul, ← hf.2.1 W Z, mul_comm]`.
-/
lemma Good.smul_right (hf : Good f) (a : ℂ) (Z W) : f Z (a • W) = star a * f Z W := by
  rw [hf.2.1 (a • W) Z, hf.smul_left, star_mul, ← hf.2.1 W Z, mul_comm]

/- English proof (translation)
Rewrite using `[hf.2.1 (W + W') Z, hf.add_left, star_add, ← hf.2.1, ← hf.2.1]`.
-/
lemma Good.add_right (hf : Good f) (Z W W') : f Z (W + W') = f Z W + f Z W' := by
  rw [hf.2.1 (W + W') Z, hf.add_left, star_add, ← hf.2.1, ← hf.2.1]

/- English proof (translation)
Rewrite using `[← conj_Q, ← conj_Q]`. Conclude with `hf.2.2 k _ _ (Q_isSymm _ _) (Q_isSymm _ _)`.
-/
lemma Good.inv_Q (hf : Good f) (k : Matrix.unitaryGroup (Fin n) ℂ) (x y z w : Fin n → ℂ) :
    f (Q (k.1 *ᵥ x) (k.1 *ᵥ y)) (Q (k.1 *ᵥ z) (k.1 *ᵥ w)) = f (Q x y) (Q z w) := by
  rw [← conj_Q, ← conj_Q]; exact hf.2.2 k _ _ (Q_isSymm _ _) (Q_isSymm _ _)

/- English proof (translation)
Rewrite using `[mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]`. Use `diagonal_one with a` and compare the differences between its conclusion and the goal. Conclude with `hd a`.
-/
lemma diag_mem (d : Fin n → ℂ) (hd : ∀ a, star (d a) * d a = 1) :
    diagonal d ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
  convert diagonal_one with a
  exact hd a

/- English proof (translation)
Use extensionality with `a`. Simplify using `[e, Pi.single_apply]`.
-/
lemma diag_e (d : Fin n → ℂ) (i : Fin n) : diagonal d *ᵥ e i = d i • e i := by
  ext a; simp [e, Pi.single_apply]

/- English proof (translation)
Use `hf.inv_Q ⟨diagonal d, diag_mem d hd⟩ (e i) (e j) (e k) (e l)` as an intermediate fact. Simplify using `only [diag_e, Q_smul_left, Q_smul_right, hf.smul_left, hf.smul_right, star_mul] at this`. Rewrite using `[star_mul]`. Conclude with `this.symm.trans (by ring)`.
-/
lemma Good.diag_factor (hf : Good f) (d : Fin n → ℂ) (hd : ∀ a, star (d a) * d a = 1)
    (i j k l : Fin n) :
    f (Q (e i) (e j)) (Q (e k) (e l)) =
      (d i * d j) * star (d k * d l) * f (Q (e i) (e j)) (Q (e k) (e l)) := by
  have := hf.inv_Q ⟨diagonal d, diag_mem d hd⟩ (e i) (e j) (e k) (e l)
  simp only [diag_e, Q_smul_left, Q_smul_right, hf.smul_left, hf.smul_right, star_mul] at this
  rw [star_mul]
  exact this.symm.trans (by ring)

/- English proof (translation)
Assume the negation of the conclusion as `hF`. Establish `cnt : ∀ m : Fin n, (if i = m then 1 else 0) + (if j = m then 1 else 0) = (if k = m then 1 else 0) + (if l = m then (1 : ℕ) else 0)`. Introduce `m`. Apply the tactic sequence `have h0 := hf.diag_factor (fun a => if a = m then Complex.I else 1) (by intro a; split_ifs <;> simp [Complex.star_def]) i j k l`. Establish `h1 : (fun a => if a = m then Complex.I else 1) i * (fun a => if a = m then Complex.I else 1) j * star ((fun a => if a = m then Complex.I else 1) k * (fun a => if a = m then Complex.I else 1) l) = 1`.

Use `h0.symm.trans (one_mul _).symm` as an intermediate fact. Conclude with `mul_right_cancel₀ hF this`. Simplify using `only at h1`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> simp [Complex.ext_iff, Complex.star_def] at h1 ⊢ <;> norm_num at h1`. Establish `hi` using `cnt i`.

Establish `hj` using `cnt j`. Simplify using `only [if_true] at hi hj`. Apply the tactic sequence `split_ifs at hi hj <;> first | omega | (apply h; subst_vars; tauto)`.
-/
lemma Good.vanish_off (hf : Good f) (i j k l : Fin n)
    (h : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) : f (Q (e i) (e j)) (Q (e k) (e l)) = 0 := by
  by_contra hF
  have cnt : ∀ m : Fin n, (if i = m then 1 else 0) + (if j = m then 1 else 0) =
      (if k = m then 1 else 0) + (if l = m then (1 : ℕ) else 0) := by
    intro m
    have h0 := hf.diag_factor (fun a => if a = m then Complex.I else 1)
      (by intro a; split_ifs <;> simp [Complex.star_def]) i j k l
    have h1 : (fun a => if a = m then Complex.I else 1) i * (fun a => if a = m then Complex.I else 1) j *
        star ((fun a => if a = m then Complex.I else 1) k * (fun a => if a = m then Complex.I else 1) l)
        = 1 := by
      have := h0.symm.trans (one_mul _).symm
      exact mul_right_cancel₀ hF this
    dsimp only at h1
    split_ifs at h1 ⊢ <;> simp [Complex.ext_iff, Complex.star_def] at h1 ⊢ <;> norm_num at h1
  have hi := cnt i
  have hj := cnt j
  simp only [if_true] at hi hj
  split_ifs at hi hj <;> first | omega | (apply h; subst_vars; tauto)

/- English proof (translation)
Establish `hs : star (1 - c • vecMulVec u u) = 1 - c • vecMulVec u u`. Rewrite using `[star_sub, star_one, star_smul, hc, star_eq_conjTranspose, conjTranspose_vecMulVec, hu]`. Rewrite using `[mem_unitaryGroup_iff, hs]`. Simplify using `only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]`. Rewrite using `[h, two_mul, add_smul]`.

Normalize the expressions using the abelian group laws.
-/
lemma refl_mem (u : Fin n → ℂ) (c : ℂ) (hu : star u = u) (hc : star c = c)
    (h : c * (c * (u ⬝ᵥ u)) = 2 * c) :
    (1 - c • vecMulVec u u) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hs : star (1 - c • vecMulVec u u) = 1 - c • vecMulVec u u := by
    rw [star_sub, star_one, star_smul, hc, star_eq_conjTranspose, conjTranspose_vecMulVec, hu]
  rw [mem_unitaryGroup_iff, hs]
  simp only [sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul,
    vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul]
  rw [h, two_mul, add_smul]
  abel

/- English proof (translation)
Use extensionality with `a`. Simplify using `only [sub_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Simplify using `[mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]`.
-/
lemma refl_apply (u x : Fin n → ℂ) (c : ℂ) :
    (1 - c • vecMulVec u u) *ᵥ x = x - (c * (u ⬝ᵥ x)) • u := by
  ext a
  simp only [sub_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  simp [mulVec, dotProduct, vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

/- English proof (translation)
Distinguish the cases in `hab : a = b`. Rewrite using `[hab]`. Use `set u : Fin n → ℂ := e a - e b with hu_def`. Establish `hu : star u = u`. Apply the tactic sequence `ext x; simp only [u, e, Pi.star_apply, Pi.sub_apply, Pi.single_apply]; split_ifs <;> simp`.

Establish `huu : u ⬝ᵥ u = 2`. Simplify using `[u, e, hab, Ne.symm hab]`. Evaluate the numerical expressions. Establish `hk` using `refl_mem u 1 hu (by simp) (by rw [huu]; ring)`. Establish `hka : (1 - (1:ℂ) • vecMulVec u u) *ᵥ e a = e b`.

Rewrite using `[refl_apply]`. Establish `: u ⬝ᵥ e a = 1` using `by simp [u, e, hab, Ne.symm hab]`. Rewrite using `[this, hu_def]`. Simplify using the standard rewrite rules. Use `hf.inv_Q ⟨_, hk⟩ (e a) (e a) (e a) (e a)` as an intermediate fact.

Simplify using `only [hka] at this`. Conclude with `this.symm`.
-/
lemma Good.diag_eq (hf : Good f) (a b : Fin n) :
    f (Q (e a) (e a)) (Q (e a) (e a)) = f (Q (e b) (e b)) (Q (e b) (e b)) := by
  by_cases hab : a = b
  · rw [hab]
  set u : Fin n → ℂ := e a - e b with hu_def
  have hu : star u = u := by
    ext x; simp only [u, e, Pi.star_apply, Pi.sub_apply, Pi.single_apply]; split_ifs <;> simp
  have huu : u ⬝ᵥ u = 2 := by
    simp [u, e, hab, Ne.symm hab]; norm_num
  have hk := refl_mem u 1 hu (by simp) (by rw [huu]; ring)
  have hka : (1 - (1:ℂ) • vecMulVec u u) *ᵥ e a = e b := by
    rw [refl_apply]
    have : u ⬝ᵥ e a = 1 := by simp [u, e, hab, Ne.symm hab]
    rw [this, hu_def]; simp
  have := hf.inv_Q ⟨_, hk⟩ (e a) (e a) (e a) (e a)
  simp only [hka] at this
  exact this.symm

/- English proof (translation)
Use `set u : Fin n → ℂ := e i + (2:ℂ) • e j with hu_def`. Establish `hu : star u = u`. Use extensionality with `x`. Simplify using `only [u, e, Pi.star_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `huu : u ⬝ᵥ u = 5`. Simplify using `[u, e, hij, Ne.symm hij]`. Evaluate the numerical expressions. Establish `hk` using `refl_mem u (2/5) hu (by simp) (by rw [huu]; ring)`. Establish `hki : (1 - (2/5:ℂ) • vecMulVec u u) *ᵥ e i = (3/5 : ℂ) • e i + (-4/5 : ℂ) • e j`.

Rewrite using `[refl_apply]`. Establish `: u ⬝ᵥ e i = 1` using `by simp [u, e, hij, Ne.symm hij]`. Rewrite using `[this, hu_def]`. Use `module`. Establish `hQ : Q ((3/5:ℂ) • e i + (-4/5:ℂ) • e j) ((3/5:ℂ) • e i + (-4/5:ℂ) • e j) = (9/25:ℂ) • Q (e i) (e i) + (-24/25:ℂ) • Q (e i) (e j) + (16/25:ℂ) • Q (e j) (e j)`.

Rewrite using `[Q_add_left, Q_add_right, Q_add_right, Q_smul_left, Q_smul_left, Q_smul_left, Q_smul_left, Q_smul_right, Q_smul_right, Q_smul_right, Q_smul_right, Q_comm (e j) (e i)]`. Use `module`. Use `hf.inv_Q ⟨_, hk⟩ (e i) (e i) (e i) (e i)` as an intermediate fact. Simplify using `only [hki, hQ, hf.add_left, hf.add_right, hf.smul_left, hf.smul_right, h0, hf.vanish_off i i i j (by simp [hij, Ne.symm hij]), hf.vanish_off i i j j (by simp [hij, Ne.symm hij]), hf.vanish_off i j i i (by simp [hij, Ne.symm hij]), hf.vanish_off i j j j (by simp [hij, Ne.symm hij] …`. Evaluate the numerical expressions using `at this`.

Conclude with `this`.
-/
lemma Good.off_diag (hf : Good f) (h0 : ∀ a, f (Q (e a) (e a)) (Q (e a) (e a)) = 0)
    (i j : Fin n) (hij : i ≠ j) : f (Q (e i) (e j)) (Q (e i) (e j)) = 0 := by
  set u : Fin n → ℂ := e i + (2:ℂ) • e j with hu_def
  have hu : star u = u := by
    ext x; simp only [u, e, Pi.star_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
    split_ifs <;> simp
  have huu : u ⬝ᵥ u = 5 := by
    simp [u, e, hij, Ne.symm hij]; norm_num
  have hk := refl_mem u (2/5) hu (by simp) (by rw [huu]; ring)
  have hki : (1 - (2/5:ℂ) • vecMulVec u u) *ᵥ e i = (3/5 : ℂ) • e i + (-4/5 : ℂ) • e j := by
    rw [refl_apply]
    have : u ⬝ᵥ e i = 1 := by simp [u, e, hij, Ne.symm hij]
    rw [this, hu_def]; module
  have hQ : Q ((3/5:ℂ) • e i + (-4/5:ℂ) • e j) ((3/5:ℂ) • e i + (-4/5:ℂ) • e j) =
      (9/25:ℂ) • Q (e i) (e i) + (-24/25:ℂ) • Q (e i) (e j) + (16/25:ℂ) • Q (e j) (e j) := by
    rw [Q_add_left, Q_add_right, Q_add_right, Q_smul_left, Q_smul_left, Q_smul_left, Q_smul_left,
      Q_smul_right, Q_smul_right, Q_smul_right, Q_smul_right, Q_comm (e j) (e i)]
    module
  have := hf.inv_Q ⟨_, hk⟩ (e i) (e i) (e i) (e i)
  simp only [hki, hQ, hf.add_left, hf.add_right, hf.smul_left, hf.smul_right, h0,
    hf.vanish_off i i i j (by simp [hij, Ne.symm hij]), hf.vanish_off i i j j (by simp [hij, Ne.symm hij]),
    hf.vanish_off i j i i (by simp [hij, Ne.symm hij]), hf.vanish_off i j j j (by simp [hij, Ne.symm hij]),
    hf.vanish_off j j i i (by simp [hij, Ne.symm hij]), hf.vanish_off j j i j (by simp [hij, Ne.symm hij])]
    at this
  norm_num at this
  exact this

/- English proof (translation)
Establish `hd : f (Q (e i) (e j)) (Q (e i) (e j)) = 0`. Distinguish the cases in `hij : i = j`. Rewrite using `[← hij]`. Conclude with `h0 i`. Conclude with `hf.off_diag h0 i j hij`.

Distinguish the cases in `h : (i = k ∧ j = l) ∨ (i = l ∧ j = k)`. Break down `h with ⟨hk, hl⟩ | ⟨hk, hl⟩` into its components or cases. Rewrite using `[← hk, ← hl]`. Conclude with `hd`. Rewrite using `[← hk, ← hl, Q_comm (e j) (e i)]`.

Conclude with `hd`. Conclude with `hf.vanish_off i j k l h`.
-/
lemma Good.vanish_basis (hf : Good f) (h0 : ∀ a, f (Q (e a) (e a)) (Q (e a) (e a)) = 0)
    (i j k l : Fin n) : f (Q (e i) (e j)) (Q (e k) (e l)) = 0 := by
  have hd : f (Q (e i) (e j)) (Q (e i) (e j)) = 0 := by
    by_cases hij : i = j
    · rw [← hij]; exact h0 i
    · exact hf.off_diag h0 i j hij
  by_cases h : (i = k ∧ j = l) ∨ (i = l ∧ j = k)
  · rcases h with ⟨hk, hl⟩ | ⟨hk, hl⟩
    · rw [← hk, ← hl]; exact hd
    · rw [← hk, ← hl, Q_comm (e j) (e i)]; exact hd
  · exact hf.vanish_off i j k l h

/- English proof (translation)
Use extensionality with `a b`. Establish `hs : Z b a = Z a b` using `by simpa using congrFun (congrFun hZ a) b`. Simplify using `[Matrix.sum_apply, Q, vecMulVec_apply, e, Pi.single_apply, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, hs]`.
-/
lemma sym_expand (Z : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.IsSymm) :
    Z = ∑ i, ∑ j, (Z i j / 2) • Q (e i) (e j) := by
  ext a b
  have hs : Z b a = Z a b := by simpa using congrFun (congrFun hZ a) b
  simp [Matrix.sum_apply, Q, vecMulVec_apply, e, Pi.single_apply, Finset.sum_add_distrib,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, hs]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hf.zero_left]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf.add_left, ih]`.
-/
lemma Good.sum_left {ι : Type} (hf : Good f) (s : Finset ι) (A : ι → Matrix (Fin n) (Fin n) ℂ) (W) :
    f (∑ x ∈ s, A x) W = ∑ x ∈ s, f (A x) W := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hf.zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf.add_left, ih]

/- English proof (translation)
Establish `key : ∀ i j, f (Q (e i) (e j)) W = 0`. Introduce `i j`. Rewrite using `[hf.2.1 W (Q _ _), sym_expand W hW]`. Simplify using `[hf.sum_left, hf.smul_left, hf.vanish_basis h0]`. Rewrite using `[sym_expand Z hZ]`.

Simplify using `[hf.sum_left, hf.smul_left, key]`.
-/
lemma Good.vanish (hf : Good f) (h0 : ∀ a, f (Q (e a) (e a)) (Q (e a) (e a)) = 0)
    (Z W : Matrix (Fin n) (Fin n) ℂ) (hZ : Z.IsSymm) (hW : W.IsSymm) : f Z W = 0 := by
  have key : ∀ i j, f (Q (e i) (e j)) W = 0 := by
    intro i j
    rw [hf.2.1 W (Q _ _), sym_expand W hW]
    simp [hf.sum_left, hf.smul_left, hf.vanish_basis h0]
  rw [sym_expand Z hZ]
  simp [hf.sum_left, hf.smul_left, key]

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a Z Z' W`. Simplify using `[add_mul, Matrix.smul_mul, trace_add, trace_smul]`. Introduce `Z W`. Rewrite using `[← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]`.

Introduce `k Z W _ _`. Establish `hk : k.1ᴴ * k.1 = 1`. Use `k.2` as an intermediate fact. Rewrite `this` using `[mem_unitaryGroup_iff', star_eq_conjTranspose]`. Conclude with `this`.

Establish `hct : (k.1ᵀ)ᴴ = (k.1ᴴ)ᵀ` using `by ext; simp`. Establish `h1 : k.1ᵀ * (k.1ᵀ)ᴴ = 1`. Rewrite using `[hct, ← transpose_mul, hk, transpose_one]`. Use `show ((k.1 * Z * k.1ᵀ) * (k.1 * W * k.1ᵀ)ᴴ).trace = (Z * Wᴴ).trace`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (k.1ᵀ), h1, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, hk, Matrix.mul_one]`.
-/
lemma good_trace : Good (n := n) (fun Z W => (Z * Wᴴ).trace) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a Z Z' W
    simp [add_mul, Matrix.smul_mul, trace_add, trace_smul]
  · intro Z W
    rw [← trace_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose]
  · intro k Z W _ _
    have hk : k.1ᴴ * k.1 = 1 := by
      have := k.2; rw [mem_unitaryGroup_iff', star_eq_conjTranspose] at this; exact this
    have hct : (k.1ᵀ)ᴴ = (k.1ᴴ)ᵀ := by ext; simp
    have h1 : k.1ᵀ * (k.1ᵀ)ᴴ = 1 := by
      rw [hct, ← transpose_mul, hk, transpose_one]
    show ((k.1 * Z * k.1ᵀ) * (k.1 * W * k.1ᵀ)ᴴ).trace = (Z * Wᴴ).trace
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (k.1ᵀ), h1, Matrix.one_mul, Matrix.trace_mul_comm, Matrix.mul_assoc,
      Matrix.mul_assoc, hk, Matrix.mul_one]

end SymSqForm

open SymSqForm in

/- English proof (translation)
Introduce `g h H1 H2 H3`. Establish `hf : Good h` using `⟨H1, H2, H3⟩`. Consider the cases of `g with`. Consider the case `zero`. Use `⟨0, fun Z W _ _ => ?_⟩` and prove the remaining obligations.

Establish `hZ : Z = 0` using `Subsingleton.elim _ _`. Rewrite using `[hZ, hf.zero_left]`. Simplify using the standard rewrite rules. Consider the case `succ m`. Establish `hs` using `good_trace (n := m + 1)`.

Use `set S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := Q (e 0) (e 0) with hS`. Use `set h0 := h S S with hh0`. Use `set s0 := (S * Sᴴ).trace with hs0`. Establish `h0r : star h0 = h0` using `(H2 S S).symm`. Establish `s0r : star s0 = s0` using `(hs.2.1 S S).symm`.

Establish `s0ne : s0 ≠ 0`. Rewrite using `[hs0, hS]`. Simplify using `[Q, e, Matrix.trace, Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, Fin.sum_univ_succ, Fin.succ_ne_zero]`. Establish `hg : Good (fun Z W => h Z W * s0 - (Z * Wᴴ).trace * h0)`. Use `⟨fun a Z Z' W => ?_, fun Z W => ?_, fun k Z W hZ hW => ?_⟩` and prove the remaining obligations.

Use `hs.1 a Z Z' W` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[H1, this]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [star_sub, star_mul', h0r, s0r]`.

Rewrite using `[H2 Z W, show (W * Zᴴ).trace = star ((Z * Wᴴ).trace) from hs.2.1 Z W]`. Use `hs.2.2 k Z W hZ hW` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[H3 k Z W hZ hW, this]`. Establish `hz : ∀ a, (fun Z W => h Z W * s0 - (Z * Wᴴ).trace * h0) (Q (e a) (e a)) (Q (e a) (e a)) = 0`.

Introduce `a`. Use `hg.diag_eq a 0` as an intermediate fact. Simplify using `only at this ⊢`. Rewrite using `[this, ← hS, ← hh0, ← hs0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hreal : (((h0 / s0).re : ℝ) : ℂ) = h0 / s0`. Apply `Complex.conj_eq_iff_re.mp` to reduce the goal to its premises. Rewrite using `[map_div₀]`. Conclude with `congrArg₂ (· / ·) h0r s0r`. Use `⟨(h0 / s0).re, fun Z W hZ hW => ?_⟩` and prove the remaining obligations.

Use `hg.vanish hz Z W hZ hW` as an intermediate fact. Rewrite using `[hreal]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `this`.
-/
theorem unitary_invariant_hermitian_form_symm_eq_smul_trace :
    ∀ (g : ℕ) (h : Matrix (Fin g) (Fin g) ℂ → Matrix (Fin g) (Fin g) ℂ → ℂ),
      (∀ (a : ℂ) Z Z' W, h (a • Z + Z') W = a * h Z W + h Z' W) →
      (∀ Z W, h W Z = star (h Z W)) →
      (∀ (k : Matrix.unitaryGroup (Fin g) ℂ) Z W, Z.IsSymm → W.IsSymm →
        h (k.1 * Z * k.1ᵀ) (k.1 * W * k.1ᵀ) = h Z W) →
      ∃ c : ℝ, ∀ Z W, Z.IsSymm → W.IsSymm → h Z W = c * (Z * Wᴴ).trace := by
  intro g h H1 H2 H3
  have hf : Good h := ⟨H1, H2, H3⟩
  cases g with
  | zero =>
    refine ⟨0, fun Z W _ _ => ?_⟩
    have hZ : Z = 0 := Subsingleton.elim _ _
    rw [hZ, hf.zero_left]; simp
  | succ m =>
    have hs := good_trace (n := m + 1)
    set S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := Q (e 0) (e 0) with hS
    set h0 := h S S with hh0
    set s0 := (S * Sᴴ).trace with hs0
    have h0r : star h0 = h0 := (H2 S S).symm
    have s0r : star s0 = s0 := (hs.2.1 S S).symm
    have s0ne : s0 ≠ 0 := by
      rw [hs0, hS]
      simp [Q, e, Matrix.trace, Matrix.mul_apply, vecMulVec_apply, Pi.single_apply, Fin.sum_univ_succ,
        Fin.succ_ne_zero]
    have hg : Good (fun Z W => h Z W * s0 - (Z * Wᴴ).trace * h0) := by
      refine ⟨fun a Z Z' W => ?_, fun Z W => ?_, fun k Z W hZ hW => ?_⟩
      · have := hs.1 a Z Z' W
        simp only at this ⊢
        rw [H1, this]; ring
      · simp only [star_sub, star_mul', h0r, s0r]
        rw [H2 Z W, show (W * Zᴴ).trace = star ((Z * Wᴴ).trace) from hs.2.1 Z W]
      · have := hs.2.2 k Z W hZ hW
        simp only at this ⊢
        rw [H3 k Z W hZ hW, this]
    have hz : ∀ a, (fun Z W => h Z W * s0 - (Z * Wᴴ).trace * h0) (Q (e a) (e a)) (Q (e a) (e a)) = 0 := by
      intro a
      have := hg.diag_eq a 0
      simp only at this ⊢
      rw [this, ← hS, ← hh0, ← hs0]
      ring
    have hreal : (((h0 / s0).re : ℝ) : ℂ) = h0 / s0 := by
      apply Complex.conj_eq_iff_re.mp
      rw [map_div₀]
      exact congrArg₂ (· / ·) h0r s0r
    refine ⟨(h0 / s0).re, fun Z W hZ hW => ?_⟩
    have := hg.vanish hz Z W hZ hW
    rw [hreal]
    field_simp
    linear_combination this

end GlobalTheory
