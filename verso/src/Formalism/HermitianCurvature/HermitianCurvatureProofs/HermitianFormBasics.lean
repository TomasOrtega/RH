import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth

open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.HermitianProjections

section proj

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def prj (H : Matrix n n ℂ) (V : Matrix n ι ℂ) : Matrix ι n ℂ := (Vᴴ * H * V)⁻¹ * Vᴴ * H

def rhoOf (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) : Matrix n n ℂ :=
  1 + V * (Φ - 1) * prj H V

/- English proof (translation)
Establish `h` using `Matrix.nonsing_inv_mul _ hΓ`. Establish `e : prj H V * V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H * V)`. Simplify using `only [prj, Matrix.mul_assoc]`. Rewrite using `[e, h]`.
-/
lemma prj_mul (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    prj H V * V = 1 := by
  have h := Matrix.nonsing_inv_mul _ hΓ
  have e : prj H V * V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H * V) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, h]

/- English proof (translation)
Establish `h` using `Matrix.mul_nonsing_inv _ hΓ`. Establish `e : (Vᴴ * H * V) * prj H V = ((Vᴴ * H * V) * (Vᴴ * H * V)⁻¹) * (Vᴴ * H)`. Simplify using `only [prj, Matrix.mul_assoc]`. Rewrite using `[e, h, Matrix.one_mul]`.
-/
lemma K_eq (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    Vᴴ * H = (Vᴴ * H * V) * prj H V := by
  have h := Matrix.mul_nonsing_inv _ hΓ
  have e : (Vᴴ * H * V) * prj H V = ((Vᴴ * H * V) * (Vᴴ * H * V)⁻¹) * (Vᴴ * H) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, h, Matrix.one_mul]

/- English proof (translation)
Establish `e : prj H V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H)`. Simplify using `only [prj, Matrix.mul_assoc]`. Rewrite using `[e, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]`.
-/
lemma prj_perp (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (x : n → ℂ) (hx : (Vᴴ * H) *ᵥ x = 0) :
    prj H V *ᵥ x = 0 := by
  have e : prj H V = (Vᴴ * H * V)⁻¹ * (Vᴴ * H) := by
    simp only [prj, Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

/- English proof (translation)
Establish `hK` using `K_eq H V hΓ`. Establish `e : (Vᴴ * H) *ᵥ (V *ᵥ (prj H V *ᵥ x)) = ((Vᴴ * H * V) * prj H V) *ᵥ x`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`. Rewrite using `[Matrix.mulVec_sub, e, ← hK, sub_self]`.
-/
lemma decomp (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) (x : n → ℂ) :
    (Vᴴ * H) *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = 0 := by
  have hK := K_eq H V hΓ
  have e : (Vᴴ * H) *ᵥ (V *ᵥ (prj H V *ᵥ x)) = ((Vᴴ * H * V) * prj H V) *ᵥ x := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [Matrix.mulVec_sub, e, ← hK, sub_self]

/- English proof (translation)
Simplify using `only [rhoOf]`. Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (V * (Φ - 1)), prj_mul H V hΓ, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one]`. Normalize the expressions using the abelian group laws.
-/
lemma rhoOf_mul (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det) :
    rhoOf H V Φ * V = V * Φ := by
  simp only [rhoOf]
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc (V * (Φ - 1)), prj_mul H V hΓ, Matrix.mul_one,
    Matrix.mul_sub, Matrix.mul_one]
  abel

/- English proof (translation)
Simplify using `only [rhoOf]`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, prj_perp H V x hx, Matrix.mulVec_zero, add_zero]`.
-/
lemma rhoOf_perp (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (x : n → ℂ)
    (hx : (Vᴴ * H) *ᵥ x = 0) : rhoOf H V Φ *ᵥ x = x := by
  simp only [rhoOf]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, prj_perp H V x hx, Matrix.mulVec_zero,
    add_zero]

/- English proof (translation)
Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Simplify using `only [Matrix.toLin'_apply]`. Establish `hd` using `decomp H V hΓ x`. Establish `h1 : g *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x)` using `hgU _ hd`.

Establish `h2 : rhoOf H V Φ *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x)` using `rhoOf_perp H V Φ _ hd`. Establish `h3 : ∀ w : ι → ℂ, g *ᵥ (V *ᵥ w) = rhoOf H V Φ *ᵥ (V *ᵥ w)` using `fun w => by`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg, rhoOf_mul H V Φ hΓ]`. Establish `hx : x = (x - V *ᵥ (prj H V *ᵥ x)) + V *ᵥ (prj H V *ᵥ x)` using `(sub_add_cancel x _).symm`. Rewrite using `[hx, Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, h3]`.
-/
lemma eq_rhoOf (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ) (hΓ : IsUnit (Vᴴ * H * V).det)
    (g : Matrix n n ℂ) (hg : g * V = V * Φ) (hgU : ∀ x, (Vᴴ * H) *ᵥ x = 0 → g *ᵥ x = x) :
    g = rhoOf H V Φ := by
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  simp only [Matrix.toLin'_apply]
  have hd := decomp H V hΓ x
  have h1 : g *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x) := hgU _ hd
  have h2 : rhoOf H V Φ *ᵥ (x - V *ᵥ (prj H V *ᵥ x)) = x - V *ᵥ (prj H V *ᵥ x) :=
    rhoOf_perp H V Φ _ hd
  have h3 : ∀ w : ι → ℂ, g *ᵥ (V *ᵥ w) = rhoOf H V Φ *ᵥ (V *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg, rhoOf_mul H V Φ hΓ]
  have hx : x = (x - V *ᵥ (prj H V *ᵥ x)) + V *ᵥ (prj H V *ᵥ x) := (sub_add_cancel x _).symm
  rw [hx, Matrix.mulVec_add, Matrix.mulVec_add, h1, h2, h3]

/- English proof (translation)
Establish `hW : rhoOf H V Φ - 1 = V * (Φ - 1) * prj H V`. Simplify using `only [rhoOf, add_sub_cancel_left]`. Establish `hP` using `prj_mul H V hΓ`. Proceed by induction on `m with`. Consider the case `zero => rw [zero_add, pow_one, pow_one, hW]`.

Consider the case `succ k ih`. Rewrite using `[pow_succ (rhoOf H V Φ - 1) (k + 1), ih, hW]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = V * (Φ - 1) ^ (k + 1 + 1) * prj H V := by`.

Rewrite using `[hP, Matrix.mul_one, pow_succ (Φ - 1) (k + 1), Matrix.mul_assoc V ((Φ - 1) ^ (k + 1)) (Φ - 1)]`.
-/
lemma rhoOf_sub_one_pow (H : Matrix n n ℂ) (V : Matrix n ι ℂ) (Φ : Matrix ι ι ℂ)
    (hΓ : IsUnit (Vᴴ * H * V).det) (m : ℕ) :
    (rhoOf H V Φ - 1) ^ (m + 1) = V * (Φ - 1) ^ (m + 1) * prj H V := by
  have hW : rhoOf H V Φ - 1 = V * (Φ - 1) * prj H V := by
    simp only [rhoOf, add_sub_cancel_left]
  have hP := prj_mul H V hΓ
  induction m with
  | zero => rw [zero_add, pow_one, pow_one, hW]
  | succ k ih =>
    rw [pow_succ (rhoOf H V Φ - 1) (k + 1), ih, hW]
    calc V * (Φ - 1) ^ (k + 1) * prj H V * (V * (Φ - 1) * prj H V)
        = V * (Φ - 1) ^ (k + 1) * (prj H V * V) * (Φ - 1) * prj H V := by
          simp only [Matrix.mul_assoc]
      _ = V * (Φ - 1) ^ (k + 1 + 1) * prj H V := by
          rw [hP, Matrix.mul_one, pow_succ (Φ - 1) (k + 1), Matrix.mul_assoc V ((Φ - 1) ^ (k + 1)) (Φ - 1)]

end proj

/- English proof (translation)
Introduce `p`. Proceed by induction on `p with`. Consider the case `zero`. Introduce `i j hij`. Rewrite using `[pow_zero]`.

Conclude with `Matrix.one_apply_ne (fun h => by subst h; omega)`. Consider the case `succ p ih`. Introduce `i j hij`. Rewrite using `[pow_succ, Matrix.mul_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k _`. Distinguish the cases in `hk : k.val < i.val + p`. Rewrite using `[ih i k hk, zero_mul]`. Rewrite using `[hM k j (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]`.
-/
lemma strict_pow_apply {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    ∀ p : ℕ, ∀ i j : Fin m, j.val < i.val + p → (M ^ p) i j = 0 := by
  intro p
  induction p with
  | zero =>
    intro i j hij
    rw [pow_zero]
    exact Matrix.one_apply_ne (fun h => by subst h; omega)
  | succ p ih =>
    intro i j hij
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k.val < i.val + p
    · rw [ih i k hk, zero_mul]
    · rw [hM k j (Fin.le_iff_val_le_val.mpr (by omega)), mul_zero]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.zero_apply]`. Conclude with `strict_pow_apply M hM m i j (by have := j.isLt; omega)`.
-/
lemma strict_pow_eq_zero {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    M ^ m = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  exact strict_pow_apply M hM m i j (by have := j.isLt; omega)

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hpq`. Rewrite using `[pow_add, h, zero_mul]`.
-/
lemma pow_eq_zero_of_le {R : Type*} [MonoidWithZero R] {x : R} {p q : ℕ} (h : x ^ p = 0)
    (hpq : p ≤ q) : x ^ q = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [pow_add, h, zero_mul]

section herm

variable {n : Type*} [Fintype n]

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_add, dotProduct_add]`.
-/
lemma herm_add_left (H : Matrix n n ℂ) (a b w : n → ℂ) : herm H (a + b) w = herm H a w + herm H b w := by
  simp only [herm, Matrix.mulVec_add, dotProduct_add]

/- English proof (translation)
Simplify using `only [herm, star_add, add_dotProduct]`.
-/
lemma herm_add_right (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a + b) = herm H v a + herm H v b := by
  simp only [herm, star_add, add_dotProduct]

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
lemma herm_smul_left (H : Matrix n n ℂ) (c : ℂ) (a w : n → ℂ) : herm H (c • a) w = c * herm H a w := by
  simp only [herm, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Simplify using `only [herm, star_smul, smul_dotProduct, smul_eq_mul]`. Both sides reduce to the same expression.
-/
lemma herm_smul_right (H : Matrix n n ℂ) (c : ℂ) (v a : n → ℂ) : herm H v (c • a) = conj c * herm H v a := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]
  rfl

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_sub, dotProduct_sub]`.
-/
lemma herm_sub_left (H : Matrix n n ℂ) (a b w : n → ℂ) : herm H (a - b) w = herm H a w - herm H b w := by
  simp only [herm, Matrix.mulVec_sub, dotProduct_sub]

/- English proof (translation)
Simplify using `only [herm, star_sub, sub_dotProduct]`.
-/
lemma herm_sub_right (H : Matrix n n ℂ) (v a b : n → ℂ) : herm H v (a - b) = herm H v a - herm H v b := by
  simp only [herm, star_sub, sub_dotProduct]

/- English proof (translation)
Simplify using `only [herm, Matrix.mulVec_zero, dotProduct_zero]`.
-/
lemma herm_zero_left (H : Matrix n n ℂ) (w : n → ℂ) : herm H 0 w = 0 := by
  simp only [herm, Matrix.mulVec_zero, dotProduct_zero]

/- English proof (translation)
Simplify using `only [herm, star_zero, zero_dotProduct]`.
-/
lemma herm_zero_right (H : Matrix n n ℂ) (v : n → ℂ) : herm H v 0 = 0 := by
  simp only [herm, star_zero, zero_dotProduct]

/- English proof (translation)
Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
lemma herm_mulVec {m ι κ : Type*} [Fintype m] [Fintype ι] [Fintype κ] (H : Matrix m m ℂ)
    (A : Matrix m ι ℂ) (B : Matrix m κ ℂ) (a : ι → ℂ) (b : κ → ℂ) :
    herm H (A *ᵥ a) (B *ᵥ b) = star b ⬝ᵥ ((Bᴴ * H * A) *ᵥ a) := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end herm

section uni

variable {n : Type*} [Fintype n] [DecidableEq n]

end uni

section sig

/- English proof (translation)
Simplify using `[Complex.mul_re, Complex.normSq_apply]`. Apply the tactic sequence `try ring`.
-/
lemma star_mul_real (a : ℝ) (x : ℂ) : (star x * ((a : ℂ) * x)).re = a * Complex.normSq x := by
  simp [Complex.mul_re, Complex.normSq_apply]
  try ring

/- English proof (translation)
Use `set U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ↑hG.eigenvectorUnitary with hUd`. Use `set lam := hG.eigenvalues with hlam`. Establish `hUU : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2`. Establish `hUU' : U * star U = 1` using `Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2`. Establish `hspec : G = U * diagonal (RCLike.ofReal ∘ lam) * star U`.

Use `hG.spectral_theorem` as an intermediate fact. Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Then use the resulting hypothesis. Establish `hD : Uᴴ * G * U = diagonal (fun i => (lam i : ℂ))`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Use `conv_lhs => rw [hspec]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]`. Both sides reduce to the same expression. Establish `hform : ∀ c, star (U *ᵥ c) ⬝ᵥ (G *ᵥ (U *ᵥ c)) = ∑ i, star (c i) * ((lam i : ℂ) * c i)`. Introduce `c`.

Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]`. Simplify using `only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]`. Establish `hlam0 : ∀ i, lam i ≠ 0`. Establish `h1 : Uᴴ.det * U.det = 1`. Rewrite using `[← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hUU, Matrix.det_one]`.

Establish `hdD : (diagonal (fun i => (lam i : ℂ))).det ≠ 0`. Rewrite using `[← hD, Matrix.det_mul, Matrix.det_mul, mul_comm (Uᴴ.det), mul_assoc, h1, mul_one]`. Conclude with `hdet`. Rewrite `hdD` using `[Matrix.det_diagonal]`. Introduce `i`.

Use `(Finset.prod_ne_zero_iff.mp hdD) i (Finset.mem_univ i)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hext : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (d : Fin p ⊕ Fin q → ℂ), (∀ i, d i = if h : P i then c ⟨i, h⟩ else 0) → ∑ i, star (d i) * ((lam i : ℂ) * d i) = ∑ j : {i // P i}, star (c j) * ((lam j.1 : ℂ) * c j)`. Introduce `P _ c d hd`. Rewrite using `[← Fintype.sum_subtype_add_sum_subtype P (fun i => star (d i) * ((lam i : ℂ) * d i))]`.

Establish `h0 : ∑ i : {x // ¬ P x}, star (d i.1) * ((lam i.1 : ℂ) * d i.1) = 0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[hd, dif_neg i.2]`. Simplify using the standard rewrite rules.

Rewrite using `[h0, add_zero]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[hd, dif_pos i.2]`. Establish `hEv : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (i : Fin p ⊕ Fin q), ((Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // P i}) => if i = j.1 then (1 : ℂ) else 0) *ᵥ c) i = if h : P i then c ⟨i, h⟩ else 0`.

Introduce `P _ c i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨i, h⟩]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `e`. Conclude with `hb (Subtype.ext e.symm)`. Simplify using the standard rewrite rules.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[if_neg]`. Introduce `e`. Conclude with `h (e ▸ b.2)`.

Establish `hcardP : Fintype.card {i // 0 < lam i} ≤ p`. Assume the negation of the conclusion as `hlt0`. Establish `hlt` using `not_le.mp hlt0`. Use `set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0`. Use `set L : ({i // 0 < lam i} → ℂ) →ₗ[ℂ] (Fin p → ℂ) := ψ₁ ∘ₗ Matrix.mulVecLin (U * E)`.

Establish `hne : LinearMap.ker L ≠ ⊥` using `LinearMap.ker_ne_bot_of_finrank_lt (by`. Rewrite using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Conclude with `hlt)`. Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hL : ψ₁ (U *ᵥ (E *ᵥ c)) = 0`.

Establish `: L c = 0` using `hc`. Simplify `this` using `[L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]`. Establish `hle` using `h₁ _ hL`. Rewrite `hle` using `[hform, hext _ c _ (hEv _ c)]`. Rewrite `hle` using `[Complex.re_sum]`.

Simplify using `only [star_mul_real] at hle`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, c j ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Conclude with `hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))`. Establish `hpos : 0 < ∑ j : {i // 0 < lam i}, lam j.1 * Complex.normSq (c j)`.

Apply `lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // 0 < lam i} => lam j.1 * Complex.normSq (c j)) (fun j _ => mul_nonneg j.2.le (Complex.normSq_nonneg _)) (Finset.mem_univ j))` to reduce the goal to its premises. Conclude with `mul_pos j.2 (Complex.normSq_pos.mpr hj)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcardN : Fintype.card {i // ¬ 0 < lam i} ≤ q`. Assume the negation of the conclusion as `hlt0`.

Establish `hlt` using `not_le.mp hlt0`. Use `set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // ¬ 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0`. Use `set L : ({i // ¬ 0 < lam i} → ℂ) →ₗ[ℂ] (Fin q → ℂ) := ψ₂ ∘ₗ Matrix.mulVecLin (U * E)`. Establish `hne : LinearMap.ker L ≠ ⊥` using `LinearMap.ker_ne_bot_of_finrank_lt (by`. Rewrite using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`.

Conclude with `hlt)`. Take `⟨c, hc, hc0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hL : ψ₂ (U *ᵥ (E *ᵥ c)) = 0`. Establish `: L c = 0` using `hc`. Simplify `this` using `[L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]`.

Establish `hle` using `h₂ _ hL`. Rewrite `hle` using `[hform, hext _ c _ (hEv _ c)]`. Rewrite `hle` using `[Complex.re_sum]`. Simplify using `only [star_mul_real] at hle`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, c j ≠ 0 := by`.

Assume the negation of the conclusion as `hall`. Conclude with `hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))`. Establish `hneg : ∀ j : {i // ¬ 0 < lam i}, lam j.1 < 0` using `fun j => lt_of_le_of_ne (not_lt.mp j.2) (hlam0 j.1)`. Establish `hpos : 0 < ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j)`. Apply `lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // ¬ 0 < lam i} => (-lam j.1) * Complex.normSq (c j)) (fun j _ => mul_nonneg (neg_nonneg.mpr (hneg j).le) (Complex.normSq_nonneg _)) (Finset.mem_univ j))` to reduce the goal to its premises.

Conclude with `mul_pos (neg_pos.mpr (hneg j)) (Complex.normSq_pos.mpr hj)`. Establish `e : ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) = -∑ j : {i // ¬ 0 < lam i}, lam j.1 * Complex.normSq (c j)`. Rewrite using `[← Finset.sum_neg_distrib]`. Simplify using `only [neg_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsum : Fintype.card {i // 0 < lam i} + Fintype.card {i // ¬ 0 < lam i} = p + q`. Rewrite using `[← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl fun i => 0 < lam i), Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`. Establish `hp : Fintype.card {i // 0 < lam i} = p` using `by omega`. Establish `hq : Fintype.card {i // ¬ 0 < lam i} = q` using `by omega`. Use `set e₁ := Fintype.equivFinOfCardEq hp`.

Use `set e₂ := Fintype.equivFinOfCardEq hq`. Use `set e : Fin p ⊕ Fin q ≃ Fin p ⊕ Fin q := (Equiv.sumCongr e₁.symm e₂.symm).trans (Equiv.sumCompl fun i => 0 < lam i)`. Establish `he1 : ∀ j, 0 < lam (e (Sum.inl j))`. Introduce `j`. Simplify using `only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]`.

Conclude with `(e₁.symm j).2`. Establish `he2 : ∀ j, lam (e (Sum.inr j)) < 0`. Introduce `j`. Simplify using `only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]`. Conclude with `lt_of_le_of_ne (not_lt.mp (e₂.symm j).2) (hlam0 _)`.

Use `set s : Fin p ⊕ Fin q → ℂ := fun i => (((Real.sqrt |lam i|)⁻¹ : ℝ) : ℂ)`. Use `set A := U * diagonal s`. Establish `hA : Aᴴ * G * A = diagonal (fun i => ((lam i / |lam i| : ℝ) : ℂ))`. Establish `: Aᴴ * G * A = (diagonal s)ᴴ * (Uᴴ * G * U) * diagonal s`. Simplify using `only [A, Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Rewrite using `[this, hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hab : 0 < |lam i|` using `abs_pos.mpr (hlam0 i)`. Establish `hsq : Real.sqrt |lam i| * Real.sqrt |lam i| = |lam i|` using `Real.mul_self_sqrt hab.le`.

Establish `hsne : Real.sqrt |lam i| ≠ 0` using `(Real.sqrt_pos.mpr hab).ne'`. Simplify using `only [s, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]`. Rewrite using `[← Complex.ofReal_mul, ← Complex.ofReal_mul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Real.sq_sqrt hab.le]`. Expand and normalize the polynomial expressions, which then agree. Establish `hQ : (A.submatrix id e)ᴴ * G * A.submatrix id e = fromBlocks 1 0 0 (-1)`. Establish `: (A.submatrix id e)ᴴ * G * A.submatrix id e = (Aᴴ * G * A).submatrix e e`. Use extensionality with `a b`.

Both sides reduce to the same expression. Rewrite using `[this, hA, Matrix.submatrix_diagonal_equiv]`. Establish `h1 : ∀ j, ((lam (e (Sum.inl j)) / |lam (e (Sum.inl j))| : ℝ) : ℂ) = 1`. Introduce `j`. Rewrite using `[abs_of_pos (he1 j), div_self (he1 j).ne']`.

Simplify using the standard rewrite rules. Establish `h2 : ∀ j, ((lam (e (Sum.inr j)) / |lam (e (Sum.inr j))| : ℝ) : ℂ) = -1`. Introduce `j`. Rewrite using `[abs_of_neg (he2 j), div_neg, div_self (he2 j).ne]`. Simplify using the standard rewrite rules.

Establish `hfe : (fun i => ((lam i / |lam i| : ℝ) : ℂ)) ∘ e = Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ))`. Use function extensionality and compare the values at `x`. Consider the cases of `x with`. Consider the case `inl j => exact h1 j`. Consider the case `inr j => exact h2 j`.

Rewrite using `[hfe, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Use `⟨A.submatrix id e, ?_, hQ⟩` and prove the remaining obligations. Establish `hdB : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)).det ≠ 0`. Rewrite using `[Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin]`. Conclude with `pow_ne_zero _ (by norm_num)`. Rewrite `hdB` using `[← hQ, Matrix.det_mul, Matrix.det_mul]`.

Conclude with `isUnit_iff_ne_zero.mpr (fun h => hdB (by rw [h, mul_zero]))`.
-/
lemma sig_split {p q : ℕ} (G : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    (ψ₁ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin p → ℂ)) (h₁ : ∀ c, ψ₁ c = 0 → (star c ⬝ᵥ (G *ᵥ c)).re ≤ 0)
    (ψ₂ : (Fin p ⊕ Fin q → ℂ) →ₗ[ℂ] (Fin q → ℂ)) (h₂ : ∀ c, ψ₂ c = 0 → 0 ≤ (star c ⬝ᵥ (G *ᵥ c)).re) :
    ∃ Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, IsUnit Q.det ∧ Qᴴ * G * Q = fromBlocks 1 0 0 (-1) := by
  classical
  set U : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ↑hG.eigenvectorUnitary with hUd
  set lam := hG.eigenvalues with hlam
  have hUU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
  have hUU' : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
  have hspec : G = U * diagonal (RCLike.ofReal ∘ lam) * star U := by
    have := hG.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hD : Uᴴ * G * U = diagonal (fun i => (lam i : ℂ)) := by
    rw [← Matrix.star_eq_conjTranspose]
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    rfl
  have hform : ∀ c, star (U *ᵥ c) ⬝ᵥ (G *ᵥ (U *ᵥ c)) = ∑ i, star (c i) * ((lam i : ℂ) * c i) := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  have hlam0 : ∀ i, lam i ≠ 0 := by
    have h1 : Uᴴ.det * U.det = 1 := by
      rw [← Matrix.det_mul, ← Matrix.star_eq_conjTranspose, hUU, Matrix.det_one]
    have hdD : (diagonal (fun i => (lam i : ℂ))).det ≠ 0 := by
      rw [← hD, Matrix.det_mul, Matrix.det_mul, mul_comm (Uᴴ.det), mul_assoc, h1, mul_one]
      exact hdet
    rw [Matrix.det_diagonal] at hdD
    intro i
    have := (Finset.prod_ne_zero_iff.mp hdD) i (Finset.mem_univ i)
    exact_mod_cast this

  have hext : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (d : Fin p ⊕ Fin q → ℂ),
      (∀ i, d i = if h : P i then c ⟨i, h⟩ else 0) →
      ∑ i, star (d i) * ((lam i : ℂ) * d i) = ∑ j : {i // P i}, star (c j) * ((lam j.1 : ℂ) * c j) := by
    intro P _ c d hd
    rw [← Fintype.sum_subtype_add_sum_subtype P (fun i => star (d i) * ((lam i : ℂ) * d i))]
    have h0 : ∑ i : {x // ¬ P x}, star (d i.1) * ((lam i.1 : ℂ) * d i.1) = 0 := by
      apply Finset.sum_eq_zero; intro i _; rw [hd, dif_neg i.2]; simp
    rw [h0, add_zero]
    apply Finset.sum_congr rfl
    intro i _
    rw [hd, dif_pos i.2]
  have hEv : ∀ (P : Fin p ⊕ Fin q → Prop) [DecidablePred P] (c : {i // P i} → ℂ) (i : Fin p ⊕ Fin q),
      ((Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // P i}) => if i = j.1 then (1 : ℂ) else 0) *ᵥ c) i =
        if h : P i then c ⟨i, h⟩ else 0 := by
    intro P _ c i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul, one_mul, zero_mul]
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i, h⟩]
      · simp
      · intro b _ hb; rw [if_neg]; intro e; exact hb (Subtype.ext e.symm)
      · simp
    · apply Finset.sum_eq_zero; intro b _; rw [if_neg]; intro e; exact h (e ▸ b.2)
  have hcardP : Fintype.card {i // 0 < lam i} ≤ p := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // 0 < lam i} → ℂ) →ₗ[ℂ] (Fin p → ℂ) := ψ₁ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₁ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₁ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hpos : 0 < ∑ j : {i // 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // 0 < lam i} => lam j.1 * Complex.normSq (c j))
        (fun j _ => mul_nonneg j.2.le (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos j.2 (Complex.normSq_pos.mpr hj)
    linarith
  have hcardN : Fintype.card {i // ¬ 0 < lam i} ≤ q := by
    by_contra hlt0
    have hlt := not_le.mp hlt0
    set E := Matrix.of fun (i : Fin p ⊕ Fin q) (j : {i // ¬ 0 < lam i}) => if i = j.1 then (1 : ℂ) else 0
    set L : ({i // ¬ 0 < lam i} → ℂ) →ₗ[ℂ] (Fin q → ℂ) := ψ₂ ∘ₗ Matrix.mulVecLin (U * E)
    have hne : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]; exact hlt)
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hL : ψ₂ (U *ᵥ (E *ᵥ c)) = 0 := by
      have : L c = 0 := hc
      simpa [L, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] using this
    have hle := h₂ _ hL
    rw [hform, hext _ c _ (hEv _ c)] at hle
    rw [Complex.re_sum] at hle
    simp only [star_mul_real] at hle
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
      by_contra hall; exact hc0 (funext fun j => not_not.mp (fun h => hall ⟨j, h⟩))
    have hneg : ∀ j : {i // ¬ 0 < lam i}, lam j.1 < 0 := fun j => lt_of_le_of_ne (not_lt.mp j.2) (hlam0 j.1)
    have hpos : 0 < ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) := by
      apply lt_of_lt_of_le _ (Finset.single_le_sum (f := fun j : {i // ¬ 0 < lam i} => (-lam j.1) * Complex.normSq (c j))
        (fun j _ => mul_nonneg (neg_nonneg.mpr (hneg j).le) (Complex.normSq_nonneg _)) (Finset.mem_univ j))
      exact mul_pos (neg_pos.mpr (hneg j)) (Complex.normSq_pos.mpr hj)
    have e : ∑ j : {i // ¬ 0 < lam i}, (-lam j.1) * Complex.normSq (c j) =
        -∑ j : {i // ¬ 0 < lam i}, lam j.1 * Complex.normSq (c j) := by
      rw [← Finset.sum_neg_distrib]; simp only [neg_mul]
    linarith
  have hsum : Fintype.card {i // 0 < lam i} + Fintype.card {i // ¬ 0 < lam i} = p + q := by
    rw [← Fintype.card_sum, Fintype.card_congr (Equiv.sumCompl fun i => 0 < lam i), Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
  have hp : Fintype.card {i // 0 < lam i} = p := by omega
  have hq : Fintype.card {i // ¬ 0 < lam i} = q := by omega
  set e₁ := Fintype.equivFinOfCardEq hp
  set e₂ := Fintype.equivFinOfCardEq hq
  set e : Fin p ⊕ Fin q ≃ Fin p ⊕ Fin q := (Equiv.sumCongr e₁.symm e₂.symm).trans (Equiv.sumCompl fun i => 0 < lam i)
  have he1 : ∀ j, 0 < lam (e (Sum.inl j)) := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
    exact (e₁.symm j).2
  have he2 : ∀ j, lam (e (Sum.inr j)) < 0 := by
    intro j; simp only [e, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact lt_of_le_of_ne (not_lt.mp (e₂.symm j).2) (hlam0 _)
  set s : Fin p ⊕ Fin q → ℂ := fun i => (((Real.sqrt |lam i|)⁻¹ : ℝ) : ℂ)
  set A := U * diagonal s
  have hA : Aᴴ * G * A = diagonal (fun i => ((lam i / |lam i| : ℝ) : ℂ)) := by
    have : Aᴴ * G * A = (diagonal s)ᴴ * (Uᴴ * G * U) * diagonal s := by
      simp only [A, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hD, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    have hab : 0 < |lam i| := abs_pos.mpr (hlam0 i)
    have hsq : Real.sqrt |lam i| * Real.sqrt |lam i| = |lam i| := Real.mul_self_sqrt hab.le
    have hsne : Real.sqrt |lam i| ≠ 0 := (Real.sqrt_pos.mpr hab).ne'
    simp only [s, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    rw [Real.sq_sqrt hab.le]
    ring
  have hQ : (A.submatrix id e)ᴴ * G * A.submatrix id e = fromBlocks 1 0 0 (-1) := by
    have : (A.submatrix id e)ᴴ * G * A.submatrix id e = (Aᴴ * G * A).submatrix e e := by
      ext a b; rfl
    rw [this, hA, Matrix.submatrix_diagonal_equiv]
    have h1 : ∀ j, ((lam (e (Sum.inl j)) / |lam (e (Sum.inl j))| : ℝ) : ℂ) = 1 := by
      intro j; rw [abs_of_pos (he1 j), div_self (he1 j).ne']; simp
    have h2 : ∀ j, ((lam (e (Sum.inr j)) / |lam (e (Sum.inr j))| : ℝ) : ℂ) = -1 := by
      intro j; rw [abs_of_neg (he2 j), div_neg, div_self (he2 j).ne]; simp
    have hfe : (fun i => ((lam i / |lam i| : ℝ) : ℂ)) ∘ e = Sum.elim (fun _ => (1 : ℂ)) (fun _ => (-1 : ℂ)) := by
      funext x
      cases x with
      | inl j => exact h1 j
      | inr j => exact h2 j
    rw [hfe, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_one]
    congr 1
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.neg_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨A.submatrix id e, ?_, hQ⟩
  have hdB : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 (-1 : Matrix (Fin q) (Fin q) ℂ)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_neg, Matrix.det_one, mul_one,
      Fintype.card_fin]
    exact pow_ne_zero _ (by norm_num)
  rw [← hQ, Matrix.det_mul, Matrix.det_mul] at hdB
  exact isUnit_iff_ne_zero.mpr (fun h => hdB (by rw [h, mul_zero]))

end sig

end Formalism.FourierDecayAlt.P.HermitianProjections
