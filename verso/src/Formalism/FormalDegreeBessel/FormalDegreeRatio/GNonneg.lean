import Formalism.FormalDegreeBessel.StatementG

open Matrix

noncomputable section

namespace Formalism.QuantumDeterminants

/- English proof (translation)
Establish `hinj : Function.Injective f`. Introduce `a b hab`. Conclude with `sub_eq_zero.mp (hf (a - b) (by rw [map_sub, hab, sub_self]))`. Establish `h` using `LinearMap.finrank_le_finrank_of_injective hinj`. Simplify `h` using `[Module.finrank_fintype_fun_eq_card]`.
-/
lemma gn_card_le_of_ker {S : Type*} [Fintype S] {m : ℕ} (f : (S → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (hf : ∀ v, f v = 0 → v = 0) : Fintype.card S ≤ m := by
  have hinj : Function.Injective f := by
    intro a b hab
    exact sub_eq_zero.mp (hf (a - b) (by rw [map_sub, hab, sub_self]))
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using h

def gnExt {ι : Type*} [DecidableEq ι] (p : ι → Prop) : Matrix ι {i // p i} ℂ :=
  fun i j => if i = j.val then 1 else 0

/- English proof (translation)
Simplify using `only [Matrix.mulVec, _root_.dotProduct, gnExt]`. Use `split_ifs with h`. Rewrite using `[Finset.sum_eq_single ⟨i, h⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`.

Establish `hne : i ≠ b.val` using `fun e => hb (Subtype.ext e.symm)`. Simplify using `[hne]`. Introduce `h'`. Conclude with `absurd (Finset.mem_univ _) h'`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `j _`. Establish `hne : i ≠ j.val` using `fun e => h (by rw [e]; exact j.property)`. Simplify using `[hne]`.
-/
lemma gnExt_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ι → Prop) [DecidablePred p]
    (v : {i // p i} → ℂ) (i : ι) :
    (gnExt p *ᵥ v) i = if h : p i then v ⟨i, h⟩ else 0 := by
  simp only [Matrix.mulVec, _root_.dotProduct, gnExt]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨i, h⟩]
    · simp
    · intro b _ hb
      have hne : i ≠ b.val := fun e => hb (Subtype.ext e.symm)
      simp [hne]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · apply Finset.sum_eq_zero
    intro j _
    have hne : i ≠ j.val := fun e => h (by rw [e]; exact j.property)
    simp [hne]

/- English proof (translation)
Establish `h1 : star w * w = (Complex.normSq w : ℂ)`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Apply the tactic sequence `first | rfl | skip`. Rewrite using `[h1, Complex.ofReal_re]`.
-/
lemma gn_re_star_mul_self (w : ℂ) : (star w * w).re = Complex.normSq w := by
  have h1 : star w * w = (Complex.normSq w : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    first | rfl | skip
  rw [h1, Complex.ofReal_re]

/- English proof (translation)
Use `set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef`. Use `set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef`. Establish `hU : star U * U = 1` using `Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2`. Establish `hs : A = U * D * star U` using `hA.spectral_theorem`. Establish `hAU : A * U = U * D`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]`. Simplify using `only [_root_.dotProduct, hDdef, Matrix.mulVec_diagonal, Function.comp_apply, Pi.star_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1 : star (d i) * d i = (Complex.normSq (d i) : ℂ)`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Apply the tactic sequence `first | rfl | skip`. Establish `h2 : (RCLike.ofReal (hA.eigenvalues i) : ℂ) = ((hA.eigenvalues i : ℝ) : ℂ)` using `rfl`. Rewrite using `[Complex.ofReal_mul, ← h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gn_quad_eig {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (d : ι → ℂ) :
    star ((hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ d) ⬝ᵥ
        (A *ᵥ ((hA.eigenvectorUnitary : Matrix ι ι ℂ) *ᵥ d)) =
      ∑ i, ((hA.eigenvalues i * Complex.normSq (d i) : ℝ) : ℂ) := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hUdef
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hDdef
  have hU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
  have hs : A = U * D * star U := hA.spectral_theorem
  have hAU : A * U = U * D := by
    calc A * U = U * D * star U * U := by rw [← hs]
      _ = U * D * (star U * U) := by simp only [Matrix.mul_assoc]
      _ = U * D := by rw [hU, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, hAU, ← Matrix.mulVec_mulVec, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.star_eq_conjTranspose, hU, Matrix.one_mulVec]
  simp only [_root_.dotProduct, hDdef, Matrix.mulVec_diagonal, Function.comp_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : star (d i) * d i = (Complex.normSq (d i) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    first | rfl | skip
  have h2 : (RCLike.ofReal (hA.eigenvalues i) : ℂ) = ((hA.eigenvalues i : ℝ) : ℂ) := rfl
  rw [Complex.ofReal_mul, ← h1, h2]
  ring

/- English proof (translation)
Establish `hi` using `i.isLt`. Simplify using `only [Matrix.mulVec, _root_.dotProduct]`. Distinguish the cases in `h : i.val < r ∨ r + k < i.val`. Rewrite using `[dif_pos h, Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]`. Establish `e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1`.

Simplify using `only [Hpk, and_true]`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)`. Rewrite using `[e, one_mul]`. Introduce `b _ hb`. Establish `hb' : b.val ≠ 2 * r + k - i.val` using `fun e => hb (Fin.ext e)`.

Establish `e : Hpk k r i b = 0`. Simplify using `only [Hpk, and_true]`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)`. Rewrite using `[e, zero_mul]`. Introduce `hb`.

Conclude with `absurd (Finset.mem_univ _) hb`. Rewrite using `[dif_neg h, Finset.sum_eq_single i]`. Establish `e : Hpk k r i i = if i.val = r + k then -1 else 1`. Simplify using `only [Hpk, and_true]`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)`.

Rewrite using `[e]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `b _ hb`. Establish `hb' : b.val ≠ i.val` using `fun e => hb (Fin.ext e)`. Establish `e : Hpk k r i b = 0`.

Simplify using `only [Hpk, and_true]`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)`. Rewrite using `[e, zero_mul]`. Introduce `hb`. Conclude with `absurd (Finset.mem_univ _) hb`.
-/
lemma gn_Hpk_mulVec (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ y) i = if _h : i.val < r ∨ r + k < i.val then y ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -y i else y i := by
  have hi := i.isLt
  simp only [Matrix.mulVec, _root_.dotProduct]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [dif_pos h, Finset.sum_eq_single (⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1))]
    · have e : Hpk k r i ⟨2 * r + k - i.val, by omega⟩ = 1 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e, one_mul]
    · intro b _ hb
      have hb' : b.val ≠ 2 * r + k - i.val := fun e => hb (Fin.ext e)
      have e : Hpk k r i b = 0 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e, zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ _) hb
  · rw [dif_neg h, Finset.sum_eq_single i]
    · have e : Hpk k r i i = if i.val = r + k then -1 else 1 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e]
      split_ifs <;> simp
    · intro b _ hb
      have hb' : b.val ≠ i.val := fun e => hb (Fin.ext e)
      have e : Hpk k r i b = 0 := by
        simp only [Hpk, and_true]
        split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)
      rw [e, zero_mul]
    · intro hb
      exact absurd (Finset.mem_univ _) hb

/- English proof (translation)
Rewrite using `[gn_Hpk_mulVec, dif_pos (Or.inl hi)]`.
-/
lemma gn_Hpk_mulVec_lo (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hi : i.val < r) : (Hpk k r *ᵥ y) i = y ⟨2 * r + k - i.val, by omega⟩ := by
  rw [gn_Hpk_mulVec, dif_pos (Or.inl hi)]

/- English proof (translation)
Establish `hy : Hpk k r *ᵥ y = y`. Use function extensionality and compare the values at `i`. Establish `hi` using `i.isLt`. Rewrite using `[gn_Hpk_mulVec]`. Use `split_ifs with hio hk`.

Break down `hio with hio | hio` into its components or cases. Establish `e` using `h1 ⟨i.val, hio⟩`. Establish `e1 : eI k r ⟨i.val, hio⟩ = i` using `Fin.ext rfl`. Establish `e2 : esI k r ⟨i.val, hio⟩ = ⟨2 * r + k - i.val, by omega⟩` using `Fin.ext rfl`. Rewrite `e` using `[e1, e2]`.

Conclude with `e.symm`. Establish `ha : 2 * r + k - i.val < r` using `by omega`. Establish `e` using `h1 ⟨2 * r + k - i.val, ha⟩`. Establish `e1 : eI k r ⟨2 * r + k - i.val, ha⟩ = ⟨2 * r + k - i.val, by omega⟩` using `Fin.ext rfl`. Establish `e2 : esI k r ⟨2 * r + k - i.val, ha⟩ = i` using `Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)`.

Rewrite `e` using `[e1, e2]`. Conclude with `e`. Establish `ei : i = ⟨r + k, by omega⟩` using `Fin.ext hk`. Rewrite using `[ei, h2, neg_zero]`. Both sides reduce to the same expression.

Simplify using `only [herm]`. Rewrite using `[hy]`. Simplify using `only [_root_.dotProduct, Pi.star_apply]`. Rewrite using `[Complex.re_sum]`. Apply `Finset.sum_nonneg` to reduce the goal to its premises.

Introduce `i _`. Rewrite using `[gn_re_star_mul_self]`. Conclude with `Complex.normSq_nonneg _`.
-/
lemma gn_herm_nonneg (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ)
    (h1 : ∀ a : Fin r, y (eI k r a) = y (esI k r a)) (h2 : y ⟨r + k, by omega⟩ = 0) :
    0 ≤ (herm (Hpk k r) y y).re := by
  have hy : Hpk k r *ᵥ y = y := by
    funext i
    have hi := i.isLt
    rw [gn_Hpk_mulVec]
    split_ifs with hio hk
    · rcases hio with hio | hio
      · have e := h1 ⟨i.val, hio⟩
        have e1 : eI k r ⟨i.val, hio⟩ = i := Fin.ext rfl
        have e2 : esI k r ⟨i.val, hio⟩ = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext rfl
        rw [e1, e2] at e
        exact e.symm
      · have ha : 2 * r + k - i.val < r := by omega
        have e := h1 ⟨2 * r + k - i.val, ha⟩
        have e1 : eI k r ⟨2 * r + k - i.val, ha⟩ = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext rfl
        have e2 : esI k r ⟨2 * r + k - i.val, ha⟩ = i :=
          Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)
        rw [e1, e2] at e
        exact e
    · have ei : i = ⟨r + k, by omega⟩ := Fin.ext hk
      rw [ei, h2, neg_zero]
    · rfl
  simp only [herm]
  rw [hy]
  simp only [_root_.dotProduct, Pi.star_apply]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [gn_re_star_mul_self]
  exact Complex.normSq_nonneg _

def gnB (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun i j => gramVec k r z z' g j i

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gramM, herm, gnB, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, _root_.dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma gn_gramM_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    gramM k r z z' g = (gnB k r z z' g)ᴴ * Hpk k r * gnB k r z z' g := by
  ext i j
  simp only [gramM, herm, gnB, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    _root_.dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

/- English proof (translation)
Use `Matrix.IsHermitian.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [Hpk, and_true]`. Apply the tactic sequence `split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)`.
-/
lemma gn_Hpk_herm (k r : ℕ) : (Hpk k r).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [Hpk, and_true]
  split_ifs <;> first | (simp; done) | omega | (simp only [Fin.ext_iff, Fin.val_mk, and_true, true_and, and_self] at *; omega)

/- English proof (translation)
Establish `hH` using `gn_Hpk_herm k r`. Unfold `Matrix.IsHermitian at hH ⊢`. Rewrite using `[gn_gramM_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]`.
-/
lemma gn_gramM_herm (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : (gramM k r z z' g).IsHermitian := by
  have hH := gn_Hpk_herm k r
  unfold Matrix.IsHermitian at hH ⊢
  rw [gn_gramM_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH, Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[gn_gramM_eq]`. Simplify using `only [herm]`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.
-/
lemma gn_quad_B (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    star c ⬝ᵥ (gramM k r z z' g *ᵥ c) =
      herm (Hpk k r) (gnB k r z z' g *ᵥ c) (gnB k r z z' g *ᵥ c) := by
  rw [gn_gramM_eq]
  simp only [herm]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/- English proof (translation)
Simplify using `only [herm, bvec, _root_.dotProduct, Pi.star_apply]`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
lemma gn_herm_bvec_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (j : Fin m) :
    herm H v (bvec j) = (H *ᵥ v) j := by
  simp only [herm, bvec, _root_.dotProduct, Pi.star_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hlo : ∀ a b : Fin (r + 1), a.val < r → gramM k r z z' g (Sum.inl a) (Sum.inl b) = 0`. Introduce `a b ha`. Simplify using `only [gramM, gramVec, fvec, ha, ↓reduceDIte]`. Rewrite using `[gn_herm_bvec_right, gn_Hpk_mulVec_lo k r _ (eI k r ⟨a.val, ha⟩) ha]`. Use `split_ifs with hb`.

Simplify using `only [bvec, Pi.single_apply, eI]`. Rewrite using `[if_neg]`. Introduce `e`. Apply the tactic sequence `first | omega | (simp only [Fin.mk.injEq] at e; omega) | (have e' := Fin.val_eq_of_eq e; simp at e'; omega)`. Conclude with `hz _ (Or.inr (by simp only [eI]; omega))`.

Establish `hA` using `a.isLt`. Establish `hB` using `b.isLt`. Distinguish the cases in `ha : a.val < r`. Rewrite using `[hlo a b ha, if_neg (by omega)]`. Distinguish the cases in `hb : b.val < r`.

Establish `e` using `congrFun (congrFun (gn_gramM_herm k r z z' g) (Sum.inl a)) (Sum.inl b)`. Rewrite `e` using `[Matrix.conjTranspose_apply, hlo b a hb, star_zero]`. Rewrite using `[← e, if_neg (by omega)]`. Establish `ha' : a.val = r` using `by omega`. Establish `hb' : b.val = r` using `by omega`.

Rewrite using `[if_pos ⟨ha', hb'⟩]`. Simplify using `only [gramM, gramVec, fvec, ha, hb, ↓reduceDIte]`.
-/
lemma gn_gram_ff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    gramM k r z z' g (Sum.inl a) (Sum.inl b) =
      if a.val = r ∧ b.val = r then herm (Hpk k r) z z else 0 := by
  have hlo : ∀ a b : Fin (r + 1), a.val < r → gramM k r z z' g (Sum.inl a) (Sum.inl b) = 0 := by
    intro a b ha
    simp only [gramM, gramVec, fvec, ha, ↓reduceDIte]
    rw [gn_herm_bvec_right, gn_Hpk_mulVec_lo k r _ (eI k r ⟨a.val, ha⟩) ha]
    split_ifs with hb
    · simp only [bvec, Pi.single_apply, eI]
      rw [if_neg]
      intro e
      first | omega | (simp only [Fin.mk.injEq] at e; omega) | (have e' := Fin.val_eq_of_eq e; simp at e'; omega)
    · exact hz _ (Or.inr (by simp only [eI]; omega))
  have hA := a.isLt
  have hB := b.isLt
  by_cases ha : a.val < r
  · rw [hlo a b ha, if_neg (by omega)]
  · by_cases hb : b.val < r
    · have e := congrFun (congrFun (gn_gramM_herm k r z z' g) (Sum.inl a)) (Sum.inl b)
      rw [Matrix.conjTranspose_apply, hlo b a hb, star_zero] at e
      rw [← e, if_neg (by omega)]
    · have ha' : a.val = r := by omega
      have hb' : b.val = r := by omega
      rw [if_pos ⟨ha', hb'⟩]
      simp only [gramM, gramVec, fvec, ha, hb, ↓reduceDIte]

/- English proof (translation)
Establish `key : star c ⬝ᵥ (gramM k r z z' g *ᵥ c) = star (c (Sum.inl (Fin.last r))) * (herm (Hpk k r) z z * c (Sum.inl (Fin.last r)))`. Simplify using `only [_root_.dotProduct, Matrix.mulVec, Fintype.sum_sum_type, hc, star_zero, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Pi.star_apply]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[gn_gram_ff k r z z' g hz, if_pos ⟨rfl, rfl⟩]`.

Introduce `b _ hb`. Rewrite using `[gn_gram_ff k r z z' g hz, if_neg, zero_mul]`. Introduce and unpack `⟨_, h2⟩`. Conclude with `hb (Fin.ext h2)`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Introduce `a _ ha`. Rewrite using `[Finset.sum_eq_zero, mul_zero]`. Introduce `b _`. Rewrite using `[gn_gram_ff k r z z' g hz, if_neg, zero_mul]`.

Introduce and unpack `⟨h1, _⟩`. Conclude with `ha (Fin.ext h1)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `h1 : star (c (Sum.inl (Fin.last r))) * c (Sum.inl (Fin.last r)) = (Complex.normSq (c (Sum.inl (Fin.last r))) : ℂ)`.

Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Apply the tactic sequence `first | rfl | skip`. Rewrite using `[key, show star (c (Sum.inl (Fin.last r))) * (herm (Hpk k r) z z * c (Sum.inl (Fin.last r))) = herm (Hpk k r) z z * (star (c (Sum.inl (Fin.last r))) * c (Sum.inl (Fin.last r))) by ring, h1, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]`. Use polynomial arithmetic with `[Complex.normSq_nonneg (c (Sum.inl (Fin.last r)))]`.
-/
lemma gn_quad_inl (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hz : inWb k r z)
    (hzz : (herm (Hpk k r) z z).re ≤ 0)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (star c ⬝ᵥ (gramM k r z z' g *ᵥ c)).re ≤ 0 := by
  have key : star c ⬝ᵥ (gramM k r z z' g *ᵥ c) =
      star (c (Sum.inl (Fin.last r))) * (herm (Hpk k r) z z * c (Sum.inl (Fin.last r))) := by
    simp only [_root_.dotProduct, Matrix.mulVec, Fintype.sum_sum_type, hc, star_zero, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero, Pi.star_apply]
    rw [Finset.sum_eq_single (Fin.last r)]
    · rw [Finset.sum_eq_single (Fin.last r)]
      · rw [gn_gram_ff k r z z' g hz, if_pos ⟨rfl, rfl⟩]
      · intro b _ hb
        rw [gn_gram_ff k r z z' g hz, if_neg, zero_mul]
        rintro ⟨_, h2⟩
        exact hb (Fin.ext h2)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · intro a _ ha
      rw [Finset.sum_eq_zero, mul_zero]
      intro b _
      rw [gn_gram_ff k r z z' g hz, if_neg, zero_mul]
      rintro ⟨h1, _⟩
      exact ha (Fin.ext h1)
    · intro h
      exact absurd (Finset.mem_univ _) h
  have h1 : star (c (Sum.inl (Fin.last r))) * c (Sum.inl (Fin.last r)) =
      (Complex.normSq (c (Sum.inl (Fin.last r))) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    first | rfl | skip
  rw [key, show star (c (Sum.inl (Fin.last r))) * (herm (Hpk k r) z z * c (Sum.inl (Fin.last r))) =
      herm (Hpk k r) z z * (star (c (Sum.inl (Fin.last r))) * c (Sum.inl (Fin.last r))) by ring, h1,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  nlinarith [Complex.normSq_nonneg (c (Sum.inl (Fin.last r)))]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, v j ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hv (funext hcon)`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_lt_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[gnExt_mulVec]`. Use `split_ifs with h`. Use `Complex.normSq_nonneg (v ⟨i, h⟩)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Simplify using the standard rewrite rules. Use `⟨j.val, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[gnExt_mulVec, dif_pos j.property]`. Use `Complex.normSq_pos.mpr (show v ⟨j.val, j.property⟩ ≠ 0 from hj)` as an intermediate fact.

Establish `hl` using `j.property`. Use the polynomial consequences of the given equalities and inequalities. Use `_ = 0 := by simp`.
-/
lemma gn_sum_neg {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ)
    (v : {i // lam i < 0} → ℂ) (hv : v ≠ 0) :
    ∑ i, lam i * Complex.normSq ((gnExt (fun i => lam i < 0) *ᵥ v) i) < 0 := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  calc ∑ i, lam i * Complex.normSq ((gnExt (fun i => lam i < 0) *ᵥ v) i) < ∑ _i : ι, (0 : ℝ) := by
        apply Finset.sum_lt_sum
        · intro i _
          rw [gnExt_mulVec]
          split_ifs with h
          · have := Complex.normSq_nonneg (v ⟨i, h⟩)
            nlinarith
          · simp
        · refine ⟨j.val, Finset.mem_univ _, ?_⟩
          rw [gnExt_mulVec, dif_pos j.property]
          have := Complex.normSq_pos.mpr (show v ⟨j.val, j.property⟩ ≠ 0 from hj)
          have hl := j.property
          nlinarith
    _ = 0 := by simp

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, v j ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hv (funext hcon)`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_lt_sum` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[gnExt_mulVec]`. Use `split_ifs with h`. Use `Complex.normSq_nonneg (v ⟨i, h⟩)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Simplify using the standard rewrite rules. Use `⟨j.val, Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[gnExt_mulVec, dif_pos j.property]`. Use `Complex.normSq_pos.mpr (show v ⟨j.val, j.property⟩ ≠ 0 from hj)` as an intermediate fact.

Establish `hl` using `j.property`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma gn_sum_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (lam : ι → ℝ)
    (v : {i // 0 < lam i} → ℂ) (hv : v ≠ 0) :
    0 < ∑ i, lam i * Complex.normSq ((gnExt (fun i => 0 < lam i) *ᵥ v) i) := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  calc (0 : ℝ) = ∑ _i : ι, (0 : ℝ) := by simp
    _ < ∑ i, lam i * Complex.normSq ((gnExt (fun i => 0 < lam i) *ᵥ v) i) := by
        apply Finset.sum_lt_sum
        · intro i _
          rw [gnExt_mulVec]
          split_ifs with h
          · have := Complex.normSq_nonneg (v ⟨i, h⟩)
            nlinarith
          · simp
        · refine ⟨j.val, Finset.mem_univ _, ?_⟩
          rw [gnExt_mulVec, dif_pos j.property]
          have := Complex.normSq_pos.mpr (show v ⟨j.val, j.property⟩ ≠ 0 from hj)
          have hl := j.property
          nlinarith

def gnPi (k r : ℕ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) where
  toFun y a := if h : a.val < r then y (eI k r ⟨a.val, h⟩) - y (esI k r ⟨a.val, h⟩)
    else y ⟨r + k, by omega⟩
  map_add' x y := by
    ext a
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c x := by
    ext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/- English proof (translation)
Introduce `k r z z' hz hz' hT _hT' g hg`. Establish `hG` using `h k r z z' hz hz' g hg`. Establish `hM` using `gn_gramM_herm k r z z' g`. Rewrite `hG` using `[hM.det_eq_prod_eigenvalues]`. Establish `hzz : (herm (Hpk k r) z z).re ≤ 0`.

Unfold `Tz at hT`. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h0 : ∃ i, hM.eigenvalues i = 0`. Take `⟨i, hi⟩` from `h0`. Rewrite `hG` using `[Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; simp), mul_zero]`.

Establish `: Gf k r z z' g = 0` using `by exact_mod_cast hG`. Rewrite using `[this]`. Use `push Not at h0`. Establish `hneg : Fintype.card {i // hM.eigenvalues i < 0} ≤ r + 1`. Use `gn_card_le_of_ker ((gnPi k r).comp (gnB k r z z' g * (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) * gnExt (fun i => hM.eigenvalues i < 0)).mulVecLin) ?_` and prove the remaining obligations.

Introduce `v hv`. Assume the negation of the conclusion as `hv0`. Take `⟨y, hy⟩ : ∃ y, y = gnB k r z z' g *ᵥ ((hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ (gnExt (fun i => hM.eigenvalues i < 0) *ᵥ v))` from `⟨_, rfl⟩`. Establish `hyv : (gnB k r z z' g * (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) * gnExt (fun i => hM.eigenvalues i < 0)) *ᵥ v = y`. Rewrite using `[hy, mulVec_mulVec, mulVec_mulVec]`.

Simplify using `only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hyv] at hv`. Establish `h1 : ∀ a : Fin r, y (eI k r a) = y (esI k r a)`. Introduce `a`. Use `congrFun hv ⟨a.val, by omega⟩` as an intermediate fact. Simplify `this` using `[gnPi, a.isLt, sub_eq_zero]`.

Establish `h2 : y ⟨r + k, by omega⟩ = 0`. Use `congrFun hv (Fin.last r)` as an intermediate fact. Simplify `this` using `[gnPi]`. Establish `hpos` using `gn_herm_nonneg k r y h1 h2`. Rewrite `hpos` using `[hy, ← gn_quad_B, gn_quad_eig hM]`.

Use `gn_sum_neg hM.eigenvalues v hv0` as an intermediate fact. Simplify using `only [Complex.re_sum, Complex.ofReal_re] at hpos`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hposc : Fintype.card {i // 0 < hM.eigenvalues i} ≤ r + 1`. Use `gn_card_le_of_ker ((((hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) * gnExt (fun i => 0 < hM.eigenvalues i)).submatrix Sum.inr id).mulVecLin) ?_` and prove the remaining obligations.

Introduce `v hv`. Assume the negation of the conclusion as `hv0`. Take `⟨c, hc⟩ : ∃ c, c = (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ (gnExt (fun i => 0 < hM.eigenvalues i) *ᵥ v)` from `⟨_, rfl⟩`. Establish `hci : ∀ b, c (Sum.inr b) = 0`. Introduce `b`.

Use `congrFun hv b` as an intermediate fact. Rewrite using `[hc, mulVec_mulVec]`. Simplify `this` using `[mulVec, dotProduct]`. Establish `hq` using `gn_quad_inl k r z z' g hz hzz c hci`. Rewrite `hq` using `[hc, gn_quad_eig hM]`.

Use `gn_sum_pos hM.eigenvalues v hv0` as an intermediate fact. Simplify using `only [Complex.re_sum, Complex.ofReal_re] at hq`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : Fintype.card {i // hM.eigenvalues i < 0} + Fintype.card {i // 0 < hM.eigenvalues i} = 2 * r + 2`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`.

Establish `: (Finset.univ.filter fun i => 0 < hM.eigenvalues i) = Finset.univ.filter fun i => ¬ (hM.eigenvalues i < 0)`. Apply `Finset.filter_congr` to reduce the goal to its premises. Introduce `i _`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `h`. Conclude with `lt_of_le_of_ne (not_lt.mp h) (Ne.symm (h0 i))`. Rewrite using `[this, Finset.card_filter_add_card_filter_not]`. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish `hcard : (Finset.univ.filter fun i => hM.eigenvalues i < 0).card = r + 1`. Rewrite using `[← Fintype.card_subtype]`. Use linear arithmetic over natural numbers and integers. Establish `key : Gf k r z z' g = (-1) ^ (r + 1) * ∏ j, hM.eigenvalues j`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[hG]`. Use `push_cast`. Both sides reduce to the same expression. Establish `e : ∀ j, hM.eigenvalues j = (if hM.eigenvalues j < 0 then (-1 : ℝ) else 1) * |hM.eigenvalues j|`.

Introduce `j`. Use `split_ifs with hj`. Rewrite using `[abs_of_neg hj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[abs_of_nonneg (not_lt.mp hj)]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hprod : ∏ j, hM.eigenvalues j = (-1) ^ (r + 1) * ∏ j, |hM.eigenvalues j|`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, hcard]`. Rewrite using `[key, hprod, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]`.

Evaluate the numerical expressions. Check the signs of the components of the expression.
-/
theorem gNonneg_of (h : GGram) : GNonneg := by
  intro k r z z' hz hz' hT _hT' g hg
  have hG := h k r z z' hz hz' g hg
  have hM := gn_gramM_herm k r z z' g
  rw [hM.det_eq_prod_eigenvalues] at hG
  have hzz : (herm (Hpk k r) z z).re ≤ 0 := by
    unfold Tz at hT
    linarith
  by_cases h0 : ∃ i, hM.eigenvalues i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi]; simp), mul_zero] at hG
    have : Gf k r z z' g = 0 := by exact_mod_cast hG
    rw [this]
  · push Not at h0
    have hneg : Fintype.card {i // hM.eigenvalues i < 0} ≤ r + 1 := by
      refine gn_card_le_of_ker ((gnPi k r).comp
        (gnB k r z z' g * (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *
          gnExt (fun i => hM.eigenvalues i < 0)).mulVecLin) ?_
      intro v hv
      by_contra hv0
      obtain ⟨y, hy⟩ : ∃ y, y = gnB k r z z' g *ᵥ ((hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ
          (gnExt (fun i => hM.eigenvalues i < 0) *ᵥ v)) := ⟨_, rfl⟩
      have hyv : (gnB k r z z' g * (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *
          gnExt (fun i => hM.eigenvalues i < 0)) *ᵥ v = y := by
        rw [hy, mulVec_mulVec, mulVec_mulVec]
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hyv] at hv
      have h1 : ∀ a : Fin r, y (eI k r a) = y (esI k r a) := by
        intro a
        have := congrFun hv ⟨a.val, by omega⟩
        simpa [gnPi, a.isLt, sub_eq_zero] using this
      have h2 : y ⟨r + k, by omega⟩ = 0 := by
        have := congrFun hv (Fin.last r)
        simpa [gnPi] using this
      have hpos := gn_herm_nonneg k r y h1 h2
      rw [hy, ← gn_quad_B, gn_quad_eig hM] at hpos
      have := gn_sum_neg hM.eigenvalues v hv0
      simp only [Complex.re_sum, Complex.ofReal_re] at hpos
      linarith
    have hposc : Fintype.card {i // 0 < hM.eigenvalues i} ≤ r + 1 := by
      refine gn_card_le_of_ker ((((hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *
          gnExt (fun i => 0 < hM.eigenvalues i)).submatrix Sum.inr id).mulVecLin) ?_
      intro v hv
      by_contra hv0
      obtain ⟨c, hc⟩ : ∃ c, c = (hM.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ
          (gnExt (fun i => 0 < hM.eigenvalues i) *ᵥ v) := ⟨_, rfl⟩
      have hci : ∀ b, c (Sum.inr b) = 0 := by
        intro b
        have := congrFun hv b
        rw [hc, mulVec_mulVec]
        simpa [mulVec, dotProduct] using this
      have hq := gn_quad_inl k r z z' g hz hzz c hci
      rw [hc, gn_quad_eig hM] at hq
      have := gn_sum_pos hM.eigenvalues v hv0
      simp only [Complex.re_sum, Complex.ofReal_re] at hq
      linarith
    have hsum : Fintype.card {i // hM.eigenvalues i < 0} +
        Fintype.card {i // 0 < hM.eigenvalues i} = 2 * r + 2 := by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      have : (Finset.univ.filter fun i => 0 < hM.eigenvalues i) =
          Finset.univ.filter fun i => ¬ (hM.eigenvalues i < 0) := by
        apply Finset.filter_congr
        intro i _
        constructor
        · intro h
          linarith
        · intro h
          exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm (h0 i))
      rw [this, Finset.card_filter_add_card_filter_not]
      simp
      omega
    have hcard : (Finset.univ.filter fun i => hM.eigenvalues i < 0).card = r + 1 := by
      rw [← Fintype.card_subtype]
      omega
    have key : Gf k r z z' g = (-1) ^ (r + 1) * ∏ j, hM.eigenvalues j := by
      apply Complex.ofReal_injective
      rw [hG]
      push_cast
      rfl
    have e : ∀ j, hM.eigenvalues j =
        (if hM.eigenvalues j < 0 then (-1 : ℝ) else 1) * |hM.eigenvalues j| := by
      intro j
      split_ifs with hj
      · rw [abs_of_neg hj]
        ring
      · rw [abs_of_nonneg (not_lt.mp hj)]
        ring
    have hprod : ∏ j, hM.eigenvalues j = (-1) ^ (r + 1) * ∏ j, |hM.eigenvalues j| := by
      calc ∏ j, hM.eigenvalues j
          = ∏ j, ((if hM.eigenvalues j < 0 then (-1 : ℝ) else 1) * |hM.eigenvalues j|) :=
            Finset.prod_congr rfl (fun j _ => e j)
        _ = (-1) ^ (r + 1) * ∏ j, |hM.eigenvalues j| := by
            rw [Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one,
              mul_one, hcard]
    rw [key, hprod, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
    positivity

end Formalism.QuantumDeterminants
