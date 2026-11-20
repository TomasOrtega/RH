import Formalism.SatakeDualWeyl.Statement

open Matrix

namespace Formalism.UG.P

open Formalism.UG

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, Matrix.conjTranspose_apply]`.
-/
theorem cT_conj_eq {m k : Type} (M : Matrix m k ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]

section Sig

variable {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Take `⟨e, P, hP⟩` from `h`. Use `⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩` and prove the remaining obligations. Use `⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e id, ?_⟩` and prove the remaining obligations. Rewrite `hP` using `[cT_conj_eq]`. Establish `hJ : J = (J.reindex e e).submatrix e e`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]`. Conclude with `hP`.
-/
theorem sig_data (J : Matrix n n ℂ) (p q : ℕ) (h : HasSignature J p q) :
    Fintype.card n = p + q ∧ ∃ Q : Matrix n (Fin p ⊕ Fin q) ℂ, Qᴴ * J * Q = Jpq p q := by
  obtain ⟨e, P, hP⟩ := h
  refine ⟨by rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin], ?_⟩
  refine ⟨(P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).submatrix e id, ?_⟩
  rw [cT_conj_eq] at hP

  have hJ : J = (J.reindex e e).submatrix e e := by
    ext i j; simp
  rw [hJ, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id]
  exact hP

/- English proof (translation)
Rewrite using `[Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hQ, ← Matrix.dotProduct_mulVec]`. Simplify using `[Jpq, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg, Matrix.neg_mulVec, Finset.sum_neg_distrib]`.
-/
theorem sig_quad {p q : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (x : Fin p ⊕ Fin q → ℂ) :
    star (Q *ᵥ x) ⬝ᵥ (J *ᵥ (Q *ᵥ x)) =
      (∑ i, star (x (Sum.inl i)) * x (Sum.inl i)) - ∑ j, star (x (Sum.inr j)) * x (Sum.inr j) := by
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
    ← Matrix.mul_assoc, hQ, ← Matrix.dotProduct_mulVec]
  simp [Jpq, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg,
    Matrix.neg_mulVec, Finset.sum_neg_distrib]

/- English proof (translation)
Establish `hz : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ)` using `fun z => by`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Both sides reduce to the same expression. Simplify using `only [hz] at h`. Rewrite `h` using `[← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_add, Complex.ofReal_eq_zero]`.

Establish `h1 : 0 ≤ ∑ i, Complex.normSq (a i)` using `Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _`. Establish `h2 : 0 ≤ ∑ j, Complex.normSq (b j)` using `Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _`. Establish `hA : ∑ i, Complex.normSq (a i) = 0` using `by linarith`. Establish `hB : ∑ j, Complex.normSq (b j) = 0` using `by linarith`. Rewrite `hA`, `hB` using `[Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _]`.

Conclude with `⟨funext fun i => Complex.normSq_eq_zero.1 (hA i (Finset.mem_univ _)),`. Use function extensionality and compare the values at `fun j => Complex.normSq_eq_zero.1 (hB j (Finset.mem_univ _))⟩`.
-/
private lemma eq_zero_of_sum_star_mul_self_add_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] (a : ι → ℂ) (b : κ → ℂ)
    (h : (∑ i, star (a i) * a i) + ∑ j, star (b j) * b j = 0) : a = 0 ∧ b = 0 := by
  have hz : ∀ z : ℂ, star z * z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    rw [Complex.normSq_eq_conj_mul_self]; rfl
  simp only [hz] at h
  rw [← Complex.ofReal_sum, ← Complex.ofReal_sum, ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h
  have h1 : 0 ≤ ∑ i, Complex.normSq (a i) := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have h2 : 0 ≤ ∑ j, Complex.normSq (b j) := Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hA : ∑ i, Complex.normSq (a i) = 0 := by linarith
  have hB : ∑ j, Complex.normSq (b j) = 0 := by linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => Complex.normSq_nonneg _] at hA hB
  exact ⟨funext fun i => Complex.normSq_eq_zero.1 (hA i (Finset.mem_univ _)),
    funext fun j => Complex.normSq_eq_zero.1 (hB j (Finset.mem_univ _))⟩

/- English proof (translation)
Set `φ : ((Fin p → ℂ) × (Fin q' → ℂ)) →ₗ[ℂ] (n → ℂ)` to `{ toFun := fun ab => Q *ᵥ Sum.elim ab.1 (0 : Fin q → ℂ) + Q' *ᵥ Sum.elim (0 : Fin p' → ℂ) ab.2 map_add' := by`. Introduce `x y`. Establish `h1 : Sum.elim (x.1 + y.1) (0 : Fin q → ℂ) = Sum.elim x.1 (0 : Fin q → ℂ) + Sum.elim y.1 (0 : Fin q → ℂ)`. Apply the tactic sequence `ext (i | i) <;> simp`. Establish `h2 : Sum.elim (0 : Fin p' → ℂ) (x.2 + y.2) = Sum.elim (0 : Fin p' → ℂ) x.2 + Sum.elim (0 : Fin p' → ℂ) y.2`.

Apply the tactic sequence `ext (i | i) <;> simp`. Simplify using `only [Prod.fst_add, Prod.snd_add, h1, h2, Matrix.mulVec_add]`. Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := by`. Introduce `c x`.

Establish `h1 : Sum.elim (c • x.1) (0 : Fin q → ℂ) = c • Sum.elim x.1 (0 : Fin q → ℂ)`. Apply the tactic sequence `ext (i | i) <;> simp`. Establish `h2 : Sum.elim (0 : Fin p' → ℂ) (c • x.2) = c • Sum.elim (0 : Fin p' → ℂ) x.2`. Apply the tactic sequence `ext (i | i) <;> simp`. Simplify using `only [Prod.smul_fst, Prod.smul_snd, h1, h2, Matrix.mulVec_smul, RingHom.id_apply, smul_add] }`.

Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨a, b⟩ hab`. Establish `hw : Q *ᵥ Sum.elim a (0 : Fin q → ℂ) = Q' *ᵥ (-(Sum.elim (0 : Fin p' → ℂ) b))`. Rewrite using `[Matrix.mulVec_neg]`.

Conclude with `eq_neg_of_add_eq_zero_left hab`. Establish `e1` using `sig_quad J Q hQ (Sum.elim a (0 : Fin q → ℂ))`. Establish `e2` using `sig_quad J Q' hQ' (-(Sum.elim (0 : Fin p' → ℂ) b))`. Rewrite `e2` using `[← hw, e1]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.neg_apply, star_zero, mul_zero, Finset.sum_const_zero, sub_zero, zero_sub, star_neg, neg_mul_neg] at e2`.

Use `eq_zero_of_sum_star_mul_self_add_eq_zero a b (by rw [e2]; ring)` as an intermediate fact. Rewrite using `[this.1, this.2]`. Both sides reduce to the same expression. Use `LinearMap.finrank_le_finrank_of_injective hinj` as an intermediate fact. Rewrite `this` using `[Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]`. Then use the resulting hypothesis.
-/
theorem sig_dim {p q p' q' : ℕ} (J : Matrix n n ℂ) (Q : Matrix n (Fin p ⊕ Fin q) ℂ)
    (hQ : Qᴴ * J * Q = Jpq p q) (Q' : Matrix n (Fin p' ⊕ Fin q') ℂ)
    (hQ' : Q'ᴴ * J * Q' = Jpq p' q') :
    p + q' ≤ Fintype.card n := by
  classical

  let φ : ((Fin p → ℂ) × (Fin q' → ℂ)) →ₗ[ℂ] (n → ℂ) :=
    { toFun := fun ab => Q *ᵥ Sum.elim ab.1 (0 : Fin q → ℂ) + Q' *ᵥ Sum.elim (0 : Fin p' → ℂ) ab.2
      map_add' := by
        intro x y
        have h1 : Sum.elim (x.1 + y.1) (0 : Fin q → ℂ) = Sum.elim x.1 (0 : Fin q → ℂ) + Sum.elim y.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (x.2 + y.2) = Sum.elim (0 : Fin p' → ℂ) x.2 + Sum.elim (0 : Fin p' → ℂ) y.2 := by
          ext (i | i) <;> simp
        simp only [Prod.fst_add, Prod.snd_add, h1, h2, Matrix.mulVec_add]
        abel
      map_smul' := by
        intro c x
        have h1 : Sum.elim (c • x.1) (0 : Fin q → ℂ) = c • Sum.elim x.1 (0 : Fin q → ℂ) := by
          ext (i | i) <;> simp
        have h2 : Sum.elim (0 : Fin p' → ℂ) (c • x.2) = c • Sum.elim (0 : Fin p' → ℂ) x.2 := by
          ext (i | i) <;> simp
        simp only [Prod.smul_fst, Prod.smul_snd, h1, h2, Matrix.mulVec_smul, RingHom.id_apply,
          smul_add] }
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ hab
    have hw : Q *ᵥ Sum.elim a (0 : Fin q → ℂ) = Q' *ᵥ (-(Sum.elim (0 : Fin p' → ℂ) b)) := by
      rw [Matrix.mulVec_neg]
      exact eq_neg_of_add_eq_zero_left hab
    have e1 := sig_quad J Q hQ (Sum.elim a (0 : Fin q → ℂ))
    have e2 := sig_quad J Q' hQ' (-(Sum.elim (0 : Fin p' → ℂ) b))
    rw [← hw, e1] at e2
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.neg_apply, star_zero, mul_zero,
      Finset.sum_const_zero, sub_zero, zero_sub, star_neg, neg_mul_neg] at e2
    have := eq_zero_of_sum_star_mul_self_add_eq_zero a b (by rw [e2]; ring)
    rw [this.1, this.2]
    rfl
  have := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
    Module.finrank_fintype_fun_eq_card] at this

end Sig

/- English proof (translation)
Introduce `n _ _ J p q p' q' h h'`. Take `⟨hc, Q, hQ⟩` from `sig_data J p q h`. Take `⟨hc', Q', hQ'⟩` from `sig_data J p' q' h'`. Establish `d1` using `sig_dim J Q hQ Q' hQ'`. Establish `d2` using `sig_dim J Q' hQ' Q hQ`.

Use linear arithmetic over natural numbers and integers.
-/
theorem signature_unique : Formalism.UG.SigUnique := by
  intro n _ _ J p q p' q' h h'
  obtain ⟨hc, Q, hQ⟩ := sig_data J p q h
  obtain ⟨hc', Q', hQ'⟩ := sig_data J p' q' h'
  have d1 := sig_dim J Q hQ Q' hQ'
  have d2 := sig_dim J Q' hQ' Q hQ
  omega

end Formalism.UG.P
