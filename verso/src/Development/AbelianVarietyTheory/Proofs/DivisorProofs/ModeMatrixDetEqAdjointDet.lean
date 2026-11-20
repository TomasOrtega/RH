import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.VdmSplit

section
open GlobalTheory.PsCo.PcEG

noncomputable section

open Matrix
open GlobalTheory.PsCo.Pc1 (Mat Poly ev OmP Mode dM dZ barM sg)
open ReciprocityTheory.ChartRestriction.DS.TRGap (physDet IsPhys)

namespace GlobalTheory.PsCo.PcEF.OmegaDeterminant

variable {n : ℕ}

/- English proof (translation)
Simplify using `[ev]`.
-/
lemma ev_X_inl (k : Mat n) (p : Fin n × Fin n) : ev k (MvPolynomial.X (Sum.inl p)) = k p.1 p.2 := by
  simp [ev]

/- English proof (translation)
Simplify using `[ev]`.
-/
lemma ev_X_inr (k : Mat n) (p : Fin n × Fin n) : ev k (MvPolynomial.X (Sum.inr p)) = star (k p.1 p.2) := by
  simp [ev]

/- English proof (translation)
Take `⟨⟨i, a⟩, hi, ha⟩` from `x`. Take `⟨⟨j, b⟩, hj, hb⟩` from `y`. Simplify using `only [OmP, dM, dZ, MvPolynomial.mkDerivation_X, Sum.elim_inr, barM, Matrix.single_apply]`. Simplify using `[ite_and, mul_ite, sg]`. Simplify using `only at hi ha hj hb`.

Apply the tactic sequence `rcases eq_or_ne a b with rfl | hab <;> rcases eq_or_ne i j with rfl | hij <;>`. Simplify using `[apply_ite MvPolynomial.C, mul_ite, ite_mul, Finset.sum_add_distrib, sub_eq_add_neg, *]`.
-/
lemma OmP_apply (ε : Fin n → Bool) (x y : Mode ε) :
    OmP ε x y = (if x.1.2 = y.1.2 then MvPolynomial.X (Sum.inr (y.1.1, x.1.1)) else 0) -
      (if x.1.1 = y.1.1 then MvPolynomial.X (Sum.inr (x.1.2, y.1.2)) else 0) := by
  obtain ⟨⟨i, a⟩, hi, ha⟩ := x
  obtain ⟨⟨j, b⟩, hj, hb⟩ := y
  simp only [OmP, dM, dZ, MvPolynomial.mkDerivation_X, Sum.elim_inr, barM, Matrix.single_apply]
  simp [ite_and, mul_ite, sg]
  simp only at hi ha hj hb
  rcases eq_or_ne a b with rfl | hab <;> rcases eq_or_ne i j with rfl | hij <;>
    simp [apply_ite MvPolynomial.C, mul_ite, ite_mul, Finset.sum_add_distrib, sub_eq_add_neg, *]

/- English proof (translation)
Rewrite using `[OmP_apply, map_sub, apply_ite (ev k), apply_ite (ev k), ev_X_inr, ev_X_inr, map_zero]`.
-/
lemma ev_OmP (ε : Fin n → Bool) (k : Mat n) (x y : Mode ε) :
    ev k (OmP ε x y) = (if x.1.2 = y.1.2 then star (k y.1.1 x.1.1) else 0) -
      (if x.1.1 = y.1.1 then star (k x.1.2 y.1.2) else 0) := by
  rw [OmP_apply, map_sub, apply_ite (ev k), apply_ite (ev k), ev_X_inr, ev_X_inr, map_zero]

/- English proof (translation)
Use `congrFun (congrFun hk.2 i) j` as an intermediate fact. Simplify using `only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at this`. Apply the tactic sequence `cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ↓reduceIte, Bool.false_eq_true] at this h`. Conclude with `absurd rfl h`. Take the linear combination `(1 / 2 : ℂ) * this`.

Take the linear combination `(-1 / 2 : ℂ) * this`. Conclude with `absurd rfl h`.
-/
lemma K_block {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) {i j : Fin n} (h : ε i ≠ ε j) :
    k i j = 0 := by
  have := congrFun (congrFun hk.2 i) j
  simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  cases hi : ε i <;> cases hj : ε j <;> simp only [hi, hj, ↓reduceIte, Bool.false_eq_true] at this h
  · exact absurd rfl h
  · linear_combination (1 / 2 : ℂ) * this
  · linear_combination (-1 / 2 : ℂ) * this
  · exact absurd rfl h

/- English proof (translation)
Use `congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hk.1) i) l` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply]`.
-/
lemma K_unit {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (i l : Fin n) :
    ∑ j, k i j * star (k l j) = if i = l then 1 else 0 := by
  have := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hk.1) i) l
  simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using this

/- English proof (translation)
Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false) (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]`.
-/
lemma sum_mode (ε : Fin n → Bool) (f : Fin n × Fin n → ℂ) :
    ∑ y : Mode ε, f y.1 = ∑ j, ∑ b, if ε j = true ∧ ε b = false then f (j, b) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => ε p.1 = true ∧ ε p.2 = false)
    (by simp) f, Finset.sum_filter, Fintype.sum_prod_type]

/- English proof (translation)
Take `⟨⟨i, a⟩, hi, ha⟩` from `x`. Take `⟨⟨l, d⟩, hl, hd⟩` from `z`. Establish `hs` using `sum_mode ε (fun p => (if a = p.2 then k i p.1 else 0) * ((if p.2 = d then star (k l p.1) else 0) - (if p.1 = l then star (k p.2 d) else 0)))`. Simplify using `only at hs ⊢`. Rewrite using `[hs]`.

Establish `h1 : ∀ j, (∑ b, if ε j = true ∧ ε b = false then (if a = b then k i j else 0) * ((if b = d then star (k l j) else 0) - (if j = l then star (k b d) else 0)) else 0) = k i j * ((if a = d then star (k l j) else 0) - (if j = l then star (k a d) else 0))`. Introduce `j`. Rewrite using `[Finset.sum_eq_single a]`. Distinguish the cases in `hj : ε j = true`. Simplify using `[hj, ha]`.

Establish `: k i j = 0` using `K_block hk (by rw [hi]; exact fun h => hj h.symm)`. Simplify using `[hj, this]`. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_congr rfl (fun j _ => h1 j)]`. Simplify using `only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Distinguish the cases in `had : a = d`. Substitute `had` using the available equality. Simplify using `only [if_true, K_unit hk]`.

Distinguish the cases in `hil : i = l`. Substitute `hil` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hil]`. Simplify using `[had]`.
-/
lemma entry {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (x z : Mode ε) :
    ∑ y : Mode ε, (if x.1.2 = y.1.2 then k x.1.1 y.1.1 else 0) *
      ((if y.1.2 = z.1.2 then star (k z.1.1 y.1.1) else 0) -
        (if y.1.1 = z.1.1 then star (k y.1.2 z.1.2) else 0)) =
    (if x = z then 1 else 0) - k x.1.1 z.1.1 * star (k x.1.2 z.1.2) := by
  obtain ⟨⟨i, a⟩, hi, ha⟩ := x
  obtain ⟨⟨l, d⟩, hl, hd⟩ := z
  have hs := sum_mode ε (fun p => (if a = p.2 then k i p.1 else 0) *
      ((if p.2 = d then star (k l p.1) else 0) - (if p.1 = l then star (k p.2 d) else 0)))
  simp only at hs ⊢
  rw [hs]
  have h1 : ∀ j, (∑ b, if ε j = true ∧ ε b = false then (if a = b then k i j else 0) *
      ((if b = d then star (k l j) else 0) - (if j = l then star (k b d) else 0)) else 0) =
      k i j * ((if a = d then star (k l j) else 0) - (if j = l then star (k a d) else 0)) := by
    intro j
    rw [Finset.sum_eq_single a]
    · by_cases hj : ε j = true
      · simp [hj, ha]
      · have : k i j = 0 := K_block hk (by rw [hi]; exact fun h => hj h.symm)
        simp [hj, this]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  by_cases had : a = d
  · subst had
    simp only [if_true, K_unit hk]
    by_cases hil : i = l
    · subst hil; simp
    · simp [hil]
  · simp [had]

def AP (ε : Fin n → Bool) : Matrix (Mode ε) (Mode ε) (Poly n) :=
  fun x y => if x.1.2 = y.1.2 then MvPolynomial.X (Sum.inl (x.1.1, y.1.1)) else 0

end OmegaDeterminant

open OmegaDeterminant in
/- English proof (translation)
Introduce `n ε`. Use `⟨(AP ε).det, fun k hk => ?_⟩` and prove the remaining obligations. Set `e : Mode ε ≃ {x : Fin n × Fin n // IsPhys ε x}` to `Equiv.subtypeEquivRight (p := fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false) (fun _ => Iff.rfl)`. Establish `key : (ev k).mapMatrix (AP ε) * (ev k).mapMatrix (OmP ε) = (Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} => (if x = y then (1 : ℂ) else 0) - k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix e e`. Use extensionality with `x z`.

Rewrite using `[Matrix.mul_apply]`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, AP, ev_OmP, Matrix.submatrix_apply, Matrix.of_apply, apply_ite (ev k), ev_X_inl, map_zero, e, EmbeddingLike.apply_eq_iff_eq]`. Apply the tactic sequence `exact entry hk x z`. Rewrite using `[RingHom.map_det, RingHom.map_det, ← Matrix.det_mul, key, Matrix.det_submatrix_equiv_self]`. Both sides reduce to the same expression.
-/
theorem modeMatrixDet_eq_adjointDet : OmDet := by
  intro n ε
  refine ⟨(AP ε).det, fun k hk => ?_⟩
  let e : Mode ε ≃ {x : Fin n × Fin n // IsPhys ε x} :=
    Equiv.subtypeEquivRight (p := fun x : Fin n × Fin n => ε x.1 = true ∧ ε x.2 = false) (fun _ => Iff.rfl)
  have key : (ev k).mapMatrix (AP ε) * (ev k).mapMatrix (OmP ε) =
      (Matrix.of fun x y : {x : Fin n × Fin n // IsPhys ε x} =>
        (if x = y then (1 : ℂ) else 0) - k x.1.1 y.1.1 * star (k x.1.2 y.1.2)).submatrix e e := by
    ext x z
    rw [Matrix.mul_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AP, ev_OmP, Matrix.submatrix_apply, Matrix.of_apply,
      apply_ite (ev k), ev_X_inl, map_zero, e, EmbeddingLike.apply_eq_iff_eq]
    exact entry hk x z
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul, key, Matrix.det_submatrix_equiv_self]
  rfl

end GlobalTheory.PsCo.PcEF

end
