import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianFormFiniteZerosOnLineCmExt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.PlaneNorm
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GramVec

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {M : ℕ}
  {J : Matrix (Fin M) (Fin M) E}

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_add_smul_right (z u v : Fin M → E) (c : E) :
    hE σ J z (u + c • v) = hE σ J z u + c * hE σ J z v := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.coe_coe]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_add_smul_left (z u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) z = hE σ J u z + σ c * hE σ J v z := by
  simp only [hE, Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.coe_coe]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[hE, GlobalTheory.HermLineZeros.hform_expand]`. Both sides reduce to the same expression.
-/
theorem hE_add_smul_self (u v : Fin M → E) (c : E) :
    hE σ J (u + c • v) (u + c • v) =
      hE σ J u u + c * hE σ J u v + σ c * hE σ J v u + σ c * c * hE σ J v v := by
  rw [hE, GlobalTheory.HermLineZeros.hform_expand]
  rfl

/- English proof (translation)
The claim follows from `GlobalTheory.HermLineZeros.hform_single _ J i j`.
-/
theorem hE_single (i j : Fin M) : hE σ J (Pi.single i 1) (Pi.single j 1) = J i j :=
  GlobalTheory.HermLineZeros.hform_single _ J i j

/- English proof (translation)
Unfold `gram2E`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermitianGramDetTwoVectors_comm (x z : Fin M → E) : gram2E σ J x z = gram2E σ J z x := by
  unfold gram2E; ring

noncomputable def gramPoly (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (z a b : Fin M → E) : Polynomial E :=
  Polynomial.C (hE σ J z z) * (Polynomial.C (hE σ J a a) + Polynomial.X * Polynomial.C (hE σ J a b + hE σ J b a)
      + Polynomial.X ^ 2 * Polynomial.C (hE σ J b b))
    - (Polynomial.C (hE σ J z a) + Polynomial.X * Polynomial.C (hE σ J z b))
      * (Polynomial.C (hE σ J a z) + Polynomial.X * Polynomial.C (hE σ J b z))

/- English proof (translation)
Unfold `gram2E gramPoly`. Rewrite using `[hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, ht]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermitianGramDetTwoVectors_eval_line (z a b : Fin M → E) (t : E) (ht : σ t = t) :
    gram2E σ J z (a + t • b) = (gramPoly σ J z a b).eval t := by
  unfold gram2E gramPoly
  rw [hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, ht]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  ring

section CM

variable [NumberField F] [NumberField E]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨d, hd⟩` from `GlobalTheory.HermLineZeros.exists_conj_ne h`. Use `set a : Fin M → E := fun i => hE σ J (Pi.single i 1) z`. Use `set b : Fin M → E := fun j => hE σ J z (Pi.single j 1)`.

Establish `hdiag : ∀ i, hE σ J z z * J i i - b i * a i = 0` using `fun i => by`. Use `hc (Pi.single i 1)` as an intermediate fact. Simplify `this` using `[gram2E, hE_single]`. Establish `key : hE σ J z z • J = Matrix.vecMulVec a b`. Use extensionality with `i j`.

Establish `e1` using `hc (Pi.single i 1 + (1 : E) • Pi.single j 1)`. Establish `e2` using `hc (Pi.single i 1 + d • Pi.single j 1)`. Simplify using `only [gram2E, hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, hE_single, map_one] at e1 e2`. Establish `e0i` using `hdiag i`. Establish `e0j` using `hdiag j`.

Establish `: (d - σ d) * (hE σ J z z * J i j - a i * b j) = 0`. Simplify using `only [a, b] at e0i e0j ⊢`. Take the linear combination `e2 - e0i - σ d * d * e0j - σ d * (e1 - e0i - e0j)`. Break down `mul_eq_zero.1 this with h0 | h0` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h0).symm hd`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]`. Conclude with `sub_eq_zero.1 h0`. Establish `hdet : (hE σ J z z • J).det ≠ 0`. Rewrite using `[Matrix.det_smul]`. Conclude with `mul_ne_zero (pow_ne_zero _ hz) hJ.2`.

Establish `hunit : IsUnit (hE σ J z z • J)` using `(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)`. Establish `hr` using `Matrix.rank_of_isUnit _ hunit`. Establish `hle : (Matrix.vecMulVec a b).rank ≤ 1`. Rewrite using `[Matrix.vecMulVec_eq Unit]`. Conclude with `(Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))`.

Rewrite `hr` using `[key, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_gram2E_ne (h : IsCMExt F E σ) (hM : 2 ≤ M) (hJ : IsHermND σ J)
    (z : Fin M → E) (hz : hE σ J z z ≠ 0) : ∃ w, gram2E σ J z w ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨d, hd⟩ := GlobalTheory.HermLineZeros.exists_conj_ne h
  set a : Fin M → E := fun i => hE σ J (Pi.single i 1) z
  set b : Fin M → E := fun j => hE σ J z (Pi.single j 1)
  have hdiag : ∀ i, hE σ J z z * J i i - b i * a i = 0 := fun i => by
    have := hc (Pi.single i 1)
    simpa [gram2E, hE_single] using this
  have key : hE σ J z z • J = Matrix.vecMulVec a b := by
    ext i j
    have e1 := hc (Pi.single i 1 + (1 : E) • Pi.single j 1)
    have e2 := hc (Pi.single i 1 + d • Pi.single j 1)
    simp only [gram2E, hE_add_smul_self, hE_add_smul_right, hE_add_smul_left, hE_single,
      map_one] at e1 e2
    have e0i := hdiag i
    have e0j := hdiag j
    have : (d - σ d) * (hE σ J z z * J i j - a i * b j) = 0 := by
      simp only [a, b] at e0i e0j ⊢
      linear_combination e2 - e0i - σ d * d * e0j - σ d * (e1 - e0i - e0j)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (sub_eq_zero.1 h0).symm hd
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
      exact sub_eq_zero.1 h0
  have hdet : (hE σ J z z • J).det ≠ 0 := by
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hz) hJ.2
  have hunit : IsUnit (hE σ J z z • J) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hr := Matrix.rank_of_isUnit _ hunit
  have hle : (Matrix.vecMulVec a b).rank ≤ 1 := by
    rw [Matrix.vecMulVec_eq Unit]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width _).trans (by simp))
  rw [key, Fintype.card_fin] at hr
  omega

end CM

end GlobalTheory.GramVec

open GlobalTheory.GramVec in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h M J hM hJ x y hx hy`. Take `⟨w0, h0⟩` from `exists_gram2E_ne h hM hJ x hx`. Take `⟨w1, h1⟩` from `exists_gram2E_ne h hM hJ y hy`. Use `set Px := gramPoly σ J x w0 (w1 - w0)`. Use `set Py := gramPoly σ J y w0 (w1 - w0)`.

Establish `hPx : Px ≠ 0`. Introduce `h0'`. Apply `h0` to reduce the goal to its premises. Use `hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) x w0 (w1 - w0) 0 (map_zero σ)` as an intermediate fact. Rewrite `this` using `[zero_smul, add_zero]`.

Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `Polynomial.eval 0 Px = 0`. Rewrite using `[h0', Polynomial.eval_zero]`. Establish `hPy : Py ≠ 0`. Introduce `h1'`.

Apply `h1` to reduce the goal to its premises. Use `hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) y w0 (w1 - w0) 1 (map_one σ)` as an intermediate fact. Rewrite `this` using `[one_smul, add_sub_cancel]`. Rewrite using `[this]`. Express the relevant statement in the definitionally equal form `Polynomial.eval 1 Py = 0`.

Rewrite using `[h1', Polynomial.eval_zero]`. Establish `hfin : {f : F | Px.IsRoot (algebraMap F E f) ∨ Py.IsRoot (algebraMap F E f)}.Finite`. Use `((Polynomial.finite_setOf_isRoot hPx).union (Polynomial.finite_setOf_isRoot hPy)).preimage (FaithfulSMul.algebraMap_injective F E).injOn` as an intermediate fact. Conclude with `this`. Use `haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective`.

Take `⟨f, hf⟩` from `hfin.infinite_compl.nonempty`. Simplify using `only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, Polynomial.IsRoot.def] at hf`. Establish `hfix : σ (algebraMap F E f) = algebraMap F E f` using `σ.commutes f`. Use `⟨w0 + algebraMap F E f • (w1 - w0), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]`.

Conclude with `hf.1`. Rewrite using `[hermitianGramDetTwoVectors_comm, hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]`. Conclude with `hf.2`.
-/
theorem GlobalTheory.exists_common_hermitianGramDetTwoVectors_ne' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ w : Fin M → E, gram2E σ J x w ≠ 0 ∧ gram2E σ J w y ≠ 0 := by
  intro F E _ _ _ _ _ σ h M J hM hJ x y hx hy
  obtain ⟨w0, h0⟩ := exists_gram2E_ne h hM hJ x hx
  obtain ⟨w1, h1⟩ := exists_gram2E_ne h hM hJ y hy
  set Px := gramPoly σ J x w0 (w1 - w0)
  set Py := gramPoly σ J y w0 (w1 - w0)
  have hPx : Px ≠ 0 := by
    intro h0'
    apply h0
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) x w0 (w1 - w0) 0 (map_zero σ)
    rw [zero_smul, add_zero] at this
    rw [this]; change Polynomial.eval 0 Px = 0; rw [h0', Polynomial.eval_zero]
  have hPy : Py ≠ 0 := by
    intro h1'
    apply h1
    have := hermitianGramDetTwoVectors_eval_line (σ := σ) (J := J) y w0 (w1 - w0) 1 (map_one σ)
    rw [one_smul, add_sub_cancel] at this
    rw [this]; change Polynomial.eval 1 Py = 0; rw [h1', Polynomial.eval_zero]
  have hfin : {f : F | Px.IsRoot (algebraMap F E f) ∨ Py.IsRoot (algebraMap F E f)}.Finite := by
    have := ((Polynomial.finite_setOf_isRoot hPx).union (Polynomial.finite_setOf_isRoot hPy)).preimage
      (FaithfulSMul.algebraMap_injective F E).injOn
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨f, hf⟩ := hfin.infinite_compl.nonempty
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, Polynomial.IsRoot.def] at hf
  have hfix : σ (algebraMap F E f) = algebraMap F E f := σ.commutes f
  refine ⟨w0 + algebraMap F E f • (w1 - w0), ?_, ?_⟩
  · rw [hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.1
  · rw [hermitianGramDetTwoVectors_comm, hermitianGramDetTwoVectors_eval_line _ _ _ _ hfix]; exact hf.2
