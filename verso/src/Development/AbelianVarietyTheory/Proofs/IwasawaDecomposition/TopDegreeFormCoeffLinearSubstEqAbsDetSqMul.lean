import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodMetric

section Subst

variable {n : ℕ}

namespace LinSubst

def rowSel (c : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i => Pi.single (c i) 1

/- English proof (translation)
Simplify using `[topCoeff, coeff_add, mul_add, Finset.sum_add_distrib]`.
-/
theorem topCoeff_add (P Q : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (P + Q) = topCoeff P + topCoeff Q := by
  simp [topCoeff, coeff_add, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [topCoeff, coeff_C_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem topCoeff_C_mul (a : ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) : topCoeff (C a * P) = a * topCoeff P := by
  simp only [topCoeff, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [topCoeff, coeff_sum, Finset.mul_sum]`. Conclude with `Finset.sum_comm`.
-/
theorem topCoeff_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, topCoeff (f i) := by
  simp only [topCoeff, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [Finsupp.finset_sum_apply]`. Rewrite using `[Finset.sum_comm]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem sum_apply_sum_single {k : ℕ} (f : Fin k → Fin n × Fin n) :
    ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x = k := by
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  simp [Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[monomial_sum_one]`. Both sides reduce to the same expression.
-/
theorem prod_X_eq_monomial' {ι : Type} [Fintype ι] (f : ι → Fin n × Fin n) :
    (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ i, Finsupp.single (f i) 1) 1 := by
  rw [monomial_sum_one]
  rfl

/- English proof (translation)
Rewrite using `[topCoeff]`. Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Rewrite using `[prod_X_eq_monomial', coeff_monomial, if_neg, mul_zero]`. Introduce `h`. Establish `: ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x = ∑ x, (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x` using `by rw [h]`.

Rewrite `this` using `[sum_apply_sum_single, sum_apply_sum_single (fun a => (a, w a))]`. Conclude with `hk this`.
-/
theorem topCoeff_prod_X_of_ne {k : ℕ} (hk : k ≠ n) (f : Fin k → Fin n × Fin n) :
    topCoeff (∏ i, X (f i)) = 0 := by
  rw [topCoeff]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [prod_X_eq_monomial', coeff_monomial, if_neg, mul_zero]
  intro h
  have : ∑ x, (∑ i, Finsupp.single (f i) 1 : Fin n × Fin n →₀ ℕ) x =
      ∑ x, (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x := by rw [h]
  rw [sum_apply_sum_single, sum_apply_sum_single (fun a => (a, w a))] at this
  exact hk this

/- English proof (translation)
Rewrite using `[Finsupp.finset_sum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem graph_apply (g : Fin n → Fin n) (x y : Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) (x, y) = if g x = y then 1 else 0 := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single x (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
  simp [Finsupp.single_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `e`. Use function extensionality and compare the values at `x`. Use `DFunLike.congr_fun e (x, g x)` as an intermediate fact. Rewrite `this` using `[graph_apply, graph_apply]`.

Assume the negation of the conclusion as `hne`. Rewrite `this` using `[if_pos rfl, if_neg (Ne.symm hne)]`. Conclude with `one_ne_zero this`. Introduce and unpack `rfl`. Both sides reduce to the same expression.
-/
theorem graph_eq_iff (g h : Fin n → Fin n) :
    (∑ a, Finsupp.single (a, g a) 1 : Fin n × Fin n →₀ ℕ) = ∑ a, Finsupp.single (a, h a) 1 ↔ g = h := by
  constructor
  · intro e
    funext x
    have := DFunLike.congr_fun e (x, g x)
    rw [graph_apply, graph_apply] at this
    by_contra hne
    rw [if_pos rfl, if_neg (Ne.symm hne)] at this
    exact one_ne_zero this
  · rintro rfl
    rfl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by`. Simplify using `only [Function.Injective, not_forall] at hc`. Take `⟨i, j, h, h'⟩` from `hc`. Conclude with `⟨i, j, h, h'⟩`. Conclude with `Matrix.det_zero_of_row_eq hne (by ext k; simp [rowSel, hij])`.
-/
theorem det_rowSel_of_not_injective {c : Fin n → Fin n} (hc : ¬ Function.Injective c) : (rowSel c).det = 0 := by
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, c i = c j ∧ i ≠ j := by
    simp only [Function.Injective, not_forall] at hc
    obtain ⟨i, j, h, h'⟩ := hc
    exact ⟨i, j, h, h'⟩
  exact Matrix.det_zero_of_row_eq hne (by ext k; simp [rowSel, hij])

/- English proof (translation)
Establish `: rowSel σ = σ.permMatrix ℂ`. Use extensionality with `i j`. Simplify using `[rowSel, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]`. Rewrite using `[this, Matrix.det_permutation]`.
-/
theorem det_rowSel_perm (σ : Equiv.Perm (Fin n)) : (rowSel σ).det = Equiv.Perm.sign σ := by
  have : rowSel σ = σ.permMatrix ℂ := by
    ext i j
    simp [rowSel, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Pi.single_apply, eq_comm]
  rw [this, Matrix.det_permutation]

/- English proof (translation)
Establish `h : (fun i => ∑ a, U i a • (Pi.single a 1 : Fin n → ℂ)) = U`. Use extensionality with `i j`. Simplify using `[Pi.single_apply]`. Use `conv_rhs => rw [← h]`. Express the relevant statement in the definitionally equal form `_ = (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _`.

Rewrite using `[← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[MultilinearMap.map_smul_univ, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem sum_prod_mul_det_rowSel (U : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c : Fin n → Fin n, (∏ i, U i (c i)) * (rowSel c).det = U.det := by
  have h : (fun i => ∑ a, U i a • (Pi.single a 1 : Fin n → ℂ)) = U := by
    ext i j
    simp [Pi.single_apply]
  conv_rhs => rw [← h]
  change _ = (Matrix.detRowAlternating : AlternatingMap ℂ (Fin n → ℂ) ℂ (Fin n)) _
  rw [← AlternatingMap.coe_multilinearMap, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

/- English proof (translation)
Rewrite using `[topCoeff, prod_X_eq_monomial']`. Simplify using `only [coeff_monomial]`. Distinguish the cases in `hc : Function.Injective c`. Establish `hcb : Function.Bijective c` using `Finite.injective_iff_bijective.mp hc set σ := Equiv.ofBijective c hcb with hσ`. Establish `e : (∑ i, Finsupp.single (c i, d i) 1 : Fin n × Fin n →₀ ℕ) = ∑ a, Finsupp.single (a, (d ∘ σ.symm) a) 1` using `by conv_rhs => rw [← Equiv.sum_comp σ]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[σ]`. Repeatedly rewrite using `[e, graph_eq_iff]`. Establish `hcσ : rowSel c = rowSel ⇑σ` using `rfl`. Rewrite using `[hcσ, det_rowSel_perm]`.

Distinguish the cases in `hd : Function.Injective d`. Use `set τ := Equiv.ofBijective d (Finite.injective_iff_bijective.mp hd) with hτ`. Establish `hdτ : d ∘ σ.symm = ⇑(σ.symm.trans τ)`. Use extensionality with `a`. Simplify using `[τ]`.

Establish `hdτ' : rowSel d = rowSel ⇑τ` using `rfl`. Rewrite using `[hdτ, hdτ', det_rowSel_perm]`. Simplify using `only [DFunLike.coe_fn_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Simplify using `[Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, mul_comm]`. Rewrite using `[det_rowSel_of_not_injective hd, mul_zero]`.

Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Apply `hd` to reduce the goal to its premises. Establish `: d = w ∘ σ`.

Rewrite using `[← h]`. Use extensionality with `a`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `w.injective.comp σ.injective`.

Rewrite using `[det_rowSel_of_not_injective hc, zero_mul]`. Use `Finset.sum_eq_zero fun w _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, ∀ i, c i ≠ x := by`.

Establish `: ¬ Function.Surjective c` using `fun hs => hc (Finite.injective_iff_surjective.mpr hs)`. Simplify `this` using `[Function.Surjective]`. Establish `h1` using `DFunLike.congr_fun h (x, w x)`. Rewrite `h1` using `[graph_apply, if_pos rfl, Finsupp.finset_sum_apply]`. Simplify using `[Finsupp.single_apply, hx] at h1`.
-/
theorem topCoeff_prod_X_pair (c d : Fin n → Fin n) :
    topCoeff (∏ i, X (c i, d i)) = (rowSel c).det * (rowSel d).det := by
  rw [topCoeff, prod_X_eq_monomial']
  simp only [coeff_monomial]
  by_cases hc : Function.Injective c
  · have hcb : Function.Bijective c := Finite.injective_iff_bijective.mp hc
    set σ := Equiv.ofBijective c hcb with hσ
    have e : (∑ i, Finsupp.single (c i, d i) 1 : Fin n × Fin n →₀ ℕ) =
        ∑ a, Finsupp.single (a, (d ∘ σ.symm) a) 1 := by
      conv_rhs => rw [← Equiv.sum_comp σ]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [σ]
    simp_rw [e, graph_eq_iff]
    have hcσ : rowSel c = rowSel ⇑σ := rfl
    rw [hcσ, det_rowSel_perm]
    by_cases hd : Function.Injective d
    · set τ := Equiv.ofBijective d (Finite.injective_iff_bijective.mp hd) with hτ
      have hdτ : d ∘ σ.symm = ⇑(σ.symm.trans τ) := by
        ext a
        simp [τ]
      have hdτ' : rowSel d = rowSel ⇑τ := rfl
      rw [hdτ, hdτ', det_rowSel_perm]
      simp only [DFunLike.coe_fn_eq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      simp [Equiv.Perm.sign_trans, Equiv.Perm.sign_symm, mul_comm]
    · rw [det_rowSel_of_not_injective hd, mul_zero]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg, mul_zero]
      intro h
      apply hd
      have : d = w ∘ σ := by
        rw [← h]
        ext a
        simp
      rw [this]
      exact w.injective.comp σ.injective
  · rw [det_rowSel_of_not_injective hc, zero_mul]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro h
    obtain ⟨x, hx⟩ : ∃ x, ∀ i, c i ≠ x := by
      have : ¬ Function.Surjective c := fun hs => hc (Finite.injective_iff_surjective.mpr hs)
      simpa [Function.Surjective] using this
    have h1 := DFunLike.congr_fun h (x, w x)
    rw [graph_apply, if_pos rfl, Finsupp.finset_sum_apply] at h1
    simp [Finsupp.single_apply, hx] at h1

/- English proof (translation)
Simplify using `[rowSel, Matrix.mul_apply, Pi.single_apply]`.
-/
theorem rowSel_mul_apply (c : Fin n → Fin n) (M : Matrix (Fin n) (Fin n) ℂ) (i b : Fin n) :
    (rowSel c * M) i b = M (c i) b := by
  simp [rowSel, Matrix.mul_apply, Pi.single_apply]

/- English proof (translation)
Proceed by induction on `u using Finsupp.induction with`. Consider the case `zero => exact ⟨0, Fin.elim0, by simp⟩`. Consider the case `single_add x m u _ _ ih`. Take `⟨k, f, hf⟩` from `ih`. Use `⟨m + k, Fin.append (fun _ => x) f, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.prod_univ_add, monomial_single_add, hf]`. Simplify using `[Fin.append_left, Fin.append_right]`.
-/
theorem exists_prod_X (u : Fin n × Fin n →₀ ℕ) :
    ∃ (k : ℕ) (f : Fin k → Fin n × Fin n), monomial u (1 : ℂ) = ∏ i, X (f i) := by
  induction u using Finsupp.induction with
  | zero => exact ⟨0, Fin.elim0, by simp⟩
  | single_add x m u _ _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    refine ⟨m + k, Fin.append (fun _ => x) f, ?_⟩
    rw [Fin.prod_univ_add, monomial_single_add, hf]
    simp [Fin.append_left, Fin.append_right]

/- English proof (translation)
Rewrite using `[map_prod]`. Simplify using `only [aeval_X]`. Establish `e : ∀ i, (∑ a, ∑ b, C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) = ∑ p : Fin n × Fin n, C (J (f i).1 p.1 * starRingEnd ℂ (J (f i).2 p.2)) * X p` using `fun i => (Fintype.sum_prod_type' (fun a b => C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b))).symm`. Repeatedly rewrite using `[e]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]`.

Repeatedly rewrite using `[Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]`. Distinguish the cases in `hk : k = n`. Substitute `hk` using the available equality. Rewrite using `[← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp, Fintype.sum_prod_type]`. Simplify using `only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]`.

Repeatedly rewrite using `[topCoeff_prod_X_pair]`. Establish `key : ∀ (c d : Fin k → Fin k), (∏ i, J (f i).1 (c i) * starRingEnd ℂ (J (f i).2 (d i))) * ((rowSel c).det * (rowSel d).det) = ((∏ i, (rowSel (fun i => (f i).1) * J) i (c i)) * (rowSel c).det) * ((∏ i, (rowSel (fun i => (f i).2) * J.map (starRingEnd ℂ)) i (d i)) * (rowSel d).det)`. Introduce `c d`. Simplify using `only [rowSel_mul_apply, Matrix.map_apply, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum, sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, Matrix.det_mul, Matrix.det_mul]`. Establish `hc : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Rewrite using `[hc]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `[topCoeff_prod_X_of_ne hk]`.
-/
theorem topCoeff_subst_prod (J : Matrix (Fin n) (Fin n) ℂ) {k : ℕ} (f : Fin k → Fin n × Fin n) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (∏ i, X (f i) : MvPolynomial (Fin n × Fin n) ℂ)) = J.det * starRingEnd ℂ J.det * topCoeff (∏ i, X (f i)) := by
  rw [map_prod]
  simp only [aeval_X]
  have e : ∀ i, (∑ a, ∑ b, C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b) :
      MvPolynomial (Fin n × Fin n) ℂ) =
      ∑ p : Fin n × Fin n, C (J (f i).1 p.1 * starRingEnd ℂ (J (f i).2 p.2)) * X p := fun i =>
    (Fintype.sum_prod_type' (fun a b => C (J (f i).1 a * starRingEnd ℂ (J (f i).2 b)) * X (a, b))).symm
  simp_rw [e]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
  simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
  by_cases hk : k = n
  · subst hk
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp, Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, J (f i).1 (c i) * starRingEnd ℂ (J (f i).2 (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (rowSel (fun i => (f i).1) * J) i (c i)) * (rowSel c).det) *
        ((∏ i, (rowSel (fun i => (f i).2) * J.map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [rowSel_mul_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, Matrix.det_mul, Matrix.det_mul]
    have hc : (J.map (starRingEnd ℂ)).det = starRingEnd ℂ J.det := by
      rw [RingHom.map_det]
      rfl
    rw [hc]
    ring
  · simp [topCoeff_prod_X_of_ne hk]

end LinSubst

open LinSubst

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial u r`. Take `⟨k, f, hf⟩` from `exists_prod_X u`. Establish `e : (monomial u r : MvPolynomial (Fin n × Fin n) ℂ) = C r * ∏ i, X (f i)`. Rewrite using `[← hf, C_mul_monomial, mul_one]`.

Rewrite using `[e, map_mul, aeval_C, algebraMap_eq, topCoeff_C_mul, topCoeff_C_mul, topCoeff_subst_prod]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add p q hp hq`. Rewrite using `[map_add, topCoeff_add, topCoeff_add, hp, hq, mul_add]`.
-/
theorem topCoeff_subst_conj (J : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    topCoeff (aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)) P) =
      J.det * starRingEnd ℂ J.det * topCoeff P := by
  induction P using MvPolynomial.induction_on' with
  | monomial u r =>
    obtain ⟨k, f, hf⟩ := exists_prod_X u
    have e : (monomial u r : MvPolynomial (Fin n × Fin n) ℂ) = C r * ∏ i, X (f i) := by
      rw [← hf, C_mul_monomial, mul_one]
    rw [e, map_mul, aeval_C, algebraMap_eq, topCoeff_C_mul, topCoeff_C_mul, topCoeff_subst_prod]
    ring
  | add p q hp hq =>
    rw [map_add, topCoeff_add, topCoeff_add, hp, hq, mul_add]

end Subst

end GlobalTheory.GoodMetric
