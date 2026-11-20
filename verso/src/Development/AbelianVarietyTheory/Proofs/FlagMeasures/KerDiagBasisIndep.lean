import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Dec

/- English proof (translation)
Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 hv`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hy.inner_right_fintype]`.
-/
theorem kerDiag_expand {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y : Fin D → H) (hy : Orthonormal ℂ y) (v : H) (hv : v ∈ Submodule.span ℂ (Set.range y)) :
    v = ∑ i, ⟪y i, v⟫_ℂ • y i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hy.inner_right_fintype]

/- English proof (translation)
Use `set u : H := ∑ i, (starRingEnd ℂ) (a i) • y i with hu`. Establish `h1 : ∀ j, ‖b j‖ = ‖⟪y' j, u⟫_ℂ‖`. Introduce `j`. Rewrite using `[norm_inner_symm, hb, hu, sum_inner]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, Complex.conj_conj, mul_comm]`. Establish `h2 : ‖u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2`. Establish `h3 : ⟪u, u⟫_ℂ = ∑ i, ((‖a i‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[hu, hy.inner_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite `h3` using `[inner_self_eq_norm_sq_to_K]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[Complex.ofReal_sum, ← h3, Complex.ofReal_pow]`.

Both sides reduce to the same expression. Simplify using `only [h1]`. Rewrite using `[← h2]`. Conclude with `hy'.sum_inner_products_le u`.
-/
theorem kerDiag_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : ℕ}
    (y y' : Fin D → H) (hy : Orthonormal ℂ y) (hy' : Orthonormal ℂ y') (a b : Fin D → ℂ)
    (hb : ∀ j, b j = ∑ i, ⟪y i, y' j⟫_ℂ * a i) :
    ∑ j, ‖b j‖ ^ 2 ≤ ∑ i, ‖a i‖ ^ 2 := by
  set u : H := ∑ i, (starRingEnd ℂ) (a i) • y i with hu
  have h1 : ∀ j, ‖b j‖ = ‖⟪y' j, u⟫_ℂ‖ := by
    intro j
    rw [norm_inner_symm, hb, hu, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, Complex.conj_conj, mul_comm]
  have h2 : ‖u‖ ^ 2 = ∑ i, ‖a i‖ ^ 2 := by
    have h3 : ⟪u, u⟫_ℂ = ∑ i, ((‖a i‖ ^ 2 : ℝ) : ℂ) := by
      rw [hu, hy.inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.conj_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [inner_self_eq_norm_sq_to_K] at h3
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, ← h3, Complex.ofReal_pow]
    rfl
  simp only [h1]
  rw [← h2]
  exact hy'.sum_inner_products_le u

/- English proof (translation)
Use `⟨h.1.add (continuous_const.mul h'.1), fun γ hγ x => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [h.2.1 γ hγ x, h'.2.1 γ hγ x]`. Use `filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', h.2.2, h'.2.2] with x h1 h2 h3 h4`. Rewrite using `[h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]`.
-/
theorem kerDiag_add_rep (B : RowsAut) (F F' : B.I.L2 B.μf B.fund) (f f' : B.I.GA → ℂ) (c : ℂ)
    (h : IsContRep B F f) (h' : IsContRep B F' f') :
    IsContRep B (F + c • F') (fun x => f x + c * f' x) := by
  refine ⟨h.1.add (continuous_const.mul h'.1), fun γ hγ x => ?_, ?_⟩
  · simp only [h.2.1 γ hγ x, h'.2.1 γ hγ x]
  · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', h.2.2, h'.2.2] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using hg`. Consider the case `insert a s ha ih`. Use `kerDiag_add_rep B _ _ _ _ (c a) ih (h a)` as an intermediate fact. Simplify using `only [Finset.sum_insert ha]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Use function extensionality and compare the values at `x`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kerDiag_sum_rep (B : RowsAut) {ι : Type} (s : Finset ι) (y : ι → B.I.L2 B.μf B.fund)
    (f : ι → B.I.GA → ℂ) (c : ι → ℂ) (F : B.I.L2 B.μf B.fund) (g : B.I.GA → ℂ)
    (hg : IsContRep B F g) (h : ∀ i, IsContRep B (y i) (f i)) :
    IsContRep B (F + ∑ i ∈ s, c i • y i) (fun x => g x + ∑ i ∈ s, c i * f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hg
  | insert a s ha ih =>
    have := kerDiag_add_rep B _ _ _ _ (c a) ih (h a)
    simp only [Finset.sum_insert ha]
    convert this using 1
    · abel
    · funext x; ring

/- English proof (translation)
Establish `e` using `kerDiag_expand y hy (y' j) (hs (Submodule.subset_span ⟨j, rfl⟩))`. Establish `h1` using `kerDiag_sum_rep B Finset.univ y f (fun i => ⟪y i, y' j⟫_ℂ) _ _ (h' j) h`. Rewrite `h1` using `[← e]`. Establish `h2` using `kerDiag_add_rep B _ _ _ _ 1 (h' j) (h' j)`. Rewrite `h2` using `[one_smul]`.

Establish `h3` using `congrFun ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B _ _ h2).2.1 _ h1) x`. Simplify using `only [one_mul, add_right_inj] at h3`. Conclude with `h3.symm`.
-/
theorem kerDiag_vals (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund)
    (f f' : Fin D → B.I.GA → ℂ) (hy : Orthonormal ℂ y)
    (hs : Submodule.span ℂ (Set.range y') ≤ Submodule.span ℂ (Set.range y))
    (h : ∀ i, IsContRep B (y i) (f i)) (h' : ∀ i, IsContRep B (y' i) (f' i)) (j : Fin D)
    (x : B.I.GA) : f' j x = ∑ i, ⟪y i, y' j⟫_ℂ * f i x := by
  have e := kerDiag_expand y hy (y' j) (hs (Submodule.subset_span ⟨j, rfl⟩))
  have h1 := kerDiag_sum_rep B Finset.univ y f (fun i => ⟪y i, y' j⟫_ℂ) _ _ (h' j) h
  rw [← e] at h1
  have h2 := kerDiag_add_rep B _ _ _ _ 1 (h' j) (h' j)
  rw [one_smul] at h2
  have h3 := congrFun ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B _ _ h2).2.1 _ h1) x
  simp only [one_mul, add_right_inj] at h3
  exact h3.symm

/- English proof (translation)
Introduce `B D y y' f f' hy hy' hs h x`. Apply `le_antisymm` to reduce the goal to its premises. Conclude with `kerDiag_le y' y hy' hy _ _ fun j => kerDiag_vals B D y' y f' f hy' hs.le (fun i => (h i).2) (fun i => (h i).1) j x`. Conclude with `kerDiag_le y y' hy hy' _ _ fun j => kerDiag_vals B D y y' f f' hy hs.ge (fun i => (h i).1) (fun i => (h i).2) j x`.
-/
theorem kerDiag_basis_indep : ∀ (B : RowsAut) (D : ℕ) (y y' : Fin D → B.I.L2 B.μf B.fund) (f f' : Fin D → B.I.GA → ℂ), Orthonormal ℂ y → Orthonormal ℂ y' → Submodule.span ℂ (Set.range y) = Submodule.span ℂ (Set.range y') → (∀ i, IsContRep B (y i) (f i) ∧ IsContRep B (y' i) (f' i)) → ∀ x, ∑ i, ‖f i x‖ ^ 2 = ∑ i, ‖f' i x‖ ^ 2 := by
  intro B D y y' f f' hy hy' hs h x
  apply le_antisymm
  · exact kerDiag_le y' y hy' hy _ _ fun j =>
      kerDiag_vals B D y' y f' f hy' hs.le (fun i => (h i).2) (fun i => (h i).1) j x
  · exact kerDiag_le y y' hy hy' _ _ fun j =>
      kerDiag_vals B D y y' f f' hy hs.ge (fun i => (h i).1) (fun i => (h i).2) j x

end GlobalTheory.Dec
