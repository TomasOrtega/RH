import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section
namespace GlobalTheory.FockDegree
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg

/- English proof (translation)
Establish `hU : ∀ t y z, inner ℂ (U t y) (U t z) = inner ℂ y z` using `fun t y z => LinearIsometry.inner_map_map (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H) y z`. Establish `h1 : HasDerivAt (fun t : ℝ => K (U t v)) (K ((Complex.I * b) • v)) 0` using `(K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv`. Establish `h2` using `HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) x) h1`. Establish `h3 : HasDerivAt (fun t : ℝ => U (-t) x) ((-1 : ℝ) • ((Complex.I * a) • x)) 0`. Establish `hx' : HasDerivAt (fun t : ℝ => U t x) ((Complex.I * a) • x) (-0)`.

Rewrite using `[neg_zero]`. Conclude with `hx`. Conclude with `hx'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))`. Establish `h4` using `HasDerivAt.inner ℂ h3 (hasDerivAt_const (0 : ℝ) (K v))`. Establish `heq : (fun t : ℝ => inner ℂ x (K (U t v))) = fun t : ℝ => inner ℂ (U (-t) x) (K v)`.

Use function extensionality and compare the values at `t`. Rewrite using `[hK, ← hU t (U (-t) x) (K v), hinv]`. Rewrite `h2` using `[heq]`. Establish `h5` using `h2.unique h4`. Simplify using `only [map_smul, inner_smul_right, inner_zero_left, inner_zero_right, add_zero, zero_add, neg_smul, one_smul, inner_neg_left, inner_smul_left, map_mul, Complex.conj_I, Complex.conj_ofReal] at h5`.

Establish `h6 : (Complex.I * ((b : ℂ) - a)) * inner ℂ x (K v) = 0`. Take the linear combination `h5`. Break down `mul_eq_zero.1 h6 with h | h` into its components or cases. It suffices to derive a contradiction. Break down `mul_eq_zero.1 h with h | h` into its components or cases.

Conclude with `Complex.I_ne_zero h`. Conclude with `hab (by exact_mod_cast (sub_eq_zero.1 h).symm)`. Conclude with `h`.
-/
theorem inner_eq_zero_of_deriv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : ℝ → H →L[ℂ] H) (hn : ∀ t x, ‖U t x‖ = ‖x‖) (hinv : ∀ t x, U t (U (-t) x) = x)
    (K : H →L[ℂ] H) (hK : ∀ t x, K (U t x) = U t (K x)) (x v : H) (a b : ℝ) (hab : a ≠ b)
    (hx : HasDerivAt (fun t : ℝ => U t x) ((Complex.I * a) • x) 0)
    (hv : HasDerivAt (fun t : ℝ => U t v) ((Complex.I * b) • v) 0) :
    inner ℂ x (K v) = 0 := by
  have hU : ∀ t y z, inner ℂ (U t y) (U t z) = inner ℂ y z := fun t y z =>
    LinearIsometry.inner_map_map (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H) y z
  have h1 : HasDerivAt (fun t : ℝ => K (U t v)) (K ((Complex.I * b) • v)) 0 :=
    (K.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hv
  have h2 := HasDerivAt.inner ℂ (hasDerivAt_const (0 : ℝ) x) h1
  have h3 : HasDerivAt (fun t : ℝ => U (-t) x) ((-1 : ℝ) • ((Complex.I * a) • x)) 0 := by
    have hx' : HasDerivAt (fun t : ℝ => U t x) ((Complex.I * a) • x) (-0) := by
      rw [neg_zero]; exact hx
    exact hx'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have h4 := HasDerivAt.inner ℂ h3 (hasDerivAt_const (0 : ℝ) (K v))
  have heq : (fun t : ℝ => inner ℂ x (K (U t v))) = fun t : ℝ => inner ℂ (U (-t) x) (K v) := by
    funext t
    rw [hK, ← hU t (U (-t) x) (K v), hinv]
  rw [heq] at h2
  have h5 := h2.unique h4
  simp only [map_smul, inner_smul_right, inner_zero_left, inner_zero_right, add_zero, zero_add,
    neg_smul, one_smul, inner_neg_left, inner_smul_left, map_mul, Complex.conj_I,
    Complex.conj_ofReal] at h5
  have h6 : (Complex.I * ((b : ℂ) - a)) * inner ℂ x (K v) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.1 h6 with h | h
  · exfalso
    rcases mul_eq_zero.1 h with h | h
    · exact Complex.I_ne_zero h
    · exact hab (by exact_mod_cast (sub_eq_zero.1 h).symm)
  · exact h

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Jm_eq_diagonal (p q : ℕ) :
    Jm p q = Matrix.diagonal (fun a => if a.isLeft then (1 : ℂ) else -1) := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `h : (Jm p q).conjTranspose = Jm p q`. Rewrite using `[Jm_eq_diagonal, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `by_cases ha : a.isLeft <;> simp [ha]`.

Simplify using `[upq, Matrix.conjTranspose_smul, h]`.
-/
theorem smul_I_Jm_mem (p q : ℕ) (t : ℝ) : t • (Complex.I • Jm p q) ∈ upq p q := by
  have h : (Jm p q).conjTranspose = Jm p q := by
    rw [Jm_eq_diagonal, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases ha : a.isLeft <;> simp [ha]
  simp [upq, Matrix.conjTranspose_smul, h]

/- English proof (translation)
Simplify using `using smul_I_Jm_mem p q 1`.
-/
theorem I_Jm_mem (p q : ℕ) : Complex.I • Jm p q ∈ upq p q := by
  simpa using smul_I_Jm_mem p q 1

/- English proof (translation)
Rewrite using `[Jm_eq_diagonal]`. Use `show X * _ = _ * X`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`.

Simplify using the standard rewrite rules. Rewrite using `[hX _ _ (by simp [sameBlock])]; simp`. Rewrite using `[hX _ _ (by simp [sameBlock])]; simp`. Simplify using the standard rewrite rules.
-/
theorem commute_Jm_of_isKC {p q : ℕ} (X : Mat p q) (hX : IsKC X) : Commute X (Jm p q) := by
  rw [Jm_eq_diagonal]
  show X * _ = _ * X
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b
  · simp
  · rw [hX _ _ (by simp [sameBlock])]; simp
  · rw [hX _ _ (by simp [sameBlock])]; simp
  · simp

/- English proof (translation)
Apply `T.emb.injective` to reduce the goal to its premises. Simplify using `only [map_mul, Prod.mk.injEq]`. Use `⟨?_, mul_comm _ _⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, T.expt_cov _ (smul_I_Jm_mem p q t)]`.

Conclude with `(((commute_Jm_of_isKC _ hk).smul_right Complex.I).smul_right t).exp_right.eq`.
-/
theorem commute_expt {p q : ℕ} (T : GrpData p q) (k : T.G) (hk : k ∈ T.Kset) (t : ℝ) :
    k * T.expt (t • (Complex.I • Jm p q)) = T.expt (t • (Complex.I • Jm p q)) * k := by
  apply T.emb.injective
  simp only [map_mul, Prod.mk.injEq]
  refine ⟨?_, mul_comm _ _⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, T.expt_cov _ (smul_I_Jm_mem p q t)]
  exact (((commute_Jm_of_isKC _ hk).smul_right Complex.I).smul_right t).exp_right.eq

/- English proof (translation)
Rewrite using `[omAct_apply, LinearMap.sum_apply]`. Establish `: ∀ l : Ln p q r s, (∑ l', (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm (Complex.I • Jm _ _)) l l' • omE l l') (MvPolynomial.monomial α 1) = (Complex.I * (((α l : ℕ) : ℂ) + 1 / 2)) • (MvPolynomial.monomial α 1 : Pol p q r s)`. Introduce `l`. Rewrite using `[Finset.sum_eq_single l]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Jm_eq_diagonal, Matrix.smul_apply, Matrix.diagonal_apply_eq, lineEquiv_isLeft, LinearMap.smul_apply]`.

Consider the cases of `hl : linePos l`. Rewrite using `[omE_neg l hl, smul_smul]`. Use `congr 1`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[omE_pos l hl, smul_smul]`. Use `congr 1`. Simplify using the standard rewrite rules. Introduce `l' _ hl'`. Establish `: lineEquiv p q r s l ≠ lineEquiv p q r s l'` using `fun h => hl' ((lineEquiv p q r s).injective h).symm`.

Simplify using `[Jm_eq_diagonal, Matrix.diagonal_apply_ne _ this]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_congr rfl fun l _ => this l, ← Finset.sum_smul, ← Finset.mul_sum]`. Use `congr 2`. Rewrite using `[Finsupp.degree_eq_sum, Finset.sum_add_distrib]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omAct_I_Jm_monomial (p q r s : ℕ) (α : Ln p q r s →₀ ℕ) :
    omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) (MvPolynomial.monomial α 1) =
    (Complex.I * ((α.degree : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2 : ℝ)) •
      MvPolynomial.monomial α 1 := by
  rw [omAct_apply, LinearMap.sum_apply]
  have : ∀ l : Ln p q r s, (∑ l', (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) l l' • omE l l') (MvPolynomial.monomial α 1) =
      (Complex.I * (((α l : ℕ) : ℂ) + 1 / 2)) • (MvPolynomial.monomial α 1 : Pol p q r s) := by
    intro l
    rw [Finset.sum_eq_single l]
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, Jm_eq_diagonal,
        Matrix.smul_apply, Matrix.diagonal_apply_eq, lineEquiv_isLeft, LinearMap.smul_apply]
      cases hl : linePos l
      · rw [omE_neg l hl, smul_smul]; congr 1; simp; ring
      · rw [omE_pos l hl, smul_smul]; congr 1; simp
    · intro l' _ hl'
      have : lineEquiv p q r s l ≠ lineEquiv p q r s l' :=
        fun h => hl' ((lineEquiv p q r s).injective h).symm
      simp [Jm_eq_diagonal, Matrix.diagonal_apply_ne _ this]
    · simp
  rw [Finset.sum_congr rfl fun l _ => this l, ← Finset.sum_smul, ← Finset.mul_sum]
  congr 2
  rw [Finsupp.degree_eq_sum, Finset.sum_add_distrib]
  simp
  ring

/- English proof (translation)
Establish `hP' : P.IsHomogeneous d` using `hP`. Use `conv_lhs => rw [P.as_sum]`. Use `conv_rhs => rw [P.as_sum]`. Rewrite using `[map_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun α hα => ?_` and prove the remaining obligations.

Establish `hd : α.degree = d`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Conclude with `hP' (MvPolynomial.mem_support_iff.1 hα)`. Establish `: (MvPolynomial.monomial α (P.coeff α) : Pol p q r s) = P.coeff α • MvPolynomial.monomial α 1`. Rewrite using `[MvPolynomial.smul_monomial]`.

Simplify using the standard rewrite rules. Rewrite using `[this, map_smul, omAct_I_Jm_monomial, hd, smul_comm]`.
-/
theorem omAct_I_Jm_homog (p q r s d : ℕ) (P : Pol p q r s) (hP : P ∈ homog (Ix p q × Ix r s) d) :
    omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm
      (Complex.I • Jm _ _)) P =
    (Complex.I * ((d : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2 : ℝ)) • P := by
  have hP' : P.IsHomogeneous d := hP
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd : α.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP' (MvPolynomial.mem_support_iff.1 hα)
  have : (MvPolynomial.monomial α (P.coeff α) : Pol p q r s) =
      P.coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial]; simp
  rw [this, map_smul, omAct_I_Jm_monomial, hd, smul_comm]

/- English proof (translation)
Use `inner_eq_zero_of_deriv (fun t => F.Om (T0.expt (t • (Complex.I • Jm _ _)))) (fun t x => F.isom _ x) ?_ (F.Om k) ?_ _ _ ((d' : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2) ((d : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2) ?_ ?_ ?_` and prove the remaining obligations. Introduce `t x`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, ← T0.expt_add _ (I_Jm_mem _ _), add_neg_cancel, zero_smul, T0.expt_zero, map_one]`. Both sides reduce to the same expression. Introduce `t x`.

Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, commute_expt T0 k hk, map_mul]`. Both sides reduce to the same expression. Introduce `h`. Conclude with `hd (by exact_mod_cast add_right_cancel h)`. Use `F.der _ (I_Jm_mem _ _) R` as an intermediate fact.

Rewrite `this` using `[omAct_I_Jm_homog p q r s d' R hR, map_smul]`. Then use the resulting hypothesis. Use `F.der _ (I_Jm_mem _ _) P` as an intermediate fact. Rewrite `this` using `[omAct_I_Jm_homog p q r s d P hP, map_smul]`. Then use the resulting hypothesis.
-/
theorem inner_Om_eq_zero {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)}
    {T1 : GrpData p q} {T2 : GrpData r s} (F : FockData T0 T1 T2) (k : T0.G) (hk : k ∈ T0.Kset)
    {d d' : ℕ} (hd : d' ≠ d) (R : Pol p q r s) (hR : R ∈ homog (Ix p q × Ix r s) d')
    (P : Pol p q r s) (hP : P ∈ homog (Ix p q × Ix r s) d) :
    inner ℂ (F.ι R) (F.Om k (F.ι P)) = 0 := by
  refine inner_eq_zero_of_deriv (fun t => F.Om (T0.expt (t • (Complex.I • Jm _ _))))
    (fun t x => F.isom _ x) ?_ (F.Om k) ?_ _ _
    ((d' : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2)
    ((d : ℝ) + (Fintype.card (Ln p q r s) : ℝ) / 2) ?_ ?_ ?_
  · intro t x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T0.expt_add _ (I_Jm_mem _ _),
      add_neg_cancel, zero_smul, T0.expt_zero, map_one]
    rfl
  · intro t x
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, commute_expt T0 k hk, map_mul]
    rfl
  · intro h
    exact hd (by exact_mod_cast add_right_cancel h)
  · have := F.der _ (I_Jm_mem _ _) R
    rwa [omAct_I_Jm_homog p q r s d' R hR, map_smul] at this
  · have := F.der _ (I_Jm_mem _ _) P
    rwa [omAct_I_Jm_homog p q r s d P hP, map_smul] at this

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[map_one, Units.val_one, Matrix.one_apply_ne]`. Introduce and unpack `rfl`. Apply the tactic sequence `rcases a with a | a <;> simp [sameBlock] at hab`.
-/
theorem one_mem_Kset {p q : ℕ} (T : GrpData p q) : (1 : T.G) ∈ T.Kset := by
  intro a b hab
  rw [map_one, Units.val_one, Matrix.one_apply_ne]
  rintro rfl
  rcases a with a | a <;> simp [sameBlock] at hab

instance finiteDimensional_homog (σ : Type) [Finite σ] (d : ℕ) :
    FiniteDimensional ℂ (homog σ d) :=
  Module.Finite.iff_fg.2 (MvPolynomial.homogeneousSubmodule_fg σ ℂ d)

/- English proof (translation)
Introduce `p q r s T0 T1 T2 F k hk d P hP`. Set `E : Submodule ℂ F.H` to `(homog (Ix p q × Ix r s) d).map F.ι`. Use `haveI : FiniteDimensional ℂ E := inferInstance`. Take `⟨e, he, w', hw', hw⟩` from `E.exists_add_mem_mem_orthogonal (F.Om k (F.ι P))`. Take `⟨Q, hQ, rfl⟩` from `he`.

Use `⟨Q, hQ, ?_⟩` and prove the remaining obligations. Establish `h0 : ∀ R, inner ℂ (F.ι R) w' = 0`. Introduce `R`. Proceed by induction on `R using MvPolynomial.induction_on' with`. Consider the case `add R S hR hS => rw [map_add, inner_add_left, hR, hS, add_zero]`.

Consider the case `monomial α c`. Establish `hm : MvPolynomial.monomial α c ∈ homog (Ix p q × Ix r s) α.degree` using `MvPolynomial.isHomogeneous_monomial c rfl`. Distinguish the cases in `h : α.degree = d`. Conclude with `hw' _ ⟨_, h ▸ hm, rfl⟩`. Establish `h1` using `inner_Om_eq_zero F k hk h _ hm P hP`.

Establish `h2` using `inner_Om_eq_zero F 1 (one_mem_Kset T0) h _ hm Q hQ`. Rewrite `h2` using `[map_one, ContinuousLinearMap.one_apply]`. Rewrite `h1` using `[hw, inner_add_right, h2, zero_add]`. Then use the resulting hypothesis. Establish `: w' = 0`. Establish `hc : IsClosed {x : F.H | inner ℂ x w' = 0}` using `isClosed_eq (by fun_prop) continuous_const`.

Establish `hsub : Set.range F.ι ⊆ {x : F.H | inner ℂ x w' = 0}`. Introduce and unpack `_ ⟨R, rfl⟩`. Conclude with `h0 R`. Use `hc.closure_subset_iff.2 hsub (F.dense w')` as an intermediate fact. Conclude with `inner_self_eq_zero.1 this`.

Rewrite using `[hw, this, add_zero]`.
-/
theorem Om_Kset_homog : ∀ (p q r s : ℕ) (T0 : GrpData (p * r + q * s) (p * s + q * r)) (T1 : GrpData p q) (T2 : GrpData r s) (F : FockData T0 T1 T2), ∀ k ∈ T0.Kset, ∀ (d : ℕ), ∀ P ∈ homog (Ix p q × Ix r s) d, ∃ Q ∈ homog (Ix p q × Ix r s) d, F.Om k (F.ι P) = F.ι Q := by
  intro p q r s T0 T1 T2 F k hk d P hP
  let E : Submodule ℂ F.H := (homog (Ix p q × Ix r s) d).map F.ι
  haveI : FiniteDimensional ℂ E := inferInstance
  obtain ⟨e, he, w', hw', hw⟩ := E.exists_add_mem_mem_orthogonal (F.Om k (F.ι P))
  obtain ⟨Q, hQ, rfl⟩ := he
  refine ⟨Q, hQ, ?_⟩
  have h0 : ∀ R, inner ℂ (F.ι R) w' = 0 := by
    intro R
    induction R using MvPolynomial.induction_on' with
    | add R S hR hS => rw [map_add, inner_add_left, hR, hS, add_zero]
    | monomial α c =>
      have hm : MvPolynomial.monomial α c ∈ homog (Ix p q × Ix r s) α.degree :=
        MvPolynomial.isHomogeneous_monomial c rfl
      by_cases h : α.degree = d
      · exact hw' _ ⟨_, h ▸ hm, rfl⟩
      · have h1 := inner_Om_eq_zero F k hk h _ hm P hP
        have h2 := inner_Om_eq_zero F 1 (one_mem_Kset T0) h _ hm Q hQ
        rw [map_one, ContinuousLinearMap.one_apply] at h2
        rwa [hw, inner_add_right, h2, zero_add] at h1
  have : w' = 0 := by
    have hc : IsClosed {x : F.H | inner ℂ x w' = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    have hsub : Set.range F.ι ⊆ {x : F.H | inner ℂ x w' = 0} := by
      rintro _ ⟨R, rfl⟩; exact h0 R
    have := hc.closure_subset_iff.2 hsub (F.dense w')
    exact inner_self_eq_zero.1 this
  rw [hw, this, add_zero]

end GlobalTheory.FockDegree
