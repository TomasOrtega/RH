import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.RealPar Matrix

namespace GlobalTheory.CoverExp

variable {p q : ℕ}

/- English proof (translation)
Use `set c : ℂ := X.trace / 2 with hc`. Use `set f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • X)) : ℂˣ) : ℂ) with hf`. Establish `hd : ∀ t, HasDerivAt f (f t * c) t`. Introduce `t`. Establish `h0 : HasDerivAt f c 0` using `Cover.hasDerivAt_sq (T := T) hX`.

Establish `h1 : HasDerivAt (fun s : ℝ => f (s - t)) c t` using `HasDerivAt.comp_sub_const t t (f := f) (f' := c) (by rw [sub_self]; exact h0)`. Establish `h2 : f = fun s => f t * f (s - t)`. Use function extensionality and compare the values at `s`. Simplify using `only [hf]`. Rewrite using `[← Units.val_mul, ← map_mul, ← T.expt_add X hX, add_sub_cancel]`.

Establish `h3` using `h1.const_mul (f t)`. Rewrite `h3` using `[← h2]`. Conclude with `h3`. Establish `hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) * f t) 0 t`. Introduce `t`.

Establish `h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t`. Establish `: HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t`. Simplify using `using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg`. Conclude with `this.cexp`. Conclude with `(h1.fun_mul (hd t)).congr_deriv (by ring)`.

Establish `h` using `is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0`. Simplify using `only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, Units.val_one] at h`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]`. Use `_ = _ := by rw [h, mul_one]`.
-/
theorem sq_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    ((T.sq (T.expt X) : ℂˣ) : ℂ) = Complex.exp (X.trace / 2) := by
  set c : ℂ := X.trace / 2 with hc
  set f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • X)) : ℂˣ) : ℂ) with hf
  have hd : ∀ t, HasDerivAt f (f t * c) t := by
    intro t
    have h0 : HasDerivAt f c 0 := Cover.hasDerivAt_sq (T := T) hX
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) c t :=
      HasDerivAt.comp_sub_const t t (f := f) (f' := c) (by rw [sub_self]; exact h0)
    have h2 : f = fun s => f t * f (s - t) := by
      funext s
      simp only [hf]
      rw [← Units.val_mul, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    have h3 := h1.const_mul (f t)
    rw [← h2] at h3
    exact h3
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) * f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    exact (h1.fun_mul (hd t)).congr_deriv (by ring)
  have h := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, Units.val_one] at h
  calc _ = Complex.exp c * (Complex.exp (-c) * ((T.sq (T.expt X) : ℂˣ) : ℂ)) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = _ := by rw [h, mul_one]

/- English proof (translation)
Set `a : Ix p q` to `finSumFinEquiv.symm ⟨0, hn⟩`. Use `⟨TorusWt.torX (Pi.single a (2 * Real.pi)), TorusWt.torX_mem _, ?_, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[T.expt_cov _ (TorusWt.torX_mem _), TorusWt.torX, Matrix.exp_diagonal, Units.val_one, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Rewrite using `[Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]`. Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Simplify using `[Complex.exp_two_pi_mul_I]`.

Simplify using `[h]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[sq_expt T (TorusWt.torX_mem _), TorusWt.torX, Matrix.trace_diagonal, Finset.sum_eq_single a]`. Rewrite using `[Pi.single_eq_same, show ((2 * Real.pi : ℝ) : ℂ) * Complex.I / 2 = Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]`. Simplify using the standard rewrite rules.

Introduce `b _ h`. Simplify using `[h]`. Simplify using the standard rewrite rules.
-/
theorem exists_expt_ker (hn : 1 ≤ p + q) (T : GrpData p q) :
    ∃ Z ∈ upq p q, T.cov (T.expt Z) = 1 ∧ T.sq (T.expt Z) = -1 := by
  let a : Ix p q := finSumFinEquiv.symm ⟨0, hn⟩
  refine ⟨TorusWt.torX (Pi.single a (2 * Real.pi)), TorusWt.torX_mem _, ?_, ?_⟩
  · apply Units.ext
    rw [T.expt_cov _ (TorusWt.torX_mem _), TorusWt.torX, Matrix.exp_diagonal, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext b
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    by_cases h : b = a
    · subst h
      simp [Complex.exp_two_pi_mul_I]
    · simp [h]
  · apply Units.ext
    rw [sq_expt T (TorusWt.torX_mem _), TorusWt.torX, Matrix.trace_diagonal, Finset.sum_eq_single a]
    · rw [Pi.single_eq_same, show ((2 * Real.pi : ℝ) : ℂ) * Complex.I / 2 = Real.pi * Complex.I by push_cast; ring,
        Complex.exp_pi_mul_I]
      simp
    · intro b _ h
      simp [h]
    · simp

/- English proof (translation)
Use `⟨finSumFinEquiv, fun i => (finSumFinEquiv.symm i).isLeft, fun i => by simp, fun j => by simp, ?_⟩` and prove the remaining obligations. Introduce and unpack `(a | a) (b | b) h`. Establish `h' : a < b` using `h`. Conclude with `h'`. Conclude with `h.elim`.

Conclude with `h.elim`. Establish `h' : a < b` using `h`. Conclude with `Nat.add_lt_add_left h' p`.
-/
theorem exists_blockOrd (p q : ℕ) : ∃ (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool), BlockOrd e ε := by
  refine ⟨finSumFinEquiv, fun i => (finSumFinEquiv.symm i).isLeft, fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) h
  · have h' : a < b := h
    exact h'
  · exact h.elim
  · exact h.elim
  · have h' : a < b := h
    exact Nat.add_lt_add_left h' p

/- English proof (translation)
Introduce `a b hab`. Use `congrFun (congrFun h a) b` as an intermediate fact. Rewrite `this` using `[Matrix.neg_apply, KStabLie.Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Simplify using `only [Sum.elim_inl] at this`.

Take the linear combination `(1 / 2 : ℂ) * this`. Simplify using `[sameBlock] at hab`. Simplify using `[sameBlock] at hab`. Simplify using `only [Sum.elim_inr] at this`. Take the linear combination `(-1 / 2 : ℂ) * this`.
-/
theorem isPC_of_anticomm {X : Mat p q} (h : X * Jm p q = -(Jm p q * X)) : IsPC X := by
  intro a b hab
  have := congrFun (congrFun h a) b
  rw [Matrix.neg_apply, KStabLie.Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  rcases a with a | a <;> rcases b with b | b
  · simp only [Sum.elim_inl] at this
    linear_combination (1 / 2 : ℂ) * this
  · simp [sameBlock] at hab
  · simp [sameBlock] at hab
  · simp only [Sum.elim_inr] at this
    linear_combination (-1 / 2 : ℂ) * this

/- English proof (translation)
Take `⟨e, ε, hb⟩` from `exists_blockOrd p q`. Take `⟨Z, X, hZ, hX, h⟩` from `Formalism.REAL.genExp_of Formalism.REAL.compact_exponential_surjective _ ε _ ((hb.inUJ_iff g).2 hg)`. Take `⟨Z, rfl⟩` from `(Matrix.reindex e e).surjective Z`. Take `⟨X, rfl⟩` from `(Matrix.reindex e e).surjective X`. Establish `hG : ∀ Y : Mat p q, Formalism.REAL.inG ε (Matrix.reindex e e Y) → Y ∈ upq p q`.

Introduce `Y h1`. Unfold `Formalism.REAL.inG at h1`. Rewrite `h1` using `[← hb.reindex_Jm, Matrix.conjTranspose_reindex]`. Apply `(Matrix.reindex e e).injective` to reduce the goal to its premises. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1`.

Simplify using `only [Matrix.reindex_apply]`. Rewrite using `[Matrix.submatrix_add]`. Conclude with `h1`. Establish `hexp : ∀ Y : Mat p q, NormedSpace.exp (Matrix.reindex e e Y) = Matrix.reindex e e (NormedSpace.exp Y)`. Introduce `Y`.

Use `open scoped Matrix.Norms.Operator in`. Conclude with `(NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by`. Conclude with `LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) Y).symm`. Use `⟨Z, hG Z hZ.1, (KStabLie.isKC_iff Z).2 ?_, X, ⟨hG X hX.1, isPC_of_anticomm ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h2` using `hZ.2`.

Rewrite `h2` using `[← hb.reindex_Jm]`. Apply `(Matrix.reindex e e).injective` to reduce the goal to its premises. Simplify `h2` using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`. Establish `h2` using `hX.2`. Rewrite `h2` using `[← hb.reindex_Jm]`.

Apply `(Matrix.reindex e e).injective` to reduce the goal to its premises. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h2`. Conclude with `h2`. Rewrite `h` using `[hexp, hexp]`. Apply `(Matrix.reindex e e).injective` to reduce the goal to its premises.

Simplify `h` using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`.
-/
theorem exists_exp_mul_exp {g : Mat p q} (hg : gᴴ * Jm p q * g = Jm p q) :
    ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, g = NormedSpace.exp Z * NormedSpace.exp X := by
  obtain ⟨e, ε, hb⟩ := exists_blockOrd p q
  obtain ⟨Z, X, hZ, hX, h⟩ := Formalism.REAL.genExp_of Formalism.REAL.compact_exponential_surjective _ ε _ ((hb.inUJ_iff g).2 hg)
  obtain ⟨Z, rfl⟩ := (Matrix.reindex e e).surjective Z
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective X
  have hG : ∀ Y : Mat p q, Formalism.REAL.inG ε (Matrix.reindex e e Y) → Y ∈ upq p q := by
    intro Y h1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_add]
    exact h1
  have hexp : ∀ Y : Mat p q, NormedSpace.exp (Matrix.reindex e e Y) = Matrix.reindex e e (NormedSpace.exp Y) := by
    intro Y
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) Y).symm
  refine ⟨Z, hG Z hZ.1, (KStabLie.isKC_iff Z).2 ?_, X, ⟨hG X hX.1, isPC_of_anticomm ?_⟩, ?_⟩
  · have h2 := hZ.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h2
  · have h2 := hX.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h2
    exact h2
  · rw [hexp, hexp] at h
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h

/- English proof (translation)
Introduce `p q hn T`. Establish `key : ∀ g : T.G, ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, T.cov g = T.cov (T.expt Z) * T.cov (T.expt X)`. Introduce `g`. Take `⟨Z, hZ, hK, X, hX, h⟩` from `exists_exp_mul_exp ((mem_Upq _).1 (T.cov_mem g))`. Conclude with `⟨Z, hZ, hK, X, hX, Units.ext (by rw [Units.val_mul, T.expt_cov Z hZ, T.expt_cov X hX.1, h])⟩`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[eq_top_iff]`. Introduce `g _`. Take `⟨Z, hZ, -, X, hX, h⟩` from `key g`. Take `⟨C, hC, hC1, hC2⟩` from `exists_expt_ker hn T`.

Establish `hm : ∀ Y ∈ upq p q, T.expt Y ∈ Subgroup.closure (T.expt '' upq p q)` using `fun Y hY => Subgroup.subset_closure ⟨Y, hY, rfl⟩`. Establish `hx` using `Subgroup.mul_mem _ (hm Z hZ) (hm X hX.1)`. Rewrite `h` using `[← map_mul]`. Use `set x := T.expt Z * T.expt X`. Establish `h2 : ((T.sq g : ℂˣ) : ℂ) ^ 2 = ((T.sq x : ℂˣ) : ℂ) ^ 2` using `by rw [T.sq_sq, T.sq_sq, h]`.

Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3` into its components or cases. Rewrite using `[Cover.ext_of h (Units.ext h3)]`. Conclude with `hx`. Establish `: g = T.expt C * x` using `Cover.ext_of (by rw [map_mul, hC1, one_mul, h]) (Units.ext (by rw [map_mul, hC2, h3]; simp))`. Rewrite using `[this]`.

Conclude with `Subgroup.mul_mem _ (hm C hC) hx`. Introduce `g`. Take `⟨Z, hZ, hK, X, hX, h⟩` from `key g`. Use `⟨g * (T.expt X)⁻¹, ?_, X, hX, by simp⟩` and prove the remaining obligations. Establish `h1` using `KStabLie.expt_mem T hZ hK 1`.

Rewrite `h1` using `[one_smul]`. Express the relevant statement in the definitionally equal form `IsKC _`. Rewrite using `[map_mul, map_inv, h, mul_inv_cancel_right]`. Conclude with `h1`.
-/
theorem closure_expt_eq_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q,
    Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  intro p q hn T
  have key : ∀ g : T.G, ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, T.cov g = T.cov (T.expt Z) * T.cov (T.expt X) := by
    intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := exists_exp_mul_exp ((mem_Upq _).1 (T.cov_mem g))
    exact ⟨Z, hZ, hK, X, hX, Units.ext (by rw [Units.val_mul, T.expt_cov Z hZ, T.expt_cov X hX.1, h])⟩
  constructor
  · rw [eq_top_iff]
    intro g _
    obtain ⟨Z, hZ, -, X, hX, h⟩ := key g
    obtain ⟨C, hC, hC1, hC2⟩ := exists_expt_ker hn T
    have hm : ∀ Y ∈ upq p q, T.expt Y ∈ Subgroup.closure (T.expt '' upq p q) :=
      fun Y hY => Subgroup.subset_closure ⟨Y, hY, rfl⟩
    have hx := Subgroup.mul_mem _ (hm Z hZ) (hm X hX.1)
    rw [← map_mul] at h
    set x := T.expt Z * T.expt X
    have h2 : ((T.sq g : ℂˣ) : ℂ) ^ 2 = ((T.sq x : ℂˣ) : ℂ) ^ 2 := by rw [T.sq_sq, T.sq_sq, h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · rw [Cover.ext_of h (Units.ext h3)]
      exact hx
    · have : g = T.expt C * x := Cover.ext_of (by rw [map_mul, hC1, one_mul, h])
        (Units.ext (by rw [map_mul, hC2, h3]; simp))
      rw [this]
      exact Subgroup.mul_mem _ (hm C hC) hx
  · intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := key g
    refine ⟨g * (T.expt X)⁻¹, ?_, X, hX, by simp⟩
    have h1 := KStabLie.expt_mem T hZ hK 1
    rw [one_smul] at h1
    change IsKC _
    rw [map_mul, map_inv, h, mul_inv_cancel_right]
    exact h1

end GlobalTheory.CoverExp

end
