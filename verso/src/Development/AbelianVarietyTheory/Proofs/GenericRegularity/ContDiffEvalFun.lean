import Mathlib

open Filter Topology

namespace GlobalTheory.SmoothPolynomialEvaluation

noncomputable def evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) : ℂ :=
  Polynomial.eval v.2 (Polynomial.map (MvPolynomial.eval v.1) p)

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C a => simpa using contDiff_const`. Consider the case `add p q hp hq => simpa using hp.add hq`. Consider the case `mul_X p i hp`. Establish `hX : ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => v.1 i)` using `(contDiff_apply ℂ ℂ i).comp contDiff_fst`.

Simplify using `using hp.mul hX`.
-/
lemma contDiff_mvEval {d : ℕ} (q : MvPolynomial (Fin d) ℂ) :
    ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => MvPolynomial.eval v.1 q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    have hX : ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => v.1 i) := (contDiff_apply ℂ ℂ i).comp contDiff_fst
    simpa using hp.mul hX

/- English proof (translation)
Establish `h : evalFun p = fun v => ∑ i ∈ Finset.range (p.natDegree + 1), MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i`. Use function extensionality and compare the values at `v`. Unfold `evalFun`. Rewrite using `[Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]`. Simplify using `[Polynomial.coeff_map]`.

Rewrite using `[h]`. Apply `ContDiff.sum` to reduce the goal to its premises. Introduce `i _`. Conclude with `(contDiff_mvEval _).mul (contDiff_snd.pow i)`.
-/
lemma contDiff_evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (evalFun p) := by
  have h : evalFun p = fun v => ∑ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v
    unfold evalFun
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
    simp [Polynomial.coeff_map]
  rw [h]
  apply ContDiff.sum
  intro i _
  exact (contDiff_mvEval _).mul (contDiff_snd.pow i)

/- English proof (translation)
Introduce `d p x₀ a h0 h1`. Use `set q := Polynomial.map (MvPolynomial.eval x₀) p with hq`. Establish `hFs : HasStrictFDerivAt (evalFun p) (fderiv ℂ (evalFun p) (x₀, a)) (x₀, a)` using `(contDiff_evalFun p).contDiffAt.hasStrictFDerivAt one_ne_zero`. Establish `hder : fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ = (1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q))`. Establish `h1' : HasFDerivAt (fun z => evalFun p (x₀, z)) (fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) a` using `hFs.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x₀ a)`.

Establish `h2' : HasFDerivAt (fun z => evalFun p (x₀, z)) ((1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q))) a` using `(Polynomial.hasDerivAt q a).hasFDerivAt`. Conclude with `h1'.unique h2'`. Establish `hinv : (fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible`. Rewrite using `[hder]`. Use `⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩` and prove the remaining obligations.

Use `ext`. Simplify using the standard rewrite rules. Set `φ` to `hFs.implicitFunctionDataOfProdDomain hinv`. Use `⟨fun x => (φ.toOpenPartialHomeomorph.symm (evalFun p (x₀, a), x)).2, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(hFs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds` as an intermediate fact.

Conclude with `this.mp rfl`. Use `⟨{x | (evalFun p (x₀, a), x) ∈ φ.toOpenPartialHomeomorph.target}, ?_, ?_⟩` and prove the remaining obligations. Apply `IsOpen.mem_nhds` to reduce the goal to its premises. Conclude with `φ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)`. Conclude with `φ.map_pt_mem_toOpenPartialHomeomorph_target`.

Conclude with `continuous_snd.comp_continuousOn (φ.toOpenPartialHomeomorph.continuousOn_symm.comp (by fun_prop) (fun x hx => hx))`. Use `hFs.eventually_apply_implicitFunctionOfProdDomain hinv filter_upwards [this] with x hx` as an intermediate fact. Conclude with `hx.trans h0`.
-/
theorem main : ∀ {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x₀ : Fin d → ℂ) (a : ℂ),
    Polynomial.eval a (Polynomial.map (MvPolynomial.eval x₀) p) = (0 : ℂ) →
    Polynomial.eval a ((Polynomial.derivative : Polynomial ℂ → Polynomial ℂ)
      (Polynomial.map (MvPolynomial.eval x₀) p)) ≠ (0 : ℂ) →
    ∃ (y : (Fin d → ℂ) → ℂ), y x₀ = a ∧ (∃ s ∈ nhds x₀, ContinuousOn y s) ∧
      ∀ᶠ (x : Fin d → ℂ) in nhds x₀,
        Polynomial.eval (y x) (Polynomial.map (MvPolynomial.eval x) p) = (0 : ℂ) := by
  intro d p x₀ a h0 h1
  set q := Polynomial.map (MvPolynomial.eval x₀) p with hq
  have hFs : HasStrictFDerivAt (evalFun p) (fderiv ℂ (evalFun p) (x₀, a)) (x₀, a) :=
    (contDiff_evalFun p).contDiffAt.hasStrictFDerivAt one_ne_zero
  have hder : fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ
      = (1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q)) := by
    have h1' : HasFDerivAt (fun z => evalFun p (x₀, z))
        (fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) a :=
      hFs.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x₀ a)
    have h2' : HasFDerivAt (fun z => evalFun p (x₀, z))
        ((1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q))) a :=
      (Polynomial.hasDerivAt q a).hasFDerivAt
    exact h1'.unique h2'
  have hinv : (fderiv ℂ (evalFun p) (x₀, a) ∘L
      ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hder]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext; simp
  let φ := hFs.implicitFunctionDataOfProdDomain hinv
  refine ⟨fun x => (φ.toOpenPartialHomeomorph.symm (evalFun p (x₀, a), x)).2, ?_, ?_, ?_⟩
  · have := (hFs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds
    exact this.mp rfl
  · refine ⟨{x | (evalFun p (x₀, a), x) ∈ φ.toOpenPartialHomeomorph.target}, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact φ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)
      · exact φ.map_pt_mem_toOpenPartialHomeomorph_target
    · exact continuous_snd.comp_continuousOn
        (φ.toOpenPartialHomeomorph.continuousOn_symm.comp (by fun_prop) (fun x hx => hx))
  · have := hFs.eventually_apply_implicitFunctionOfProdDomain hinv
    filter_upwards [this] with x hx
    exact hx.trans h0

end GlobalTheory.SmoothPolynomialEvaluation
