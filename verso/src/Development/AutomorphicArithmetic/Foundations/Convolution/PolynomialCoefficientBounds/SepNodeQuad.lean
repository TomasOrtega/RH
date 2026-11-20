import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.TwoNode
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebClosed

open MvPolynomial Filter Topology

private noncomputable def UpperTheory.ConvolutionTheory.FX.sepNode (y : ℝ) (b : Bool) : ℝ :=
  if b then y + Real.sqrt (y ^ 2 - 1) else y - Real.sqrt (y ^ 2 - 1)

/- English proof (translation)
Establish `hs : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1` using `Real.sq_sqrt (by nlinarith)`. Apply the tactic sequence `cases b <;> simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] <;>`. Take the linear combination `hs`.
-/
private theorem UpperTheory.ConvolutionTheory.FX.sepNode_quad (y : ℝ) (hy : 1 < y) (b : Bool) :
    UpperTheory.ConvolutionTheory.FX.sepNode y b ^ 2 + 1 = 2 * y * UpperTheory.ConvolutionTheory.FX.sepNode y b := by
  have hs : Real.sqrt (y ^ 2 - 1) ^ 2 = y ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  cases b <;> simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] <;>
    linear_combination hs

/- English proof (translation)
Establish `q` using `UpperTheory.ConvolutionTheory.FX.sepNode_quad y hy b`. Establish `q'` using `UpperTheory.ConvolutionTheory.FX.sepNode_quad y' hy' b'`. Rewrite `q'` using `[← h]`. Establish `ht : UpperTheory.ConvolutionTheory.FX.sepNode y b ≠ 0`. Introduce `h0`.

Rewrite `q` using `[h0]`. Evaluate the numerical expressions using `at q`. Establish `hyy : y = y'`. Apply `mul_right_cancel₀ ht` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Substitute `hyy` using the available equality. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Establish `hs : 0 < Real.sqrt (y ^ 2 - 1)` using `Real.sqrt_pos.mpr (by nlinarith)`. Apply the tactic sequence `cases b <;> cases b' <;>`. Apply the tactic sequence `simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] at h <;>`.

Apply the tactic sequence `first | rfl | (exfalso; linarith)`.
-/
private theorem UpperTheory.ConvolutionTheory.FX.sepNode_inj (y y' : ℝ) (hy : 1 < y) (hy' : 1 < y') (b b' : Bool)
    (h : UpperTheory.ConvolutionTheory.FX.sepNode y b = UpperTheory.ConvolutionTheory.FX.sepNode y' b') : y = y' ∧ b = b' := by
  have q := UpperTheory.ConvolutionTheory.FX.sepNode_quad y hy b
  have q' := UpperTheory.ConvolutionTheory.FX.sepNode_quad y' hy' b'
  rw [← h] at q'
  have ht : UpperTheory.ConvolutionTheory.FX.sepNode y b ≠ 0 := by
    intro h0
    rw [h0] at q
    norm_num at q
  have hyy : y = y' := by
    apply mul_right_cancel₀ ht
    linarith
  subst hyy
  refine ⟨rfl, ?_⟩
  have hs : 0 < Real.sqrt (y ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  cases b <;> cases b' <;>
    simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false] at h <;>
    first | rfl | (exfalso; linarith)

/- English proof (translation)
Introduce `η hη I _ a ζ ha _ hinj`. Establish `hy : ∀ i, 1 < 2 * a i / η - 1` using `fun i => by`. Establish `: 2 < 2 * a i / η`. Rewrite using `[lt_div_iff₀ hη]`. Combine the linear relations using `[ha i]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨s₀, K, hK⟩` from `UpperTheory.ConvolutionTheory.FX.two_node (I × Bool) (fun p => ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ)) (fun p => ζ p.1) (by`. Introduce and unpack `⟨i, b⟩ ⟨i', b'⟩ h`. Simplify using `only [Prod.mk.injEq, Complex.ofReal_inj] at h`. Take `⟨h1, h2⟩` from `UpperTheory.ConvolutionTheory.FX.sepNode_inj _ _ (hy i) (hy i') _ _ h.1`.

Establish `h3 : a i = a i'`. Clear denominators, using `at h1` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : i = i'` using `hinj (Prod.ext h3 h.2)`. Rewrite using `[h4, h2])`.

Use `⟨s₀, 2 * K, fun m j c ε hε i => ?_⟩` and prove the remaining obligations. Establish `key` using `hK (fun p => c p.1 * ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ) ^ m * ζ p.1 ^ j / 2) ε (by`. Introduce `s hs s' hs'`. Use `le_of_eq_of_le ?_ (hε s hs s' hs')` and prove the remaining obligations. Use `congr 1`.

Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[((UpperTheory.ConvolutionTheory.FX.cheb_facts (m + s) _).2 (hy i).le).1, Fintype.sum_bool]`. Simplify using `only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false]`. Generalize the expression as in `Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r`.

Generalize the expression as in `2 * a i / η - 1 = y`. Use `push_cast`. Use the proof step `ring) (i, true)`. Simplify using `only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true] at key`. Establish `hyi` using `hy i`.

Establish `hr` using `Real.sqrt_nonneg ((2 * a i / η - 1) ^ 2 - 1)`. Generalize the expression as in `Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r at key hr`. Generalize the expression as in `2 * a i / η - 1 = y at key hyi`. Rewrite `key` using `[norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ y + r), Complex.norm_two]`. Establish `h5 : ‖c i‖ * y ^ m * ‖ζ i‖ ^ j ≤ ‖c i‖ * (y + r) ^ m * ‖ζ i‖ ^ j`.

Establish `: y ≤ y + r` using `by linarith`. Establish `: 0 ≤ y` using `by linarith`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.ConvolutionTheory.FX.separate0 :
    ∀ (η : ℝ), 0 < η → ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∃ (s₀ : ℕ) (K : ℝ), ∀ (m j : ℕ) (c : I → ℂ) (ε : ℝ),
    (∀ s ≤ s₀, ∀ s' ≤ s₀, ‖∑ i, c i * (((Polynomial.Chebyshev.T ℝ ((m + s : ℕ) : ℤ)).eval (2 * a i / η - 1) : ℝ) : ℂ) * ζ i ^ (j + s')‖ ≤ ε) →
    ∀ i, ‖c i‖ * (2 * a i / η - 1) ^ m * ‖ζ i‖ ^ j ≤ K * ε := by
  intro η hη I _ a ζ ha _ hinj
  have hy : ∀ i, 1 < 2 * a i / η - 1 := fun i => by
    have : 2 < 2 * a i / η := by
      rw [lt_div_iff₀ hη]
      linarith [ha i]
    linarith
  obtain ⟨s₀, K, hK⟩ := UpperTheory.ConvolutionTheory.FX.two_node (I × Bool)
    (fun p => ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ)) (fun p => ζ p.1) (by
      rintro ⟨i, b⟩ ⟨i', b'⟩ h
      simp only [Prod.mk.injEq, Complex.ofReal_inj] at h
      obtain ⟨h1, h2⟩ := UpperTheory.ConvolutionTheory.FX.sepNode_inj _ _ (hy i) (hy i') _ _ h.1
      have h3 : a i = a i' := by
        field_simp at h1
        linarith
      have h4 : i = i' := hinj (Prod.ext h3 h.2)
      rw [h4, h2])
  refine ⟨s₀, 2 * K, fun m j c ε hε i => ?_⟩
  have key := hK (fun p => c p.1 *
      ((UpperTheory.ConvolutionTheory.FX.sepNode (2 * a p.1 / η - 1) p.2 : ℝ) : ℂ) ^ m * ζ p.1 ^ j / 2) ε (by
    intro s hs s' hs'
    refine le_of_eq_of_le ?_ (hε s hs s' hs')
    congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [((UpperTheory.ConvolutionTheory.FX.cheb_facts (m + s) _).2 (hy i).le).1, Fintype.sum_bool]
    simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true, Bool.false_eq_true, if_false]
    generalize Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r
    generalize 2 * a i / η - 1 = y
    push_cast
    ring) (i, true)
  simp only [UpperTheory.ConvolutionTheory.FX.sepNode, if_true] at key
  have hyi := hy i
  have hr := Real.sqrt_nonneg ((2 * a i / η - 1) ^ 2 - 1)
  generalize Real.sqrt ((2 * a i / η - 1) ^ 2 - 1) = r at key hr
  generalize 2 * a i / η - 1 = y at key hyi
  rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ y + r), Complex.norm_two] at key
  have h5 : ‖c i‖ * y ^ m * ‖ζ i‖ ^ j ≤ ‖c i‖ * (y + r) ^ m * ‖ζ i‖ ^ j := by
    have : y ≤ y + r := by linarith
    have : 0 ≤ y := by linarith
    gcongr
  linarith
