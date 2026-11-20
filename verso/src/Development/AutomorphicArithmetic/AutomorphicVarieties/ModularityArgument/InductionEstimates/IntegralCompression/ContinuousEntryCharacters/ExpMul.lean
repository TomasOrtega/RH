import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IntegralCompression.LAbove

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
open scoped ComplexConjugate Classical InnerProductSpace

/- English proof (translation)
Unfold `chi`. Rewrite using `[← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]`. Use `congr 2`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Int.cast_add, add_mul]`.
-/
private lemma chi_add (ν ν' : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) :
    chi (ν + ν') θ = chi ν θ * chi ν' θ := by
  unfold chi
  rw [← Complex.exp_add, ← mul_add, ← Finset.sum_add_distrib]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Int.cast_add, add_mul]

/- English proof (translation)
Establish `h1` using `h 1 (fun i => -(((π.symm i : Fin (2 + 2)) : ℕ) : ℤ)) (by`. Introduce `a b hab`. Simplify using `only [Function.comp_apply, Equiv.symm_apply_apply, neg_le_neg_iff, Nat.cast_le]`. Conclude with `hab)`. Rewrite `h1` using `[← Equiv.sum_comp π, ← Equiv.sum_comp π (fun i => μ i * _)]`.

Simplify `h1` using `only [Equiv.Perm.one_apply, Equiv.symm_apply_apply]`.
-/
private lemma weak (π : Equiv.Perm (Fin (2 + 2))) (ν μ : Fin (2 + 2) → ℤ)
    (h : ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) →
      ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i) :
    ∑ i, ν (π i) * (-((i : ℕ) : ℤ)) ≤ ∑ i, μ (π i) * (-((i : ℕ) : ℤ)) := by
  have h1 := h 1 (fun i => -(((π.symm i : Fin (2 + 2)) : ℕ) : ℤ)) (by
    intro a b hab
    simp only [Function.comp_apply, Equiv.symm_apply_apply, neg_le_neg_iff, Nat.cast_le]
    exact hab)
  rw [← Equiv.sum_comp π, ← Equiv.sum_comp π (fun i => μ i * _)] at h1
  simpa only [Equiv.Perm.one_apply, Equiv.symm_apply_apply] using h1

/- English proof (translation)
Introduce and unpack `π ψ ψ' μ μ' ⟨J, _, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩ ⟨J', _, j₀', a', b', ν', hc', he', ha', hb', hν', hw', hf, hf'⟩`. Use `⟨J × J', inferInstance, (j₀, j₀'), fun j h => a j.1 h * a' j.2 h, fun j h => b j.1 h * b' j.2 h, fun j => ν j.1 + ν' j.2, fun j => ⟨(hc j.1).1.mul (hc' j.2).1, (hc j.1).2.mul (hc' j.2).2⟩, fun h k => ?_, ?_, ?_, ?_, fun j θ h => ?_, fun j w y hy => ?_, fun j hj => ?_⟩` and prove the remaining obligations. Simplify using `only [he, he', Finset.sum_mul_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [ha, ha']`. Simplify using `only [hb, hb']`. Simplify using `only [hν, hν']`. Take `⟨h1, h2, h3⟩` from `hw j.1 θ h`. Take `⟨h1', h2', h3'⟩` from `hw' j.2 θ h`.

Simplify using `only [h1, h2, h3, h1', h2', h3', chi_add]`. Use `⟨by ring, by ring, by ring⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`. Conclude with `add_le_add (hg j.1 w y hy) (hf j.2 w y hy)`. Simplify using `only [Pi.add_apply, add_mul, Finset.sum_add_distrib]`.

Distinguish the cases in `h1 : j.1 = j₀`. Establish `h2 : j.2 ≠ j₀'` using `fun h2 => hj (Prod.ext h1 h2)`. Conclude with `add_lt_add_of_le_of_lt (weak π _ _ (hg j.1)) (hf' j.2 h2)`. Conclude with `add_lt_add_of_lt_of_le (hg' j.1 h1) (weak π _ _ (hf j.2))`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA.expMul :
    ∀ π ψ ψ' μ μ', OExp π ψ μ → OExp π ψ' μ' → OExp π (fun k => ψ k * ψ' k) (μ + μ') := by
  rintro π ψ ψ' μ μ' ⟨J, _, j₀, a, b, ν, hc, he, ha, hb, hν, hw, hg, hg'⟩
    ⟨J', _, j₀', a', b', ν', hc', he', ha', hb', hν', hw', hf, hf'⟩
  refine ⟨J × J', inferInstance, (j₀, j₀'), fun j h => a j.1 h * a' j.2 h, fun j h => b j.1 h * b' j.2 h,
    fun j => ν j.1 + ν' j.2, fun j => ⟨(hc j.1).1.mul (hc' j.2).1, (hc j.1).2.mul (hc' j.2).2⟩,
    fun h k => ?_, ?_, ?_, ?_, fun j θ h => ?_, fun j w y hy => ?_, fun j hj => ?_⟩
  · simp only [he, he', Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · simp only [ha, ha']
  · simp only [hb, hb']
  · simp only [hν, hν']
  · obtain ⟨h1, h2, h3⟩ := hw j.1 θ h
    obtain ⟨h1', h2', h3'⟩ := hw' j.2 θ h
    simp only [h1, h2, h3, h1', h2', h3', chi_add]
    refine ⟨by ring, by ring, by ring⟩
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_le_add (hg j.1 w y hy) (hf j.2 w y hy)
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    by_cases h1 : j.1 = j₀
    · have h2 : j.2 ≠ j₀' := fun h2 => hj (Prod.ext h1 h2)
      exact add_lt_add_of_le_of_lt (weak π _ _ (hg j.1)) (hf' j.2 h2)
    · exact add_lt_add_of_lt_of_le (hg' j.1 h1) (weak π _ _ (hf j.2))
