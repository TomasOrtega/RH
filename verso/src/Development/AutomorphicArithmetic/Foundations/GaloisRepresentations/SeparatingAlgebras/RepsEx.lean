import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `F _ _ _ _ n _ _ μ _ h`. Establish `hKc` using `GLnLocal.isCompact_integralGL F n`. Establish `hKo : IsOpen ((GLnLocal.integralGL F n : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F))` using `(integralOpen F n).isOpen`. Establish `hbi` using `HeckeAlgebra.HeckeAlgebraLevel.val_mem hKc hKo h`. Establish `hsupp : HasCompactSupport ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h)` using `(HeckeAlgebra.mem _).2`.

Use `set φ : GL (Fin n) F → ℂ := ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h) with hφ`. Establish `hright : ∀ g k, k ∈ GLnLocal.integralGL F n → φ (g * k) = φ g` using `fun g k hk => (hbi k hk g).2`. Use `set S := (finite_image_mk_tsupport (integralOpen F n) hsupp).toFinset with hS`. Use `⟨S.image Quotient.out, ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg g' hg' hgg`.

Simplify using `only [Finset.mem_image] at hg hg'`. Take `⟨x, -, rfl⟩` from `hg`. Take `⟨y, -, rfl⟩` from `hg'`. Establish `hxy : x = y`. Rewrite using `[← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y]`.

Conclude with `QuotientGroup.eq.2 hgg`. Rewrite using `[hxy]`. Introduce `f hf`. Establish `hint` using `integral_eq_smul_finsum_coset μ (integralOpen F n) hKc (f := fun x => φ x * f x) hsupp.mul_right (fun g k hk => by simp only [hright g k hk, hf g k hk])`. Rewrite using `[hint, Complex.real_smul]`.

Use `congr 1`. Rewrite using `[finsum_eq_sum_of_support_subset (s := S) _ ?_, Finset.sum_image]`. Both sides reduce to the same expression. Introduce `x _ y _ hxy`. Conclude with `Quotient.out_injective hxy`.

Introduce `x hx`. Establish `hne : φ (Quotient.out x) ≠ 0` using `left_ne_zero_of_mul hx`. Rewrite using `[hS, Set.Finite.coe_toFinset]`. Conclude with `⟨Quotient.out x, subset_tsupport _ hne, QuotientGroup.out_eq' x⟩`.
-/
theorem UpperTheory.Gal.Gen.repsEx_pf :
    UpperTheory.Gal.Gen.RepsEx := by
  intro F _ _ _ _ n _ _ μ _ h
  classical
  have hKc := GLnLocal.isCompact_integralGL F n
  have hKo : IsOpen ((GLnLocal.integralGL F n : Subgroup (GL (Fin n) F)) : Set (GL (Fin n) F)) :=
    (integralOpen F n).isOpen
  have hbi := HeckeAlgebra.HeckeAlgebraLevel.val_mem hKc hKo h
  have hsupp : HasCompactSupport ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h) := (HeckeAlgebra.mem _).2
  set φ : GL (Fin n) F → ℂ := ⇑(HeckeAlgebra.HeckeAlgebraLevel.val hKc hKo h) with hφ
  have hright : ∀ g k, k ∈ GLnLocal.integralGL F n → φ (g * k) = φ g := fun g k hk => (hbi k hk g).2
  set S := (finite_image_mk_tsupport (integralOpen F n) hsupp).toFinset with hS
  refine ⟨S.image Quotient.out, ?_, ?_⟩
  · intro g hg g' hg' hgg
    simp only [Finset.mem_image] at hg hg'
    obtain ⟨x, -, rfl⟩ := hg
    obtain ⟨y, -, rfl⟩ := hg'
    have hxy : x = y := by
      rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' y]
      exact QuotientGroup.eq.2 hgg
    rw [hxy]
  · intro f hf
    have hint := integral_eq_smul_finsum_coset μ (integralOpen F n) hKc (f := fun x => φ x * f x)
      hsupp.mul_right (fun g k hk => by simp only [hright g k hk, hf g k hk])
    rw [hint, Complex.real_smul]
    congr 1
    rw [finsum_eq_sum_of_support_subset (s := S) _ ?_, Finset.sum_image]
    · rfl
    · intro x _ y _ hxy
      exact Quotient.out_injective hxy
    · intro x hx
      have hne : φ (Quotient.out x) ≠ 0 := left_ne_zero_of_mul hx
      rw [hS, Set.Finite.coe_toFinset]
      exact ⟨Quotient.out x, subset_tsupport _ hne, QuotientGroup.out_eq' x⟩
