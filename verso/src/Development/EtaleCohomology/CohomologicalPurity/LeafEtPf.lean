import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

noncomputable section
open TensorProduct KaehlerDifferential

namespace LateralTheory.CohomologicalPurity.LeafEtPf

/- English proof (translation)
Break down `subsingleton_or_nontrivial A with hA0 | hA0` into its components or cases. Conclude with `ChartCut.etale_of_subsingleton _`. Use `letI : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval z).toRingHom.toAlgebra`. Establish `: IsScalarTower R (MvPolynomial ι R) A` using `IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.aeval_C z r).symm`. Use `hA` as an intermediate fact.

Establish `: Algebra.IsStandardSmooth R A` using `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n`. Establish `hD : ∀ k, mapBaseChange R (MvPolynomial ι R) A ((1 : A) ⊗ₜ D R (MvPolynomial ι R) (MvPolynomial.X k)) = D R A (z k)`. Introduce `k`. Rewrite using `[mapBaseChange_tmul, one_smul, map_D]`. Use `congr 1`.

Conclude with `MvPolynomial.aeval_X z k`. Establish `hsurj : Function.Surjective (mapBaseChange R (MvPolynomial ι R) A)`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, hD k⟩`.

Use `haveI hΩ : Subsingleton Ω[A⁄MvPolynomial ι R] := by`. Use `subsingleton_of_forall_eq 0 fun ω => ?_` and prove the remaining obligations. Take `⟨w, rfl⟩` from `map_surjective R (MvPolynomial ι R) A ω`. Take `⟨u, rfl⟩` from `hsurj w`. Conclude with `(exact_mapBaseChange_map R (MvPolynomial ι R) A).apply_apply_eq_zero u`.

Establish `hfin : Module.finrank A Ω[A⁄R] = n` using `Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)`. Set `b` to `Algebra.TensorProduct.basis A (mvPolynomialBasis R ι)`. Establish `hli : LinearIndependent A (mapBaseChange R (MvPolynomial ι R) A ∘ b)`. Establish `: (mapBaseChange R (MvPolynomial ι R) A ∘ b) = fun k => D R A (z k)`. Use function extensionality and compare the values at `k`.

Simplify using `only [Function.comp_apply, b, Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hD]`. Rewrite using `[this]`. Conclude with `linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (hn.trans hfin.symm)`. Establish `hinj : Function.Injective (mapBaseChange R (MvPolynomial ι R) A)` using `LinearMap.injective_of_linearIndependent b.span_eq hli`. Use `haveI hH1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι R) A) := by`.

Use `subsingleton_of_forall_eq 0 fun h => ?_` and prove the remaining obligations. Establish `h1 : Algebra.H1Cotangent.δ R (MvPolynomial ι R) A h = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `(Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) A).apply_apply_eq_zero h`.

Take `⟨g, rfl⟩` from `((Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) A) h).mp h1`. Rewrite using `[Subsingleton.elim g 0, map_zero]`. Establish `: Algebra.FinitePresentation (MvPolynomial ι R) A` using `Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A`. Establish `: Algebra.IsStandardSmooth (MvPolynomial ι R) A` using `Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (I := Empty) (Module.Basis.empty _) (by rintro _ ⟨i, _⟩; exact i.elim)`. Establish `: Algebra.FormallyUnramified (MvPolynomial ι R) A` using `⟨hΩ⟩`.

Establish `: Algebra.Etale (MvPolynomial ι R) A` using `Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩`. Conclude with `RingHom.etale_algebraMap.mpr this`.
-/
theorem etale_main (n : ℕ) (R A ι : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] (z : ι → A)
    (hn : Fintype.card ι = n) (hA : Algebra.IsStandardSmoothOfRelativeDimension n R A)
    (hspan : Submodule.span A (Set.range fun k => KaehlerDifferential.D R A (z k)) = ⊤) :
    (MvPolynomial.eval₂Hom (algebraMap R A) z).Etale := by
  rcases subsingleton_or_nontrivial A with hA0 | hA0
  · exact ChartCut.etale_of_subsingleton _
  letI : Algebra (MvPolynomial ι R) A := (MvPolynomial.aeval z).toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.aeval_C z r).symm
  have := hA
  have : Algebra.IsStandardSmooth R A := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have hD : ∀ k, mapBaseChange R (MvPolynomial ι R) A
      ((1 : A) ⊗ₜ D R (MvPolynomial ι R) (MvPolynomial.X k)) = D R A (z k) := by
    intro k
    rw [mapBaseChange_tmul, one_smul, map_D]
    congr 1
    exact MvPolynomial.aeval_X z k
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial ι R) A) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hD k⟩
  haveI hΩ : Subsingleton Ω[A⁄MvPolynomial ι R] := by
    refine subsingleton_of_forall_eq 0 fun ω => ?_
    obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial ι R) A ω
    obtain ⟨u, rfl⟩ := hsurj w
    exact (exact_mapBaseChange_map R (MvPolynomial ι R) A).apply_apply_eq_zero u
  have hfin : Module.finrank A Ω[A⁄R] = n :=
    Module.finrank_eq_of_rank_eq (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n)
  let b := Algebra.TensorProduct.basis A (mvPolynomialBasis R ι)
  have hli : LinearIndependent A (mapBaseChange R (MvPolynomial ι R) A ∘ b) := by
    have : (mapBaseChange R (MvPolynomial ι R) A ∘ b) = fun k => D R A (z k) := by
      funext k
      simp only [Function.comp_apply, b, Algebra.TensorProduct.basis_apply, mvPolynomialBasis_apply, hD]
    rw [this]
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (hn.trans hfin.symm)
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial ι R) A) :=
    LinearMap.injective_of_linearIndependent b.span_eq hli
  haveI hH1 : Subsingleton (Algebra.H1Cotangent (MvPolynomial ι R) A) := by
    refine subsingleton_of_forall_eq 0 fun h => ?_
    have h1 : Algebra.H1Cotangent.δ R (MvPolynomial ι R) A h = 0 := by
      apply hinj
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R (MvPolynomial ι R) A).apply_apply_eq_zero h
    obtain ⟨g, rfl⟩ := ((Algebra.H1Cotangent.exact_map_δ R (MvPolynomial ι R) A) h).mp h1
    rw [Subsingleton.elim g 0, map_zero]
  have : Algebra.FinitePresentation (MvPolynomial ι R) A :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R (MvPolynomial ι R) A
  have : Algebra.IsStandardSmooth (MvPolynomial ι R) A :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential (I := Empty) (Module.Basis.empty _) (by rintro _ ⟨i, _⟩; exact i.elim)
  have : Algebra.FormallyUnramified (MvPolynomial ι R) A := ⟨hΩ⟩
  have : Algebra.Etale (MvPolynomial ι R) A :=
    Algebra.Etale.iff_formallyUnramified_and_smooth.mpr ⟨inferInstance, inferInstance⟩
  exact RingHom.etale_algebraMap.mpr this

/- English proof (translation)
Introduce `n R A ι _ _ _ _ z hn hA hspan`. Conclude with `etale_main n R A ι z hn hA hspan`.
-/
theorem LeafEt_of : ChartCut.LeafEt := by
  intro n R A ι _ _ _ _ z hn hA hspan
  exact etale_main n R A ι z hn hA hspan

end LateralTheory.CohomologicalPurity.LeafEtPf
