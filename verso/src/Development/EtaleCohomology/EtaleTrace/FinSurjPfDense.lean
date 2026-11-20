import Development.EtaleCohomology.EtaleTrace.FinSurjPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Use `⟨z, ?_⟩` and prove the remaining obligations. Simplify using `[RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]`.
-/
theorem loc_generic_top (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : z ∈ loc X (genericPoint X) := by
  refine ⟨z, ?_⟩
  simp [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]

/- English proof (translation)
Introduce `k _ X _ p d π w cw hind`. Establish `hz : ∀ (n : ℕ) (g : MvPolynomial (Fin (d + 1)) k), g.IsHomogeneous n → g ∈ (π (genericPoint X)).asHomogeneousIdeal → g = 0`. Introduce `n g hg hmem`. Establish `hgX : (g * MvPolynomial.X 0).IsHomogeneous (n + 1)` using `hg.mul (isHomogeneous_X k (0 : Fin (d + 1)))`. Establish `h1` using `(cw.opens (n + 1) (Nat.succ_pos n) (g * MvPolynomial.X 0) hgX (genericPoint X))`.

Establish `hnot : genericPoint X ∉ π ⁻¹ᵁ Proj.basicOpen _ (g * MvPolynomial.X 0)`. Introduce `h`. Establish `h' : π (genericPoint X) ∈ Proj.basicOpen _ (g * MvPolynomial.X 0)` using `h`. Rewrite `h'` using `[Proj.mem_basicOpen]`. Conclude with `h' (Ideal.mul_mem_right _ _ hmem)`.

Establish `he : eval₂ (kHom p) w (g * MvPolynomial.X 0) = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hnot (h1.2 ⟨hne, fun _ _ => loc_generic_top X _⟩)`. Use `hind (n + 1) _ hgX he` as an intermediate fact. Break down `mul_eq_zero.mp this with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h (X_ne_zero 0)`. Establish `hbot : ∀ a ∈ (π (genericPoint X)).asHomogeneousIdeal, a = 0`. Introduce `a ha`. Rewrite using `[← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin (d + 1)) k) a]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Use `hz i _ ?_ ((π (genericPoint X)).asHomogeneousIdeal.isHomogeneous i ha)` and prove the remaining obligations. Conclude with `(mem_homogeneousSubmodule i _).mp (SetLike.coe_mem _)`. Prove the components needed by the constructor for the conclusion. Introduce `y`.

Establish `hle : (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from π (genericPoint X)) ≤ (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from y)`. Rewrite using `[← ProjectiveSpectrum.as_ideal_le_as_ideal]`. Introduce `a ha`. Rewrite using `[hbot a ha]`. Conclude with `zero_mem _`.

Establish `hc` using `(ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp hle`. Conclude with `closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _)) hc`.
-/
theorem FSDense_pf : FSDense := by
  intro k _ X _ p d π w cw hind

  have hz : ∀ (n : ℕ) (g : MvPolynomial (Fin (d + 1)) k), g.IsHomogeneous n →
      g ∈ (π (genericPoint X)).asHomogeneousIdeal → g = 0 := by
    intro n g hg hmem
    have hgX : (g * MvPolynomial.X 0).IsHomogeneous (n + 1) := hg.mul (isHomogeneous_X k (0 : Fin (d + 1)))
    have h1 := (cw.opens (n + 1) (Nat.succ_pos n) (g * MvPolynomial.X 0) hgX (genericPoint X))
    have hnot : genericPoint X ∉ π ⁻¹ᵁ Proj.basicOpen _ (g * MvPolynomial.X 0) := by
      intro h
      have h' : π (genericPoint X) ∈ Proj.basicOpen _ (g * MvPolynomial.X 0) := h
      rw [Proj.mem_basicOpen] at h'
      exact h' (Ideal.mul_mem_right _ _ hmem)
    have he : eval₂ (kHom p) w (g * MvPolynomial.X 0) = 0 := by
      by_contra hne
      exact hnot (h1.2 ⟨hne, fun _ _ => loc_generic_top X _⟩)
    have := hind (n + 1) _ hgX he
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h (X_ne_zero 0)
  have hbot : ∀ a ∈ (π (genericPoint X)).asHomogeneousIdeal, a = 0 := by
    intro a ha
    classical
    rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin (d + 1)) k) a]
    refine Finset.sum_eq_zero fun i _ => ?_
    refine hz i _ ?_ ((π (genericPoint X)).asHomogeneousIdeal.isHomogeneous i ha)
    exact (mem_homogeneousSubmodule i _).mp (SetLike.coe_mem _)
  constructor
  intro y
  have hle : (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from π (genericPoint X)) ≤
      (show ProjectiveSpectrum (homogeneousSubmodule (Fin (d + 1)) k) from y) := by
    rw [← ProjectiveSpectrum.as_ideal_le_as_ideal]
    intro a ha
    rw [hbot a ha]
    exact zero_mem _
  have hc := (ProjectiveSpectrum.le_iff_mem_closure _ _ _).mp hle
  exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _)) hc

/- English proof (translation)
The claim follows from `FinSurj_of h1 hA FSDense_pf`.
-/
theorem FinSurj_of_basic (h1 : PNBasic) (hA : FSAffine) : FinSurj := FinSurj_of h1 hA FSDense_pf
