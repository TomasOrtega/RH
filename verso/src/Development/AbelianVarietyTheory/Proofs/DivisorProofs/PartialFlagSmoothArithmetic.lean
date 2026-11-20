import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCellStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))

/- English proof (translation)
Use `HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar a l))) (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Nat.card (CellVar a l))))` as an intermediate fact. Set `𝒰 : (Part a l).OpenCover` to `Scheme.Cover.mkOfCovers (ι → Equiv.Perm (Fin N)) (fun _ => Sp (MvPolynomial (CellVar a l) ℤ)) (cell a l) hc ho`. Use `IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar a l))) 𝒰 fun (w : ι → Equiv.Perm (Fin N)) => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `SmoothOfRelativeDimension _ (cell a l w ≫ _)`. Rewrite using `[toZ_ext (cell a l w ≫ _) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (MvPolynomial (CellVar a l) ℤ))))]`.

Use `(HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card (CellVar a l)))).2 ?_` and prove the remaining obligations. Use `RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_` and prove the remaining obligations. Conclude with `(RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2 (Adelic.isStandardSmooth_mvPolynomial ℤ (CellVar a l))`.
-/
theorem smoothOfRelativeDimension_str_of_cells (ho : ∀ w, IsOpenImmersion (cell a l w))
    (hc : ∀ x : Part a l, ∃ w, x ∈ Set.range (cell a l w)) :
    SmoothOfRelativeDimension (Nat.card (CellVar a l)) (str a l) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource
    (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar a l)))
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension (Nat.card (CellVar a l))))
  let 𝒰 : (Part a l).OpenCover := Scheme.Cover.mkOfCovers (ι → Equiv.Perm (Fin N))
    (fun _ => Sp (MvPolynomial (CellVar a l) ℤ)) (cell a l) hc ho
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension.{0} (Nat.card (CellVar a l))) 𝒰
    fun (w : ι → Equiv.Perm (Fin N)) => ?_
  change SmoothOfRelativeDimension _ (cell a l w ≫ _)
  rw [toZ_ext (cell a l w ≫ _) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (MvPolynomial (CellVar a l) ℤ))))]
  refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Nat.card (CellVar a l)))).2 ?_
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap _).2
    (Adelic.isStandardSmooth_mvPolynomial ℤ (CellVar a l))

/- English proof (translation)
Establish `hd : ∀ w, topologicalKrullDim (Set.range (cell a l w)) = (Nat.card (CellVar a l) + 1 : ℕ)` using `fun w => by`. Use `ho w` as an intermediate fact. Rewrite using `[← IsHomeomorph.topologicalKrullDim_eq _ (cell a l w).isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph]`. Use `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := MvPolynomial (CellVar a l) ℤ)).trans ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]`.

Simplify using `[add_comm]`. Use `le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ((hd 1).ge.trans (topologicalKrullDim_subspace_le _ _))` and prove the remaining obligations. Take `⟨w, hw⟩` from `hc x`. Use `ho w` as an intermediate fact. Conclude with `⟨_, (cell a l w).isOpenEmbedding.isOpen_range, hw, (hd w).le⟩`.
-/
theorem topologicalKrullDim_part_of_cells (ho : ∀ w, IsOpenImmersion (cell a l w))
    (hc : ∀ x : Part a l, ∃ w, x ∈ Set.range (cell a l w)) :
    topologicalKrullDim (Part a l) = (Nat.card (CellVar a l) + 1 : ℕ) := by
  have hd : ∀ w, topologicalKrullDim (Set.range (cell a l w)) = (Nat.card (CellVar a l) + 1 : ℕ) := fun w => by
    have := ho w
    rw [← IsHomeomorph.topologicalKrullDim_eq _
      (cell a l w).isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := MvPolynomial (CellVar a l) ℤ)).trans ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
    simp [add_comm]
  refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_)
    ((hd 1).ge.trans (topologicalKrullDim_subspace_le _ _))
  obtain ⟨w, hw⟩ := hc x
  have := ho w
  exact ⟨_, (cell a l w).isOpenEmbedding.isOpen_range, hw, (hd w).le⟩

/- English proof (translation)
Introduce `ι κ _ _ N a l` and use `have ho := GlobalTheory.T.schubert_cell_open_immersion ι κ N a l have hc := GlobalTheory.T.flag_point_in_some_cell ι κ N a l ⟨smoothOfRelativeDimension_str_of_cells a l ho hc, topologicalKrullDim_part_of_cells a l ho hc, isArithVar_of_dim a l (topologicalKrullDim_part_of_cells a …`.
-/
theorem smooth_dim_isArithVar_part : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)),
    SmoothOfRelativeDimension (Nat.card (CellVar a l)) (str a l) ∧
      topologicalKrullDim (Part a l) = (Nat.card (CellVar a l) + 1 : ℕ) ∧
      GlobalTheory.IsArithVar (str a l) (Nat.card (CellVar a l)) := fun ι κ _ _ N a l =>
  have ho := GlobalTheory.T.schubert_cell_open_immersion ι κ N a l
  have hc := GlobalTheory.T.flag_point_in_some_cell ι κ N a l
  ⟨smoothOfRelativeDimension_str_of_cells a l ho hc, topologicalKrullDim_part_of_cells a l ho hc,
    isArithVar_of_dim a l (topologicalKrullDim_part_of_cells a l ho hc)⟩

end GlobalTheory.FlagZ
