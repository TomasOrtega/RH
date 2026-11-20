import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReducedClosurePointFibreSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceOfClosedImmersionContainsDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPairSpecializesDiagonalGenericPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldMapDoubleSpaceGenericPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

/- English proof (translation)
Introduce `F _ Y K _ ψ₁ ψ₂ hg`. Take `⟨h, hsp⟩` from `GlobalTheory.T.genericPair_specializes_diagonal_genericPoint F Y K ψ₁ ψ₂ hg`. Take `⟨Z, hZi, p₁, p₂, hZ, ζ, hci, hζ₁, hζ₂, hζg⟩` from `GlobalTheory.T.exists_reduced_closure_point_fibreSquare F Y K (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h`. Use `haveI := hZi`. Establish `hcomp : ζ ≫ Limits.pullback.lift p₁ p₂ hZ = Limits.pullback.lift (f` using `Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by`.

Apply `Limits.pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, Limits.pullback.lift_fst]`. Conclude with `hζ₁.trans (Limits.pullback.lift_fst _ _ _).symm`. Rewrite using `[Category.assoc, Limits.pullback.lift_snd]`. Conclude with `hζ₂.trans (Limits.pullback.lift_snd _ _ _).symm`.

Establish `hmem : Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ hZ)`. Establish `hcl : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ hZ))` using `hci.base_closed.isClosed_range`. Use `hsp.mem_closed hcl ⟨ζ (IsLocalRing.closedPoint K), ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomp]`. Apply the tactic sequence `first | rfl | exact (Scheme.Hom.comp_apply _ _ _).symm | simp`.

Take `⟨hproj, δ, hδc, hδ₁, hδ₂, hdiag⟩` from `GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal F Y Z p₁ p₂ hZ hci hmem`. Set `W : Dbl Y` to `{ Z := Z, integral := hZi, p₁ := p₁, p₂ := p₂, δ := δ, str_eq := hZ, proj := hproj, closed := hδc, δ₁ := hδ₁, δ₂ := hδ₂, diag := hdiag }`. Take `⟨j, hj₁, hj₂⟩` from `GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint F Y W K ψ₁ ψ₂ ζ hζg hζ₁ hζ₂`. Conclude with `⟨W, j, hj₁, hj₂⟩`.
-/
theorem exists_dbl_of_genPair : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ (W : Dbl Y) (j : W.Z.functionField →+* K), j.comp W.α₁ = ψ₁ ∧ j.comp W.α₂ = ψ₂ := by
  intro F _ Y K _ ψ₁ ψ₂ hg
  obtain ⟨h, hsp⟩ := GlobalTheory.T.genericPair_specializes_diagonal_genericPoint F Y K ψ₁ ψ₂ hg
  obtain ⟨Z, hZi, p₁, p₂, hZ, ζ, hci, hζ₁, hζ₂, hζg⟩ :=
    GlobalTheory.T.exists_reduced_closure_point_fibreSquare F Y K (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
  haveI := hZi
  have hcomp : ζ ≫ Limits.pullback.lift p₁ p₂ hZ =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]; exact hζ₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · rw [Category.assoc, Limits.pullback.lift_snd]; exact hζ₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hmem : Limits.pullback.diagonal Y.str (genericPoint Y.X) ∈ Set.range (Limits.pullback.lift p₁ p₂ hZ) := by
    have hcl : IsClosed (Set.range (Limits.pullback.lift p₁ p₂ hZ)) := hci.base_closed.isClosed_range
    refine hsp.mem_closed hcl ⟨ζ (IsLocalRing.closedPoint K), ?_⟩
    rw [← hcomp]
    first | rfl | exact (Scheme.Hom.comp_apply _ _ _).symm | simp
  obtain ⟨hproj, δ, hδc, hδ₁, hδ₂, hdiag⟩ := GlobalTheory.T.doubleSpace_of_closedImmersion_contains_diagonal F Y Z p₁ p₂ hZ hci hmem
  let W : Dbl Y :=
    { Z := Z, integral := hZi, p₁ := p₁, p₂ := p₂, δ := δ, str_eq := hZ, proj := hproj, closed := hδc,
      δ₁ := hδ₁, δ₂ := hδ₂, diag := hdiag }
  obtain ⟨j, hj₁, hj₂⟩ := GlobalTheory.T.exists_functionField_map_doubleSpace_genericPoint F Y W K ψ₁ ψ₂ ζ hζg hζ₁ hζ₂
  exact ⟨W, j, hj₁, hj₂⟩

end GlobalTheory.FlagPush
