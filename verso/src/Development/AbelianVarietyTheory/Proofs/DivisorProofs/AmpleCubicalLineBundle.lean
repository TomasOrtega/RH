import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfCubeAbelianSchemeOverArbitraryBase

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SS.AbAmple

open GlobalTheory.CechPic GlobalTheory.TripleExt

/- English proof (translation)
Take `⟨L, hL, rfl⟩` from `cls_surj c`. Establish `h` using `GlobalTheory.CubeTop.cubeTheorem S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)`. Establish `h₀` using `(cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h`. Rewrite `h₀` using `[cls_linComb hL, Fin.sum_univ_eight]`. Establish `e : x3 A = ![x3 A 0, x3 A 1, x3 A 2]`.

Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Rewrite using `[e, GlobalTheory.SS.AmpCub.cubeCls_three]`. Rewrite using `[← h₀]`. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.
-/
theorem cubeCls_eq_zero {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) : cubeCls (x3 A) c = 0 := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have h := GlobalTheory.CubeTop.cubeTheorem S A hA L hL (G3 A) (x3 A 0) (x3 A 1) (x3 A 2)
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).2 h
  rw [cls_linComb hL, Fin.sum_univ_eight] at h₀
  have e : x3 A = ![x3 A 0, x3 A 1, x3 A 2] := by
    funext i; fin_cases i <;> rfl
  rw [e, GlobalTheory.SS.AmpCub.cubeCls_three]
  rw [← h₀]
  simp
  abel

end GlobalTheory.SS.AbAmple

namespace GlobalTheory.SS

open GlobalTheory.CechPic AbAmple

/- English proof (translation)
Introduce `k _ _ B _ hB`. Use `hB.comm` as an intermediate fact. Use `hB.smooth` as an intermediate fact. Use `hB.proper` as an intermediate fact. Use `hB.geomConnected` as an intermediate fact.

Establish `: GeometricallyIntegral B.hom` using `geometricallyIntegral_of_smooth _`. Establish `: IsIntegral B.left` using `GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)`. Establish `: IsLocallyNoetherian B.left` using `LocallyOfFiniteType.isLocallyNoetherian B.hom`. Establish `: CompactSpace B.left` using `QuasiCompact.compactSpace_of_compactSpace B.hom`. Establish `: B.left.IsSeparated` using `⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩`.

Establish `hst : ∀ x : B.left, UniqueFactorizationMonoid (B.left.presheaf.stalk x)` using `fun x =>`. Use `ExtendRig.isRegularRing_stalk isRegularRing_of_smooth k B.hom x` as an intermediate fact. Use `uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing isPrincipal_map_away_of_hasProjectiveDimensionLE _`. Take `⟨y⟩ : Nonempty B.left` from `inferInstance`. Take `⟨W, hW, hy, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial`.

Take `⟨L, s, hL, hs⟩` from `exists_nonzeroLocus_eq_of_isAffineOpen B.left hst W hW ⟨y, hy⟩`. Conclude with `AmpCub.exists_ampleCub (cubeCls_eq_zero B hB (cls L hL)) ⟨L, hL, s, rfl, hs⟩ hW ⟨y, hy⟩`.
-/
theorem exists_ampleCub_of_isAbelianScheme :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B], IsAbelianScheme B →
      ∃ L : LB B.left, GlobalTheory.SS.AmpleCub B L := by
  intro k _ _ B _ hB
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have : GeometricallyIntegral B.hom := geometricallyIntegral_of_smooth _
  have : IsIntegral B.left :=
    GeometricallyIntegral.geometrically_isIntegral (f := B.hom) (𝟙 _) _ _ (IsPullback.id_horiz B.hom)
  have : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : B.left.IsSeparated := ⟨by rw [← terminal.comp_from B.hom]; infer_instance⟩
  have hst : ∀ x : B.left, UniqueFactorizationMonoid (B.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth k B.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  obtain ⟨y⟩ : Nonempty B.left := inferInstance
  obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  obtain ⟨L, s, hL, hs⟩ := exists_nonzeroLocus_eq_of_isAffineOpen B.left hst W hW ⟨y, hy⟩
  exact AmpCub.exists_ampleCub (cubeCls_eq_zero B hB (cls L hL)) ⟨L, hL, s, rfl, hs⟩ hW ⟨y, hy⟩

end GlobalTheory.SS
