import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFourierJacobiExpansionOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FourierJacobiExpansionOverFieldInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.BijectiveOfIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueExpansionOfChartExpansionStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ChartExpansionOfValueExpansionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ExpansionClause

/- English proof (translation)
Introduce `h1 h2 V _ _ _ hV D A G _ _ U U' hM k hk hFE hsurj`. Establish `hT : U'.SecK k = LB.Sec (LB.LinComb U.P.L.L (K` using `Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))) := by`. Unfold `UnifPre.SecK`. Rewrite using `[hM.LG]`. Establish `hK` using `GlobalTheory.GenericFibreSections.sameK_bijective V _ D.toPre A G U k`.

Establish `hu` using `GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D.toPre A G U (FractionRing V) k`. Establish `ht` using `GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D.toPre A G U (FractionRing V) k hk`. Establish `e1` using `GlobalTheory.T.valueExpansion_of_chartExpansion V _ D A G U U' hM k`. Establish `e2` using `GlobalTheory.T.chartExpansion_of_valueExpansion V _ D A G U U' hM k`. Unfold `UnifPre.ExpBij`.

Use `⟨fun σ => ?_, fun s => ?_⟩` and prove the remaining obligations. Take `⟨t, hσt, -⟩` from `hK.1 (cast hT σ)`. Take `⟨s, hs⟩` from `ht t`. Use `⟨⟨s, hFE t s hs⟩, e2 σ _ t _ (cast_heq hT σ).symm hσt hs, fun s' hs' => ?_⟩` and prove the remaining obligations. Establish `h` using `(hu t t s'.s s (e1 σ _ t s' (cast_heq hT σ).symm hσt hs') hs).1 rfl`.

Take `⟨s', fe⟩` from `s'`. Consider the cases of `h`. Both sides reduce to the same expression. Take `⟨t, hts⟩` from `hsurj s`. Take `⟨σ₀, hσt, huniq⟩` from `hK.2 t`.

Use `⟨cast hT.symm σ₀, e2 _ σ₀ t s (cast_heq hT.symm σ₀) hσt hts, fun σ hσ => ?_⟩` and prove the remaining obligations. Take `⟨t', hσt', -⟩` from `hK.1 (cast hT σ)`. Establish `h` using `(hu t' t s.s s.s (e1 σ _ t' s (cast_heq hT σ).symm hσt' hσ) hts).2 rfl`. Substitute `h` using the available equality. Rewrite using `[← huniq _ hσt']`.

Simplify using the standard rewrite rules.
-/
theorem expBij_of_match : Laws → Laws2 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : PreU (IsLocalRing.maximalIdeal V) D.toPre A G) (U' : UnifPre (IsLocalRing.maximalIdeal V) D A G), Match U U' → ∀ k : ℕ, 1 ≤ k → U.FE (FractionRing V) k → (∀ s : Fam D.toPre (FractionRing V) k, ∃ t, U.ExpF (FractionRing V) k t s.s) → U'.ExpBij k := by
  intro h1 h2 V _ _ _ hV D A G _ _ U U' hM k hk hFE hsurj
  have hT : U'.SecK k = LB.Sec (LB.LinComb U.P.L.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ))) := by
    unfold UnifPre.SecK
    rw [hM.LG]
  have hK := GlobalTheory.GenericFibreSections.sameK_bijective V _ D.toPre A G U k
  have hu := GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D.toPre A G U (FractionRing V) k
  have ht := GlobalTheory.T.exists_fourierJacobi_expansion_over_field h1 h2 V hV D.toPre A G U (FractionRing V) k hk
  have e1 := GlobalTheory.T.valueExpansion_of_chartExpansion V _ D A G U U' hM k
  have e2 := GlobalTheory.T.chartExpansion_of_valueExpansion V _ D A G U U' hM k
  unfold UnifPre.ExpBij
  refine ⟨fun σ => ?_, fun s => ?_⟩
  · obtain ⟨t, hσt, -⟩ := hK.1 (cast hT σ)
    obtain ⟨s, hs⟩ := ht t
    refine ⟨⟨s, hFE t s hs⟩, e2 σ _ t _ (cast_heq hT σ).symm hσt hs, fun s' hs' => ?_⟩
    have h := (hu t t s'.s s (e1 σ _ t s' (cast_heq hT σ).symm hσt hs') hs).1 rfl
    obtain ⟨s', fe⟩ := s'
    cases h
    rfl
  · obtain ⟨t, hts⟩ := hsurj s
    obtain ⟨σ₀, hσt, huniq⟩ := hK.2 t
    refine ⟨cast hT.symm σ₀, e2 _ σ₀ t s (cast_heq hT.symm σ₀) hσt hts, fun σ hσ => ?_⟩
    obtain ⟨t', hσt', -⟩ := hK.1 (cast hT σ)
    have h := (hu t' t s.s s.s (e1 σ _ t' s (cast_heq hT σ).symm hσt' hσ) hts).2 rfl
    subst h
    rw [← huniq _ hσt']
    simp

end GlobalTheory.ExpansionClause
