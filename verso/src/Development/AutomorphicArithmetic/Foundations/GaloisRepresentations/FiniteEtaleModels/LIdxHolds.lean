import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Introduce `p _ D G L N hN`. Take `⟨K1, h1⟩` from `GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L 1 one_pos`. Take `⟨KN, hKN⟩` from `GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN`. Establish `hc : CompactSpace (L.KN 1)`. Rewrite using `[← h1]`.

Conclude with `isCompact_iff_compactSpace.1 K1.compact`. Establish `ho : IsOpen (((L.KN N).subgroupOf (L.KN 1) : Subgroup (L.KN 1)) : Set (L.KN 1))`. Rewrite using `[← hKN]`. Conclude with `KN.K.isOpen.preimage continuous_subtype_val`. Establish `hf : Finite ((L.KN 1) ⧸ (L.KN N).subgroupOf (L.KN 1))` using `Subgroup.quotient_finite_of_isOpen _ ho`.

Conclude with `Nat.card_pos.ne'`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.lIdx_holds :
    LIdx := by
  intro p _ D G L N hN
  obtain ⟨K1, h1⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L 1 one_pos
  obtain ⟨KN, hKN⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N hN
  have hc : CompactSpace (L.KN 1) := by
    rw [← h1]
    exact isCompact_iff_compactSpace.1 K1.compact
  have ho : IsOpen (((L.KN N).subgroupOf (L.KN 1) : Subgroup (L.KN 1)) : Set (L.KN 1)) := by
    rw [← hKN]
    exact KN.K.isOpen.preimage continuous_subtype_val
  have hf : Finite ((L.KN 1) ⧸ (L.KN N).subgroupOf (L.KN 1)) :=
    Subgroup.quotient_finite_of_isOpen _ ho
  exact Nat.card_pos.ne'
