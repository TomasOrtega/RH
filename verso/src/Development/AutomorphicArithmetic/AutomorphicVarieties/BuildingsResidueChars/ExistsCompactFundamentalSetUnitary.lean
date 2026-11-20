import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdmissibleLocalComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
import Development.AutomorphicArithmetic.DivisorFrames.ExistsIsOpenIsCompactSubgroupFiniteAdelicUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFiniteStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryInfinitePointEqListProdPlacePartsStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.DefU

/- English proof (translation)
Introduce `E _ _ _ n`. Take `⟨K, hKo, hKc⟩` from `UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E n`. Take `⟨S, hS⟩` from `GlobalTheory.T.definiteUnitary_classSet_finite E n K hKo`. Use `haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ`. Use `haveI : ∀ v : InfinitePlace E, CompactSpace (embU n v.embedding) := fun v => by`.

Take `⟨e, -⟩` from `GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding`. Conclude with `e.toHomeomorph.symm.compactSpace`. Set `P : (∀ v : InfinitePlace E, embU n v.embedding) → UA E n` to `fun y => (Finset.univ.toList.map fun v => (y v : UA E n)).prod`. Establish `hP : Continuous P` using `continuous_list_prod _ fun v _ => continuous_subtype_val.comp (continuous_apply v)`. Establish `hPc : IsCompact (Set.range P)` using `isCompact_range hP`.

Establish `hKc' : IsCompact (Subtype.val '' (K : Set (finU E n)))` using `hKc.image continuous_subtype_val`. Use `⟨_, (S.finite_toSet.isCompact.mul hPc).mul hKc', fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, s, hs, x, hx, k, hk, e⟩` from `hS g`. Take `⟨y, hy, -, hyx⟩` from `GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x hx`. Use `⟨γ, hγ, s * x * k, Set.mul_mem_mul (Set.mul_mem_mul hs ⟨fun v => ⟨y v, hy v⟩, hyx⟩) ⟨k, hk, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, mul_assoc, mul_assoc, mul_assoc]`.
-/
theorem UpperTheory.exists_compact_fundamental_set_unitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ C : Set (UA E n), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU E n, ∃ c ∈ C, g = γ * c := by
  intro E _ _ _ n
  classical
  obtain ⟨K, hKo, hKc⟩ := UpperTheory.exists_isOpen_isCompact_subgroup_finiteAdelicUnitary E n
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hKo
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : ∀ v : InfinitePlace E, CompactSpace (embU n v.embedding) := fun v => by
    obtain ⟨e, -⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    exact e.toHomeomorph.symm.compactSpace
  let P : (∀ v : InfinitePlace E, embU n v.embedding) → UA E n :=
    fun y => (Finset.univ.toList.map fun v => (y v : UA E n)).prod
  have hP : Continuous P :=
    continuous_list_prod _ fun v _ => continuous_subtype_val.comp (continuous_apply v)
  have hPc : IsCompact (Set.range P) := isCompact_range hP
  have hKc' : IsCompact (Subtype.val '' (K : Set (finU E n))) := hKc.image continuous_subtype_val
  refine ⟨_, (S.finite_toSet.isCompact.mul hPc).mul hKc', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hS g
  obtain ⟨y, hy, -, hyx⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x hx
  refine ⟨γ, hγ, s * x * k, Set.mul_mem_mul (Set.mul_mem_mul hs ⟨fun v => ⟨y v, hy v⟩, hyx⟩) ⟨k, hk, rfl⟩, ?_⟩
  rw [e, mul_assoc, mul_assoc, mul_assoc]
