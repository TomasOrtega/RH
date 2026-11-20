import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.UniformizerIntegrality.PtTopOf

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Sym.PT

/- English proof (translation)
Introduce `Ω _ _ _ ε X M`. Set `L` to `topL X M`. Set `L' : IntermediateField Ω X.K` to `{ L with algebraMap_mem' := fun c => algebraMap_mem_lev X _ c }`. Set `F : IntermediateField Ω X.K` to `IntermediateField.adjoin Ω {X.jK}`. Establish `hFL : F ≤ L'` using `IntermediateField.adjoin_simple_le_iff.mpr (jK_mem_lev X _)`.

Establish `hle : F.toSubfield ≤ L` using `fun x hx => hFL hx`. Use `letI : Algebra F L := (Subfield.inclusion hle).toAlgebra`. Use `haveI : IsScalarTower F L X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.IsAlgebraic L X.K := ⟨fun f => (X.alg_j f).tower_top L⟩`. Use `haveI : IsAlgClosure L (Kb X) := IsAlgClosure.ofAlgebraic L X.K (Kb X)`.

Set `e : topBar X M ≃ₐ[L] Kb X` to `IsAlgClosure.equiv L (topBar X M) (Kb X)`. Use `⟨e.toRingEquiv, fun f => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e (algebraMap L (topBar X M) f) = algebraMap X.K (Kb X) (f : X.K)`. Rewrite using `[AlgEquiv.commutes]`. Conclude with `IsScalarTower.algebraMap_apply L X.K (Kb X) f`.
-/
theorem UpperTheory.V.Z.Kato.Sym.PT.isoEx :
    UpperTheory.V.Z.Kato.Sym.PT.IsoEx := by
  intro Ω _ _ _ ε X M
  let L := topL X M
  let L' : IntermediateField Ω X.K :=
    { L with algebraMap_mem' := fun c => algebraMap_mem_lev X _ c }
  let F : IntermediateField Ω X.K := IntermediateField.adjoin Ω {X.jK}
  have hFL : F ≤ L' :=
    IntermediateField.adjoin_simple_le_iff.mpr (jK_mem_lev X _)
  have hle : F.toSubfield ≤ L := fun x hx => hFL hx
  letI : Algebra F L := (Subfield.inclusion hle).toAlgebra
  haveI : IsScalarTower F L X.K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic L X.K :=
    ⟨fun f => (X.alg_j f).tower_top L⟩
  haveI : IsAlgClosure L (Kb X) := IsAlgClosure.ofAlgebraic L X.K (Kb X)
  let e : topBar X M ≃ₐ[L] Kb X := IsAlgClosure.equiv L (topBar X M) (Kb X)
  refine ⟨e.toRingEquiv, fun f => ?_⟩
  change e (algebraMap L (topBar X M) f) = algebraMap X.K (Kb X) (f : X.K)
  rw [AlgEquiv.commutes]
  exact IsScalarTower.algebraMap_apply L X.K (Kb X) f
