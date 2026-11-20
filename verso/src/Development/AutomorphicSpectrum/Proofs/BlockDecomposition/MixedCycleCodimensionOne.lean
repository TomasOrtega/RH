import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.CompanionTheory.MixZ

/- English proof (translation)
Introduce `X _ p D hD z hz`. Set `C : Closeds X` to `⟨closure {z}, isClosed_closure⟩`. Set `I` to `Scheme.IdealSheafData.vanishingIdeal C`. Use `haveI : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal C`. Establish `hrange : Set.range I.subschemeι = closure {z}`.

Rewrite using `[Scheme.IdealSheafData.range_subschemeι]`. Both sides reduce to the same expression. Establish `hemb : Topology.IsEmbedding I.subschemeι` using `I.subschemeι.isClosedEmbedding.isEmbedding`. Use `haveI : IrreducibleSpace I.subscheme := by`. Establish `hs : IsIrreducible (Set.range I.subschemeι)`.

Rewrite using `[hrange]`. Conclude with `isIrreducible_singleton.closure`. Use `haveI := Subtype.irreducibleSpace hs`. Establish `h2` using `(IrreducibleSpace.isIrreducible_univ (Set.range I.subschemeι)).image hemb.toHomeomorph.symm hemb.toHomeomorph.symm.continuous.continuousOn`. Rewrite `h2` using `[Set.image_univ_of_surjective hemb.toHomeomorph.symm.surjective]`.

Conclude with `(irreducibleSpace_def _).2 h2`. Use `haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _`. Establish `hgen : I.subschemeι (genericPoint I.subscheme) = z`. Establish `h1` using `(genericPoint_spec I.subscheme).image I.subschemeι.continuous`. Rewrite `h1` using `[Set.image_univ, hrange, closure_closure]`.

Conclude with `h1.eq isGenericPoint_closure`. Establish `key` using `GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one ℤ X p D hD I.subscheme I.subschemeι (by rw [hgen]; exact hz)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem codimOne_holds : CodimOne := by
  intro X _ p D hD z hz
  let C : Closeds X := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  haveI : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal C
  have hrange : Set.range I.subschemeι = closure {z} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hemb : Topology.IsEmbedding I.subschemeι := I.subschemeι.isClosedEmbedding.isEmbedding
  haveI : IrreducibleSpace I.subscheme := by
    have hs : IsIrreducible (Set.range I.subschemeι) := by
      rw [hrange]; exact isIrreducible_singleton.closure
    haveI := Subtype.irreducibleSpace hs
    have h2 := (IrreducibleSpace.isIrreducible_univ (Set.range I.subschemeι)).image
      hemb.toHomeomorph.symm hemb.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ_of_surjective hemb.toHomeomorph.symm.surjective] at h2
    exact (irreducibleSpace_def _).2 h2
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hgen : I.subschemeι (genericPoint I.subscheme) = z := by
    have h1 := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
    rw [Set.image_univ, hrange, closure_closure] at h1
    exact h1.eq isGenericPoint_closure
  have key := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one ℤ X p D hD I.subscheme I.subschemeι
    (by rw [hgen]; exact hz)
  calc topologicalKrullDim (closure ({z} : Set X))
      = topologicalKrullDim I.subscheme := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb hrange
    _ = D := key

end GlobalTheory.CompanionTheory.MixZ
