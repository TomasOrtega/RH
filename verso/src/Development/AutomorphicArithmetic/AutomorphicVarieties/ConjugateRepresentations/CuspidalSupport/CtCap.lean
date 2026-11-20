import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsConstantTermLinearMapEquivariantUniversalE
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermUnipotentLeftInvariant

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ n r φ hφ`. Establish `ha` using `(UpperTheory.V.Cm.isAutForm_iff φ).1 hφ`. Take `⟨f, hf, hfu⟩` from `UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping E n r`. Set `φ' : GroundTheory.Automorphic.AutomorphicForm.automorphicForms E n` to `⟨φ.1, ha⟩`. Use `⟨(UpperTheory.V.Cm.smEq E n).symm (f φ'), hf φ', fun X g => ?_, fun t u => ?_⟩` and prove the remaining obligations.

Rewrite using `[UpperTheory.V.Cm.coe_smEq_symm, hf]`. Conclude with `UpperTheory.constantTerm_unipotent_left_invariant E n r φ.1 ha.isLeftInvariant X g`. Take `⟨p, -, q, -, e⟩` from `UpperTheory.V.Cm.mem_Zalg_iff.1 (UpperTheory.V.Cm.cap_mem_Zalg (a := n) t u)`. Establish `h` using `hf (GroundTheory.Automorphic.AutomorphicForm.uActionAF E n p φ' + Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E n q φ')`. Rewrite `h` using `[map_add, map_smul, hfu, hfu]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem UpperTheory.V.Cj.S.ctCap :
    UpperTheory.V.Cj.S.CtCap := by
  intro E _ _ _ n r φ hφ
  have ha := (UpperTheory.V.Cm.isAutForm_iff φ).1 hφ
  obtain ⟨f, hf, hfu⟩ := UpperTheory.exists_constantTerm_linearMap_equivariant_universalEnveloping E n r
  let φ' : GroundTheory.Automorphic.AutomorphicForm.automorphicForms E n := ⟨φ.1, ha⟩
  refine ⟨(UpperTheory.V.Cm.smEq E n).symm (f φ'), hf φ', fun X g => ?_, fun t u => ?_⟩
  · rw [UpperTheory.V.Cm.coe_smEq_symm, hf]
    exact UpperTheory.constantTerm_unipotent_left_invariant E n r φ.1 ha.isLeftInvariant X g
  · obtain ⟨p, -, q, -, e⟩ := UpperTheory.V.Cm.mem_Zalg_iff.1 (UpperTheory.V.Cm.cap_mem_Zalg (a := n) t u)
    have h := hf (GroundTheory.Automorphic.AutomorphicForm.uActionAF E n p φ' +
      Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E n q φ')
    rw [map_add, map_smul, hfu, hfu] at h
    rw [e]
    exact h
