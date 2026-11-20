import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

/- English proof (translation)
Introduce `E _ _ _ a g`. Establish `h0 : mk (latticeGL E a) (Quotient.out (mk (latticeGL E a) g)) = mk (latticeGL E a) g` using `Quotient.out_eq _`. Take `⟨⟨l, hl⟩, e⟩` from `mk_eq_iff.1 h0.symm`. Take `⟨γ, n, rfl⟩` from `mem_latticeGL_iff.1 hl`. Establish `hγ1 : AdelicGLn.diagonal E a γ ∈ Reduction.normOneGL E a` using `Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩`.

Establish `hγΓ : (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL E a) ∈ UpperTheory.V.KernelIndexFullLattice.Γ1 E a` using `⟨γ, rfl⟩`. Establish `h1 : retractOne (ratGL E a γ * splitCentre E a 1 ^ n * g) = (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL E a) * retractOne g`. Establish `h2` using `retractOne_coe_mul (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL E a) (splitCentre E a 1 ^ n * g)`. Establish `h3 : retractOne (K` using `E) (n := a) (splitCentre E a 1 ^ n * g) = retractOne g := by`. Rewrite using `[← splitCentre_intCast, UpperTheory.V.KernelIndexFullLattice.splitEq_holds, retractOne_mul, retractOne_centralSection, one_mul]`.

Rewrite `h2` using `[h3]`. Rewrite using `[mul_assoc]`. Conclude with `h2`. Unfold `UpperTheory.V.KernelIndexFullLattice.quotMap`. Rewrite using `[← e]`.

Conclude with `(congrArg _ h1).trans (RightCosetSpace.mk_mul_of_mem hγΓ _)`.
-/
theorem UpperTheory.V.KernelIndexFullLattice.quotMk_holds :
    UpperTheory.V.KernelIndexFullLattice.QuotMk := by
  intro E _ _ _ a g
  have h0 : mk (latticeGL E a) (Quotient.out (mk (latticeGL E a) g)) = mk (latticeGL E a) g :=
    Quotient.out_eq _
  obtain ⟨⟨l, hl⟩, e⟩ := mk_eq_iff.1 h0.symm
  obtain ⟨γ, n, rfl⟩ := mem_latticeGL_iff.1 hl
  have hγ1 : AdelicGLn.diagonal E a γ ∈ Reduction.normOneGL E a := Reduction.rationalGL_le_normOneGL ⟨γ, rfl⟩
  have hγΓ : (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL E a) ∈ UpperTheory.V.KernelIndexFullLattice.Γ1 E a := ⟨γ, rfl⟩
  have h1 : retractOne (ratGL E a γ * splitCentre E a 1 ^ n * g) =
      (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL E a) * retractOne g := by
    have h2 := retractOne_coe_mul (⟨AdelicGLn.diagonal E a γ, hγ1⟩ : Reduction.normOneGL E a)
      (splitCentre E a 1 ^ n * g)
    have h3 : retractOne (K := E) (n := a) (splitCentre E a 1 ^ n * g) = retractOne g := by
      rw [← splitCentre_intCast, UpperTheory.V.KernelIndexFullLattice.splitEq_holds, retractOne_mul, retractOne_centralSection, one_mul]
    rw [h3] at h2
    rw [mul_assoc]
    exact h2
  unfold UpperTheory.V.KernelIndexFullLattice.quotMap
  rw [← e]
  exact (congrArg _ h1).trans (RightCosetSpace.mk_mul_of_mem hγΓ _)
