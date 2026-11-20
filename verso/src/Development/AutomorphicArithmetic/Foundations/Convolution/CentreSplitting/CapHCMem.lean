import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HarishChandraProjQuantumDetEqProd

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

open GroundTheory.Automorphic.HarishChandra in
/- English proof (translation)
Establish `hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j))`. Introduce `i j k l`. Conclude with `e_mul_sub_mul (i, j) (k, l)`. Use `mem_center_of_commute_e fun a => ?_` and prove the remaining obligations. Conclude with `(Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm`.
-/
private theorem UpperTheory.ConvolutionTheory.Dp.capHC_mem (n : ℕ) (u : ℂ) :
    Formalism.REAL.qdet (fun i j : Fin n => e (i, j)) u ∈ Subalgebra.center ℂ (U n) := by
  have hgl : Formalism.REAL.GlRel (fun i j : Fin n => e (i, j)) := by
    intro i j k l
    exact e_mul_sub_mul (i, j) (k, l)
  refine mem_center_of_commute_e fun a => ?_
  exact (Formalism.REAL.qDetCentral (U n) n _ hgl u a.1 a.2).symm

/- English proof (translation)
Introduce `n u`. Use `⟨⟨_, capHC_mem n (u + ((n : ℂ) - 1) / 2)⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[HarishChandra.harishChandraHom_apply]`. Simplify using `only`. Rewrite using `[UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Unfold `GroundTheory.Automorphic.HarishChandra.translate`. Rewrite using `[map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq, add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]`. Use `congr 2`. Simplify using `only [HarishChandra.rhoVec, Pi.neg_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.ConvolutionTheory.Dp.capHC :
    UpperTheory.ConvolutionTheory.Dp.CapHC := by
  intro n u
  refine ⟨⟨_, capHC_mem n (u + ((n : ℂ) - 1) / 2)⟩, rfl, ?_⟩
  rw [HarishChandra.harishChandraHom_apply]
  dsimp only
  rw [UpperTheory.harishChandraProj_quantumDet_eq_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  unfold GroundTheory.Automorphic.HarishChandra.translate
  rw [map_add, MvPolynomial.aeval_C, MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq,
    add_comm (MvPolynomial.X k), ← add_assoc, ← map_add]
  congr 2
  simp only [HarishChandra.rhoVec, Pi.neg_apply]
  ring
