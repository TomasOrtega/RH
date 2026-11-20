import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ a L hL`. Establish `ho : IsOpen ((L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) : Set (GL (Fin a) (Af E)))` using `hL.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)`. Establish `hev` using `LocSph.eventually_mem (ho.mem_nhds (one_mem _))`. Use `⟨_, ho, inf_le_left, _, Filter.eventually_cofinite.1 hev, fun w hw => ?_⟩` and prove the remaining obligations. Establish `hw'` using `not_not.1 hw`.

Establish `h1 : ∀ k ∈ KGL w a, locGL E a w k ∈ L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a`. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `hw' g`. Use `⟨h1, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hk : GeneralLinearGroup.map (pLoc E w) u ∈ KGL w a`.

Take `⟨h2, h3⟩` from `(GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E a).1 hu.2`. Use `GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Conclude with `h2 i j w`. Rewrite using `[← map_inv]`. Conclude with `h3 i j w`.

Conclude with `⟨_, hk, _, mul_mem (inv_mem (h1 _ hk)) hu, LocEx.map_pLoc_inv_mul w u, (mul_inv_cancel_left _ _).symm⟩`.
-/
theorem UpperTheory.V.Cj.S.levelSplit :
    UpperTheory.V.Cj.S.LevelSplit := by
  intro E _ _ a L hL
  have ho : IsOpen ((L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := hL.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E a)
  have hev := LocSph.eventually_mem (ho.mem_nhds (one_mem _))
  refine ⟨_, ho, inf_le_left, _, Filter.eventually_cofinite.1 hev, fun w hw => ?_⟩
  have hw' := not_not.1 hw
  have h1 : ∀ k ∈ KGL w a, locGL E a w k ∈ L ⊓ GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E a := by
    rintro _ ⟨g, rfl⟩
    exact hw' g
  refine ⟨h1, fun u hu => ?_⟩
  have hk : GeneralLinearGroup.map (pLoc E w) u ∈ KGL w a := by
    obtain ⟨h2, h3⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E a).1 hu.2
    refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩
    · exact h2 i j w
    · rw [← map_inv]
      exact h3 i j w
  exact ⟨_, hk, _, mul_mem (inv_mem (h1 _ hk)) hu, LocEx.map_pLoc_inv_mul w u, (mul_inv_cancel_left _ _).symm⟩
