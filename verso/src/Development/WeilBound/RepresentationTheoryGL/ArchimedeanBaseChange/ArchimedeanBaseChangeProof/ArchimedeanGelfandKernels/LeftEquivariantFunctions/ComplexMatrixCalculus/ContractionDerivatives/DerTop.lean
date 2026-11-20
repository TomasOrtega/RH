import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ContractionDerivatives.SumSingleSmul

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.CxbDer

open PositivityTheory.RgBcC

variable {n : ℕ}

def Gpi (g : X n) : Finset (Md n) → Finset (Md n) → ℂ := fun B' A => F (fb n A) g B'

/- English proof (translation)
Use function extensionality and compare the values at `g B' A`. Simplify using `only [gamM, matL, Gpi, F, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, Module.Basis.equivFun_apply]`.
-/
theorem gamM_fun : (fun g : X n => (gamM (n := n) (Matrix.of g) : Finset (Md n) → Finset (Md n) → ℂ)) = Gpi := by
  funext g B' A
  simp only [gamM, matL, Gpi, F, LinearMap.toMatrix_apply, AlgHom.toLinearMap_apply, Module.Basis.equivFun_apply]

/- English proof (translation)
The claim follows from `contDiff_pi.2 fun B' => contDiff_pi.2 fun A => contDiff_pi.1 (key (fb n A)).1 B'`.
-/
theorem Gpi_contDiff : ContDiff ℂ ∞ (Gpi (n := n)) :=
  contDiff_pi.2 fun B' => contDiff_pi.2 fun A => contDiff_pi.1 (key (fb n A)).1 B'

def Lpi (n : ℕ) : X n →L[ℂ] (Finset (Md n) → Finset (Md n) → ℂ) :=
  ContinuousLinearMap.pi fun B' => ContinuousLinearMap.pi fun A =>
    (ContinuousLinearMap.proj B').comp (Classical.choose (key (n := n) (fb n A)).2)

/- English proof (translation)
Use `hasFDerivAt_pi.2 fun B' => ?_` and prove the remaining obligations. Use `hasFDerivAt_pi.2 fun A => ?_` and prove the remaining obligations. Establish `h` using `(Classical.choose_spec (key (n := n) (fb n A)).2).1`. Conclude with `(hasFDerivAt_pi'.1 h) B'`.
-/
theorem Gpi_hasFDerivAt : HasFDerivAt (Gpi (n := n)) (Lpi n) (one' n) := by
  refine hasFDerivAt_pi.2 fun B' => ?_
  refine hasFDerivAt_pi.2 fun A => ?_
  have h := (Classical.choose_spec (key (n := n) (fb n A)).2).1
  exact (hasFDerivAt_pi'.1 h) B'

/- English proof (translation)
Simplify using `only [Lpi, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]`. Rewrite using `[(Classical.choose_spec (key (n := n) (fb n A)).2).2 B]`.
-/
theorem Lpi_apply (B : X n) (B' A : Finset (Md n)) :
    Lpi n B B' A = (fb n).equivFun (Dop B (fb n A)) B' := by
  simp only [Lpi, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [(Classical.choose_spec (key (n := n) (fb n A)).2).2 B]

/- English proof (translation)
Use function extensionality and compare the values at `B' A`. Simplify using `only [matL, LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]`.
-/
theorem matL_Dop (B : X n) : (matL n (Dop B) : Finset (Md n) → Finset (Md n) → ℂ) =
    fun B' A => (fb n).equivFun (Dop B (fb n A)) B' := by
  funext B' A
  simp only [matL, LinearMap.toMatrix_apply, Module.Basis.equivFun_apply]

/- English proof (translation)
Simplify using `only [Ers, matL, creL, annL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_mk, AddHom.coe_mk]`. Conclude with `LinearMap.toMatrix_mul _ _ _`.
-/
theorem matL_Ers (r s : Md n) : matL n (Ers r s) = creL n (Pi.single r 1) * annL n (Pi.single s 1) := by
  simp only [Ers, matL, creL, annL, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.coe_mk,
    AddHom.coe_mk]
  exact LinearMap.toMatrix_mul _ _ _

/- English proof (translation)
Simplify using `only [Dop, map_sum, map_smul, matL_Ers]`.
-/
theorem matL_Dop_sum (B : X n) : matL n (Dop B) = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  simp only [Dop, map_sum, map_smul, matL_Ers]

end PositivityTheory.RgBcC.CxbDer

namespace PositivityTheory.RgBcC

open PositivityTheory.RgBcC.CxbDer

section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Conclude with `(funext fun B' => funext fun A => Lpi_apply B B' A).trans ((matL_Dop B).symm.trans (matL_Dop_sum B))`.
-/
theorem Lpi_eq {n : ℕ} (B : Matrix (Md n) (Md n) ℂ) :
    (Lpi n B : Finset (Md n) → Finset (Md n) → ℂ) = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  exact (funext fun B' => funext fun A => Lpi_apply B B' A).trans ((matL_Dop B).symm.trans (matL_Dop_sum B))

/- English proof (translation)
Use `⟨Lpi n, ?_, Lpi_eq⟩` and prove the remaining obligations. Establish `h` using `Gpi_hasFDerivAt (n := n)`. Rewrite `h` using `[← gamM_fun]`. Establish `h1 : (1 : Matrix (Md n) (Md n) ℂ) = one' n`. Use extensionality with `i j`.

Simplify using `[one', Matrix.one_apply]`. Rewrite using `[h1]`. Conclude with `h`.
-/
theorem gamM_hasFDerivAt (n : ℕ) : ∃ L : type_of% (fderiv ℂ (gamM (n := n)) 1), HasFDerivAt (gamM (n := n)) L 1 ∧
    ∀ B : Matrix (Md n) (Md n) ℂ, L B = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1)) := by
  refine ⟨Lpi n, ?_, Lpi_eq⟩
  have h := Gpi_hasFDerivAt (n := n)
  rw [← gamM_fun] at h
  have h1 : (1 : Matrix (Md n) (Md n) ℂ) = one' n := by
    ext i j
    simp [one', Matrix.one_apply]
  rw [h1]
  exact h

/- English proof (translation)
Establish `h` using `Gpi_contDiff (n := n)`. Rewrite `h` using `[← gamM_fun]`. Conclude with `h`.
-/
theorem gamM_contDiff (n : ℕ) : ContDiff ℂ ∞ (gamM (n := n)) := by
  have h := Gpi_contDiff (n := n)
  rw [← gamM_fun] at h
  exact h

/- English proof (translation)
Introduce `n`. Take `⟨L, hL, hv⟩` from `gamM_hasFDerivAt n`. Use `⟨gamM_contDiff n, fun B => ?_⟩` and prove the remaining obligations. Rewrite using `[hL.fderiv, hv B]`.
-/
theorem gamDer : GamDer := by
  intro n
  obtain ⟨L, hL, hv⟩ := gamM_hasFDerivAt n
  refine ⟨gamM_contDiff n, fun B => ?_⟩
  rw [hL.fderiv, hv B]

end

end PositivityTheory.RgBcC
