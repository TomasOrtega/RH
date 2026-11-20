import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsFiniteProjectiveComplexQuasiIso

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Establish `h0` using `(quasiIsoAt_zero_iff φ).1 inferInstance`. Establish `h1` using `(quasiIsoAt_succ_iff φ 0).1 inferInstance`. Use `⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun hC x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Establish `hx' : (K.d 0 1).hom x = 0` using `hx`. Express the relevant statement in the definitionally equal form `(C.d 0 1).hom ((φ.f 0).hom x) = 0`.

Rewrite using `[cochain_comm_apply, hx', map_zero]`. Establish `hx' : (K.d 0 1).hom x = 0` using `hx`. Establish `hy' : (K.d 0 1).hom y = 0` using `hy`. Conclude with `sub_eq_zero.1 (h0.2 (x - y) (by rw [map_sub, hx', hy', sub_zero]) (by rw [map_sub, hxy, sub_self]))`. Take `⟨x, hx, hx'⟩` from `h0.1 y hy`.

Conclude with `⟨x, hx, hx'⟩`. Take `⟨z, hz⟩` from `(hC ((φ.f 1).hom x)).1 (by rw [cochain_comm_apply, hx, map_zero])`. Conclude with `h1.2 x z hx hz`. Introduce and unpack `⟨w, rfl⟩`. Conclude with `cochain_d_d_apply K 0 1 2 w`.
-/
theorem bijOn_ker_and_exact_of_quasiIso {R : Type} [CommRing R]
    {K C : CochainComplex (ModuleCat.{0} R) ℕ} (φ : K ⟶ C) (h : QuasiIso φ) :
    Set.BijOn (φ.f 0).hom (LinearMap.ker (K.d 0 1).hom) (LinearMap.ker (C.d 0 1).hom) ∧
      (Function.Exact (C.d 0 1).hom (C.d 1 2).hom → Function.Exact (K.d 0 1).hom (K.d 1 2).hom) := by
  have h0 := (quasiIsoAt_zero_iff φ).1 inferInstance
  have h1 := (quasiIsoAt_succ_iff φ 0).1 inferInstance
  refine ⟨⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_⟩, fun hC x => ⟨fun hx => ?_, ?_⟩⟩
  · have hx' : (K.d 0 1).hom x = 0 := hx
    change (C.d 0 1).hom ((φ.f 0).hom x) = 0
    rw [cochain_comm_apply, hx', map_zero]
  · have hx' : (K.d 0 1).hom x = 0 := hx
    have hy' : (K.d 0 1).hom y = 0 := hy
    exact sub_eq_zero.1 (h0.2 (x - y) (by rw [map_sub, hx', hy', sub_zero])
      (by rw [map_sub, hxy, sub_self]))
  · obtain ⟨x, hx, hx'⟩ := h0.1 y hy
    exact ⟨x, hx, hx'⟩
  · obtain ⟨z, hz⟩ := (hC ((φ.f 1).hom x)).1 (by rw [cochain_comm_apply, hx, map_zero])
    exact h1.2 x z hx hz
  · rintro ⟨w, rfl⟩
    exact cochain_d_d_apply K 0 1 2 w

/- English proof (translation)
Establish `key` using `bijOn_ker_and_exact_of_quasiIso _ h`. Use `clear h`. Generalize the expression as in `hf : algebraMap R R' = f at key`. Establish `e : inst = f.toAlgebra` using `Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)`. Substitute `e` using the available equality.

Conclude with `key`.
-/
theorem bijOn_ker_and_exact_of_quasiIso_baseChange (R R' : Type) [CommRing R] [CommRing R']
    [inst : Algebra R R'] (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C)
    (h : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ)) :
    Set.BijOn ((φ.f 0).hom.baseChange R') (LinearMap.ker ((K.d 0 1).hom.baseChange R'))
        (LinearMap.ker ((C.d 0 1).hom.baseChange R')) ∧
      (Function.Exact ((C.d 0 1).hom.baseChange R') ((C.d 1 2).hom.baseChange R') →
        Function.Exact ((K.d 0 1).hom.baseChange R') ((K.d 1 2).hom.baseChange R')) := by
  have key := bijOn_ker_and_exact_of_quasiIso _ h
  clear h
  generalize hf : algebraMap R R' = f at key
  have e : inst = f.toAlgebra := Algebra.algebra_ext _ _ (fun r => by rw [hf]; rfl)
  subst e
  exact key

end GlobalTheory
