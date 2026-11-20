import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory

open PDiv

/- English proof (translation)
Introduce `p R _ G n a ha`. Establish `ha0 : counit (R` using `R) a = 0 := ha`. Establish `hb : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n))`. Express the relevant statement in the definitionally equal form `counit (R := R) (G.res n a) = 0`. Rewrite using `[CoalgHomClass.counit_comp_apply, ha0]`.

Establish `h1 : mulBy R _ p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1))`. Rewrite using `[← G.mulP_res n a]`. Conclude with `Ideal.mem_map_of_mem _ hb`. Establish `h2 : dUnit R (mulBy R _ p a - (p : R) • a) = 0`. Establish `e1 : dUnit R (mulBy R _ p a - (p : R) • a) = dUnit R (mulBy R _ p a) - dUnit R ((p : R) • a)` using `map_sub (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _`.

Establish `e2 : dUnit R ((p : R) • a) = (p : R) • dUnit R a` using `map_smul (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _`. Rewrite using `[e1, e2, ← cotMap_d, cotMap_mulBy, sub_self]`. Establish `h3 : mulBy R _ p a - (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2`. Establish `h` using `(AugCot.d_eq_zero_iff _ _).1 h2`. Establish `he : Bialgebra.counitAlgHom R (G.A (n + 1)) (mulBy R _ p a - (p : R) • a) = 0`.

Express the relevant statement in the definitionally equal form `counit (R := R) (mulBy R _ p a - (p : R) • a) = 0`. Rewrite using `[map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha0, smul_zero, sub_zero]`. Rewrite `h` using `[he, map_zero, sub_zero]`. Then use the resulting hypothesis. Establish `: (p : R) • a = mulBy R _ p a - (mulBy R _ p a - (p : R) • a)` using `by abel`. Rewrite using `[this]`.

Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h3)`.
-/
theorem PDivGroup.natCast_smul_mem_augSq_sup_map : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ),
    ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))),
      (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 ⊔
        (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
          ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n a ha
  have ha0 : counit (R := R) a = 0 := ha
  have hb : G.res n a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A n)) := by
    change counit (R := R) (G.res n a) = 0
    rw [CoalgHomClass.counit_comp_apply, ha0]
  have h1 : mulBy R _ p a ∈ (RingHom.ker (Bialgebra.counitAlgHom R (G.A n))).map
      ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
    rw [← G.mulP_res n a]
    exact Ideal.mem_map_of_mem _ hb
  have h2 : dUnit R (mulBy R _ p a - (p : R) • a) = 0 := by
    have e1 : dUnit R (mulBy R _ p a - (p : R) • a) = dUnit R (mulBy R _ p a) - dUnit R ((p : R) • a) :=
      map_sub (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    have e2 : dUnit R ((p : R) • a) = (p : R) • dUnit R a :=
      map_smul (AugCot.d (Bialgebra.counitAlgHom R (G.A (n + 1)))) _ _
    rw [e1, e2, ← cotMap_d, cotMap_mulBy, sub_self]
  have h3 : mulBy R _ p a - (p : R) • a ∈ RingHom.ker (Bialgebra.counitAlgHom R (G.A (n + 1))) ^ 2 := by
    have h := (AugCot.d_eq_zero_iff _ _).1 h2
    have he : Bialgebra.counitAlgHom R (G.A (n + 1)) (mulBy R _ p a - (p : R) • a) = 0 := by
      change counit (R := R) (mulBy R _ p a - (p : R) • a) = 0
      rw [map_sub, map_smul, CoalgHomClass.counit_comp_apply, ha0, smul_zero, sub_zero]
    rwa [he, map_zero, sub_zero] at h
  have : (p : R) • a = mulBy R _ p a - (mulBy R _ p a - (p : R) • a) := by abel
  rw [this]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h3)

end GlobalTheory
