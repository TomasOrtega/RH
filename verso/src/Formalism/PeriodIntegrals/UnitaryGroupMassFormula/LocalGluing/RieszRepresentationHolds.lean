import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalGluing.LocGlueOfPair

noncomputable section

open ValuativeRel
open Formalism.MainNotions.S.Loc

namespace PI.LocHerm.Glue

/- English proof (translation)
Introduce `F _ _ _ E _ _ _ _ M V _ _ H f`. Establish `: Module.Free F E` using `M.L.free`. Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)`. Establish `: IsArtinianRing E` using `IsArtinianRing.of_finite F E`. Establish `: Module.Free E V` using `H.free`.

Establish `: Module.Finite E V` using `H.fin`. Set `b` to `Module.Free.chooseBasis E V`. Set `ℓ : V → V →ₗ[E] E` to `fun y => { toFun := fun v => H.h v y map_add' := fun v w => H.h_add_left v w y map_smul' := fun c v => by`. Simplify using `only [RingHom.id_apply, smul_eq_mul]`. Conclude with `H.h_smul_left c v y }`.

Establish `hℓ : ∀ v y, ℓ y v = H.h v y` using `fun _ _ => rfl`. Establish `key : ∀ (v : V) (a : Module.Free.ChooseBasisIndex E V → E), H.h v (∑ j, a j • b j) = ∑ j, M.L.cj (a j) * H.h v (b j)`. Introduce `v a`. Rewrite using `[H.h_herm (∑ j, a j • b j) v]`. Establish `hs : H.h (∑ j, a j • b j) v = ∑ j, a j * H.h (b j) v`.

Rewrite using `[← hℓ, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hℓ, smul_eq_mul]`. Rewrite using `[hs, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, ← H.h_herm]`. Set `A : Matrix (Module.Free.ChooseBasisIndex E V) (Module.Free.ChooseBasisIndex E V) E` to `Matrix.of fun i j => H.h (b i) (b j)`. Establish `hA : ∀ u i, H.h (b i) (∑ j, M.L.cj (u j) • b j) = A.mulVecLin u i`. Introduce `u i`. Rewrite using `[key, Matrix.mulVecLin_apply]`.

Simplify using `only [M.L.cj_cj, Matrix.mulVec, dotProduct, A, Matrix.of_apply]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hext : ∀ (x : V) (g : V →ₗ[E] E), (∀ i, H.h (b i) x = g (b i)) → ∀ v, H.h v x = g v`. Introduce `x g hg v`.

Establish `: ℓ x = g` using `b.ext fun i => by rw [hℓ]; exact hg i`. Rewrite using `[← hℓ, this]`. Establish `hinj : Function.Injective A.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `u hu`.

Establish `hx : ∀ v, H.h v (∑ j, M.L.cj (u j) • b j) = (0 : V →ₗ[E] E) v`. Use `hext _ 0 fun i => ?_` and prove the remaining obligations. Rewrite using `[hA, hu]`. Both sides reduce to the same expression. Establish `hx0 : (∑ j, M.L.cj (u j) • b j) = 0`.

Use `H.nondeg _ fun y => ?_` and prove the remaining obligations. Rewrite using `[H.h_herm y, hx y, LinearMap.zero_apply, map_zero]`. Establish `hc : (fun j => M.L.cj (u j)) = 0`. Apply `b.equivFun.symm.injective` to reduce the goal to its premises. Rewrite using `[Module.Basis.equivFun_symm_apply, hx0, map_zero]`.

Use function extensionality and compare the values at `j`. Use `congrFun hc j` as an intermediate fact. Simplify using `only [Pi.zero_apply] at this`. Establish `h2` using `congrArg M.L.cj this`. Rewrite `h2` using `[M.L.cj_cj, map_zero]`.

Conclude with `h2`. Take `⟨u, hu⟩` from `IsArtinian.surjective_of_injective_endomorphism A.mulVecLin hinj (fun i => f (b i))`. Use `⟨∑ j, M.L.cj (u j) • b j, hext _ f fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hA, hu]`.
-/
theorem rieszRepresentation_holds : Riesz := by
  intro F _ _ _ E _ _ _ _ M V _ _ H f
  have : Module.Free F E := M.L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [M.L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have : Module.Free E V := H.free
  have : Module.Finite E V := H.fin
  let b := Module.Free.chooseBasis E V
  let ℓ : V → V →ₗ[E] E := fun y =>
    { toFun := fun v => H.h v y
      map_add' := fun v w => H.h_add_left v w y
      map_smul' := fun c v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact H.h_smul_left c v y }
  have hℓ : ∀ v y, ℓ y v = H.h v y := fun _ _ => rfl
  have key : ∀ (v : V) (a : Module.Free.ChooseBasisIndex E V → E),
      H.h v (∑ j, a j • b j) = ∑ j, M.L.cj (a j) * H.h v (b j) := by
    intro v a
    rw [H.h_herm (∑ j, a j • b j) v]
    have hs : H.h (∑ j, a j • b j) v = ∑ j, a j * H.h (b j) v := by
      rw [← hℓ, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, hℓ, smul_eq_mul]
    rw [hs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← H.h_herm]
  let A : Matrix (Module.Free.ChooseBasisIndex E V) (Module.Free.ChooseBasisIndex E V) E :=
    Matrix.of fun i j => H.h (b i) (b j)
  have hA : ∀ u i, H.h (b i) (∑ j, M.L.cj (u j) • b j) = A.mulVecLin u i := by
    intro u i
    rw [key, Matrix.mulVecLin_apply]
    simp only [M.L.cj_cj, Matrix.mulVec, dotProduct, A, Matrix.of_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hext : ∀ (x : V) (g : V →ₗ[E] E), (∀ i, H.h (b i) x = g (b i)) → ∀ v, H.h v x = g v := by
    intro x g hg v
    have : ℓ x = g := b.ext fun i => by rw [hℓ]; exact hg i
    rw [← hℓ, this]
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    have hx : ∀ v, H.h v (∑ j, M.L.cj (u j) • b j) = (0 : V →ₗ[E] E) v := by
      refine hext _ 0 fun i => ?_
      rw [hA, hu]
      rfl
    have hx0 : (∑ j, M.L.cj (u j) • b j) = 0 := by
      refine H.nondeg _ fun y => ?_
      rw [H.h_herm y, hx y, LinearMap.zero_apply, map_zero]
    have hc : (fun j => M.L.cj (u j)) = 0 := by
      apply b.equivFun.symm.injective
      rw [Module.Basis.equivFun_symm_apply, hx0, map_zero]
    funext j
    have := congrFun hc j
    simp only [Pi.zero_apply] at this
    have h2 := congrArg M.L.cj this
    rw [M.L.cj_cj, map_zero] at h2
    exact h2
  obtain ⟨u, hu⟩ := IsArtinian.surjective_of_injective_endomorphism A.mulVecLin hinj
    (fun i => f (b i))
  refine ⟨∑ j, M.L.cj (u j) • b j, hext _ f fun i => ?_⟩
  rw [hA, hu]

end PI.LocHerm.Glue
