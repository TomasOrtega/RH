import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxExtGr0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz R' _ _ _ f f' hf`. Use `haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ X R W hz`. Set `ι : ↥(W.gr 0) →ₐ[Λ] W.A` to `{ toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }`. Establish `hzA : ∀ s, ((W.zA s : W.A) : R) = W.z s` using `fun _ => rfl`. Establish `h0 : f.comp ι = f'.comp ι`.

Use `sxExtGr0 W hz R' _ _ ?_` and prove the remaining obligations. Introduce `b n _ hb`. Establish `hbA : (b : W.A) = n.prod fun s k => W.zA s ^ k`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hb]`.

Simplify using `[Finsupp.prod, hzA]`. Use `show f (b : W.A) = f' (b : W.A)`. Rewrite using `[hbA]`. Simplify using `[Finsupp.prod, map_prod, map_pow, hf]`. Use `AlgHom.ext_of_adjoin_eq_top (gr_gen Λ R X W) ?_` and prove the remaining obligations.

Introduce and unpack `x (hx | ⟨s, rfl⟩)`. Conclude with `congrArg (fun g => g ⟨x, hx⟩) h0`. Conclude with `hf s`.
-/
theorem UpperTheory.V.Ws.sxExtA :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R] (W : WPres Λ X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] (f f' : W.A →ₐ[Λ] R'), (∀ s, f (W.zA s) = f' (W.zA s)) → f = f' := by
  intro Λ _ _ _ _ X _ _ _ _ R _ _ _ W hz R' _ _ _ f f' hf
  haveI := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ X R W hz
  let ι : ↥(W.gr 0) →ₐ[Λ] W.A :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl, commutes' := fun _ => rfl }
  have hzA : ∀ s, ((W.zA s : W.A) : R) = W.z s := fun _ => rfl
  have h0 : f.comp ι = f'.comp ι := by
    refine sxExtGr0 W hz R' _ _ ?_
    intro b n _ hb
    have hbA : (b : W.A) = n.prod fun s k => W.zA s ^ k := by
      apply Subtype.ext
      rw [hb]
      simp [Finsupp.prod, hzA]
    show f (b : W.A) = f' (b : W.A)
    rw [hbA]
    simp [Finsupp.prod, map_prod, map_pow, hf]
  refine AlgHom.ext_of_adjoin_eq_top (gr_gen Λ R X W) ?_
  rintro x (hx | ⟨s, rfl⟩)
  · exact congrArg (fun g => g ⟨x, hx⟩) h0
  · exact hf s
