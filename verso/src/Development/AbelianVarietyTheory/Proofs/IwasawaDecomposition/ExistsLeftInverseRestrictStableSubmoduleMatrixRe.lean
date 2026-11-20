import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.StableSubMat

/- English proof (translation)
Use `set b := Module.finrank L V`. Set `f : (Fin b → L) →ₗ[L] (Fin a → L)` to `V.subtype ∘ₗ (Module.finBasis L V).equivFun.symm.toLinearMap`. Establish `hfinj : LinearMap.ker f = ⊥`. Rewrite using `[LinearMap.ker_eq_bot]`. Conclude with `Subtype.val_injective.comp (Module.finBasis L V).equivFun.symm.injective`.

Establish `hfr : LinearMap.range f = V`. Rewrite using `[LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]`. Take `⟨g₀, hg₀⟩` from `LinearMap.exists_leftInverse_of_injective f hfinj`. Use `set E : Matrix (Fin a) (Fin b) L := LinearMap.toMatrix' f with hE`. Use `set D : Matrix (Fin b) (Fin a) L := LinearMap.toMatrix' g₀ with hD`.

Establish `hEf : E.mulVecLin = f` using `by rw [hE]; exact Matrix.toLin'_toMatrix' f`. Establish `hDf : D.mulVecLin = g₀` using `by rw [hD]; exact Matrix.toLin'_toMatrix' g₀`. Establish `hDE : D * E = 1`. Rewrite using `[hD, hE, ← LinearMap.toMatrix'_comp, hg₀, LinearMap.toMatrix'_id]`. Establish `hrange : LinearMap.range E.mulVecLin = V` using `by rw [hEf, hfr]`.

Establish `hED : ∀ v ∈ V, (E * D).mulVec v = v`. Introduce `v hv`. Rewrite `hv` using `[← hfr]`. Take `⟨w, rfl⟩` from `hv`. Rewrite using `[← Matrix.mulVec_mulVec]`.

Establish `h1 : D.mulVec (f w) = g₀ (f w)` using `by rw [← hDf]; rfl`. Establish `h2 : ∀ u, E.mulVec u = f u` using `fun u => by rw [← hEf]; rfl`. Rewrite using `[h1, h2, ← LinearMap.comp_apply g₀ f, hg₀, LinearMap.id_apply]`. Establish `key : ∀ g, E * D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E`. Introduce `g`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Simplify using `only [Matrix.toLin'_apply]`. Rewrite using `[Matrix.mul_assoc (E * D), ← Matrix.mulVec_mulVec (M := E * D)]`.

Apply `hED` to reduce the goal to its premises. Rewrite using `[← Matrix.mulVec_mulVec]`. Apply `hV` to reduce the goal to its premises. Rewrite using `[← hrange]`. Conclude with `⟨x, rfl⟩`.

Set `σm : Γ →* Matrix (Fin b) (Fin b) L` to `{ toFun := fun g => D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E map_one' := by simp [hDE] map_mul' := by`. Introduce `g h`. Simplify using `only [map_mul, Units.val_mul]`. Establish `k` using `key h`. Simplify using `only [Matrix.mul_assoc] at k ⊢`.

Rewrite using `[k] }`. Use `⟨b, E, D, σm.toHomUnits, hDE, hrange, fun g => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.coe_toHomUnits]`. Both sides reduce to the same expression. Rewrite using `[MonoidHom.coe_toHomUnits]`.

Express the relevant statement in the definitionally equal form `_ = E * (D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E)`. Establish `k` using `key g`. Simplify using `only [Matrix.mul_assoc] at k ⊢`. Conclude with `k.symm`.
-/
theorem exists_restrict {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (V : Submodule L (Fin a → L)) (hV : IsInv τ V) :
    ∃ (b : ℕ) (E : Matrix (Fin a) (Fin b) L) (D : Matrix (Fin b) (Fin a) L) (σ : Γ →* GL (Fin b) L),
      D * E = 1 ∧ LinearMap.range E.mulVecLin = V ∧
      ∀ g, ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) =
          D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E ∧
        ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
          E * ((σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
  classical
  set b := Module.finrank L V
  let f : (Fin b → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ (Module.finBasis L V).equivFun.symm.toLinearMap
  have hfinj : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp (Module.finBasis L V).equivFun.symm.injective
  have hfr : LinearMap.range f = V := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  obtain ⟨g₀, hg₀⟩ := LinearMap.exists_leftInverse_of_injective f hfinj
  set E : Matrix (Fin a) (Fin b) L := LinearMap.toMatrix' f with hE
  set D : Matrix (Fin b) (Fin a) L := LinearMap.toMatrix' g₀ with hD
  have hEf : E.mulVecLin = f := by rw [hE]; exact Matrix.toLin'_toMatrix' f
  have hDf : D.mulVecLin = g₀ := by rw [hD]; exact Matrix.toLin'_toMatrix' g₀
  have hDE : D * E = 1 := by
    rw [hD, hE, ← LinearMap.toMatrix'_comp, hg₀, LinearMap.toMatrix'_id]
  have hrange : LinearMap.range E.mulVecLin = V := by rw [hEf, hfr]

  have hED : ∀ v ∈ V, (E * D).mulVec v = v := by
    intro v hv
    rw [← hfr] at hv
    obtain ⟨w, rfl⟩ := hv
    rw [← Matrix.mulVec_mulVec]
    have h1 : D.mulVec (f w) = g₀ (f w) := by rw [← hDf]; rfl
    have h2 : ∀ u, E.mulVec u = f u := fun u => by rw [← hEf]; rfl
    rw [h1, h2, ← LinearMap.comp_apply g₀ f, hg₀, LinearMap.id_apply]
  have key : ∀ g, E * D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E =
      ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E := by
    intro g
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply]
    rw [Matrix.mul_assoc (E * D), ← Matrix.mulVec_mulVec (M := E * D)]
    apply hED
    rw [← Matrix.mulVec_mulVec]
    apply hV
    rw [← hrange]
    exact ⟨x, rfl⟩
  let σm : Γ →* Matrix (Fin b) (Fin b) L :=
    { toFun := fun g => D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E
      map_one' := by simp [hDE]
      map_mul' := by
        intro g h
        simp only [map_mul, Units.val_mul]
        have k := key h
        simp only [Matrix.mul_assoc] at k ⊢
        rw [k] }
  refine ⟨b, E, D, σm.toHomUnits, hDE, hrange, fun g => ⟨?_, ?_⟩⟩
  · rw [MonoidHom.coe_toHomUnits]; rfl
  · rw [MonoidHom.coe_toHomUnits]
    change _ = E * (D * ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * E)
    have k := key g
    simp only [Matrix.mul_assoc] at k ⊢
    exact k.symm

end GlobalTheory.StableSubMat
