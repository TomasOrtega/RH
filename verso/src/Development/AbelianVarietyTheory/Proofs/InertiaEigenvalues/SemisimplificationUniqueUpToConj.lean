import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

noncomputable def bnMatRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) :
    Γ →* GL (Fin a) k :=
  MonoidHom.toHomUnits
    (((LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom).comp s)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bnMatRep_val {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)
      = LinearMap.toMatrix b b (s g) := rfl

/- English proof (translation)
Rewrite using `[bnMatRep_val]`. Conclude with `LinearMap.toMatrix_mulVec_repr b b (s g) v`.
-/
theorem bnMatRep_mulVec {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W) (g : Γ)
    (v : W) :
    ((bnMatRep b s g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).mulVec (b.equivFun v)
      = b.equivFun (s g v) := by
  rw [bnMatRep_val]
  exact LinearMap.toMatrix_mulVec_repr b b (s g) v

/- English proof (translation)
Introduce `U hU`. Take `⟨U', hU', hc⟩` from `hs (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) (by`. Introduce `g v hv`. Use `hU g _ hv` as an intermediate fact. Simplify using `only [Submodule.mem_comap, LinearEquiv.coe_coe] at this ⊢`.

Rewrite using `[← bnMatRep_mulVec]`. Conclude with `this)`. Use `⟨U'.map (b.equivFun : W →ₗ[k] (Fin a → k)), ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `g _ ⟨v, hv, rfl⟩`. Use `⟨s g v, hU' g v hv, ?_⟩` and prove the remaining obligations.

Conclude with `(bnMatRep_mulVec b s g v).symm`. Establish `h` using `(Submodule.orderIsoMapComap b.equivFun).isCompl hc`. Establish `h1 : (Submodule.orderIsoMapComap b.equivFun) (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) = U` using `Submodule.map_comap_eq_of_surjective b.equivFun.surjective U`. Rewrite `h` using `[h1]`. Conclude with `h`.
-/
theorem bnMatRep_isSSRep {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W]
    [Module k W] {a : ℕ} (b : Module.Basis (Fin a) k W) (s : Representation k Γ W)
    (hs : IsSS s) : IsSSRep (bnMatRep b s) := by
  intro U hU
  obtain ⟨U', hU', hc⟩ := hs (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) (by
    intro g v hv
    have := hU g _ hv
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe] at this ⊢
    rw [← bnMatRep_mulVec]
    exact this)
  refine ⟨U'.map (b.equivFun : W →ₗ[k] (Fin a → k)), ?_, ?_⟩
  · rintro g _ ⟨v, hv, rfl⟩
    refine ⟨s g v, hU' g v hv, ?_⟩
    exact (bnMatRep_mulVec b s g v).symm
  · have h := (Submodule.orderIsoMapComap b.equivFun).isCompl hc
    have h1 : (Submodule.orderIsoMapComap b.equivFun)
        (U.comap (b.equivFun : W →ₗ[k] (Fin a → k))) = U :=
      Submodule.map_comap_eq_of_surjective b.equivFun.surjective U
    rw [h1] at h
    exact h

/- English proof (translation)
Introduce `H k Γ _ _ W _ _ _ V _ _ _ s s' hs hs' hc`. Establish `hdim : Module.finrank k V = Module.finrank k W`. Rewrite using `[← LinearMap.charpoly_natDegree (s 1), ← LinearMap.charpoly_natDegree (s' 1), hc]`. Set `b : Module.Basis (Fin (Module.finrank k W)) k W` to `Module.finBasis k W`. Set `b' : Module.Basis (Fin (Module.finrank k W)) k V` to `Module.finBasisOfFinrankEq k V hdim`.

Take `⟨h, hh⟩` from `H Γ k _ (bnMatRep b s) (bnMatRep b' s') (bnMatRep_isSSRep b s hs) (bnMatRep_isSSRep b' s' hs') (by`. Introduce `g`. Rewrite using `[bnMatRep_val, bnMatRep_val, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hc])`. Set `m : (Fin (Module.finrank k W) → k) ≃ₗ[k] (Fin (Module.finrank k W) → k)` to `(Matrix.GeneralLinearGroup.toLin h).toLinearEquiv`. Establish `hm : ∀ x, m x = (h : Matrix _ _ k).mulVec x` using `fun x => rfl`.

Use `⟨b.equivFun.trans (m.trans b'.equivFun.symm), fun g v => ?_⟩` and prove the remaining obligations. Apply `b'.equivFun.injective` to reduce the goal to its premises. Rewrite using `[← bnMatRep_mulVec]`. Simplify using `only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hm]`. Rewrite using `[← bnMatRep_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hh g, inv_mul_cancel_right]`.
-/
theorem brauerNesbitt_abstract_of_matrix : (∀ (Γ k : Type) [Group Γ] [Field k] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) k), IsSSRep ρ → IsSSRep ρ' → (∀ g, ((ρ g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly = ((ρ' g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).charpoly) → ∃ h : GL (Fin a) k, ∀ g, ρ' g = h * ρ g * h⁻¹) → ∀ {k Γ : Type} [Field k] [Group Γ] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V] (s : Representation k Γ W) (s' : Representation k Γ V), IsSS s → IsSS s' → (∀ g, LinearMap.charpoly (s g) = LinearMap.charpoly (s' g)) → ∃ e : W ≃ₗ[k] V, ∀ g v, e (s g v) = s' g (e v) := by
  intro H k Γ _ _ W _ _ _ V _ _ _ s s' hs hs' hc
  have hdim : Module.finrank k V = Module.finrank k W := by
    rw [← LinearMap.charpoly_natDegree (s 1), ← LinearMap.charpoly_natDegree (s' 1), hc]
  let b : Module.Basis (Fin (Module.finrank k W)) k W := Module.finBasis k W
  let b' : Module.Basis (Fin (Module.finrank k W)) k V := Module.finBasisOfFinrankEq k V hdim
  obtain ⟨h, hh⟩ := H Γ k _ (bnMatRep b s) (bnMatRep b' s') (bnMatRep_isSSRep b s hs)
    (bnMatRep_isSSRep b' s' hs') (by
      intro g
      rw [bnMatRep_val, bnMatRep_val, LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix, hc])
  let m : (Fin (Module.finrank k W) → k) ≃ₗ[k] (Fin (Module.finrank k W) → k) :=
    (Matrix.GeneralLinearGroup.toLin h).toLinearEquiv
  have hm : ∀ x, m x = (h : Matrix _ _ k).mulVec x := fun x => rfl
  refine ⟨b.equivFun.trans (m.trans b'.equivFun.symm), fun g v => ?_⟩
  apply b'.equivFun.injective
  rw [← bnMatRep_mulVec]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, hm]
  rw [← bnMatRep_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    ← Units.val_mul, hh g, inv_mul_cancel_right]

end GlobalTheory
