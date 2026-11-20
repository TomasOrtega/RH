import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

abbrev cmap {κ X A : Type} [AddCommGroup X] [CommRing A] (b : Module.Basis κ ℤ X) (v : κ → Aˣ) :
    Multiplicative X →* A :=
  (Units.coeHom A).comp (AddMonoidHom.toMultiplicativeLeft
    (b.constr ℤ (fun k => Additive.ofMul (v k))).toAddMonoidHom)

/- English proof (translation)
Establish `hlin : b.constr ℤ (fun k => Additive.ofMul (v' k)) = (MonoidHom.toAdditive (Units.map (ρ : A →* A'))).toIntLinearMap ∘ₗ b.constr ℤ (fun k => Additive.ofMul (v k))`. Use `b.ext (fun k => ?_)` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]`. Use `show Additive.ofMul (v' k) = Additive.ofMul (Units.map (ρ : A →* A') (v k))`. Use `congr 1`.

Conclude with `Units.ext (by simpa using hv k)`. Establish `hx` using `congrArg (fun f => ((Additive.toMul (f (Multiplicative.toAdd x)) : A'ˣ) : A')) hlin`. Use `first`. Consider the case `exact hx`. Consider the case `simpa using hx`.
-/
theorem cmap_comp {κ X A A' : Type} [AddCommGroup X] [CommRing A] [CommRing A']
    (b : Module.Basis κ ℤ X) (ρ : A →+* A') (v : κ → Aˣ) (v' : κ → A'ˣ)
    (hv : ∀ k, (v' k).val = ρ (v k).val) (x : Multiplicative X) :
    cmap b v' x = ρ (cmap b v x) := by
  have hlin : b.constr ℤ (fun k => Additive.ofMul (v' k)) =
      (MonoidHom.toAdditive (Units.map (ρ : A →* A'))).toIntLinearMap ∘ₗ
        b.constr ℤ (fun k => Additive.ofMul (v k)) := by
    refine b.ext (fun k => ?_)
    rw [LinearMap.comp_apply, Module.Basis.constr_basis, Module.Basis.constr_basis]
    show Additive.ofMul (v' k) = Additive.ofMul (Units.map (ρ : A →* A') (v k))
    congr 1
    exact Units.ext (by simpa using hv k)
  have hx := congrArg (fun f => ((Additive.toMul (f (Multiplicative.toAdd x)) : A'ˣ) : A')) hlin
  first
  | exact hx
  | simpa using hx

open ReciprocityTheory.ChartRestriction.G.Semi in
/- English proof (translation)
Establish `key : g.app U₀ ≫ Y.presheaf.map (homOfLE hW).op ≫ Y.presheaf.map (homOfLE hVW).op = X.presheaf.map (homOfLE hU).op ≫ g.appLE U V hV`. Rewrite using `[Scheme.Hom.map_appLE, ← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]`. Establish `h2` using `congrArg (fun f => f.hom u.val) key`. Use `first`. Consider the case `exact h2`.

Consider the case `simpa [res, pullU] using h2`.
-/
theorem appLE_res {X Y : Scheme.{0}} (g : Y ⟶ X) {U U₀ : X.Opens} (hU : U ≤ U₀) {V W : Y.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ g ⁻¹ᵁ U₀) (hVW : V ≤ W) (u : Γ(X, U₀)ˣ) :
    (res hVW (res hW (pullU g U₀ u))).val = (g.appLE U V hV).hom (res hU u).val := by
  have key : g.app U₀ ≫ Y.presheaf.map (homOfLE hW).op ≫ Y.presheaf.map (homOfLE hVW).op =
      X.presheaf.map (homOfLE hU).op ≫ g.appLE U V hV := by
    rw [Scheme.Hom.map_appLE, ← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have h2 := congrArg (fun f => f.hom u.val) key
  first
  | exact h2
  | simpa [res, pullU] using h2

end ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
