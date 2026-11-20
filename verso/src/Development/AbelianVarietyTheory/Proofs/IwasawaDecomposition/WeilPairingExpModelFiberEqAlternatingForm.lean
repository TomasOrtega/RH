import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PushExLeft
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedPointMemRange

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

/- English proof (translation)
Set `β` to `GlobalTheory.UU.toBaseHom (hw := h.1.w) (GlobalTheory.TowerAlg.toBase_mul h) T`. Establish `hinj : Function.Injective β` using `fun a b e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))`. Conclude with `hinj ((map_pow β x N).trans (hx.trans (map_one β).symm))`.
-/
theorem pow_eq_one_of_toBase {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {T : Over S'} (x : T ⟶ G') (N : ℕ)
    (hx : Out.toBase h.1.w x ^ N = 1) : x ^ N = 1 := by
  let β := GlobalTheory.UU.toBaseHom (hw := h.1.w) (GlobalTheory.TowerAlg.toBase_mul h) T
  have hinj : Function.Injective β := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  exact hinj ((map_pow β x N).trans (hx.trans (map_one β).symm))

/- English proof (translation)
Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Establish `tors : ∀ d : (Fu.Di i).La, Fu.ex i P ((k : ℂ)⁻¹ • P d) ^ k = 1` using `fun d => by`. Establish `hpow : ∀ (n : ℕ) (z : Fin g → ℂ), Fu.ex i P z ^ n = Fu.ex i P (n • z)` using `fun n z => by`. Proceed by induction on `n with`. Consider the case `zero => simpa using ((Fu.ex_ker i P hP 0).2 (zero_mem _)).symm`.

Consider the case `succ n ih => rw [pow_succ, ih, ← Fu.ex_add i P hP, succ_nsmul]`. Rewrite using `[hpow, Fu.ex_ker i P hP]`. Conclude with `⟨d, by`. Use extensionality with `j`. Simplify using `[hk']⟩`.

Establish `h₀ : GlobalTheory.UU.CubWeil Xo.univ.t.cub k (Fu.ex i P ((k : ℂ)⁻¹ • P a)) (Fu.ex i P ((k : ℂ)⁻¹ • P b)) (unitOn ζ)` using `(GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme Xo.univ) (tors a) (tors b) _).2 (by exact_mod_cast Fu.ex_weil i P hP k a b ζ hk hζ)`. Set `f₀` to `pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)`. Set `m₀` to `Z.m0.toSABMap`. Set `σ : Over.mk (y ≫ f₀) ⟶ Over.mk (Fu.u i P)` to `Over.homMk (𝟙 _) ((Category.id_comp _).trans hu)`. Establish `h₁` using `h₀.comp σ`.

Establish `e₁ : Units.map σ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ`. Use `ext`. Simplify using `[σ]`. Rewrite `h₁` using `[e₁]`. Set `lf : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G)` to `fun z => Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)`.

Establish `eb : ∀ z, Out.toBase m₀.cart.1.w (lf z) = σ ≫ Fu.ex i P z` using `fun z => Over.OverMorphism.ext ((liftEx_fst Z Fu y i P hu z).trans (by simp [σ]))`. Establish `tl : ∀ d : (Fu.Di i).La, lf ((k : ℂ)⁻¹ • P d) ^ k = 1` using `fun d => pow_eq_one_of_toBase m₀.cart _ k (by`. Rewrite using `[eb, ← MonObj.comp_pow, tors, MonObj.comp_one])`. Take `⟨ζ', hζ', -⟩` from `GlobalTheory.UU.existsUnique_cubWeil Z.oF.t.cub (tl a) (tl b)`. Establish `h₂` using `GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₀ _ _ m₀.cm m₀.cart.1.w (GlobalTheory.TowerAlg.toBase_mul m₀.cart) _ _ _ _ m₀.lin k _ _ _ ζ' hζ'`.

Rewrite `h₂` using `[eb, eb]`. Take `rfl : ζ' = unitOn ζ` from `h₂.unique h₁`. Establish `h₃` using `GlobalTheory.UU.cubWeil_of_isPullCubical _ _ _ _ _ Z.m.cm Z.m.cart.1.w (GlobalTheory.TowerAlg.toBase_mul Z.m.cart) _ _ _ _ Z.m.lin k _ _ _ _ hζ'`. Set `τ : Over.mk p ⟶ Over.mk ((Over.mk y).hom ≫ Z.jQ ≫ pullback.fst Z.s (spMap β))` to `Over.homMk (𝟙 _) ((Category.id_comp _).trans hp)`. Establish `h₄` using `h₃.comp τ`.

Establish `e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ`. Use `ext`. Simplify using `[τ]`. Rewrite `h₄` using `[e₂]`. Establish `e₃ : ∀ z, τ ≫ Out.toBase Z.m.cart.1.w (lf z) = pushEx Z Fu y i P p hu hp z` using `fun z => Over.OverMorphism.ext (Category.id_comp _)`.

Rewrite `h₄` using `[e₃, e₃]`. Then use the resulting hypothesis.
-/
theorem pushEx_cubWeil (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ)
    (hk : 0 < k) (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k)) :
    GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b))
      (unitOn ζ) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'

  have tors : ∀ d : (Fu.Di i).La, Fu.ex i P ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d => by
    have hpow : ∀ (n : ℕ) (z : Fin g → ℂ), Fu.ex i P z ^ n = Fu.ex i P (n • z) := fun n z => by
      induction n with
      | zero => simpa using ((Fu.ex_ker i P hP 0).2 (zero_mem _)).symm
      | succ n ih => rw [pow_succ, ih, ← Fu.ex_add i P hP, succ_nsmul]
    rw [hpow, Fu.ex_ker i P hP]
    exact ⟨d, by
      ext j
      simp [hk']⟩
  have h₀ : GlobalTheory.UU.CubWeil Xo.univ.t.cub k (Fu.ex i P ((k : ℂ)⁻¹ • P a)) (Fu.ex i P ((k : ℂ)⁻¹ • P b)) (unitOn ζ) :=
    (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme Xo.univ) (tors a) (tors b) _).2
      (by exact_mod_cast Fu.ex_weil i P hP k a b ζ hk hζ)
  let f₀ := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let m₀ := Z.m0.toSABMap

  let σ : Over.mk (y ≫ f₀) ⟶ Over.mk (Fu.u i P) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hu)
  have h₁ := h₀.comp σ
  have e₁ : Units.map σ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [σ]
  rw [e₁] at h₁

  let lf : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
    Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
  have eb : ∀ z, Out.toBase m₀.cart.1.w (lf z) = σ ≫ Fu.ex i P z := fun z =>
    Over.OverMorphism.ext ((liftEx_fst Z Fu y i P hu z).trans (by simp [σ]))
  have tl : ∀ d : (Fu.Di i).La, lf ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d =>
    pow_eq_one_of_toBase m₀.cart _ k (by
      rw [eb, ← MonObj.comp_pow, tors, MonObj.comp_one])
  obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil Z.oF.t.cub (tl a) (tl b)
  have h₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₀ _ _ m₀.cm m₀.cart.1.w (GlobalTheory.TowerAlg.toBase_mul m₀.cart) _ _ _ _ m₀.lin
    k _ _ _ ζ' hζ'
  rw [eb, eb] at h₂
  obtain rfl : ζ' = unitOn ζ := h₂.unique h₁
  have h₃ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ _ _ _ Z.m.cm Z.m.cart.1.w (GlobalTheory.TowerAlg.toBase_mul Z.m.cart) _ _ _ _ Z.m.lin
    k _ _ _ _ hζ'

  let τ : Over.mk p ⟶ Over.mk ((Over.mk y).hom ≫ Z.jQ ≫ pullback.fst Z.s (spMap β)) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hp)
  have h₄ := h₃.comp τ
  have e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [τ]
  rw [e₂] at h₄
  have e₃ : ∀ z, τ ≫ Out.toBase Z.m.cart.1.w (lf z) = pushEx Z Fu y i P p hu hp z := fun z =>
    Over.OverMorphism.ext (Category.id_comp _)
  rwa [e₃, e₃] at h₄

end GlobalTheory.ShFam.Hor.LogCh
