import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K']

/- English proof (translation)
Rewrite using `[map_mul, DVR.res_res']`.
-/
theorem res_top_mul {U V : Y.Opens} (hV : V ≤ U) (a : Γ(Y, ⊤)ˣ) (x : Γ(Y, U)ˣ) :
    res hV (res le_top a * x) = res le_top a * res hV x := by
  rw [map_mul, DVR.res_res']

/- English proof (translation)
Use `ext`. Simplify using `only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]`. Use `congr 1`. Simplify using `only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]`.

Use `erw [Scheme.Hom.appLE_map]`.
-/
theorem pull_top_res (h : Z ⟶ Y) {U : Y.Opens} {W : Z.Opens} (hW : W ≤ h ⁻¹ᵁ U) (a : Γ(Y, ⊤)ˣ) :
    res hW (pullU h U (res le_top a)) = res le_top (Units.map h.appTop.hom.toMonoidHom a) := by
  ext
  simp only [res, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply]
  congr 1
  simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  erw [Scheme.Hom.appLE_map]

/- English proof (translation)
Consider the cases of `g`. Simplify using `only [scaleGenG, map_one, one_mul]`.
-/
theorem scaleGenG_one (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε 1 g = g := by
  cases g
  simp only [scaleGenG, map_one, one_mul]

/- English proof (translation)
Unfold `LB.pullGen scaleGenG`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `erw [map_mul, map_mul, pull_top_res]`.
-/
theorem pullGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (h : Z ⟶ Y) :
    LB.pullGen t.PP.L φ ε (scaleGenG t φ ε v g) h =
      scaleGenG t (fun k => h ≫ φ k) ε (Units.map h.appTop.hom.toMonoidHom v) (LB.pullGen t.PP.L φ ε g h) := by
  unfold LB.pullGen scaleGenG
  congr 1
  funext j
  erw [map_mul, map_mul, pull_top_res]

/- English proof (translation)
Unfold `LB.mulGen scaleGenG`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]`. Both sides reduce to the same expression.
-/
theorem mulGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (φ' : K' → (Y ⟶ t.G.left)) (ε' : K' → ℤ)
    (v v' : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (g' : LB.Gen (LB.LinComb t.PP.L φ' ε')) :
    LB.mulGen t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g') =
      scaleGenG t _ _ (v * v') (LB.mulGen t.PP.L φ ε φ' ε' g g') := by
  unfold LB.mulGen scaleGenG
  congr 1
  funext j
  erw [res_top_mul, res_top_mul, map_mul, mul_mul_mul_comm]
  rfl

/- English proof (translation)
Unfold `LB.invGen scaleGenG`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `erw [map_inv, mul_inv_rev, mul_comm]`. Both sides reduce to the same expression.
-/
theorem invGen_scaleGenG (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (v : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    LB.invGen t.PP.L φ ε (scaleGenG t φ ε v g) = scaleGenG t φ _ v⁻¹ (LB.invGen t.PP.L φ ε g) := by
  unfold LB.invGen scaleGenG
  congr 1
  funext j
  erw [map_inv, mul_inv_rev, mul_comm]
  rfl

/- English proof (translation)
Introduce `j j' hj hj' hm`. Establish `e` using `hc j j' hj hj' hm`. Unfold `scaleGenG`. Simplify using `only`. Use `erw [res_top_mul, res_top_mul, e]`.
-/
theorem corr_scaleGenG {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') (v : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v g') := by
  intro j j' hj hj' hm
  have e := hc j j' hj hj' hm
  unfold scaleGenG
  dsimp only
  erw [res_top_mul, res_top_mul, e]

/- English proof (translation)
Use `DVR.units_ext_cover ⊤ (fun ρ => ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ) (fun _ => inf_le_left) (DVR.le_iSup_piece t.PP.L φ φ' hL ⊤) v v' fun ρ => ?_` and prove the remaining obligations. Establish `hj : LB.Coh t.PP.L φ (ρ ∘ φ)` using `fun k₁ k₂ e => by simp [e]`. Establish `hj' : LB.Coh t.PP.L φ' (ρ ∘ φ')` using `fun k₁ k₂ e => by simp [e]`. Establish `hm : ∀ k k', φ k = φ' k' → (ρ ∘ φ) k = (ρ ∘ φ') k'` using `fun k k' e => by simp [e]`. Establish `e1` using `h _ _ hj hj' hm`.

Establish `e2` using `hc _ _ hj hj' hm`. Unfold `scaleGenG at e1`. Simplify using `only at e1`. Use `erw [res_top_mul, res_top_mul, e2, mul_left_inj] at e1`. Establish `e3` using `congrArg (res (show ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ ≤ LB.wchart t.PP.L φ (ρ ∘ φ) ⊓ LB.wchart t.PP.L φ' (ρ ∘ φ') from inf_le_right)) e1`.

Simplify `e3` using `only [DVR.res_res']`.
-/
theorem scale_eq_of_corr (hL : t.PP.L.IsLB) {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {φ' : K' → (Y ⟶ t.G.left)} {ε' : K' → ℤ}
    {g : LB.Gen (LB.LinComb t.PP.L φ ε)} {g' : LB.Gen (LB.LinComb t.PP.L φ' ε')}
    (hc : LB.Gen.Corr t.PP.L φ ε φ' ε' g g') {v v' : Γ(Y, ⊤)ˣ}
    (h : LB.Gen.Corr t.PP.L φ ε φ' ε' (scaleGenG t φ ε v g) (scaleGenG t φ' ε' v' g')) : v = v' := by
  refine DVR.units_ext_cover ⊤ (fun ρ => ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ) (fun _ => inf_le_left)
    (DVR.le_iSup_piece t.PP.L φ φ' hL ⊤) v v' fun ρ => ?_
  have hj : LB.Coh t.PP.L φ (ρ ∘ φ) := fun k₁ k₂ e => by simp [e]
  have hj' : LB.Coh t.PP.L φ' (ρ ∘ φ') := fun k₁ k₂ e => by simp [e]
  have hm : ∀ k k', φ k = φ' k' → (ρ ∘ φ) k = (ρ ∘ φ') k' := fun k k' e => by simp [e]
  have e1 := h _ _ hj hj' hm
  have e2 := hc _ _ hj hj' hm
  unfold scaleGenG at e1
  dsimp only at e1
  erw [res_top_mul, res_top_mul, e2, mul_left_inj] at e1
  have e3 := congrArg (res (show ⊤ ⊓ DVR.piece t.PP.L φ φ' ρ ≤
    LB.wchart t.PP.L φ (ρ ∘ φ) ⊓ LB.wchart t.PP.L φ' (ρ ∘ φ') from inf_le_right)) e1
  simpa only [DVR.res_res'] using e3

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0)

/- English proof (translation)
Use `ext`. Simplify using `only [unitΓ, toΓ, homAt, Over.homMk_left, spMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]`. Both sides reduce to the same expression.
-/
theorem unitΓ_homAt {A B : Type} [CommRing A] [Algebra S A] [CommRing B] [Algebra S B] (f : A →ₐ[S] B)
    (u : Aˣ) :
    Units.map (homAt x0 f).left.appTop.hom.toMonoidHom (unitΓ u) = unitΓ (Units.map f.toMonoidHom u) := by
  ext
  simp only [unitΓ, toΓ, homAt, Over.homMk_left, spMap, Units.coe_map, MonoidHom.coe_coe,
    RingHom.toMonoidHom_eq_coe]
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/- English proof (translation)
Introduce `u u' h`. Use `ext`. Establish `h1` using `congrArg Units.val h`. Simplify using `only [unitΓ, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, toΓ] at h1`. Establish `h2` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom h1`.

Simplify using `using h2`.
-/
theorem unitΓ_injective {A : Type} [CommRing A] : Function.Injective (unitΓ (A := A)) := by
  intro u u' h
  ext
  have h1 := congrArg Units.val h
  simp only [unitΓ, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, toΓ] at h1
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom h1
  simpa using h2

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdLB
