import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdLB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {Y Z : Scheme.{0}} {K : Type} [Fintype K]

end Gen

section GenX

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {Y Z : Scheme.{0}} {K : Type} [Fintype K]

end GenX

section Sec

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `Iff.rfl`.
-/
theorem isPullSec_congr {T T' : Over S0} {h₁ h₂ : T' ⊗ A ⟶ T ⊗ A} (e : h₁ = h₂)
    (hh₁ : h₁ ≫ snd T A = snd T' A) (hh₂ : h₂ ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L a T')) :
    IsPullSec A L a h₁ hh₁ s s' ↔ IsPullSec A L a h₂ hh₂ s s' := by
  subst e
  exact Iff.rfl

/- English proof (translation)
Take `⟨f1, c1⟩` from `s'`. Take `⟨f2, c2⟩` from `s''`. Establish `hf : f1 = f2` using `funext fun j => (h' j).trans (h'' j).symm`. Substitute `hf` using the available equality. Both sides reduce to the same expression.
-/
theorem isPullSec_unique {T T' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' s'' : LB.Sec (LPow A L a T')}
    (h' : IsPullSec A L a h hh s s') (h'' : IsPullSec A L a h hh s s'') : s' = s'' := by
  obtain ⟨f1, c1⟩ := s'
  obtain ⟨f2, c2⟩ := s''
  have hf : f1 = f2 := funext fun j => (h' j).trans (h'' j).symm
  subst hf
  rfl

end Sec

section Val

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

/- English proof (translation)
Establish `e : ptSecT A (g ≫ z) ≫ (g ▷ A) = g ≫ ptSecT A z`. Unfold `ptSecT`. Apply the tactic sequence `ext <;> simp`. Establish `e'` using `congrArg CommaMorphism.left e`. Simplify using `using e'`.
-/
theorem ptSecT_whisker {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) :
    (ptSecT A (g ≫ z)).left ≫ (g ▷ A).left = g.left ≫ (ptSecT A z).left := by
  have e : ptSecT A (g ≫ z) ≫ (g ▷ A) = g ≫ ptSecT A z := by
    unfold ptSecT
    ext <;> simp
  have e' := congrArg CommaMorphism.left e
  simpa using e'

/- English proof (translation)
Introduce `j`. Establish `hW : ∀ x ∈ LB.wchart L (fun _ : Fin 1 => (g ≫ z).left) j, g.left x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j` using `fun x hx => Set.mem_iInter.2 fun k => by`. Establish `h1` using `Set.mem_iInter.1 hx k`. Simplify `h1` using `[Over.comp_left, Scheme.Hom.comp_base]`. Apply `fn_ext` to reduce the goal to its premises.

Introduce `x hx`. Establish `hx'` using `hW x hx`. Establish `hPz` using `val_le A L z j hx'`. Establish `hPgz` using `val_le A L (g ≫ z) j hx`. Use `erw [gs_res _ x _ hx, gs_pull (𝟙 _) _ x _ hPgz, Category.id_comp, hs j, gs_res _ x _ hPgz, gs_pull (ptSecT A (g ≫ z)).left (g ▷ A).left x ((LPow A L a T).U j) (chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j (show (ptSecT A (g ≫ z)).left x ∈ (LPow A L a T').U j from hPgz)), p …`.

Use `erw [gs_mul _ x _ hx, gs_res _ x le_top hx, gs_pull (𝟙 T'.left) g.left x ⊤ (by simp), Category.id_comp]`. Use `congr 1`. Simplify using `only`. Use `show gs g.left x (LB.wchart L (fun _ : Fin 1 => z.left) j) (τ.s j).val = gs (𝟙 _) x _ (((T'.left.presheaf.map (homOfLE _).op).hom ((g.left.app _).hom (τ.s j).val)))`. Use `erw [gs_res _ x _ hx, gs_pull (𝟙 _) g.left x _ hx', Category.id_comp]`.
-/
theorem isValueAt_pull {T T' : Over S0} (g : T' ⟶ T) (z : T ⟶ A) {s : LB.Sec (LPow A L a T)}
    {s' : LB.Sec (LPow A L a T')} (hs : IsPullSec A L a (g ▷ A) (whiskerRight_snd g A) s s')
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (hv : IsValueAt A L a s z τ v) :
    IsValueAt A L a s' (g ≫ z) (LB.pullGen L (fun _ => z.left) (fun _ => a) τ g.left) (g.left.appTop.hom v) := by
  intro j
  have hW : ∀ x ∈ LB.wchart L (fun _ : Fin 1 => (g ≫ z).left) j,
      g.left x ∈ LB.wchart L (fun _ : Fin 1 => z.left) j := fun x hx =>
    Set.mem_iInter.2 fun k => by
      have h1 := Set.mem_iInter.1 hx k
      simpa [Over.comp_left, Scheme.Hom.comp_base] using h1
  apply fn_ext
  intro x hx
  have hx' := hW x hx
  have hPz := val_le A L z j hx'
  have hPgz := val_le A L (g ≫ z) j hx

  erw [gs_res _ x _ hx, gs_pull (𝟙 _) _ x _ hPgz, Category.id_comp, hs j,
    gs_res _ x _ hPgz, gs_pull (ptSecT A (g ≫ z)).left (g ▷ A).left x ((LPow A L a T).U j)
      (chart_le_res A L (g ▷ A) (whiskerRight_snd g A) a j
        (show (ptSecT A (g ≫ z)).left x ∈ (LPow A L a T').U j from hPgz)),
    ptSecT_whisker, ← gs_pull g.left (ptSecT A z).left x _ hPz, ← gs_res _ x (val_le A L z j) hx',
    hv j, gs_mul _ x _ hx', gs_res _ x le_top hx']

  erw [gs_mul _ x _ hx, gs_res _ x le_top hx, gs_pull (𝟙 T'.left) g.left x ⊤ (by simp), Category.id_comp]
  congr 1
  dsimp only
  show gs g.left x (LB.wchart L (fun _ : Fin 1 => z.left) j) (τ.s j).val =
    gs (𝟙 _) x _ (((T'.left.presheaf.map (homOfLE _).op).hom ((g.left.app _).hom (τ.s j).val)))
  erw [gs_res _ x _ hx, gs_pull (𝟙 _) g.left x _ hx', Category.id_comp]

end Val

section Rig

/- English proof (translation)
Use `ext`. Simplify using `only [res, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
private theorem res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)ˣ) :
    res h2 (res h1 x) = res (h2.trans h1) x := by
  ext
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Substitute `hf` using the available equality. Establish `hA : V ≤ (g ≫ f) ⁻¹ᵁ U` using `fun y hy => hW (hV hy)`. Simplify using `only [map_zpow]`. Use `congr 1`. Rewrite using `[← DVR.res_pullU_comp' g f hW hV hA x, res_res_lemma, res_res_lemma]`.
-/
theorem shape_rig {X T T' : Scheme.{0}} (g : T' ⟶ T) (f : T ⟶ X) (f' : T' ⟶ X) (hf : g ≫ f = f')
    {U : X.Opens} {W : T.Opens} (hW : W ≤ f ⁻¹ᵁ U) {V : T'.Opens} (hV : V ≤ g ⁻¹ᵁ W) {V' : T'.Opens}
    (hV' : V' ≤ f' ⁻¹ᵁ U) {O : T'.Opens} (o1 : O ≤ V) (o2 : O ≤ V') (x : Γ(X, U)ˣ) (k : ℤ) :
    res o1 (res hV (pullU g W ((res hW (pullU f U x)) ^ k))) = res o2 ((res hV' (pullU f' U x)) ^ k) := by
  subst hf
  have hA : V ≤ (g ≫ f) ⁻¹ᵁ U := fun y hy => hW (hV hy)
  simp only [map_zpow]
  congr 1
  rw [← DVR.res_pullU_comp' g f hW hV hA x, res_res_lemma, res_res_lemma]

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left)

/- English proof (translation)
Unfold `LB.Gen.Corr`. Introduce `j j' _ _ hjj`. Establish `hj : j = j'` using `funext fun i => by fin_cases i`. Conclude with `hjj 0 0 (by rw [← Category.assoc, Over.w g])`. Substitute `hj` using the available equality.

Conclude with `shape_rig g.left T.hom T'.hom (Over.w g) _ _ _ _ _ _ k`.
-/
theorem corr_rigT_pull (rig : LB.Gen (L.pull (eSec A))) {T T' : Over S0} (g : T' ⟶ T) (k : ℤ) :
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ (rigT A L rig T k) g.left) (rigT A L rig T' k) := by
  unfold LB.Gen.Corr
  intro j j' _ _ hjj
  have hj : j = j' := funext fun i => by
    fin_cases i
    exact hjj 0 0 (by rw [← Category.assoc, Over.w g])
  subst hj
  exact shape_rig g.left T.hom T'.hom (Over.w g) _ _ _ _ _ _ k

end Rig

section SecComp

variable {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (a : ℤ)

/- English proof (translation)
Introduce `j`. Rewrite using `[h2 j, h1 j]`. Simplify using `only [Over.comp_left, Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE_assoc]`.
-/
theorem isPullSec_comp {T T' T'' : Over S0} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {h' : T'' ⊗ A ⟶ T' ⊗ A} {hh' : h' ≫ snd T' A = snd T'' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} {s'' : LB.Sec (LPow A L a T'')}
    (h1 : IsPullSec A L a h hh s s') (h2 : IsPullSec A L a h' hh' s' s'') :
    IsPullSec A L a (h' ≫ h) (by rw [Category.assoc, hh, hh']) s s'' := by
  intro j
  rw [h2 j, h1 j]
  simp only [Over.comp_left, Scheme.Hom.comp_app, Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply,
    Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE_assoc]

/- English proof (translation)
Introduce `j`. Simplify using `only [Over.id_left, Scheme.Hom.id_app, CommRingCat.id_apply]`. Rewrite using `[show (homOfLE (chart_le_res A L (𝟙 (T ⊗ A)) hh a j)).op = 𝟙 _ from Subsingleton.elim _ _]`. Use `erw [CategoryTheory.Functor.map_id]`. Use `erw [CommRingCat.hom_id]`.

Both sides reduce to the same expression.
-/
theorem isPullSec_id {T : Over S0} (hh : 𝟙 (T ⊗ A) ≫ snd T A = snd T A) (s : LB.Sec (LPow A L a T)) :
    IsPullSec A L a (𝟙 (T ⊗ A)) hh s s := by
  intro j
  simp only [Over.id_left, Scheme.Hom.id_app, CommRingCat.id_apply]
  rw [show (homOfLE (chart_le_res A L (𝟙 (T ⊗ A)) hh a j)).op = 𝟙 _ from Subsingleton.elim _ _]
  erw [CategoryTheory.Functor.map_id]
  erw [CommRingCat.hom_id]
  rfl

end SecComp

end Formalism.MainNotions.ModuliIntegralCharts.H1.LBPull
