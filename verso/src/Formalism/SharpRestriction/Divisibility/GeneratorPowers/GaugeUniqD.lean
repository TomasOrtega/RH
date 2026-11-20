import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqC
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeBeta

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def gam (A : Type) [CommRing A] : Γ(Sp A, ⊤) →+* A := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

/- English proof (translation)
Simplify using `[gam, toΓ]`.
-/
theorem gam_toΓ (A : Type) [CommRing A] (a : A) : gam A (toΓ A a) = a := by
  simp [gam, toΓ]

/- English proof (translation)
Establish `h` using `congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h`. Simplify using `only [gam, spMap]`. Conclude with `h`.
-/
theorem gam_pull {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : Γ(Sp A, ⊤)) :
    gam B (((spMap f).app ⊤).hom x) = f (gam A x) := by
  have h := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  simp only [gam, spMap]
  exact h

/- English proof (translation)
Simplify using `only [pullUnit, pullU, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `gam_pull f (u : Γ(Sp A, ⊤))`.
-/
theorem gam_pullUnit {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Γ(Sp A, ⊤)ˣ) :
    gam B (pullUnit (spMap f) u : Γ(Sp B, ⊤)) = f (gam A u) := by
  simp only [pullUnit, pullU, Units.coe_map, MonoidHom.coe_coe]
  exact gam_pull f (u : Γ(Sp A, ⊤))

/- English proof (translation)
Unfold `IsScaled at h ⊢`. Introduce `j`. Use `show t'.s j ^ k = _ * t.s j ^ k`. Rewrite using `[h j, mul_pow, map_pow]`. Both sides reduce to the same expression.
-/
theorem scaled_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {Y : Scheme.{0}} {K : Type} [Fintype K]
    (φ : K → (Y ⟶ Xo.univ.t.G.left)) (ε : K → ℤ) {u : Γ(Y, ⊤)ˣ}
    {t t' : LB.Gen (LB.LinComb Xo.univ.t.PP.L φ ε)} (h : IsScaled u t t') (k : ℕ) :
    IsScaled (u ^ k) (genPow φ ε t k) (genPow φ ε t' k) := by
  unfold IsScaled at h ⊢
  intro j
  show t'.s j ^ k = _ * t.s j ^ k
  rw [h j, mul_pow, map_pow]
  rfl

/- English proof (translation)
Unfold `IsValueAt at h h'`. Unfold `IsScaled at hs`. Establish `key : ∀ j, (T.left.presheaf.map (homOfLE (le_top : (LB.LinComb L (Y` using `T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom v = (T.left.presheaf.map (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom ((U : Γ(T.left, ⊤)) * v') := by`. Introduce `j`. Establish `e` using `(h j).symm.trans (h' j)`.

Establish `e2` using `congrArg Units.val (hs j)`. Simplify using `only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e2`. Simplify using `only [e2] at e`. Rewrite using `[map_mul]`. Use `(Units.mul_left_inj (τ.s j)).mp ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hcov : (⊤ : T.left.Opens) ≤ ⨆ j, (LB.LinComb L (Y` using `T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := by`. Introduce `x _`. Establish `hx : z.left.base x ∈ (⊤ : A.left.Opens)` using `trivial`. Rewrite `hx` using `[← hL.cover]`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.mp hx`. Use `TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ => i, ?_⟩` and prove the remaining obligations. Use `show x ∈ L.wchart (fun _ => z.left) (fun _ => i)`. Unfold `LB.wchart`. Conclude with `Set.mem_iInter.mpr fun _ => hi`.

Conclude with `T.left.sheaf.eq_of_locally_eq' _ ⊤ (fun j => homOfLE le_top) hcov v ((U : Γ(T.left, ⊤)) * v') key`.
-/
theorem value_scaled {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (hL : L.IsLB) (a : ℤ)
    {T : Over S0} (s : LB.Sec (LPow A L a T)) (z : T ⟶ A)
    (τ τ' : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)))
    (v v' : Γ(T.left, ⊤)) (U : Γ(T.left, ⊤)ˣ) (h : IsValueAt A L a s z τ v) (h' : IsValueAt A L a s z τ' v')
    (hs : IsScaled U τ τ') : v = (U : Γ(T.left, ⊤)) * v' := by
  unfold IsValueAt at h h'
  unfold IsScaled at hs
  have key : ∀ j, (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom v =
      (T.left.presheaf.map
      (homOfLE (le_top : (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j ≤ ⊤)).op).hom ((U : Γ(T.left, ⊤)) * v') := by
    intro j
    have e := (h j).symm.trans (h' j)
    have e2 := congrArg Units.val (hs j)
    simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe] at e2
    simp only [e2] at e
    rw [map_mul]
    refine (Units.mul_left_inj (τ.s j)).mp ?_
    calc _ = _ := e
      _ = _ := mul_left_comm _ _ _
      _ = _ := (mul_assoc _ _ _).symm
  have hcov : (⊤ : T.left.Opens) ≤ ⨆ j, (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a)).U j := by
    intro x _
    have hx : z.left.base x ∈ (⊤ : A.left.Opens) := trivial
    rw [← hL.cover] at hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨fun _ => i, ?_⟩
    show x ∈ L.wchart (fun _ => z.left) (fun _ => i)
    unfold LB.wchart
    exact Set.mem_iInter.mpr fun _ => hi
  exact T.left.sheaf.eq_of_locally_eq' _ ⊤ (fun j => homOfLE le_top) hcov v ((U : Γ(T.left, ⊤)) * v') key

end GaugeR

end Formalism.MainNotions.ModuliIntegralCharts.H1
