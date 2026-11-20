import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HkLiftIsPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Rewrite using `[eSec]`. Use `show (toUnit _ ≫ η[G]).left = _`. Rewrite using `[Over.comp_left]`. Use `congr 1`.
-/
private theorem one_left_eq_eSec {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (y : Y ⟶ S) :
    (1 : Over.mk y ⟶ G).left = y ≫ eSec G := by
  rw [eSec]
  show (toUnit _ ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

/- English proof (translation)
Rewrite using `[eSec]`. Use `Over.w η[G]` as an intermediate fact. Simplify using `using this`.
-/
private theorem eSec_hom {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] : eSec G ≫ G.hom = 𝟙 _ := by
  rw [eSec]
  have := Over.w η[G]
  simpa using this

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'`. Establish `key₁ : (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkLift Z h hx = h ≫ eSec Z.o₁.t.G`. Apply `Z.m₁.cart.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hkLift_φ, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc, Z.m₁.cm.e_comm, Z.m₁.base, ← Category.assoc, ← hx]`. Rewrite using `[Category.assoc, hkLift_hom, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc, Category.assoc, eSec_hom]`.

Simplify using the standard rewrite rules. Use `haveI := Z.isog.1.1`. Establish `hψ : eSec Z.o₁.t.G ≫ Z.ψ.left = eSec Z.o₂.t.G`. Rewrite using `[eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]`. Apply `GlobalTheory.HeckeFrCompare.gx_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hkMap_fst, ptSecT, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst, GlobalTheory.HeckeFrCompare.lift_l_fst]`. Both sides reduce to the same expression. Rewrite using `[Category.assoc, hkMap_snd, ← Category.assoc, key₁, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc, ← Category.assoc (eSec _), hψ, Z.m₂.cm.e_comm, Z.m₂.base, ← Category.assoc, ← hx']`.
-/
theorem hkMap_ptSec_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : Corr Xo P p i) (T : Type) [CommRing T] (h : Sp T ⟶ Z.Hk) (x x' : Sp T ⟶ Xo.X) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂), (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkMap Z hx hx' = (ptSecT Xo.univ.t.G (1 : Over.mk x' ⟶ Xo.univ.t.G)).left := by
  intro E _ _ _ H Dw l Xo P p i Z T _ h x x' hx hx'
  have key₁ : (ptSecT Xo.univ.t.G (1 : Over.mk x ⟶ Xo.univ.t.G)).left ≫ hkLift Z h hx = h ≫ eSec Z.o₁.t.G := by
    apply Z.m₁.cart.1.hom_ext
    · rw [Category.assoc, hkLift_φ, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec, Category.assoc,
        Z.m₁.cm.e_comm, Z.m₁.base, ← Category.assoc, ← hx]
    · rw [Category.assoc, hkLift_hom, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst_assoc, Category.assoc, eSec_hom]
      simp
  haveI := Z.isog.1.1
  have hψ : eSec Z.o₁.t.G ≫ Z.ψ.left = eSec Z.o₂.t.G := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  apply GlobalTheory.HeckeFrCompare.gx_ext
  · rw [Category.assoc, hkMap_fst, ptSecT, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_fst, GlobalTheory.HeckeFrCompare.lift_l_fst]
    rfl
  · rw [Category.assoc, hkMap_snd, ← Category.assoc, key₁, ptSecT, GlobalTheory.HeckeFrCompare.lift_l_snd, one_left_eq_eSec,
      Category.assoc, ← Category.assoc (eSec _), hψ, Z.m₂.cm.e_comm, Z.m₂.base, ← Category.assoc, ← hx']

end GlobalTheory.HeckeEx
