import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieModelsAgreeStatement
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LatticeIntegrallyClosedTorsion
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Imports
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistOkAllStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.OmDvrK

section torsion
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G₀ : Over (Sp Ω)} {G G' : Over X}
  [GrpObj G₀] [GrpObj G] [GrpObj G'] {φ : G₀.left ⟶ G.left} {φ' : G₀.left ⟶ G'.left}

def pushHom (hp : IsGrpPullback G₀ G ξ φ) (T : Over (Sp Ω)) : (T ⟶ G₀) →* (Over.mk (T.hom ≫ ξ) ⟶ G) :=
  MonoidHom.mk' (pushPt hp.1.w) (fun x y => Over.OverMorphism.ext (hp.2 T x y _ _ rfl rfl).symm)

/- English proof (translation)
Introduce `x y h`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Apply `hp.1.hom_ext` to reduce the goal to its premises. Conclude with `congrArg (fun z => z.left) h`. Rewrite using `[Over.w x, Over.w y]`.
-/
theorem pushHom_injective (hp : IsGrpPullback G₀ G ξ φ) (T : Over (Sp Ω)) :
    Function.Injective (pushHom hp T) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · exact congrArg (fun z => z.left) h
  · rw [Over.w x, Over.w y]

/- English proof (translation)
Introduce `k _ i g hg`. Set `T : Over (Sp Ω)` to `Over.mk (spMap i)`. Set `a : T ⟶ G₀` to `Over.homMk (h'.1.lift g.left (spMap i) (Over.w g)) (h'.1.lift_snd _ _ _)`. Establish `ha : pushHom h' T a = g` using `Over.OverMorphism.ext (h'.1.lift_fst _ _ _)`. Establish `han : a ^ n = 1`.

Apply `pushHom_injective h' T` to reduce the goal to its premises. Rewrite using `[map_pow, ha, hg, map_one]`. Establish `hb : (pushHom h T a) ^ n = 1` using `by rw [← map_pow, han, map_one]`. Take `⟨x, hx⟩` from `hf k i (pushHom h T a) hb`. Establish `hw : x.left ≫ G.hom = 𝟙 _ ≫ ξ` using `by simpa using Over.w x`.

Set `y : Sp Ω ⟶ G₀.left` to `h.1.lift x.left (𝟙 _) hw`. Establish `hy : y ≫ G₀.hom = 𝟙 _` using `h.1.lift_snd _ _ _`. Establish `hay : a.left = spMap i ≫ y`. Apply `h.1.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, h.1.lift_fst]`.

Conclude with `hx`. Rewrite using `[Category.assoc, hy, Category.comp_id]`. Conclude with `Over.w a`. Use `⟨Over.homMk (y ≫ φ') ?_, ?_⟩` and prove the remaining obligations. Use `show (y ≫ φ') ≫ G'.hom = ξ`.

Rewrite using `[Category.assoc, h'.1.w, ← Category.assoc, hy, Category.id_comp]`. Establish `: g.left = a.left ≫ φ'` using `(congrArg (fun z => z.left) ha).symm`. Rewrite using `[this, hay]`. Simplify using the standard rewrite rules.
-/
theorem fullTorsion_of_common_fibre (h : IsGrpPullback G₀ G ξ φ) (h' : IsGrpPullback G₀ G' ξ φ') {n : ℕ}
    (hf : FullTorsion G ξ n) : FullTorsion G' ξ n := by
  intro k _ i g hg
  let T : Over (Sp Ω) := Over.mk (spMap i)
  let a : T ⟶ G₀ := Over.homMk (h'.1.lift g.left (spMap i) (Over.w g)) (h'.1.lift_snd _ _ _)
  have ha : pushHom h' T a = g := Over.OverMorphism.ext (h'.1.lift_fst _ _ _)
  have han : a ^ n = 1 := by
    apply pushHom_injective h' T
    rw [map_pow, ha, hg, map_one]
  have hb : (pushHom h T a) ^ n = 1 := by rw [← map_pow, han, map_one]
  obtain ⟨x, hx⟩ := hf k i (pushHom h T a) hb
  have hw : x.left ≫ G.hom = 𝟙 _ ≫ ξ := by simpa using Over.w x
  let y : Sp Ω ⟶ G₀.left := h.1.lift x.left (𝟙 _) hw
  have hy : y ≫ G₀.hom = 𝟙 _ := h.1.lift_snd _ _ _
  have hay : a.left = spMap i ≫ y := by
    apply h.1.hom_ext
    · rw [Category.assoc, h.1.lift_fst]
      exact hx
    · rw [Category.assoc, hy, Category.comp_id]
      exact Over.w a
  refine ⟨Over.homMk (y ≫ φ') ?_, ?_⟩
  · show (y ≫ φ') ≫ G'.hom = ξ
    rw [Category.assoc, h'.1.w, ← Category.assoc, hy, Category.id_comp]
  · have : g.left = a.left ≫ φ' := (congrArg (fun z => z.left) ha).symm
    rw [this, hay]
    simp

end torsion

/- English proof (translation)
Introduce `E _ _ _ H D l B _ b g X Ω _ _ ξ s o t t' m m' V _ _ M M' n q hξ hn hf hv hq`. Take `⟨a⟩` from `PositivityTheory.UnitarySelfGeneration.tw_iso E H D g`. Establish `hok` using `GlobalTheory.T.twist_ok_all E H D l B b (Sp Ω) s o g a`. Establish `hf' : FullTorsion t'.G ξ n` using `fullTorsion_of_common_fibre (G₀ := o.t.G) m.cart m'.cart hf`. Take `⟨hd, hdvr⟩` from `id hq`.

Establish `hic : IsIntegrallyClosed (X.presheaf.stalk q.1)` using `inferInstance`. Establish `hno : IsNoetherianRing (X.presheaf.stalk q.1)` using `inferInstance`. Establish `e1` using `(PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l B b X Ω ξ s o t m V M n q hξ hn hf hic hno).2.2`. Establish `e2` using `(PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l B b X Ω ξ s (twistObj o g a hok) t' m' V M' n q hξ hn hf' hic hno).2.2`. Establish `e3` using `GlobalTheory.T.semiabelian_lie_models_agree X Ω ξ hξ t.G t'.G o.t.G m.φ m'.φ t.semi t'.semi m.cart m'.cart V M M' hv n q hq`.

Rewrite using `[e2, e1, e3]`.
-/
theorem htOm_eq_of_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t t' : SAB H X) (m : SABMap o.t t ξ) (m' : SABMap (twistSAB o.t g) t' ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ o.t.G, v.left ≫ m.φ = (M.pt e).left ∧ v.left ≫ m'.φ = (M'.pt e).left) → (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) → M'.htOm t'.PP.L n q = M.htOm t.PP.L n q := by
  intro E _ _ _ H D l B _ b g X Ω _ _ ξ s o t t' m m' V _ _ M M' n q hξ hn hf hv hq
  obtain ⟨a⟩ := PositivityTheory.UnitarySelfGeneration.tw_iso E H D g
  have hok := GlobalTheory.T.twist_ok_all E H D l B b (Sp Ω) s o g a
  have hf' : FullTorsion t'.G ξ n := fullTorsion_of_common_fibre (G₀ := o.t.G) m.cart m'.cart hf
  obtain ⟨hd, hdvr⟩ := id hq
  have hic : IsIntegrallyClosed (X.presheaf.stalk q.1) := inferInstance
  have hno : IsNoetherianRing (X.presheaf.stalk q.1) := inferInstance
  have e1 := (PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l B b X Ω ξ s o t m V M n q hξ hn hf hic hno).2.2
  have e2 := (PositivityTheory.UnitarySelfGeneration.lattice_integrally_closed_torsion E H D l B b X Ω ξ s (twistObj o g a hok) t' m' V M' n q hξ hn hf' hic hno).2.2
  have e3 := GlobalTheory.T.semiabelian_lie_models_agree X Ω ξ hξ t.G t'.G o.t.G m.φ m'.φ t.semi t'.semi m.cart m'.cart V M M' hv n q hq
  rw [e2, e1, e3]

end GlobalTheory.CompanionTheory.Ar.OmDvrK

namespace PositivityTheory.UnitarySelfGeneration

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
The claim follows from `@GlobalTheory.CompanionTheory.Ar.OmDvrK.htOm_eq_of_dvr`.
-/
theorem lattice_stalk_dvr_twisted_models : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (g : HostAut H) (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X) (s : Sp Ω ⟶ Sp B) (o : Obj D l b s) (t t' : SAB H X) (m : SABMap o.t t ξ) (m' : SABMap (twistSAB o.t g) t' ξ) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ V) (n : ℕ) (q : Cpt ξ), IsCptGen ξ → 0 < n → FullTorsion t.G ξ n → (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ o.t.G, v.left ≫ m.φ = (M.pt e).left ∧ v.left ≫ m'.φ = (M'.pt e).left) → (∃ _ : IsDomain (X.presheaf.stalk q.1), IsDiscreteValuationRing (X.presheaf.stalk q.1)) → M'.htOm t'.PP.L n q = M.htOm t.PP.L n q :=
  @GlobalTheory.CompanionTheory.Ar.OmDvrK.htOm_eq_of_dvr

end PositivityTheory.UnitarySelfGeneration
