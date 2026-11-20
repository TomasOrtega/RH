import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasicOpenKTrivOfFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedImmersionGenericUnitLocusStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

/- English proof (translation)
Introduce `hG R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hA h hL hL₀ hw hP hk`. Take `⟨hO, -, hK⟩` from `GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ G L hL`. Take `⟨H, j, hj, hH⟩` from `GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R G hA hP L _ hL hO`. Establish `hrep : ∀ (T : Over (Sp R)) (x : T ⟶ G), GlobalTheory.UU.InK G L x ↔ ∃ y : T ⟶ H, y ≫ j = x` using `fun T x => (hK _ rfl T x).trans (hH T x)`. Establish `hm : Mono j` using `(Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))`.

Take `⟨e, he⟩` from `(hrep _ _).1 (GlobalTheory.UU.inK_one hL (𝟙_ _))`. Establish `hprop` using `hA.proper`. Establish `hH' : IsProper H.hom` using `by rw [← Over.w j]; infer_instance`. Establish `hsec : e.left ≫ H.hom = 𝟙 (Sp R)` using `Over.w e`. Establish `hcl : IsClosedImmersion e.left`.

Establish `: IsClosedImmersion (e.left ≫ H.hom)`. Rewrite using `[hsec]`. Conclude with `(inferInstance : IsClosedImmersion (𝟙 (Sp R)))`. Conclude with `IsClosedImmersion.of_comp e.left H.hom`. Take `⟨a, ha, key⟩` from `GlobalTheory.T.closed_immersion_generic_unit_locus R K _ _ e.left H.hom hcl inferInstance inferInstance (fun B _ y t hy => by`.

Establish `hdi : (y ≫ j.left) ≫ G.hom = t ≫ spMap (algebraMap R K)`. Rewrite using `[Category.assoc, Over.w j, hy]`. Set `x : Over.mk t ⟶ A` to `Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)`. Set `z : Over.mk (t ≫ spMap (algebraMap R K)) ⟶ H` to `Over.homMk y hy`. Establish `hz : z ≫ j = pushPt h.1.w x` using `Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm`.

Establish `hx : x = 1` using `GlobalTheory.UU.InK.eq_one hk (GlobalTheory.UU.inK_of_push h hL hL₀ hw x ((hrep _ _).2 ⟨z, hz⟩))`. Establish `hx' : pushPt h.1.w x = 1` using `(congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)`. Establish `h1 : toUnit _ ≫ e = z`. Rewrite using `[← cancel_mono j, hz, hx', Category.assoc, he, MonObj.comp_one]`. Conclude with `⟨(toUnit (Over.mk (t ≫ spMap (algebraMap R K)))).left, congrArg (fun q => q.left) h1⟩)`.

Use `⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' hw' B _ t x hx => ?_⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `(hrep _ _).1 (GlobalTheory.KTrivSpread.memKL_push h' hL hL' hw' t x hx)`. Take `⟨y, hy⟩` from `key R' g hg _ z.left t (Over.w z)`. Set `u : Over.mk (t ≫ spMap g) ⟶ 𝟙_ (Over (Sp R))` to `Over.homMk y (by`. Use `Over.w z` as an intermediate fact.

Rewrite `this` using `[← hy, Category.assoc, hsec]`. Conclude with `this)`. Establish `hu : u ≫ e = z` using `Over.OverMorphism.ext hy`. Establish `h1 : pushPt h'.1.w x = pushPt h'.1.w (1 : Over.mk t ⟶ G')`. Use `Eq.trans ?_ (map_one (pushHom h' (Over.mk t))).symm` and prove the remaining obligations.

Rewrite using `[← hz, ← hu, Category.assoc, he, MonObj.comp_one]`. Conclude with `Over.OverMorphism.ext (h'.1.hom_ext (congrArg (fun q => q.left) h1) (by rw [Over.w, Over.w]))`.
-/
theorem exists_kTriv : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → GlobalTheory.AbLaw.IsProjBy G.hom → KTriv A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → KTriv G' L' := by
  intro hG R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hA h hL hL₀ hw hP hk
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ G L hL
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG R G hA hP L _ hL hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ G), GlobalTheory.UU.InK G L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (GlobalTheory.UU.inK_one hL (𝟙_ _))
  have hprop := hA.proper
  have hH' : IsProper H.hom := by rw [← Over.w j]; infer_instance
  have hsec : e.left ≫ H.hom = 𝟙 (Sp R) := Over.w e
  have hcl : IsClosedImmersion e.left := by
    have : IsClosedImmersion (e.left ≫ H.hom) := by
      rw [hsec]
      exact (inferInstance : IsClosedImmersion (𝟙 (Sp R)))
    exact IsClosedImmersion.of_comp e.left H.hom
  obtain ⟨a, ha, key⟩ := GlobalTheory.T.closed_immersion_generic_unit_locus R K _ _ e.left H.hom hcl inferInstance inferInstance (fun B _ y t hy => by
    have hdi : (y ≫ j.left) ≫ G.hom = t ≫ spMap (algebraMap R K) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ A := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (algebraMap R K)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := GlobalTheory.UU.InK.eq_one hk (GlobalTheory.UU.inK_of_push h hL hL₀ hw x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : toUnit _ ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, he, MonObj.comp_one]
    exact ⟨(toUnit (Over.mk (t ≫ spMap (algebraMap R K)))).left, congrArg (fun q => q.left) h1⟩)
  refine ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' hw' B _ t x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hrep _ _).1 (GlobalTheory.KTrivSpread.memKL_push h' hL hL' hw' t x hx)
  obtain ⟨y, hy⟩ := key R' g hg _ z.left t (Over.w z)
  let u : Over.mk (t ≫ spMap g) ⟶ 𝟙_ (Over (Sp R)) := Over.homMk y (by
    have := Over.w z
    rw [← hy, Category.assoc, hsec] at this
    exact this)
  have hu : u ≫ e = z := Over.OverMorphism.ext hy
  have h1 : pushPt h'.1.w x = pushPt h'.1.w (1 : Over.mk t ⟶ G') := by
    refine Eq.trans ?_ (map_one (pushHom h' (Over.mk t))).symm
    rw [← hz, ← hu, Category.assoc, he, MonObj.comp_one]
  exact Over.OverMorphism.ext (h'.1.hom_ext (congrArg (fun q => q.left) h1) (by rw [Over.w, Over.w]))

end GlobalTheory.GenSpread
