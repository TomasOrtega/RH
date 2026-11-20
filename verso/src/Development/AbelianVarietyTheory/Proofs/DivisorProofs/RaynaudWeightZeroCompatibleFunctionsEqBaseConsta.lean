import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConstGlob

open GlobalTheory.KS.GlueDer

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

/- English proof (translation)
Rewrite using `[rsT_eq h, rsT_eq (pre_mono _ h), res_app]`.
-/
theorem app_rsT {U V : Q.P.A.left.Opens} (h : V ≤ U) (a : Γ(Q.P.A.left, U)) :
    (Y.q.left.app V).hom (rsT a V) = rsT ((Y.q.left.app U).hom a) (Y.q.left ⁻¹ᵁ V) := by
  rw [rsT_eq h, rsT_eq (pre_mono _ h), res_app]

/- English proof (translation)
The claim follows from `app_const (RingHom.id R) Q.P.A.hom Y.H.hom Y.q.left ((Over.w Y.q).trans ((Category.comp_id _).symm.trans (congrArg (Y.H.hom ≫ ·) (Spec.map_id _).symm))) V r`.
-/
theorem app_constFn (V : Q.P.A.left.Opens) (r : R) :
    (Y.q.left.app V).hom (constFn Q.P.A.hom V r) = constFn Y.H.hom _ r :=
  app_const (RingHom.id R) Q.P.A.hom Y.H.hom Y.q.left
    ((Over.w Y.q).trans ((Category.comp_id _).symm.trans (congrArg (Y.H.hom ≫ ·) (Spec.map_id _).symm))) V r

/- English proof (translation)
Take `⟨s, rfl⟩` from `(GlobalTheory.allSixLaws.1.globalFns (Sp R) Q.P.A Q.P.isAb).2 t`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s, ?_⟩` and prove the remaining obligations. Simplify using `only [constFn]`. Rewrite using `[Iso.hom_inv_id_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.
-/
theorem exists_constFn_top (t : Γ(Q.P.A.left, ⊤)) : ∃ r : R, t = constFn Q.P.A.hom ⊤ r := by
  obtain ⟨s, rfl⟩ := (GlobalTheory.allSixLaws.1.globalFns (Sp R) Q.P.A Q.P.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s, ?_⟩
  simp only [constFn]
  rw [Iso.hom_inv_id_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

/- English proof (translation)
Use `Y.smooth_q` as an intermediate fact. Use `(GlobalTheory.Heat.AbConst.surjective_q Y).1` as an intermediate fact. Establish `inj` using `FunDescent.app_injective Y.q.left`. Use `choose a ha using fun k => GlobalTheory.Heat.AbConst.exists_app_eq Y (hF k)`. Establish `cov : (⊤ : Q.P.A.left.Opens) ≤ ⨆ k, V k`.

Introduce `y _`. Take `⟨x, rfl⟩` from `Y.q.left.surjective y`. Establish `hx : x ∈ ⨆ k, Y.q.left ⁻¹ᵁ V k` using `by rw [hc]; trivial`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩`.

Take `⟨t, ht⟩` from `GlobalTheory.KS.exists_rsT_eq V (O := ⊤) (fun _ => le_top) cov a fun k l => by`. Apply `inj` to reduce the goal to its premises. Rewrite using `[app_rsT Y inf_le_left, app_rsT Y inf_le_right, ha, ha]`. Conclude with `hag k l _ (le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right))`. Take `⟨r, rfl⟩` from `exists_constFn_top t`.

Use `⟨r, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[← ha, ← ht k, GlobalTheory.KS.rsT_constFn _ le_top, app_constFn]`.
-/
theorem exists_const_of_preimage [IsLocalRing R] [IsNoetherianRing R] {K : Type} (V : K → Q.P.A.left.Opens)
    (hc : ⨆ k, Y.q.left ⁻¹ᵁ V k = ⊤) (F : ∀ k, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V k)) (hF : ∀ k, IsWt Y 0 _ (F k))
    (hag : ∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Y.q.left ⁻¹ᵁ V k ⊓ Y.q.left ⁻¹ᵁ V k' →
      rsT (F k) Wo = rsT (F k') Wo) :
    ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  have := Y.smooth_q
  have := (GlobalTheory.Heat.AbConst.surjective_q Y).1
  have inj := FunDescent.app_injective Y.q.left
  choose a ha using fun k => GlobalTheory.Heat.AbConst.exists_app_eq Y (hF k)
  have cov : (⊤ : Q.P.A.left.Opens) ≤ ⨆ k, V k := by
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Y.q.left ⁻¹ᵁ V k := by rw [hc]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq V (O := ⊤) (fun _ => le_top) cov a fun k l => by
    apply inj
    rw [app_rsT Y inf_le_left, app_rsT Y inf_le_right, ha, ha]
    exact hag k l _ (le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right))
  obtain ⟨r, rfl⟩ := exists_constFn_top t
  refine ⟨r, fun k => ?_⟩
  rw [← ha, ← ht k, GlobalTheory.KS.rsT_constFn _ le_top, app_constFn]

end GlobalTheory.Heat.AbConstGlob

open GlobalTheory.Heat.AbConstGlob in
/- English proof (translation)
Introduce `R _ _ _ _ Q O _ _ _ oa Y K Wk hW hc F hF hag`. Use `choose V hV using hW`. Take `rfl : Wk = fun k => Y.q.left ⁻¹ᵁ V k` from `funext hV`. Conclude with `exists_const_of_preimage Y V hc F hF hag`.
-/
theorem GlobalTheory.Heat.AbConstGlob.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (K : Type) (Wk : K → Y.H.left.Opens), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → ∀ F : ∀ k, Γ(Y.H.left, Wk k), (∀ k, IsWt Y 0 _ (F k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (F k) Wo = rsT (F k') Wo) → ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  intro R _ _ _ _ Q O _ _ _ oa Y K Wk hW hc F hF hag
  choose V hV using hW
  obtain rfl : Wk = fun k => Y.q.left ⁻¹ᵁ V k := funext hV
  exact exists_const_of_preimage Y V hc F hF hag
