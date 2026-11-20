import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.UnifAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

/- English proof (translation)
Establish `key : ∀ x : O, io (β x) ∈ (algebraMap T.V T.Fr).range`. Introduce `x`. Establish `h1 : valV T.V (io (β x)) ≤ 1`. Distinguish the cases in `h0 : β x = 0`. Rewrite using `[h0, map_zero, map_zero]`.

Conclude with `zero_le_one`. Establish `h2` using `ho.2 (β x)`. Establish `h3 : WithZero.log (la.valuation K (β x)) ≤ 0`. Use `(WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 (hβ x)` as an intermediate fact. Simplify using `using this`.

Establish `h4 : 0 ≤ vV T.V (io (β x))`. Rewrite using `[h2]`. Conclude with `mul_nonneg (Nat.cast_nonneg e) (by unfold vLa; omega)`. Establish `h5 : valV T.V (io (β x)) ≠ 0` using `valV_ne_zero ((map_ne_zero io).2 h0)`. Use `(WithZero.log_le_log h5 one_ne_zero).1 ?_` and prove the remaining obligations.

Unfold `vV at h4`. Rewrite using `[WithZero.log_one]`. Use linear arithmetic over natural numbers and integers. Conclude with `IsDiscreteValuationRing.exists_lift_of_le_one h1`. Establish `hinj : Function.Injective (algebraMap T.V T.Fr).rangeRestrict` using `fun a b h => IsFractionRing.injective T.V T.Fr (congrArg Subtype.val h)`.

Set `eq : T.V ≃+* (algebraMap T.V T.Fr).range` to `RingEquiv.ofBijective _ ⟨hinj, (algebraMap T.V T.Fr).rangeRestrict_surjective⟩`. Use `⟨eq.symm.toRingHom.comp ((io.comp β).codRestrict _ key), RingHom.ext fun x => ?_⟩` and prove the remaining obligations. Conclude with `congrArg Subtype.val (eq.apply_symm_apply ⟨io (β x), key x⟩)`.
-/
theorem exists_base_map_of_overLa {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)}
    {O : Type} [CommRing O] {β : O →+* K} (hβ : ∀ x : O, la.valuation K (β x) ≤ 1)
    (T : CDVR) (io : K →+* T.Fr) (e : ℕ) (ho : OverLa la T.V io e) :
    ∃ b : O →+* T.V, (algebraMap T.V T.Fr).comp b = io.comp β := by
  have key : ∀ x : O, io (β x) ∈ (algebraMap T.V T.Fr).range := by
    intro x
    have h1 : valV T.V (io (β x)) ≤ 1 := by
      by_cases h0 : β x = 0
      · rw [h0, map_zero, map_zero]; exact zero_le_one
      have h2 := ho.2 (β x)
      have h3 : WithZero.log (la.valuation K (β x)) ≤ 0 := by
        have := (WithZero.log_le_log ((la.valuation K).ne_zero_iff.2 h0) one_ne_zero).2 (hβ x)
        simpa using this
      have h4 : 0 ≤ vV T.V (io (β x)) := by
        rw [h2]
        exact mul_nonneg (Nat.cast_nonneg e) (by unfold vLa; omega)
      have h5 : valV T.V (io (β x)) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 h0)
      refine (WithZero.log_le_log h5 one_ne_zero).1 ?_
      unfold vV at h4
      rw [WithZero.log_one]; omega
    exact IsDiscreteValuationRing.exists_lift_of_le_one h1
  have hinj : Function.Injective (algebraMap T.V T.Fr).rangeRestrict := fun a b h =>
    IsFractionRing.injective T.V T.Fr (congrArg Subtype.val h)
  let eq : T.V ≃+* (algebraMap T.V T.Fr).range :=
    RingEquiv.ofBijective _ ⟨hinj, (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
  refine ⟨eq.symm.toRingHom.comp ((io.comp β).codRestrict _ key), RingHom.ext fun x => ?_⟩
  exact congrArg Subtype.val (eq.apply_symm_apply ⟨io (β x), key x⟩)

/- English proof (translation)
Establish `: IsDominant (spMap i)`. Use `⟨?_⟩` and prove the remaining obligations. Use `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical i).2 (by rw [(RingHom.injective_iff_ker_eq_bot i).1 hi]; exact bot_le)` as an intermediate fact. Conclude with `this`. Conclude with `ext_of_isDominant_of_isSeparated s h' (spMap i) h`.
-/
theorem point_ext_of_injective {A B : Type} [CommRing A] [IsDomain A] [CommRing B] (i : A →+* B)
    (hi : Function.Injective i) {X S : Scheme.{0}} (s : X ⟶ S) [IsSeparated s] (u v : Sp A ⟶ X)
    (h : spMap i ≫ u = spMap i ≫ v) (h' : u ≫ s = v ≫ s) : u = v := by
  have : IsDominant (spMap i) := by
    refine ⟨?_⟩
    have := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical i).2
      (by rw [(RingHom.injective_iff_ker_eq_bot i).1 hi]; exact bot_le)
    exact this
  exact ext_of_isDominant_of_isSeparated s h' (spMap i) h

/- English proof (translation)
Use `show Spec.map _ ≫ Spec.map _ = Spec.map _`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y la hB T io e ho x s G I hxs T' φ G' mG U hU hT p C Pc eF f h1' h2' h3' h4'`. Take `⟨b, hb⟩` from `exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho`. Establish `hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Rewrite using `[hxs, spMap_comp_spMap]`. Set `z : Sp T.Fr ⟶ Xo.XF c` to `pullback.lift x (spMap io) hcond`.

Establish `hzs : z ≫ pullback.snd _ _ = spMap io` using `pullback.lift_snd _ _ _`. Establish `hzf : z ≫ pullback.fst _ _ = x` using `pullback.lift_fst _ _ _`. Establish `hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b` using `by show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]`. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`.

Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]`. Take `⟨yt, h1, h2⟩` from `extPt Y T b z hx`. Take `⟨PP', cub, sym, adj, prim, mP, -⟩` from `sabPull Out.CubePf.cubePull yt Y.t`. Set `tP : SAB H (Sp T.V)` to `⟨(Over.pullback yt).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi, OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩`. Set `mP' : SABMap tP Y.t yt` to `mP`.

Take `⟨mF, -⟩` from `sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t I.t' (pullback.fst _ _) z Y.m0.toSABMap (PullbackSections.sabMapCast I.m1 hzf.symm)`. Take `⟨mJ, -⟩` from `sabComp pullCubComp E H _ _ _ Y.t Y.oF.t I.t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF`. Establish `hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt` using `h1.symm`. Take `⟨mK, -⟩` from `sabCancel pullCubCancel E H _ _ _ Y.t tP I.t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)`. Establish `hprop : IsProper I.t'.G.hom` using `MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper`.

Take `⟨ψ, -⟩` from `GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP I.t' hprop I.m2 mK`. Take `⟨n, -⟩` from `sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ`. Set `n' : SABMap G Y.t yt` to `PullbackSections.sabMapCast n (Category.id_comp yt)`. Take `⟨n2, -⟩` from `sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n' mG`. Establish `hprY : IsProper Y.s` using `projProper O Y.X Y.s Y.proj`.

Establish `hr : (intO ↥C.S).subtype.comp (f.comp φ) = eF.comp (algebraMap T.V T.Fr)` using `RingHom.ext h3'`. Establish `hy : Pc.y = spMap eF ≫ z`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[h2', Category.assoc, hzf]`. Rewrite using `[Pc.y_over, Category.assoc, hzs, spMap_comp_spMap, h1']`.

Establish `halg : (f.comp φ).comp b = Pc.alg`. Use `RingHom.ext fun a => Subtype.ext ?_` and prove the remaining obligations. Establish `q1` using `DFunLike.congr_fun Pc.compat a`. Establish `q2` using `DFunLike.congr_fun hb a`. Establish `q3` using `DFunLike.congr_fun h1' (β a)`.

Simplify using `only [RingHom.comp_apply] at q1 q2 q3 ⊢`. Rewrite using `[h3', q2, q3]`. Conclude with `q1.symm`. Establish `hfac : spMap f ≫ spMap φ ≫ yt = Pc.yt`. Use `point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc (spMap f), spMap_comp_spMap, ← Category.assoc, spMap_comp_spMap, hr, ← spMap_comp_spMap, Category.assoc]`. Rewrite using `[Pc.yt_over, Category.assoc, Category.assoc, h2, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, halg]`. Establish `hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G` using `Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q`. Set `A : DatAt Y Pc` to `{ R := T'.V noeth := inferInstance normal := inferInstance complete := inferInstance := spMap φ ≫ yt f := f f_loc := h4' fac := hfac t := G' m := n2 U := U unitOn := fun χ => by rw [hab]; exact hU χ tors := hT }`. Conclude with `⟨A, LinearEquiv.refl _ _, fun _ _ => rfl⟩`.
-/
theorem datAt_of_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (la : HeightOneSpectrum (𝓞 c.F)), PointsOfFlagModel.BaseAt la β → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X) (s : LB.Sec (PPx x)) (G : SAB H (Sp T.V)) (_ : IntSec Xo T.V x s G), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (T' : CDVR) (φ : T.V →+* T'.V) (G' : SAB H (Sp T'.V)) (_ : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G'), (∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) → U.TorsionIso → ∀ (p : ℕ) (C : SCF p) (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (f : T'.V →+* intO ↥C.S), eF.comp io = Pc.fK → Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x → (∀ a, ((f (φ a) : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) → (∀ a ∈ maximalIdeal T'.V, ‖((f a : intO ↥C.S) : ↥C.S)‖ < 1) → ∃ (A : DatAt Y Pc) (e' : A.Ylat ≃ₗ[𝓞 E] U.D.toPre.X), ∀ a b, A.beta a b = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p (e' a) (e' b) := by
  intro E _ _ _ H Dw l Xo c O _ β Y la hB T io e ho x s G I hxs T' φ G' mG U hU hT p C Pc eF f h1' h2' h3' h4'
  obtain ⟨b, hb⟩ := exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, h2⟩ := extPt Y T b z hx
  obtain ⟨PP', cub, sym, adj, prim, mP, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
  let tP : SAB H (Sp T.V) := ⟨(Over.pullback yt).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi,
    OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩
  let mP' : SABMap tP Y.t yt := mP
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t I.t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast I.m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t I.t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP I.t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper I.t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) I.m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP I.t' hprop I.m2 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  let n' : SABMap G Y.t yt := PullbackSections.sabMapCast n (Category.id_comp yt)
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n' mG
  have hprY : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hr : (intO ↥C.S).subtype.comp (f.comp φ) = eF.comp (algebraMap T.V T.Fr) := RingHom.ext h3'
  have hy : Pc.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2', Category.assoc, hzf]
    · rw [Pc.y_over, Category.assoc, hzs, spMap_comp_spMap, h1']
  have halg : (f.comp φ).comp b = Pc.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun Pc.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1' (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3 ⊢
    rw [h3', q2, q3]; exact q1.symm
  have hfac : spMap f ≫ spMap φ ≫ yt = Pc.yt := by
    refine point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_
    · rw [Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc (spMap f), spMap_comp_spMap, ← Category.assoc,
        spMap_comp_spMap, hr, ← spMap_comp_spMap, Category.assoc]
    · rw [Pc.yt_over, Category.assoc, Category.assoc, h2, ← Category.assoc, spMap_comp_spMap, spMap_comp_spMap, halg]
  have hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q
  let A : DatAt Y Pc :=
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ ≫ yt
      f := f
      f_loc := h4'
      fac := hfac
      t := G'
      m := n2
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hT }
  exact ⟨A, LinearEquiv.refl _ _, fun _ _ => rfl⟩

end GlobalTheory.EtaVal
