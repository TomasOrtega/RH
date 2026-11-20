import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.LatPAddRight
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ResChPrime
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.DegenerationDataAtModelPointOfUniformisation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEmbeddingCompleteAlgClosedFixedCarrierStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DegenerationDataCoordsNeZeroLatticesIsomorphicStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
open Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.ModelIndep

/- English proof (translation)
Establish `h1 : ‖((f u : intO C) : C)‖ ≤ 1` using `(f u).2`. Establish `h2 : ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ ≤ 1` using `(f (u⁻¹ : Vˣ)).2`. Establish `h3 : ‖((f u : intO C) : C)‖ * ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ = 1`. Rewrite using `[← norm_mul, ← Subring.coe_mul, ← map_mul, Units.mul_inv, map_one, Subring.coe_one, norm_one]`. Use `le_antisymm h1 ?_` and prove the remaining obligations.

Use polynomial arithmetic with `[norm_nonneg ((f u : intO C) : C)]`.
-/
theorem norm_unit_eq_one {V C : Type} [CommRing V] [NormedField C] [IsUltrametricDist C] (f : V →+* intO C) (u : Vˣ) :
    ‖((f u : intO C) : C)‖ = 1 := by
  have h1 : ‖((f u : intO C) : C)‖ ≤ 1 := (f u).2
  have h2 : ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ ≤ 1 := (f (u⁻¹ : Vˣ)).2
  have h3 : ‖((f u : intO C) : C)‖ * ‖((f (u⁻¹ : Vˣ) : intO C) : C)‖ = 1 := by
    rw [← norm_mul, ← Subring.coe_mul, ← map_mul, Units.mul_inv, map_one, Subring.coe_one, norm_one]
  refine le_antisymm h1 ?_
  nlinarith [norm_nonneg ((f u : intO C) : C)]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Establish `key : ∀ (C : SCF p) (f : V →+* intO ↥C.S) (n : ℕ) (u : Vˣ), ‖((f (u * ϖ ^ n) : intO ↥C.S) : ↥C.S)‖ = ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ n`. Introduce `C f n u`. Rewrite using `[map_mul, map_pow, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, norm_unit_eq_one, one_mul]`. Establish `hp0 : (p : V) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`.

Take `⟨e, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ`. Establish `hpe : ∀ (C : SCF p) (f : V →+* intO ↥C.S), ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ e = (p : ℝ)⁻¹`. Introduce `C f`. Rewrite using `[← key C f e w, ← hw, map_natCast, ← C.norm_p]`. Simplify using the standard rewrite rules.

Establish `he : e ≠ 0`. Introduce and unpack `rfl`. Establish `h` using `hpe C f`. Rewrite `h` using `[pow_zero]`. Establish `h2 : (p : ℝ) = 1` using `inv_eq_one.1 h.symm`.

Conclude with `hp.ne_one (by exact_mod_cast h2)`. Establish `hϖ' : ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ = ‖((f' ϖ : intO ↥C'.S) : ↥C'.S)‖` using `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) he).1 ((hpe C f).trans (hpe C' f').symm)`. Distinguish the cases in `hr : r = 0`. Substitute `hr` using the available equality. Simplify using the standard rewrite rules.

Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ`. Rewrite using `[key, key, hϖ']`.
-/
theorem norm_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (r : V) :
    ‖((f r : intO ↥C.S) : ↥C.S)‖ = ‖((f' r : intO ↥C'.S) : ↥C'.S)‖ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have key : ∀ (C : SCF p) (f : V →+* intO ↥C.S) (n : ℕ) (u : Vˣ),
      ‖((f (u * ϖ ^ n) : intO ↥C.S) : ↥C.S)‖ = ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ n := by
    intro C f n u
    rw [map_mul, map_pow, Subring.coe_mul, Subring.coe_pow, norm_mul, norm_pow, norm_unit_eq_one, one_mul]
  have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨e, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hpe : ∀ (C : SCF p) (f : V →+* intO ↥C.S), ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ ^ e = (p : ℝ)⁻¹ := by
    intro C f
    rw [← key C f e w, ← hw, map_natCast, ← C.norm_p]
    simp
  have he : e ≠ 0 := by
    rintro rfl
    have h := hpe C f
    rw [pow_zero] at h
    have h2 : (p : ℝ) = 1 := inv_eq_one.1 h.symm
    exact hp.ne_one (by exact_mod_cast h2)
  have hϖ' : ‖((f ϖ : intO ↥C.S) : ↥C.S)‖ = ‖((f' ϖ : intO ↥C'.S) : ↥C'.S)‖ :=
    (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) he).1 ((hpe C f).trans (hpe C' f').symm)
  by_cases hr : r = 0
  · subst hr; simp
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [key, key, hϖ']

/- English proof (translation)
Establish `h : ∀ χ, vPsiAt D ((intO ↥C.S).subtype.comp f) p χ = vPsiAt D ((intO ↥C'.S).subtype.comp f') p χ`. Introduce `χ`. Unfold `vPsiAt`. Use `split_ifs with h`. Conclude with `congrArg (fun x => -Real.logb p x) (norm_eq_of_dvr hp C C' f f' h.choose)`.

Both sides reduce to the same expression. Simplify using `only [betaAt, h]`.
-/
theorem betaAt_eq_of_dvr {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] {p : ℕ}
    (hp : p.Prime) (C C' : SCF p) (f : V →+* intO ↥C.S) (f' : V →+* intO ↥C'.S) (D : DegPre V) (a b : D.X) :
    betaAt D ((intO ↥C.S).subtype.comp f) p a b = betaAt D ((intO ↥C'.S).subtype.comp f') p a b := by
  have h : ∀ χ, vPsiAt D ((intO ↥C.S).subtype.comp f) p χ = vPsiAt D ((intO ↥C'.S).subtype.comp f') p χ := by
    intro χ
    unfold vPsiAt
    split_ifs with h
    · exact congrArg (fun x => -Real.logb p x) (norm_eq_of_dvr hp C C' f f' h.choose)
    · rfl
  simp only [betaAt, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨b, hb⟩` from `GlobalTheory.EtaVal.exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho`. Establish `hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Rewrite using `[hxs, GlobalTheory.EtaVal.spMap_comp_spMap]`. Set `z : Sp T.Fr ⟶ Xo.XF c` to `pullback.lift x (spMap io) hcond`. Establish `hzs : z ≫ pullback.snd _ _ = spMap io` using `pullback.lift_snd _ _ _`.

Establish `hzf : z ≫ pullback.fst _ _ = x` using `pullback.lift_fst _ _ _`. Establish `hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b` using `by show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]`. Use `show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]`.

Take `⟨yt, h1, h2⟩` from `extPt Y T b z hx`. Take `⟨PP', cub, sym, adj, prim, mP, -⟩` from `sabPull Out.CubePf.cubePull yt Y.t`. Take `⟨mF, -⟩` from `sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap (PullbackSections.sabMapCast m1 hzf.symm)`. Take `⟨mJ, -⟩` from `sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF`. Establish `hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt` using `h1.symm`.

Take `⟨mK, -⟩` from `sabCancel pullCubCancel E H _ _ _ Y.t _ t' yt (Out.jK T.V) mP (PullbackSections.sabMapCast mJ hj)`. Take `⟨-, ψ, -⟩` from `GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr x G _ t' t' m1 m2 m1 mK`. Take `⟨n, -⟩` from `sabComp pullCubComp E H _ _ _ Y.t _ G yt (𝟙 _) mP ψ`. Establish `hprY : IsProper Y.s` using `projProper O Y.X Y.s Y.proj`. Establish `hr : (intO ↥C.S).subtype.comp g = eF.comp (algebraMap T.V T.Fr)` using `RingHom.ext h3'`.

Establish `hy : Pc.y = spMap eF ≫ z`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[h2', Category.assoc, hzf]`. Rewrite using `[Pc.y_over, Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap, h1']`. Establish `halg : g.comp b = Pc.alg`.

Use `RingHom.ext fun a => Subtype.ext ?_` and prove the remaining obligations. Establish `q1` using `DFunLike.congr_fun Pc.compat a`. Establish `q2` using `DFunLike.congr_fun hb a`. Establish `q3` using `DFunLike.congr_fun h1' (β a)`. Simplify using `only [RingHom.comp_apply] at q1 q2 q3 ⊢`.

Rewrite using `[h3', q2, q3]`. Conclude with `q1.symm`. Use `⟨yt, ?_, ⟨PullbackSections.sabMapCast n (Category.id_comp yt)⟩⟩` and prove the remaining obligations. Use `GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hr, ← GlobalTheory.EtaVal.spMap_comp_spMap, Category.assoc]`.

Rewrite using `[Pc.yt_over, Category.assoc, h2, GlobalTheory.EtaVal.spMap_comp_spMap, halg]`.
-/
theorem exists_extension {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S) (g : T.V →+* intO ↥C.S)
    (h1' : eF.comp io = Pc.fK) (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (h3' : ∀ a, ((g a : intO ↥C.S) : ↥C.S) = eF (algebraMap T.V T.Fr a)) :
    ∃ yt : Sp T.V ⟶ Y.X, spMap g ≫ yt = Pc.yt ∧ Nonempty (SABMap G Y.t yt) := by
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (fun a => (hB.2 (β a)).1 ⟨a, rfl⟩) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
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
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t _ t' yt (Out.jK T.V) mP (PullbackSections.sabMapCast mJ hj)
  obtain ⟨-, ψ, -⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T.V T.Fr x G _ t' t' m1 m2 m1 mK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t _ G yt (𝟙 _) mP ψ
  have hprY : IsProper Y.s := projProper O Y.X Y.s Y.proj
  have hr : (intO ↥C.S).subtype.comp g = eF.comp (algebraMap T.V T.Fr) := RingHom.ext h3'
  have hy : Pc.y = spMap eF ≫ z := by
    apply pullback.hom_ext
    · rw [h2', Category.assoc, hzf]
    · rw [Pc.y_over, Category.assoc, hzs, GlobalTheory.EtaVal.spMap_comp_spMap, h1']
  have halg : g.comp b = Pc.alg := by
    refine RingHom.ext fun a => Subtype.ext ?_
    have q1 := DFunLike.congr_fun Pc.compat a
    have q2 := DFunLike.congr_fun hb a
    have q3 := DFunLike.congr_fun h1' (β a)
    simp only [RingHom.comp_apply] at q1 q2 q3 ⊢
    rw [h3', q2, q3]; exact q1.symm
  refine ⟨yt, ?_, ⟨PullbackSections.sabMapCast n (Category.id_comp yt)⟩⟩
  refine GlobalTheory.EtaVal.point_ext_of_injective (intO ↥C.S).subtype Subtype.val_injective Y.s _ _ ?_ ?_
  · rw [Pc.ext, hy, Category.assoc, ← h1, ← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hr,
      ← GlobalTheory.EtaVal.spMap_comp_spMap, Category.assoc]
  · rw [Pc.yt_over, Category.assoc, h2, GlobalTheory.EtaVal.spMap_comp_spMap, halg]

/- English proof (translation)
Set `g : T.V →+* intO ↥C.S` to `(eF.comp (algebraMap T.V T.Fr)).codRestrict _ hle`. Establish `hg : Function.Injective g` using `fun a b h => IsFractionRing.injective T.V T.Fr (eF.injective (congrArg Subtype.val h))`. Take `⟨yt, hyt, ⟨n⟩⟩` from `exists_extension Y hB T io e ho x hxs G t' m1 m2 Pc eF g h1' h2' (fun _ => rfl)`. Establish `hpm : (p : T.V) ∈ maximalIdeal T.V`. Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`.

Introduce and unpack `⟨u, hu⟩`. Establish `h` using `norm_unit_eq_one g u`. Rewrite `h` using `[hu, map_natCast]`. Establish `h' : ‖(p : ↥C.S)‖ = 1` using `by simpa using h`. Rewrite `h'` using `[C.norm_p]`.

Conclude with `hp.ne_one (by exact_mod_cast inv_eq_one.1 h')`. Take `⟨f, hf, -, hfl⟩` from `(GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier T p hp hT hpm).2 C g T' φ hg hlt hφ hφf`. Take `⟨n2, -⟩` from `sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n mG`. Establish `hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G` using `Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q`. Set `A₀ : DatAt Y Pc` to `{ R := T'.V noeth := inferInstance normal := inferInstance complete := inferInstance := spMap φ ≫ yt f := f f_loc := hfl fac := by rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hf, hyt] t := G' m := n2 U := U unitOn := fun χ => by rw [hab]; exact hU χ tors := hTo }`.

Take `⟨-, q, hq⟩` from `GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C Pc hp T g yt hT hg hlt hyt A₀ A`. Conclude with `⟨f, q, hq⟩`.
-/
theorem exists_equiv_of_uniformisation {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β) (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (T' : CDVR) (φ : T.V →+* T'.V) (hφ : Function.Injective φ) (hφf : φ.Finite) (G' : SAB H (Sp T'.V))
    (mG : SABMap G' G (spMap φ)) (U : PELUnif (maximalIdeal T'.V) G')
    (hU : ∀ χ, PsiUnitOn U.D.toPre χ (abLocus G'.G)) (hTo : U.TorsionIso)
    {p : ℕ} (hp : p.Prime) {C : SCF p} (Pc : PointsOfFlagModel.PtC Y C) (eF : T.Fr →+* ↥C.S)
    (h1' : eF.comp io = Pc.fK) (hle : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (hlt : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (h2' : Pc.y ≫ pullback.fst _ _ = spMap eF ≫ x) (A : DatAt Y Pc) :
    ∃ (f : T'.V →+* intO ↥C.S) (q : U.D.toPre.X ≃ₗ[𝓞 E] A.Ylat),
      ∀ a b, A.beta (q a) (q b) = betaAt U.D.toPre ((intO ↥C.S).subtype.comp f) p a b := by
  let g : T.V →+* intO ↥C.S := (eF.comp (algebraMap T.V T.Fr)).codRestrict _ hle
  have hg : Function.Injective g := fun a b h =>
    IsFractionRing.injective T.V T.Fr (eF.injective (congrArg Subtype.val h))
  obtain ⟨yt, hyt, ⟨n⟩⟩ := exists_extension Y hB T io e ho x hxs G t' m1 m2 Pc eF g h1' h2' (fun _ => rfl)
  have hpm : (p : T.V) ∈ maximalIdeal T.V := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h := norm_unit_eq_one g u
    rw [hu, map_natCast] at h
    have h' : ‖(p : ↥C.S)‖ = 1 := by simpa using h
    rw [C.norm_p] at h'
    exact hp.ne_one (by exact_mod_cast inv_eq_one.1 h')
  obtain ⟨f, hf, -, hfl⟩ := (GlobalTheory.T.exists_embedding_completeAlgClosed_fixedCarrier T p hp hT hpm).2 C g T' φ hg hlt hφ hφf
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G G' yt (spMap φ) n mG
  have hab : (spMap φ ≫ yt) ⁻¹' abLocus Y.t.G = abLocus G'.G :=
    Set.ext fun q => abLocus_pullback abLocusOne Y.t.semi n2.cart.1 q
  let A₀ : DatAt Y Pc :=
    { R := T'.V
      noeth := inferInstance
      normal := inferInstance
      complete := inferInstance
      «ι» := spMap φ ≫ yt
      f := f
      f_loc := hfl
      fac := by rw [← Category.assoc, GlobalTheory.EtaVal.spMap_comp_spMap, hf, hyt]
      t := G'
      m := n2
      U := U
      unitOn := fun χ => by rw [hab]; exact hU χ
      tors := hTo }
  obtain ⟨-, q, hq⟩ := GlobalTheory.T.degenerationData_coords_ne_zero_lattices_isomorphic E H Dw l Xo c O β Y p C Pc hp T g yt hT hg hlt hyt A₀ A
  exact ⟨f, q, hq⟩

/- English proof (translation)
Take `⟨T', φ, G', mG, hφ, hφf, -, -, U, hU, hTo⟩` from `GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m2 x m1 hT`. Take `⟨f, q, hq⟩` from `exists_equiv_of_uniformisation Y hB T hT io e ho x hxs G t' m1 m2 T' φ hφ hφf G' mG U hU hTo hp P eF a1 a2 a3 a4 A`. Take `⟨f', q', hq'⟩` from `exists_equiv_of_uniformisation Y' hB' T hT io e ho x hxs G t' m1 m2 T' φ hφ hφf G' mG U hU hTo hp P' eF' b1 b2 b3 b4 A'`. Use `⟨q.symm.trans q', fun a b => ?_⟩` and prove the remaining obligations. Establish `h1` using `hq (q.symm a) (q.symm b)`.

Rewrite `h1` using `[LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Conclude with `(hq' (q.symm a) (q.symm b)).trans ((betaAt_eq_of_dvr hp _ _ f' f _ _ _).trans h1.symm)`.
-/
theorem exists_equiv_two_models {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    (Y : Model Xo c β) (Y' : Model Xo c β') {la : HeightOneSpectrum (𝓞 c.F)} (hB : PointsOfFlagModel.BaseAt la β)
    (hB' : PointsOfFlagModel.BaseAt la β') (T : CDVR) (hT : T.FinRes) (io : c.F →+* T.Fr) (e : ℕ)
    (ho : OverLa la T.V io e) (x : Sp T.Fr ⟶ Xo.X)
    (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    {p : ℕ} (hp : p.Prime) {C C' : SCF p} (P : PointsOfFlagModel.PtC Y C) (P' : PointsOfFlagModel.PtC Y' C')
    (eF : T.Fr →+* ↥C.S) (a1 : eF.comp io = P.fK) (a2 : ∀ a : T.V, ‖eF (algebraMap T.V T.Fr a)‖ ≤ 1)
    (a3 : ∀ a ∈ maximalIdeal T.V, ‖eF (algebraMap T.V T.Fr a)‖ < 1)
    (a4 : P.y ≫ pullback.fst _ _ = spMap eF ≫ x)
    (eF' : T.Fr →+* ↥C'.S) (b1 : eF'.comp io = P'.fK) (b2 : ∀ a : T.V, ‖eF' (algebraMap T.V T.Fr a)‖ ≤ 1)
    (b3 : ∀ a ∈ maximalIdeal T.V, ‖eF' (algebraMap T.V T.Fr a)‖ < 1)
    (b4 : P'.y ≫ pullback.fst _ _ = spMap eF' ≫ x) (A : DatAt Y P) (A' : DatAt Y' P') :
    ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b := by
  obtain ⟨T', φ, G', mG, hφ, hφf, -, -, U, hU, hTo⟩ :=
    GlobalTheory.UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m2 x m1 hT
  obtain ⟨f, q, hq⟩ := exists_equiv_of_uniformisation Y hB T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P eF a1 a2 a3 a4 A
  obtain ⟨f', q', hq'⟩ := exists_equiv_of_uniformisation Y' hB' T hT io e ho x hxs G t' m1 m2
    T' φ hφ hφf G' mG U hU hTo hp P' eF' b1 b2 b3 b4 A'
  refine ⟨q.symm.trans q', fun a b => ?_⟩
  have h1 := hq (q.symm a) (q.symm b)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
  exact (hq' (q.symm a) (q.symm b)).trans ((betaAt_eq_of_dvr hp _ _ f' f _ _ _).trans h1.symm)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c la Tw Tw' hTw hTw' T io e y ho hy z z' hz hz' A A'`. Use `letI := io.toAlgebra`. Take `⟨y, hy1, G, t', m1, m2, hy2⟩` from `y`. Take `⟨v, C, P, Fl⟩` from `z`. Take `⟨v', C', P', Fl'⟩` from `z'`.

Take `⟨hv, eF, a1, a2, a3, a4, -⟩` from `hz`. Take `⟨hv', eF', b1, b2, b3, b4, -⟩` from `hz'`. Take `rfl : v = lamOf la` from `hv`. Take `rfl : v' = lamOf la` from `hv'`. Conclude with `exists_equiv_two_models (Tw.Y (lamOf la)) (Tw'.Y (lamOf la)) (hTw.1 (lamOf la)).1 (hTw'.1 (lamOf la)).1 T hy io e ho y.x y.x_over G t' m1 m2 (resCh_prime la) P P' eF a1 a2 a3 a4 eF' b1 b2 b3 b4 A A'`.
-/
theorem datIndep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), DatIndep Xo c := by
  intro E _ _ _ H Dw l Xo c la Tw Tw' hTw hTw' T io e y ho hy z z' hz hz' A A'
  letI := io.toAlgebra
  obtain ⟨y, hy1, G, t', m1, m2, hy2⟩ := y
  obtain ⟨v, C, P, Fl⟩ := z
  obtain ⟨v', C', P', Fl'⟩ := z'
  obtain ⟨hv, eF, a1, a2, a3, a4, -⟩ := hz
  obtain ⟨hv', eF', b1, b2, b3, b4, -⟩ := hz'
  obtain rfl : v = lamOf la := hv
  obtain rfl : v' = lamOf la := hv'
  exact exists_equiv_two_models (Tw.Y (lamOf la)) (Tw'.Y (lamOf la)) (hTw.1 (lamOf la)).1 (hTw'.1 (lamOf la)).1 T hy
    io e ho y.x y.x_over G t' m1 m2 (resCh_prime la) P P' eF a1 a2 a3 a4 eF' b1 b2 b3 b4 A A'

end GlobalTheory.ModelIndep
