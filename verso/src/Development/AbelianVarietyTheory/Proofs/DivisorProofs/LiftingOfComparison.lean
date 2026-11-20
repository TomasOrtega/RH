import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationExtensionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicNormLeOneIffValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSubextensionPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelChangeLocallyFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteDvrExtensionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

/- English proof (translation)
Establish `hv : ValuativeCriterion f`. Rewrite `hp` using `[IsProper.eq_valuativeCriterion]`. Conclude with `hp.1.1.1`. Set `S : ValuativeCommSq f` to `{ R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }`. Take `⟨U⟩` from `hv S`.

Conclude with `⟨U.default.l, U.default.fac_left.symm⟩`.
-/
theorem exists_extend_of_isProper {X B : Scheme.{0}} (f : X ⟶ B) (hp : IsProper f) {V : Type} [CommRing V] [IsDomain V]
    [ValuationRing V] (y : Sp (FractionRing V) ⟶ X) (s : Sp V ⟶ B) (h : y ≫ f = spMap (algebraMap V (FractionRing V)) ≫ s) :
    ∃ χ : Sp V ⟶ X, y = spMap (algebraMap V (FractionRing V)) ≫ χ := by
  have hv : ValuativeCriterion f := by
    rw [IsProper.eq_valuativeCriterion] at hp
    exact hp.1.1.1
  let S : ValuativeCommSq f := { R := V, K := FractionRing V, i₁ := y, i₂ := s, commSq := ⟨h⟩ }
  obtain ⟨U⟩ := hv S
  exact ⟨U.default.l, U.default.fac_left.symm⟩

/- English proof (translation)
Introduce `E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle Z la p _ Xw hc _ T io e y₀ ho halg k y hy`. Use `letI := io.toAlgebra`. Establish `hfin : T.FinRes` using `halg.1`. Take `⟨hOI, hW, -, -, -, -, -, -, hlift⟩` from `hc`. Choose the witnesses or unpack the hypotheses as in `⟨kO, hk⟩ : ∃ kO : T.V →+* 𝓞_ℂ_[p], ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by`.

Use `letI := H.starRing`. Take `⟨-, kO, P, _, _, hP, -⟩` from `hy`. Conclude with `⟨kO, hP.1⟩`. Set `kk : T.Fr →+* ℂ_[p]` to `k.toRingHom`. Use `letI algT : Algebra T.Fr ℂ_[p] := kk.toAlgebra`.

Set `K : IntermediateField T.Fr ℂ_[p]` to `algebraicClosure T.Fr ℂ_[p]`. Use `haveI hKc : IsAlgClosure T.Fr K := algebraicClosure.isAlgClosure T.Fr ℂ_[p]`. Use `haveI : IsAlgClosed K := hKc.isAlgClosed`. Establish `hKa : Algebra.IsAlgebraic T.Fr K` using `hKc.isAlgebraic`. Set `O : ValuationSubring K` to `(𝓞_ℂ_[p]).comap K.val.toRingHom`.

Establish `hO : ∀ x : K, x ∈ O ↔ ‖(x : ℂ_[p])‖ ≤ 1` using `fun x => by show (Valued.v (x : ℂ_[p]) ≤ 1) ↔ _`. Rewrite using `[← coe_valued]`. Conclude with `NNReal.coe_le_one.symm`. Set `g : c.F →+* K` to `(algebraMap T.Fr K).comp io`. Establish `hg : ∀ x : c.F, (x : ℂ) ∈ W ↔ g x ∈ O` using `fun x => by`.

Rewrite using `[hW, hO, ← GlobalTheory.T.p_adic_norm_le_one_iff_valuation la p T io e ho kk kO hk x]`. Both sides reduce to the same expression. Take `⟨fK, hfK1, hfK2⟩` from `GlobalTheory.T.exists_valuation_extension_field c.F c'.F hle c'.fin W K O g hg`. Establish `hgf : (algebraMap T.Fr K).comp (algebraMap c.F T.Fr) = fK.comp (IntermediateField.inclusion hle).toRingHom` using `RingHom.ext fun x => (hfK1 x).symm`. Take `⟨yy, hyy1, hyy2, hyy3⟩` from `hlift K fK (spMap (algebraMap T.Fr K) ≫ ptF y₀.1) (by`.

Rewrite using `[Category.assoc, ptF, pullback.lift_snd, spMap_spMap, hgf]) (by`. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `halg.2 _)`. Take `⟨L, yL, hLfin, hyL1, hyL2⟩` from `GlobalTheory.T.exists_finite_subextension_point _ _ r (GlobalTheory.T.level_change_locally_finite_type r hle hOI) T.Fr K hKa yy (ptF y₀.1) hyy2`. Take `⟨kL, hkL⟩ : ∃ kL : L →+* ℂ_[p], kL = K.val.toRingHom.comp L.val.toRingHom` from `⟨_, rfl⟩`.

Establish `hkL1 : ∀ x : L, kL x = ((x : K) : ℂ_[p])` using `fun x => by rw [hkL]; rfl`. Take `⟨T', i, iF, ψ, kO', hT'fin, hkO'inj, hi, hψ, hkO', hint⟩` from `GlobalTheory.T.exists_finite_dvr_extension p T hfin kO kk hk L kL (fun a => by rw [hkL1]; rfl)`. Take `⟨φ, hφ⟩` from `Spec.map_surjective (yL ≫ pullback.snd _ _ : Sp L ⟶ Sp c'.F)`. Take `⟨fL, hfLφ⟩ : ∃ fL : c'.F →+* L, fL = φ.hom` from `⟨_, rfl⟩`. Establish `hφ' : yL ≫ pullback.snd _ _ = spMap fL` using `by rw [← hφ, hfLφ]; rfl`.

Establish `hfL : ∀ x, ((fL x : K)) = fK x` using `fun x => by`. Establish `e1 : spMap ((algebraMap L K).comp fL) = spMap fK`. Rewrite using `[← spMap_spMap, ← hφ', ← Category.assoc, hyL1, hyy1]`. Establish `e2` using `congrArg (fun f => (CommRingCat.Hom.hom f) x) (Spec.map_injective e1)`. Conclude with `e2`.

Take `⟨β', hβ'⟩` from `hint (c'.V W) (fL.comp (c'.V W).subtype) (fun a => by`. Rewrite using `[RingHom.comp_apply, hkL1, hfL, ← hO]`. Conclude with `hfK2 a a.2)`. Take `⟨yyT, hyyT⟩ : ∃ t : Sp T'.Fr ⟶ Xo'.XF c', t = spMap ψ.toRingHom ≫ yL` from `⟨_, rfl⟩`. Establish `hring : ψ.toRingHom.comp (fL.comp (c'.V W).subtype) = (algebraMap T'.V T'.Fr).comp β'` using `RingHom.ext fun a => (hβ' a).symm`.

Establish `hsq : (yyT ≫ Y.j) ≫ Y.s = spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap β'`. Establish `hj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype`. Rewrite using `[Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]`. Rewrite using `[hyyT, Category.assoc, Category.assoc, hj, ← Category.assoc yL, hφ', spMap_spMap, spMap_spMap, spMap_spMap, hring]`. Take `⟨yT, hyT⟩` from `exists_extend_of_isProper Y.s (projProper _ _ _ Y.proj) (yyT ≫ Y.j) (spMap β') hsq`.

Take `⟨k', hk'⟩ : ∃ k' : T'.Fr →+* ℂ_[p], k' = kL.comp ψ.symm.toRingHom` from `⟨_, rfl⟩`. Establish `hk'iF : ∀ a, k' (iF a) = k a` using `fun a => by`. Rewrite using `[hk', RingHom.comp_apply, ← hψ a]`. Use `show kL (ψ.symm (ψ _)) = _`. Rewrite using `[RingEquiv.symm_apply_apply, hkL1]`.

Both sides reduce to the same expression. Establish `hkO'' : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k' (algebraMap T'.V T'.Fr a)` using `fun a => by`. Rewrite using `[hk', hkO' a]`. Both sides reduce to the same expression. Establish `hψi : ψ.toRingHom.comp (algebraMap T.Fr L) = iF` using `RingHom.ext hψ`.

Establish `hyyTr : yyT ≫ r = spMap iF ≫ ptF y₀.1`. Rewrite using `[hyyT, Category.assoc, hyL2, ← Category.assoc, spMap_spMap, hψi]`. Take `⟨P, π, ψ2, hHT⟩` from `hC E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p T T' i iF hi io y₀ k y hy k' kO' hkO'' hk'iF yT yyT hyT.symm hyyTr`. Use `⟨spMap kO' ≫ yT, spMap k' ≫ yyT, ⟨⟨T', kO', yT, hT'fin, hkO'inj, rfl⟩, ?_⟩, P, π, ψ2, hHT⟩` and prove the remaining obligations. Establish `hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' = k'.comp (algebraMap T'.V T'.Fr)` using `RingHom.ext hkO''`.

Establish `e3 : spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO' ≫ yT = (spMap k' ≫ spMap ψ.toRingHom) ≫ yL ≫ Y.j`. Rewrite using `[← Category.assoc, spMap_spMap, hrk, ← spMap_spMap, Category.assoc, ← hyT, hyyT]`. Simplify using `only [Category.assoc]`. Rewrite using `[e3]`. Introduce and unpack `_ ⟨q, rfl⟩`.

Take `⟨q0⟩ : Nonempty (Sp K)` from `inferInstance`. Establish `hq : (spMap k' ≫ spMap ψ.toRingHom) q = spMap (algebraMap L K) q0` using `Subsingleton.elim (α := PrimeSpectrum L) _ _`. Rewrite using `[Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, ← Category.assoc, hyL1]`. Conclude with `hyy3 ⟨q0, rfl⟩`.
-/
theorem liftSt_of_cmpSt (hC : CmpSt) : LiftSt := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle Z la p _ Xw hc _ T io e y₀ ho halg k y hy
  letI := io.toAlgebra
  have hfin : T.FinRes := halg.1
  obtain ⟨hOI, hW, -, -, -, -, -, -, hlift⟩ := hc
  obtain ⟨kO, hk⟩ : ∃ kO : T.V →+* 𝓞_ℂ_[p], ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO a) = k (algebraMap T.V T.Fr a) := by
    letI := H.starRing
    obtain ⟨-, kO, P, _, _, hP, -⟩ := hy
    exact ⟨kO, hP.1⟩
  let kk : T.Fr →+* ℂ_[p] := k.toRingHom
  letI algT : Algebra T.Fr ℂ_[p] := kk.toAlgebra
  let K : IntermediateField T.Fr ℂ_[p] := algebraicClosure T.Fr ℂ_[p]
  haveI hKc : IsAlgClosure T.Fr K := algebraicClosure.isAlgClosure T.Fr ℂ_[p]
  haveI : IsAlgClosed K := hKc.isAlgClosed
  have hKa : Algebra.IsAlgebraic T.Fr K := hKc.isAlgebraic
  let O : ValuationSubring K := (𝓞_ℂ_[p]).comap K.val.toRingHom
  have hO : ∀ x : K, x ∈ O ↔ ‖(x : ℂ_[p])‖ ≤ 1 := fun x => by
    show (Valued.v (x : ℂ_[p]) ≤ 1) ↔ _
    rw [← coe_valued]
    exact NNReal.coe_le_one.symm
  let g : c.F →+* K := (algebraMap T.Fr K).comp io
  have hg : ∀ x : c.F, (x : ℂ) ∈ W ↔ g x ∈ O := fun x => by
    rw [hW, hO, ← GlobalTheory.T.p_adic_norm_le_one_iff_valuation la p T io e ho kk kO hk x]
    rfl
  obtain ⟨fK, hfK1, hfK2⟩ := GlobalTheory.T.exists_valuation_extension_field c.F c'.F hle c'.fin W K O g hg
  have hgf : (algebraMap T.Fr K).comp (algebraMap c.F T.Fr) = fK.comp (IntermediateField.inclusion hle).toRingHom :=
    RingHom.ext fun x => (hfK1 x).symm
  obtain ⟨yy, hyy1, hyy2, hyy3⟩ := hlift K fK (spMap (algebraMap T.Fr K) ≫ ptF y₀.1) (by
      rw [Category.assoc, ptF, pullback.lift_snd, spMap_spMap, hgf]) (by
      rintro _ ⟨q, rfl⟩
      exact halg.2 _)
  obtain ⟨L, yL, hLfin, hyL1, hyL2⟩ := GlobalTheory.T.exists_finite_subextension_point _ _ r (GlobalTheory.T.level_change_locally_finite_type r hle hOI) T.Fr K hKa yy (ptF y₀.1) hyy2
  obtain ⟨kL, hkL⟩ : ∃ kL : L →+* ℂ_[p], kL = K.val.toRingHom.comp L.val.toRingHom := ⟨_, rfl⟩
  have hkL1 : ∀ x : L, kL x = ((x : K) : ℂ_[p]) := fun x => by rw [hkL]; rfl
  obtain ⟨T', i, iF, ψ, kO', hT'fin, hkO'inj, hi, hψ, hkO', hint⟩ :=
    GlobalTheory.T.exists_finite_dvr_extension p T hfin kO kk hk L kL (fun a => by rw [hkL1]; rfl)
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (yL ≫ pullback.snd _ _ : Sp L ⟶ Sp c'.F)
  obtain ⟨fL, hfLφ⟩ : ∃ fL : c'.F →+* L, fL = φ.hom := ⟨_, rfl⟩
  have hφ' : yL ≫ pullback.snd _ _ = spMap fL := by rw [← hφ, hfLφ]; rfl
  have hfL : ∀ x, ((fL x : K)) = fK x := fun x => by
    have e1 : spMap ((algebraMap L K).comp fL) = spMap fK := by
      rw [← spMap_spMap, ← hφ', ← Category.assoc, hyL1, hyy1]
    have e2 := congrArg (fun f => (CommRingCat.Hom.hom f) x) (Spec.map_injective e1)
    exact e2
  obtain ⟨β', hβ'⟩ := hint (c'.V W) (fL.comp (c'.V W).subtype) (fun a => by
    rw [RingHom.comp_apply, hkL1, hfL, ← hO]
    exact hfK2 a a.2)
  obtain ⟨yyT, hyyT⟩ : ∃ t : Sp T'.Fr ⟶ Xo'.XF c', t = spMap ψ.toRingHom ≫ yL := ⟨_, rfl⟩
  have hring : ψ.toRingHom.comp (fL.comp (c'.V W).subtype) = (algebraMap T'.V T'.Fr).comp β' :=
    RingHom.ext fun a => (hβ' a).symm
  have hsq : (yyT ≫ Y.j) ≫ Y.s = spMap (algebraMap T'.V (FractionRing T'.V)) ≫ spMap β' := by
    have hj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap (c'.V W).subtype := by
      rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [hyyT, Category.assoc, Category.assoc, hj, ← Category.assoc yL, hφ', spMap_spMap, spMap_spMap, spMap_spMap,
      hring]
  obtain ⟨yT, hyT⟩ := exists_extend_of_isProper Y.s (projProper _ _ _ Y.proj) (yyT ≫ Y.j) (spMap β') hsq
  obtain ⟨k', hk'⟩ : ∃ k' : T'.Fr →+* ℂ_[p], k' = kL.comp ψ.symm.toRingHom := ⟨_, rfl⟩
  have hk'iF : ∀ a, k' (iF a) = k a := fun a => by
    rw [hk', RingHom.comp_apply, ← hψ a]
    show kL (ψ.symm (ψ _)) = _
    rw [RingEquiv.symm_apply_apply, hkL1]
    rfl
  have hkO'' : ∀ a, algebraMap 𝓞_ℂ_[p] ℂ_[p] (kO' a) = k' (algebraMap T'.V T'.Fr a) := fun a => by
    rw [hk', hkO' a]; rfl
  have hψi : ψ.toRingHom.comp (algebraMap T.Fr L) = iF := RingHom.ext hψ
  have hyyTr : yyT ≫ r = spMap iF ≫ ptF y₀.1 := by
    rw [hyyT, Category.assoc, hyL2, ← Category.assoc, spMap_spMap, hψi]
  obtain ⟨P, π, ψ2, hHT⟩ := hC E H Dw l l' Xo Xo' c c' W Y r ν hle hOI p T T' i iF hi io y₀ k y hy k' kO'
    hkO'' hk'iF yT yyT hyT.symm hyyTr
  refine ⟨spMap kO' ≫ yT, spMap k' ≫ yyT, ⟨⟨T', kO', yT, hT'fin, hkO'inj, rfl⟩, ?_⟩, P, π, ψ2, hHT⟩
  have hrk : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO' = k'.comp (algebraMap T'.V T'.Fr) := RingHom.ext hkO''
  have e3 : spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ spMap kO' ≫ yT = (spMap k' ≫ spMap ψ.toRingHom) ≫ yL ≫ Y.j := by
    rw [← Category.assoc, spMap_spMap, hrk, ← spMap_spMap, Category.assoc, ← hyT, hyyT]
    simp only [Category.assoc]
  rw [e3]
  rintro _ ⟨q, rfl⟩
  obtain ⟨q0⟩ : Nonempty (Sp K) := inferInstance
  have hq : (spMap k' ≫ spMap ψ.toRingHom) q = spMap (algebraMap L K) q0 :=
    Subsingleton.elim (α := PrimeSpectrum L) _ _
  rw [Scheme.Hom.comp_apply, hq, ← Scheme.Hom.comp_apply, ← Category.assoc, hyL1]
  exact hyy3 ⟨q0, rfl⟩

end GlobalTheory.FlatModel

end
