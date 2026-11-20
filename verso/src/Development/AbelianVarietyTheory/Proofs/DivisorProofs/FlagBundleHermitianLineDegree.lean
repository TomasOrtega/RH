import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolAVFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.HTLat GlobalTheory.CompHt GlobalTheory.FlatModel GlobalTheory.AllWt
open Formalism.MainNotions.DIV.Cons (intO)
open scoped NNReal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HalfGeo

/- English proof (translation)
Introduce `hInt E _ _ _ H Dw l Xo c Z hpq p _ K _ k z₀ hK z yy hk hz`. Take `⟨hpu, hcomp, -, hvI, ⟨g₀⟩⟩` from `hInt p`. Take `⟨T, kO, yT, hfin, hkO, hT⟩` from `GlobalTheory.DetHT.TestPt.exists_integral_point Z.s (projProper _ _ _ Z.proj) p k hK (z₀ ≫ Z.j)`. Establish `hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p])` using `(PadicComplexInt.integers p).hom_inj`. Establish `hgX : Set.range (spMap (algebraMap T.V T.Fr) ≫ yT) ⊆ Set.range Z.j`.

Introduce and unpack `_ ⟨s, rfl⟩`. Take `rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)` from `Subsingleton.elim (α := PrimeSpectrum T.Fr) _ _`. Establish `h1` using `bot_map (IsFractionRing.injective T.V T.Fr) yT`. Establish `h2` using `bot_map (φ := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) (hiO.comp hkO) yT`. Rewrite `h2` using `[← sp_sp, hT]`.

Rewrite using `[h1, ← h2, ← Category.assoc]`. Conclude with `⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩`. Take `⟨yyT, hyyT⟩` from `GlobalTheory.DetHT.exists_lift_int Z _ hgX`. Take `⟨io, hio⟩ : ∃ io : c.F →+* T.Fr, yyT ≫ pullback.snd _ _ = spMap io` from `⟨(Spec.preimage (yyT ≫ pullback.snd _ _)).hom, (Spec.map_preimage (yyT ≫ pullback.snd _ _)).symm⟩`. Set `x : Sp T.Fr ⟶ Xo.X` to `yyT ≫ pullback.fst _ _`.

Establish `hx : (letI` using `io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) := by`. Use `letI := io.toAlgebra`. Use `show (yyT ≫ pullback.fst _ _) ≫ Xo.s = _`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc yyT, hio, sOf, spMap_spMap]`. Take `⟨T', i, rr, hrr, hv, hfin', y₀, hy₀⟩` from `GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c hpq T io hfin x hx`.

Take `⟨φ, hφ, hloc⟩` from `GlobalTheory.GoodChartExt.exists_local_restrict T T' i rr hrr hv`. Establish `hφi : Function.Injective φ`. Introduce `a b h`. Apply `i.injective.comp (IsFractionRing.injective T.V T.Fr)` to reduce the goal to its premises. Establish `ha` using `RingHom.congr_fun hφ a`.

Establish `hb` using `RingHom.congr_fun hφ b`. Simplify using `only [RingHom.comp_apply] at ha hb`. Simplify using `only [Function.comp_apply, ← ha, ← hb, h]`. Establish `hfinφ : φ.Finite` using `GlobalTheory.CompHS.finite_of_finRes hfin' φ hφi`. Set `e : 𝓞_ℂ_[p] →+* intO ℂ_[p]` to `(algebraMap 𝓞_ℂ_[p] ℂ_[p]).codRestrict (intO ℂ_[p]) fun a => (GlobalTheory.CdvrLiftCp.mem_int_iff' _).1 a.2`.

Establish `he : (algebraMap (intO ℂ_[p]) ℂ_[p]).comp e = algebraMap 𝓞_ℂ_[p] ℂ_[p]` using `rfl`. Establish `hinjO : Function.Injective ((algebraMap (intO ℂ_[p]) ℂ_[p]).comp (e.comp kO))`. Rewrite using `[← RingHom.comp_assoc, he]`. Conclude with `hiO.comp hkO`. Take `⟨kO', hkO', hinj'⟩` from `exists_ext_of_integral (Valued.v : Valuation ℂ_[p] ℝ≥0) hvI φ hφi hfinφ.to_isIntegral (e.comp kO) hinjO`.

Set `k' : T'.Fr →+* ℂ_[p]` to `IsFractionRing.lift hinj'`. Establish `hk' : ∀ a, algebraMap (intO ℂ_[p]) ℂ_[p] (kO' a) = k' (algebraMap T'.V T'.Fr a)` using `fun a => (IsFractionRing.lift_algebraMap hinj' a).symm`. Use `letI : Algebra ℤ_[p] (intO ℂ_[p]) := g₀.toAlgebra`. Use `letI algC : Algebra ℤ_[p] ℂ_[p] := ((algebraMap (intO ℂ_[p]) ℂ_[p]).comp g₀).toAlgebra`. Use `haveI : @IsScalarTower ℤ_[p] (intO ℂ_[p]) ℂ_[p] _ _ algC.toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : Fact ¬IsUnit (p : intO ℂ_[p]) := ⟨hpu⟩`. Use `letI := H.starRing`. Take `⟨P, ψ, hPO⟩` from `exists_pointOver E H Dw l Xo c p ℂ_[p] (Valued.v : Valuation ℂ_[p] ℝ≥0) (intO ℂ_[p]) (fun _ => rfl) hvI T' (i.comp io) y₀ hfin' k' kO' hk'`. Take `⟨-, G, t', m₁, m₂, π₀, φ₀, hπ₀, hact₀, hφ₀, hgen₀, hψ₀, hL⟩` from `hPO`. Set `yT' : Sp T'.V ⟶ Z.X` to `spMap φ ≫ yT`.

Set `yyT' : Sp T'.Fr ⟶ Xo.XF c` to `spMap i ≫ yyT`. Establish `hcomm : spMap (algebraMap T'.V T'.Fr) ≫ yT' = yyT' ≫ Z.j` using `by show spMap (algebraMap T'.V T'.Fr) ≫ spMap φ ≫ yT = (spMap i ≫ yyT) ≫ Z.j`. Rewrite using `[sp_sp, hφ, ← sp_sp, Category.assoc, hyyT]`. Establish `hx' : (letI` using `(i.comp io).toAlgebra; y₀.1.x = yyT' ≫ pullback.fst _ _) := by`. Use `letI := (i.comp io).toAlgebra`.

Rewrite using `[hy₀, Category.assoc]`. Establish `hring : ((algebraMap T'.V T'.Fr).comp φ).comp (RingHom.id T.V) = (algebraMap T'.V T'.Fr).comp φ` using `rfl`. Establish `hkk : (k'.comp (algebraMap T'.V T'.Fr)).comp φ = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO`. Use extensionality with `a`. Simplify using `only [RingHom.comp_apply]`.

Rewrite using `[← hk' (φ a), show kO' (φ a) = e (kO a) from RingHom.congr_fun hkO' a]`. Both sides reduce to the same expression. Establish `hyy : spMap k' ≫ yyT' = yy`. Use `GlobalTheory.DetHT.mono_j_int Z` as an intermediate fact. Rewrite using `[← cancel_mono Z.j, Category.assoc, ← hcomm, ← hk, Category.assoc, ← hT]`.

Use `show spMap k' ≫ spMap (algebraMap T'.V T'.Fr) ≫ spMap φ ≫ yT = _`. Rewrite using `[sp_sp, sp_sp, sp_sp, ← hkk]`. Establish `hzz : spMap (intO ℂ_[p]).subtype ≫ spMap kO' ≫ yT' = yy ≫ Z.j` using `by show spMap (intO ℂ_[p]).subtype ≫ spMap kO' ≫ spMap φ ≫ yT = _`. Rewrite using `[← hyy, Category.assoc, ← hcomm]`. Use `show _ = spMap k' ≫ spMap (algebraMap T'.V T'.Fr) ≫ spMap φ ≫ yT`.

Rewrite using `[sp_sp, sp_sp, sp_sp, sp_sp]`. Use `congr 2`. Use extensionality with `a`. Conclude with `hk' (φ a)`. Establish `hzeq : spMap kO' ≫ yT' = z` using `by haveI : IsDomain (intO ℂ_[p]) := hvI.hom_inj.isDomain _ haveI : ValuationRing (intO ℂ_[p]) := ValuationRing.of_integers _ hvI haveI : IsFractionRing (intO ℂ_[p]) ℂ_[p] := hvI.isFractionRing haveI : IsProper Z.s := projProper _ _ _ Z.proj haveI : IsSeparated (terminal.from Z.X) …`.

Rewrite using `[show terminal.from Z.X = Z.s ≫ terminal.from _ from terminal.hom_ext _ _]`. Use `infer_instance`. Establish `hU : ValuativeCriterion.Uniqueness (terminal.from Z.X)` using `IsSeparated.valuativeCriterion _`. Set `S : ValuativeCommSq (terminal.from Z.X)` to `{ R := intO ℂ_[p], K := ℂ_[p], i₁ := yy ≫ Z.j, i₂ := terminal.from _ commSq := ⟨terminal.hom_ext _ _⟩ }`. Use `(hU S).elim ⟨spMap kO' ≫ yT', hzz, terminal.hom_ext _ _⟩ ⟨z, hz, terminal.hom_ext _ _⟩` as an intermediate fact.

Conclude with `congrArg CommSq.LiftStruct.l this`. Establish `tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ`. Introduce `S S' s s' f g h m`. Substitute `h` using the available equality. Conclude with `⟨m, rfl⟩`.

Take `⟨Yt', ⟨b⟩⟩` from `exists_sab yT' Z.t`. Take `⟨t₂, ⟨q⟩⟩` from `exists_sab yyT' Z.oF.t`. Take `⟨n₁, hn₁⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m0.toSABMap q`. Take `⟨e₂, he₂⟩` from `sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m q`. Take `⟨e₂', he₂'⟩` from `tr (show yyT' ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap T'.V T'.Fr) ≫ yT' from hcomm.symm) e₂`.

Take `⟨n₂, hn₂⟩` from `sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'`. Take `⟨m₁'', hm₁''⟩` from `tr hx' m₁`. Take `⟨κ, nn, hκ, hnn⟩` from `GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr _ G Yt' t' t₂ m₁'' m₂ n₁ n₂`. Establish `hψν : (φ₀ ≫ κ.φ ≫ q.φ) ≫ Z.m0.toSABMap.φ = ψ`. Rewrite using `[Category.assoc, Category.assoc, ← hn₁, hκ, hm₁'', hψ₀]`.

Establish `hlin : LBIso Z.oF.t.PP.L (Xo.univ.t.PP.L.pull Z.m0.toSABMap.φ)`. Take `⟨w, g, -⟩` from `Z.m0.toSABMap.lin`. Conclude with `⟨w, g⟩`. Use `⟨Valued.v, 𝓞 E, inferInstance, H.starRing, P, π₀ ≫ nn.φ ≫ b.φ, φ₀ ≫ κ.φ ≫ q.φ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `((hπ₀.comp nn.cart).comp b.cart).congr (by rw [Category.comp_id, hzeq]) (by rw [Category.assoc])`.

Conclude with `((hφ₀.comp κ.cart).comp q.cart).congr (by rw [Category.comp_id, hyy]) (by rw [Category.assoc])`. Establish `h2 : q.φ ≫ Z.m.φ = n₂.φ ≫ b.φ` using `by rw [← he₂, ← he₂', hn₂]`. Rewrite using `[Category.assoc, Category.assoc, h2, ← Category.assoc κ.φ, ← hnn]`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hgen₀]`.

Establish `h3` using `GlobalTheory.ArcDataDescent.lbIso_pull hlin (φ₀ ≫ κ.φ ≫ q.φ) hψν.symm`. Conclude with `hL.trans P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB Z.oF.t.PP.isLB _) h3.symm`.
-/
theorem pointSt_of_intSt : IntSt → PointSt := by
  intro hInt E _ _ _ H Dw l Xo c Z hpq p _ K _ k z₀ hK z yy hk hz
  obtain ⟨hpu, hcomp, -, hvI, ⟨g₀⟩⟩ := hInt p

  obtain ⟨T, kO, yT, hfin, hkO, hT⟩ :=
    GlobalTheory.DetHT.TestPt.exists_integral_point Z.s (projProper _ _ _ Z.proj) p k hK (z₀ ≫ Z.j)
  have hiO : Function.Injective (algebraMap 𝓞_ℂ_[p] ℂ_[p]) := (PadicComplexInt.integers p).hom_inj
  have hgX : Set.range (spMap (algebraMap T.V T.Fr) ≫ yT) ⊆ Set.range Z.j := by
    rintro _ ⟨s, rfl⟩
    obtain rfl : s = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr) := Subsingleton.elim (α := PrimeSpectrum T.Fr) _ _
    have h1 := bot_map (IsFractionRing.injective T.V T.Fr) yT
    have h2 := bot_map (φ := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO) (hiO.comp hkO) yT
    rw [← sp_sp, hT] at h2
    rw [h1, ← h2, ← Category.assoc]
    exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
  obtain ⟨yyT, hyyT⟩ := GlobalTheory.DetHT.exists_lift_int Z _ hgX
  obtain ⟨io, hio⟩ : ∃ io : c.F →+* T.Fr, yyT ≫ pullback.snd _ _ = spMap io :=
    ⟨(Spec.preimage (yyT ≫ pullback.snd _ _)).hom, (Spec.map_preimage (yyT ≫ pullback.snd _ _)).symm⟩
  let x : Sp T.Fr ⟶ Xo.X := yyT ≫ pullback.fst _ _
  have hx : (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) := by
    letI := io.toAlgebra
    show (yyT ≫ pullback.fst _ _) ≫ Xo.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc yyT, hio, sOf, spMap_spMap]
  obtain ⟨T', i, rr, hrr, hv, hfin', y₀, hy₀⟩ := GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c hpq T io hfin x hx
  obtain ⟨φ, hφ, hloc⟩ := GlobalTheory.GoodChartExt.exists_local_restrict T T' i rr hrr hv
  have hφi : Function.Injective φ := by
    intro a b h
    apply i.injective.comp (IsFractionRing.injective T.V T.Fr)
    have ha := RingHom.congr_fun hφ a
    have hb := RingHom.congr_fun hφ b
    simp only [RingHom.comp_apply] at ha hb
    simp only [Function.comp_apply, ← ha, ← hb, h]
  have hfinφ : φ.Finite := GlobalTheory.CompHS.finite_of_finRes hfin' φ hφi

  let e : 𝓞_ℂ_[p] →+* intO ℂ_[p] := (algebraMap 𝓞_ℂ_[p] ℂ_[p]).codRestrict (intO ℂ_[p]) fun a =>
    (GlobalTheory.CdvrLiftCp.mem_int_iff' _).1 a.2
  have he : (algebraMap (intO ℂ_[p]) ℂ_[p]).comp e = algebraMap 𝓞_ℂ_[p] ℂ_[p] := rfl
  have hinjO : Function.Injective ((algebraMap (intO ℂ_[p]) ℂ_[p]).comp (e.comp kO)) := by
    rw [← RingHom.comp_assoc, he]; exact hiO.comp hkO
  obtain ⟨kO', hkO', hinj'⟩ := exists_ext_of_integral (Valued.v : Valuation ℂ_[p] ℝ≥0) hvI
    φ hφi hfinφ.to_isIntegral (e.comp kO) hinjO
  let k' : T'.Fr →+* ℂ_[p] := IsFractionRing.lift hinj'
  have hk' : ∀ a, algebraMap (intO ℂ_[p]) ℂ_[p] (kO' a) = k' (algebraMap T'.V T'.Fr a) := fun a =>
    (IsFractionRing.lift_algebraMap hinj' a).symm

  letI : Algebra ℤ_[p] (intO ℂ_[p]) := g₀.toAlgebra
  letI algC : Algebra ℤ_[p] ℂ_[p] := ((algebraMap (intO ℂ_[p]) ℂ_[p]).comp g₀).toAlgebra
  haveI : @IsScalarTower ℤ_[p] (intO ℂ_[p]) ℂ_[p] _ _ algC.toSMul := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Fact ¬IsUnit (p : intO ℂ_[p]) := ⟨hpu⟩
  letI := H.starRing
  obtain ⟨P, ψ, hPO⟩ := exists_pointOver E H Dw l Xo c p ℂ_[p] (Valued.v : Valuation ℂ_[p] ℝ≥0) (intO ℂ_[p])
    (fun _ => rfl) hvI T' (i.comp io) y₀ hfin' k' kO' hk'
  obtain ⟨-, G, t', m₁, m₂, π₀, φ₀, hπ₀, hact₀, hφ₀, hgen₀, hψ₀, hL⟩ := hPO

  let yT' : Sp T'.V ⟶ Z.X := spMap φ ≫ yT
  let yyT' : Sp T'.Fr ⟶ Xo.XF c := spMap i ≫ yyT
  have hcomm : spMap (algebraMap T'.V T'.Fr) ≫ yT' = yyT' ≫ Z.j := by
    show spMap (algebraMap T'.V T'.Fr) ≫ spMap φ ≫ yT = (spMap i ≫ yyT) ≫ Z.j
    rw [sp_sp, hφ, ← sp_sp, Category.assoc, hyyT]
  have hx' : (letI := (i.comp io).toAlgebra; y₀.1.x = yyT' ≫ pullback.fst _ _) := by
    letI := (i.comp io).toAlgebra
    rw [hy₀, Category.assoc]
  have hring : ((algebraMap T'.V T'.Fr).comp φ).comp (RingHom.id T.V) = (algebraMap T'.V T'.Fr).comp φ := rfl
  have hkk : (k'.comp (algebraMap T'.V T'.Fr)).comp φ = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO := by
    ext a
    simp only [RingHom.comp_apply]
    rw [← hk' (φ a), show kO' (φ a) = e (kO a) from RingHom.congr_fun hkO' a]
    rfl
  have hyy : spMap k' ≫ yyT' = yy := by
    have := GlobalTheory.DetHT.mono_j_int Z
    rw [← cancel_mono Z.j, Category.assoc, ← hcomm, ← hk, Category.assoc, ← hT]
    show spMap k' ≫ spMap (algebraMap T'.V T'.Fr) ≫ spMap φ ≫ yT = _
    rw [sp_sp, sp_sp, sp_sp, ← hkk]
  have hzz : spMap (intO ℂ_[p]).subtype ≫ spMap kO' ≫ yT' = yy ≫ Z.j := by
    show spMap (intO ℂ_[p]).subtype ≫ spMap kO' ≫ spMap φ ≫ yT = _
    rw [← hyy, Category.assoc, ← hcomm]
    show _ = spMap k' ≫ spMap (algebraMap T'.V T'.Fr) ≫ spMap φ ≫ yT
    rw [sp_sp, sp_sp, sp_sp, sp_sp]
    congr 2
    ext a
    exact hk' (φ a)

  have hzeq : spMap kO' ≫ yT' = z := by
    haveI : IsDomain (intO ℂ_[p]) := hvI.hom_inj.isDomain _
    haveI : ValuationRing (intO ℂ_[p]) := ValuationRing.of_integers _ hvI
    haveI : IsFractionRing (intO ℂ_[p]) ℂ_[p] := hvI.isFractionRing
    haveI : IsProper Z.s := projProper _ _ _ Z.proj
    haveI : IsSeparated (terminal.from Z.X) := by
      rw [show terminal.from Z.X = Z.s ≫ terminal.from _ from terminal.hom_ext _ _]
      infer_instance
    have hU : ValuativeCriterion.Uniqueness (terminal.from Z.X) := IsSeparated.valuativeCriterion _
    let S : ValuativeCommSq (terminal.from Z.X) :=
      { R := intO ℂ_[p], K := ℂ_[p], i₁ := yy ≫ Z.j, i₂ := terminal.from _
        commSq := ⟨terminal.hom_ext _ _⟩ }
    have := (hU S).elim ⟨spMap kO' ≫ yT', hzz, terminal.hom_ext _ _⟩ ⟨z, hz, terminal.hom_ext _ _⟩
    exact congrArg CommSq.LiftStruct.l this

  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g →
      ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩
  obtain ⟨Yt', ⟨b⟩⟩ := exists_sab yT' Z.t
  obtain ⟨t₂, ⟨q⟩⟩ := exists_sab yyT' Z.oF.t
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m0.toSABMap q
  obtain ⟨e₂, he₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Z.m q
  obtain ⟨e₂', he₂'⟩ := tr (show yyT' ≫ Z.jQ ≫ pullback.fst _ _ = spMap (algebraMap T'.V T'.Fr) ≫ yT' from hcomm.symm) e₂
  obtain ⟨n₂, hn₂⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'
  obtain ⟨m₁'', hm₁''⟩ := tr hx' m₁
  obtain ⟨κ, nn, hκ, hnn⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr _ G Yt' t' t₂ m₁'' m₂ n₁ n₂
  have hψν : (φ₀ ≫ κ.φ ≫ q.φ) ≫ Z.m0.toSABMap.φ = ψ := by
    rw [Category.assoc, Category.assoc, ← hn₁, hκ, hm₁'', hψ₀]
  have hlin : LBIso Z.oF.t.PP.L (Xo.univ.t.PP.L.pull Z.m0.toSABMap.φ) := by
    obtain ⟨w, g, -⟩ := Z.m0.toSABMap.lin
    exact ⟨w, g⟩
  refine ⟨Valued.v, 𝓞 E, inferInstance, H.starRing, P, π₀ ≫ nn.φ ≫ b.φ, φ₀ ≫ κ.φ ≫ q.φ, ?_, ?_, ?_, ?_⟩
  · exact ((hπ₀.comp nn.cart).comp b.cart).congr (by rw [Category.comp_id, hzeq]) (by rw [Category.assoc])
  · exact ((hφ₀.comp κ.cart).comp q.cart).congr (by rw [Category.comp_id, hyy]) (by rw [Category.assoc])
  · have h2 : q.φ ≫ Z.m.φ = n₂.φ ≫ b.φ := by rw [← he₂, ← he₂', hn₂]
    rw [Category.assoc, Category.assoc, h2, ← Category.assoc κ.φ, ← hnn]
    simp only [Category.assoc]
    rw [reassoc_of% hgen₀]
  · have h3 := GlobalTheory.ArcDataDescent.lbIso_pull hlin (φ₀ ≫ κ.φ ≫ q.φ) hψν.symm
    exact hL.trans P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB Z.oF.t.PP.isLB _) h3.symm

end GlobalTheory.HalfGeo
