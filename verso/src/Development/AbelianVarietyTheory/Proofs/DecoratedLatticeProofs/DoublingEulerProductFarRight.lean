import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SetIntegralUnramifiedPlacesUnionEqLocalFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TendstoSetIntegralUnramifiedOutsideOpenSubsetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasProdPartialLFunctionTwistedByCharLocalFactorsStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.EulerProd

open Filter Topology

/- English proof (translation)
Set `e : {v : ι // v ∉ (S : Set ι)} ↪ ι` to `Function.Embedding.subtype _`. Establish `ht : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => S ∪ T.map e) atTop atTop`. Use `tendsto_atTop.2 fun b => (eventually_ge_atTop (b.subtype fun v => v ∉ (S : Set ι))).mono fun T hT u hu => ?_` and prove the remaining obligations. Distinguish the cases in `hS : u ∈ S`. Conclude with `Finset.mem_union_left _ hS`.

Conclude with `Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨u, hS⟩, hT (Finset.mem_subtype.2 hu), rfl⟩)`. Establish `h1` using `hJ.comp ht`. Establish `h2 : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => (∏ v ∈ T, f v.1) * I S) atTop (𝓝 (P * I S))` using `Tendsto.mul_const _ hP`. Use `tendsto_nhds_unique h1 (h2.congr fun T => ?_)` and prove the remaining obligations. Rewrite using `[Function.comp_apply, h (T.map e) _ ?_ fun u => Finset.mem_union, Finset.prod_map]`.

Both sides reduce to the same expression. Use `Finset.disjoint_left.2 fun u hu hu' => ?_` and prove the remaining obligations. Take `⟨w, -, rfl⟩` from `Finset.mem_map.1 hu'`. Conclude with `w.2 hu`.
-/
theorem limit_eq_prod_mul {ι : Type} (S : Finset ι) (f : ι → ℂ) (I : Finset ι → ℂ) {P J : ℂ}
    (hP : HasProd (fun v : {v : ι // v ∉ (S : Set ι)} => f v.1) P) (hJ : Tendsto I atTop (𝓝 J))
    (h : ∀ T U : Finset ι, Disjoint S T → (∀ u, u ∈ U ↔ u ∈ S ∨ u ∈ T) → I U = (∏ v ∈ T, f v) * I S) :
    J = P * I S := by
  classical
  let e : {v : ι // v ∉ (S : Set ι)} ↪ ι := Function.Embedding.subtype _
  have ht : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => S ∪ T.map e) atTop atTop := by
    refine tendsto_atTop.2 fun b => (eventually_ge_atTop (b.subtype fun v => v ∉ (S : Set ι))).mono fun T hT u hu => ?_
    by_cases hS : u ∈ S
    · exact Finset.mem_union_left _ hS
    · exact Finset.mem_union_right _ (Finset.mem_map.2 ⟨⟨u, hS⟩, hT (Finset.mem_subtype.2 hu), rfl⟩)
  have h1 := hJ.comp ht
  have h2 : Tendsto (fun T : Finset {v : ι // v ∉ (S : Set ι)} => (∏ v ∈ T, f v.1) * I S) atTop (𝓝 (P * I S)) :=
    Tendsto.mul_const _ hP
  refine tendsto_nhds_unique h1 (h2.congr fun T => ?_)
  rw [Function.comp_apply, h (T.map e) _ ?_ fun u => Finset.mem_union, Finset.prod_map]
  · rfl
  · refine Finset.disjoint_left.2 fun u hu hu' => ?_
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hu'
    exact w.2 hu

/- English proof (translation)
Introduce `w hw`. Establish `hv : w.under (𝓞 D.host.F) ∉ Sf` using `hw`. Establish `h0 : u ≠ 0` using `(hpar _ hw w rfl).ne_zero`. Establish `hs : SphFun A L Sf u` using `fun v hv k hk g => by`. Choose the witnesses or unpack the hypotheses as in `⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v := by`.

Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, e⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1 (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)`. Use `⟨⟨Q, hQ.isPrime, fun hb => v.ne_bot ?_⟩, HeightOneSpectrum.ext e⟩` and prove the remaining obligations. Rewrite using `[← e, hb, Ideal.comap_bot_of_injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `(congrFun ((hpar v hv w' hw').mem_fixed ⟨k, hk⟩) g).trans (by simp)`.

Establish `hc` using `GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified hP D θ A cA L hθ m hm Sf u hu u hu par hpar hs _ hv 1 (map_one _)`. Establish `h1 : MemL2Quotient (GQ A) m u` using `memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu).1`. Establish `hpos` using `petersson_self_pos h1 (mem_cuspForms.1 hu).1.1.toIsAutFun.cont h0`. Establish `hne : rcoef m u u (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) ≠ 0`. Establish `e : rTr A (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) u = u` using `funext fun g => by`.

Simplify using `only [rTr, map_one, mul_one]`. Rewrite using `[rcoef, e]`. Introduce `h`. Rewrite `hpos` using `[h]`. Conclude with `lt_irrefl _ hpos`.

Take `⟨h2, h3⟩` from `hB A L hL _ trivial par _ hc hne w rfl`. Conclude with `⟨h2.le, h3⟩`.
-/
theorem bounded_of_isParamFun (hP : GlobalTheory.Published.CuspRapidDecay) {D : D7} (hB : ParamBoundOn D (fun _ => True))
    {θ : InfFam D} {A : HSp D} {cA : CptF A} {L : Lat A} (hθ : IsInfFam θ) (hL : IsSelfDualC A L)
    (m : Measure (GA D A)) (hm : m.IsHaarMeasure) {Sf : Finset (FinPl D)} {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA)
    {par : GlobalTheory.LFun.Fam D.host.E} (hpar : GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u par) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sf : Set (FinPl D))) par A.rank ((A.rank : ℝ) / 2) := by
  intro w hw
  have hv : w.under (𝓞 D.host.F) ∉ Sf := hw
  have h0 : u ≠ 0 := (hpar _ hw w rfl).ne_zero
  have hs : SphFun A L Sf u := fun v hv k hk g => by
    obtain ⟨w', hw'⟩ : ∃ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v := by
      have := v.isMaximal
      obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
        (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
          (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
      refine ⟨⟨Q, hQ.isPrime, fun hb => v.ne_bot ?_⟩, HeightOneSpectrum.ext e⟩
      rw [← e, hb, Ideal.comap_bot_of_injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (FaithfulSMul.algebraMap_injective _ _)]
    exact (congrFun ((hpar v hv w' hw').mem_fixed ⟨k, hk⟩) g).trans (by simp)
  have hc := GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified hP D θ A cA L hθ m hm Sf u hu u hu par hpar hs _ hv 1 (map_one _)
  have h1 : MemL2Quotient (GQ A) m u := memL2_of_cusp_form hP hθ (mem_cuspForms.1 hu).1
  have hpos := petersson_self_pos h1 (mem_cuspForms.1 hu).1.1.toIsAutFun.cont h0
  have hne : rcoef m u u (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) ≠ 0 := by
    have e : rTr A (1 * emb D.sp.cm.sig A.gram (w.under (𝓞 D.host.F)) 1) u = u := funext fun g => by
      simp only [rTr, map_one, mul_one]
    rw [rcoef, e]
    intro h
    rw [h] at hpos
    exact lt_irrefl _ hpos
  obtain ⟨h2, h3⟩ := hB A L hL _ trivial par _ hc hne w rfl
  exact ⟨h2.le, h3⟩

/- English proof (translation)
Introduce `hP D hS hZ hB ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph s hs hint`. Establish `ha : (0 : ℝ) ≤ A.rank` using `Nat.cast_nonneg _`. Establish `hb` using `bounded_of_isParamFun hP hB hp.setting.2.2.2.1 hU.sdA m hm hu₁ hpar`. Establish `hL` using `GlobalTheory.T.hasProd_partialLFunctionTwistedByChar_local_factors D Sf par χB _ _ hb (s + 1 / 2) (by`. Establish `: (s + 1 / 2 : ℂ).re = s.re + 1 / 2` using `by simp`.

Rewrite using `[this]`. Use the proof step `linarith)`. Take `⟨hd0, hdv, hd⟩` from `(GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank).2 s (by linarith)`. Use `limit_eq_prod_mul Sf (fun v => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s) (fun S => ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) ?_ (GlobalTheory.T.tendsto_setIntegral_unramifiedOuts …` and prove the remaining obligations. Conclude with `(Tendsto.div hL hd hd0).congr fun T => (Finset.prod_div_distrib _ _).symm`.
-/
theorem eulerRight : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) →
    ParamBoundOn D (fun _ => True) → EulerRight D := by
  intro hP D hS hZ hB ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph
    s hs hint
  have ha : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
  have hb := bounded_of_isParamFun hP hB hp.setting.2.2.2.1 hU.sdA m hm hu₁ hpar
  have hL := GlobalTheory.T.hasProd_partialLFunctionTwistedByChar_local_factors D Sf par χB _ _ hb (s + 1 / 2) (by
    have : (s + 1 / 2 : ℂ).re = s.re + 1 / 2 := by simp
    rw [this]; linarith)
  obtain ⟨hd0, hdv, hd⟩ := (GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank).2 s (by linarith)
  refine limit_eq_prod_mul Sf
    (fun v => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s)
    (fun S => ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) ?_
    (GlobalTheory.T.tendsto_setIntegral_unramifiedOutsideOpenSubset D A LA hU.sdA m _ hint) fun T U hT hTU =>
      GlobalTheory.T.setIntegral_unramified_places_union_eq_local_factors hP D hS hZ ψ θ A B χA χB sA sB t cA a om ν 𝓕 hp LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par
        hpar hsph s (by linarith) hint Sf T le_rfl hT U hTU
  exact (Tendsto.div hL hd hd0).congr fun T => (Finset.prod_div_distrib _ _).symm

end GlobalTheory.Core.Rk.EulerProd

end
