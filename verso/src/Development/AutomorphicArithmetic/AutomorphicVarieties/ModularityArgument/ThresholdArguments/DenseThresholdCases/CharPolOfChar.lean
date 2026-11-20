import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.CharPolSupp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {rc : IrrGL (w.adicCompletion E) → WD h}
/- English proof (translation)
Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Take `⟨𝔪, hm⟩` from `GlobalTheory.langlandsExhaustionGL_holds (w.adicCompletion E) x`. Establish `hs' : HasSupport x.rep (msupp 𝔪)` using `GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm`. Establish `he : s = msupp 𝔪` using `GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds hZ _ x _ _ hs hs'`. Rewrite using `[he, H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map, msupp, Multiset.map_bind, Multiset.prod_bind]`.

Establish `hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]), (l.map F).prod = ((l : Multiset _).map F).prod` using `fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]`. Rewrite using `[hl, Multiset.coe_toList]`. Conclude with `congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => GlobalTheory.RoadU.CharSupport.charPol_seg H Δ g)`.
-/
private theorem charPol_supp (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) (H : UpperTheory.Zero.LLC.LawsT a ha rc)
    (x : IrrGL (w.adicCompletion E)) (s : Multiset (IrrGL (w.adicCompletion E))) (hs : HasSupport x.rep s) (g : Weil h) :
    (rc x).charPol g = (s.map fun y => (rc y).charPol g).prod := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨𝔪, hm⟩ := GlobalTheory.langlandsExhaustionGL_holds (w.adicCompletion E) x
  have hs' : HasSupport x.rep (msupp 𝔪) := GlobalTheory.LocGL.hasSupport_msupp_of_isL hZ _ 𝔪 x hm
  have he : s = msupp 𝔪 :=
    GlobalTheory.LocGL.SupportUnique.hasSupport_unique GlobalTheory.RecT.geometricLemma_holds GlobalTheory.bernsteinZelevinskyFiniteness_holds
      hZ _ x _ _ hs hs'
  rw [he, H.langlands 𝔪.toList x (by rw [Multiset.coe_toList]; exact hm), segSum, CuspExt.charPol_sumList, List.map_map,
    msupp, Multiset.map_bind, Multiset.prod_bind]
  have hl : ∀ (l : List (Segment (w.adicCompletion E))) (F : Segment (w.adicCompletion E) → ℂ[X]),
      (l.map F).prod = ((l : Multiset _).map F).prod := fun l F => by rw [Multiset.map_coe, Multiset.prod_coe]
  rw [hl, Multiset.coe_toList]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun Δ _ => GlobalTheory.RoadU.CharSupport.charPol_seg H Δ g)
/- English proof (translation)
Rewrite using `[H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]`. Simplify using the standard rewrite rules.
-/
private theorem charPol_ofChar (H : UpperTheory.Zero.LLC.LawsT a ha rc) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (g : Weil h) : (rc (IrrGL.ofChar χ hχ)).charPol g = X - C (χ (a g) : ℂ) := by
  rw [H.one, WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
  simp
end
/- English proof (translation)
Introduce `P L Ω _ _ _ _ _ l _ ι n r w hl A h a ha τ hτ hP ψ hψ hsub s`. Establish `Q` using `P.litN`. Take `⟨rc, hrc⟩` from `UpperTheory.Zero.LLC.recTExists L Ω A w h`. Establish `hg : UpperTheory.V.Z.Win.Gd (rc (algNorm τ))` using `UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP`. Establish `hx` using `((hτ A h rc hrc).1 hl).isWDOf hg`.

Establish `hw` using `hx.wdOf_eq hl`. Take `⟨t, ht, φ, hφ, N, b, hN, -⟩` from `hx`. Establish `hpol : (rc (algNorm τ)).charPol s = (r (s : G L Ω)).val.charpoly.map ι.toRingHom`. Rewrite using `[← hw]`. Conclude with `hN.charPol_wdOf hl ht ι s`.

Take `⟨a', ha', H⟩` from `hrc`. Choose the witnesses or unpack the hypotheses as in `rfl : a' = a := by`. Take `⟨art, hart⟩` from `Q.aut.art L Ω`. Establish `hinj` using `GlobalTheory.ArtinLocalInj.artin_localIdele_injective Q.loc.chev L Ω art hart w`. Conclude with `MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)`.

Use `haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _`. Set `τ' : IrrRep (GL (Fin n) (w.adicCompletion L))` to `⟨_, τ.ρ, τ.smooth, τ.irred⟩`. Establish `h1` using `(hasSupport_of_isSubquotient_prinSeries _ n _ hψ τ' hsub).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)`. Establish `h2` using `SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)`. Establish `hc` using `charPol_supp Q.loc.zel H (algNorm τ) _ h2 s`.

Establish `e0 : (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = -(((n : ℂ) - 1) / 2)` using `by push_cast; ring`. Rewrite using `[← hpol, hc, UpperTheory.V.Z.Sym.W.psPol, Finset.prod_eq_multiset_prod]`. Simplify using `only [Multiset.map_map, Function.comp_def]`. Use `congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)` and prove the remaining obligations. Establish `e1 : (IrrGL.ofChar (ψ i) (hψ i)).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = IrrGL.ofChar (ψ i * absPow (w.adicCompletion L) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)) ((hψ i).mul (isSmoothChar_absPow _))` using `IrrGL.tw_ofChar _ _ _ _`.

Rewrite using `[e1, charPol_ofChar H]`. Simplify using `only [e0, MonoidHom.mul_apply]`.
-/
theorem UpperTheory.V.Z.Sym.W.eigW_alt :
    _root_.UpperTheory.V.Z.Sym.W.EigWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι n r w hl A h a ha τ hτ hP ψ hψ hsub s
  have Q := P.litN
  obtain ⟨rc, hrc⟩ := UpperTheory.Zero.LLC.recTExists L Ω A w h
  have hg : UpperTheory.V.Z.Win.Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc n τ hP
  have hx := ((hτ A h rc hrc).1 hl).isWDOf hg
  have hw := hx.wdOf_eq hl
  obtain ⟨t, ht, φ, hφ, N, b, hN, -⟩ := hx
  have hpol : (rc (algNorm τ)).charPol s =
      (r (s : G L Ω)).val.charpoly.map ι.toRingHom := by
    rw [← hw]; exact hN.charPol_wdOf hl ht ι s
  obtain ⟨a', ha', H⟩ := hrc
  obtain rfl : a' = a := by
    obtain ⟨art, hart⟩ := Q.aut.art L Ω
    have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective Q.loc.chev L Ω art hart w
    exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  let τ' : IrrRep (GL (Fin n) (w.adicCompletion L)) := ⟨_, τ.ρ, τ.smooth, τ.irred⟩
  have h1 := (hasSupport_of_isSubquotient_prinSeries _ n _ hψ τ' hsub).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  have h2 := SupportRing.hasSupport_nu h1 (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)
  have hc := charPol_supp Q.loc.zel H (algNorm τ) _ h2 s
  have e0 : (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) = -(((n : ℂ) - 1) / 2) := by push_cast; ring
  rw [← hpol, hc, UpperTheory.V.Z.Sym.W.psPol, Finset.prod_eq_multiset_prod]
  simp only [Multiset.map_map, Function.comp_def]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun i _ => ?_)
  have e1 : (IrrGL.ofChar (ψ i) (hψ i)).nu (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) =
      IrrGL.ofChar (ψ i * absPow (w.adicCompletion L) (((1 - (n : ℝ)) / 2 : ℝ) : ℂ))
        ((hψ i).mul (isSmoothChar_absPow _)) := IrrGL.tw_ofChar _ _ _ _
  rw [e1, charPol_ofChar H]
  simp only [e0, MonoidHom.mul_apply]
end
end
