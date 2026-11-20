import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.NumberField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeaklyAttachedGaloisRepresentationBaseChangeRest
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeParametersUniqueStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel UpperTheory.Gal.TypesAndIwahori GlobalTheory.Cong UpperTheory.Gal.NearKilling

open GlobalTheory.WeakBaseChange in
/- English proof (translation)
Introduce `E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr`. Take `⟨hc, hss, hatt⟩` from `hr`. Use `⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩` and prove the remaining obligations. Use `haveI := finiteIndex_range_res E M Ω set H := (UpperTheory.V.Af.Bc.res E Ω M).range with hH haveI : (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).FiniteIndex := finiteIndex_comap _ _`. Use `isSSRep_of_finiteIndex _ (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)) ?_` and prove the remaining obligations.

Establish `hrange : ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype).range = H.normalCore`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`.

Introduce `hx`. Take `⟨y, hy⟩` from `(Subgroup.normalCore_le H hx : x ∈ (UpperTheory.V.Af.Bc.res E Ω M).range)`. Conclude with `⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩`. Use `UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype) (by rw [hrange]; exact Subgroup.normalCore_normal H) hss` as an intermediate fact. Rewrite using `[MonoidHom.comp_assoc]` and apply the resulting hypothesis.

Unfold `UpperTheory.V.Published.WeakBC at hL filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt, hL] with w h hW`. Take `⟨B, hB, hF⟩` from `h`. Establish `h2` using `GlobalTheory.AttResTower.normV_under_pow (K := E) w`. Use `set f := w.asIdeal.inertiaDeg (𝓞 E)`. Take `⟨B', hB', hP⟩` from `hW f h2`.

Establish `hBB : B' = B` using `GlobalTheory.T.cuspRep_satakeParameters_unique E a (CG.mk π) (w.under (𝓞 E)) B' B hB' hB`. Substitute `hBB` using the available equality. Use `⟨B'.map (· ^ f), hP, ?_⟩` and prove the remaining obligations. Establish `h3` using `(UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF`. Rewrite using `[h2, algSat_pow]`.

Conclude with `h3`.
-/
theorem UpperTheory.Gal.NearKilling.weakRes :
    WeakRes := by
  intro E M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι a π P hL r hr
  obtain ⟨hc, hss, hatt⟩ := hr
  refine ⟨hc.comp (UpperTheory.V.Af.continuous_restrictScalarsHom E M Ω), ?_, ?_⟩
  · haveI := finiteIndex_range_res E M Ω
    set H := (UpperTheory.V.Af.Bc.res E Ω M).range with hH
    haveI : (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).FiniteIndex := finiteIndex_comap _ _
    refine isSSRep_of_finiteIndex _ (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)) ?_
    have hrange : ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype).range = H.normalCore := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.2
      · intro hx
        obtain ⟨y, hy⟩ := (Subgroup.normalCore_le H hx : x ∈ (UpperTheory.V.Af.Bc.res E Ω M).range)
        exact ⟨⟨y, by rw [Subgroup.mem_comap, hy]; exact hx⟩, hy⟩
    have := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r ((UpperTheory.V.Af.Bc.res E Ω M).comp (H.normalCore.comap (UpperTheory.V.Af.Bc.res E Ω M)).subtype)
      (by rw [hrange]; exact Subgroup.normalCore_normal H) hss
    rwa [MonoidHom.comp_assoc]
  · unfold UpperTheory.V.Published.WeakBC at hL
    filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under E M).eventually hatt, hL] with w h hW
    obtain ⟨B, hB, hF⟩ := h
    have h2 := GlobalTheory.AttResTower.normV_under_pow (K := E) w
    set f := w.asIdeal.inertiaDeg (𝓞 E)
    obtain ⟨B', hB', hP⟩ := hW f h2
    have hBB : B' = B := GlobalTheory.T.cuspRep_satakeParameters_unique E a (CG.mk π) (w.under (𝓞 E)) B' B hB' hB
    subst hBB
    refine ⟨B'.map (· ^ f), hP, ?_⟩
    have h3 := (UpperTheory.frobenius_power_compatibility E M Ω l ι w f h2).1 a r _ hF
    rw [h2, algSat_pow]
    exact h3
