import Formalism.WachLatticeTwists.CupProductVanishing.H2MapInjective

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

/- English proof (translation)
Introduce `O _ _ _ _ Γ _ _ ε hNat Y R _ _ _ _ _ _ _ _ _ _ hY hR i hic hii z hz hzc hfz`. Take `⟨f, hf, hfz⟩` from `hfz`. Take `⟨θ⟩` from `hNat`. Establish `htw : ∀ (M : Type) [AddCommGroup M] [Module O M] (g : Γ) (m : M), Formalism.RepresentationBoundsCohomology.LOC.twist ε M g m = ((ε g : Oˣ) : O) • m` using `fun M _ _ g m => rfl`. Set `zz : ReciprocityTheory.Gal.Z2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y)` to `⟨fun p => z p.1 p.2, hzc, fun g h k => hz g h k⟩`.

Establish `hzero : ReciprocityTheory.Gal.mapH2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) (Formalism.RepresentationBoundsCohomology.LOC.twist ε R) i hic (ReciprocityTheory.ChartRestriction.T2.twist_map ε i) (Submodule.Quotient.mk zz) = 0`. Rewrite using `[ReciprocityTheory.Gal.mapH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]`. Use `⟨f, hf, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Take `⟨g, h⟩` from `p`.

Rewrite using `[ReciprocityTheory.Gal.d1_apply, htw]`. Conclude with `(hfz g h).symm`. Establish `hθ` using `θ.nat Y R hY hR i hic (Submodule.Quotient.mk zz)`. Rewrite `hθ` using `[hzero, map_zero]`. Establish `h0 : θ.θ Y hY (Submodule.Quotient.mk zz) = 0` using `hii (hθ.symm.trans (map_zero i).symm)`.

Establish `hmk : (Submodule.Quotient.mk zz : ReciprocityTheory.Gal.H2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y)) = 0` using `(θ.θ Y hY).injective (by rw [h0, map_zero])`. Rewrite `hmk` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]`. Take `⟨c, hc, hcz⟩` from `hmk`. Use `⟨c, hc, fun g h => ?_⟩` and prove the remaining obligations. Establish `e` using `congrFun hcz (g, h)`.

Rewrite `e` using `[ReciprocityTheory.Gal.d1_apply, htw]`. Conclude with `e.symm`.
-/
theorem h2Map_injective_statement : H2MapInjective := by
  intro O _ _ _ _ Γ _ _ ε hNat Y R _ _ _ _ _ _ _ _ _ _ hY hR i hic hii z hz hzc hfz
  obtain ⟨f, hf, hfz⟩ := hfz
  obtain ⟨θ⟩ := hNat
  have htw : ∀ (M : Type) [AddCommGroup M] [Module O M] (g : Γ) (m : M),
      Formalism.RepresentationBoundsCohomology.LOC.twist ε M g m = ((ε g : Oˣ) : O) • m := fun M _ _ g m => rfl

  let zz : ReciprocityTheory.Gal.Z2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) := ⟨fun p => z p.1 p.2, hzc, fun g h k => hz g h k⟩
  have hzero : ReciprocityTheory.Gal.mapH2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) (Formalism.RepresentationBoundsCohomology.LOC.twist ε R) i hic
      (ReciprocityTheory.ChartRestriction.T2.twist_map ε i) (Submodule.Quotient.mk zz) = 0 := by
    rw [ReciprocityTheory.Gal.mapH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]
    refine ⟨f, hf, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    rw [ReciprocityTheory.Gal.d1_apply, htw]
    exact (hfz g h).symm
  have hθ := θ.nat Y R hY hR i hic (Submodule.Quotient.mk zz)
  rw [hzero, map_zero] at hθ
  have h0 : θ.θ Y hY (Submodule.Quotient.mk zz) = 0 := hii (hθ.symm.trans (map_zero i).symm)
  have hmk : (Submodule.Quotient.mk zz : ReciprocityTheory.Gal.H2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y)) = 0 :=
    (θ.θ Y hY).injective (by rw [h0, map_zero])
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem] at hmk
  obtain ⟨c, hc, hcz⟩ := hmk
  refine ⟨c, hc, fun g h => ?_⟩
  have e := congrFun hcz (g, h)
  rw [ReciprocityTheory.Gal.d1_apply, htw] at e
  exact e.symm

/- English proof (translation)
Introduce `O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hA hNat z hz hzc hfz`. Use `haveI : IsNoetherian O A := by haveI := hA.fg infer_instance`. Use `haveI := hA.t2`. Use `haveI := hA.csmul`. Use `haveI : ContinuousConstSMul O (Ymod r χ E) := ⟨fun a => continuous_induced_rng.2 ((continuous_const_smul a).comp continuous_subtype_val)⟩`.

Set `i : Ymod r χ E →ₗ[O] A` to `(Ymod r χ E).subtype.restrictScalars O`. Establish `hYfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop O (Ymod r χ E)` using `⟨Module.Finite.of_injective i Subtype.val_injective, inferInstance, ⟨continuous_induced_rng.2 (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))⟩⟩`. Conclude with `h2Map_injective_statement O Dw (ε.comp Dw.subtype) hNat (Ymod r χ E) A hYfg hA i continuous_subtype_val Subtype.val_injective z hz hzc hfz`.
-/
theorem clause4 : CupClause := by
  intro O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hA hNat z hz hzc hfz
  haveI : IsNoetherian O A := by
    haveI := hA.fg
    infer_instance
  haveI := hA.t2
  haveI := hA.csmul
  haveI : ContinuousConstSMul O (Ymod r χ E) :=
    ⟨fun a => continuous_induced_rng.2 ((continuous_const_smul a).comp continuous_subtype_val)⟩
  let i : Ymod r χ E →ₗ[O] A := (Ymod r χ E).subtype.restrictScalars O
  have hYfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop O (Ymod r χ E) :=
    ⟨Module.Finite.of_injective i Subtype.val_injective, inferInstance,
      ⟨continuous_induced_rng.2 (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))⟩⟩
  exact h2Map_injective_statement O Dw (ε.comp Dw.subtype) hNat (Ymod r χ E) A hYfg hA i continuous_subtype_val
    Subtype.val_injective z hz hzc hfz

end Formalism.RepresentationBoundsCohomology.T2
