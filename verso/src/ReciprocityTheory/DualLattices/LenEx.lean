import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
import ReciprocityTheory.DualLattices.UpSmith
import ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
Introduce `C _ v R _ _ hv g Ht A B`. Establish `: IsDomain R` using `hv.hom_inj.isDomain`. Use `ValuationRing.of_integers v hv` as an intermediate fact. Use `set Mm := LinearMap.range (Matrix.mulVecLin Aᵀ) with hMm`. Use `set N := (LinearMap.range (Matrix.mulVecLin B)).map (Matrix.mulVecLin Ht) with hN`.

Establish `hfgM : Mm.FG`. Rewrite using `[hMm, LinearMap.range_eq_map]`. Conclude with `Module.Finite.fg_top.map _`. Establish `hfgN : N.FG`. Rewrite using `[hN, LinearMap.range_eq_map]`.

Conclude with `(Module.Finite.fg_top.map _).map _`. Use `set S := Mm ⊔ N with hS`. Establish `hfgS : S.FG` using `hfgM.sup hfgN`. Establish `: Module.Finite R S` using `Module.Finite.iff_fg.2 hfgS`. Establish `: Module.Free R S` using `L2.SecondCohomologyLattice.free_of_finite_torsionFree S (by`.

Introduce and unpack `r ⟨x, hx⟩ hr h`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun (congrArg Subtype.val h) i` as an intermediate fact. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero, Pi.zero_apply] at this`.

Conclude with `(mul_eq_zero.1 this).resolve_left hr)`. Use `set bS := (Module.Free.chooseBasis R S).reindex (Fintype.equivFin _) with hbS`. Use `set e := bS.equivFun with he`. Use `set N' := N.comap S.subtype with hN'`. Establish `hfgN' : N'.FG`.

Apply `Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype` to reduce the goal to its premises. Rewrite using `[hN', Submodule.map_comap_subtype, inf_eq_right.2 le_sup_right]`. Conclude with `hfgN`. Use `set K := N'.map e.toLinearMap with hK`. Establish `hfgK : K.FG` using `hfgN'.map _`.

Take `⟨n, gK, hgK⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hfgK`. Take `⟨c, ⟨ec⟩⟩` from `Smith.smith_gen hv _ gK`. Use `⟨∏ i, v (algebraMap R C (c i)), _, c, ⟨?_⟩, rfl⟩` and prove the remaining obligations. Establish `h1 : N.comap Mm.subtype = Mm.comap Mm.subtype ⊓ N.comap Mm.subtype`. Rewrite using `[Submodule.comap_subtype_self, top_inf_eq]`.

Conclude with `(Submodule.quotEquivOfEq _ _ h1).trans ((LinearMap.quotientInfEquivSupQuotient Mm N).trans ((Submodule.Quotient.equiv N' K e rfl).trans ((Submodule.quotEquivOfEq _ _ hgK.symm).trans ec)))`.
-/
theorem lenEx : LenExStatement := by
  intro C _ v R _ _ hv g Ht A B
  classical
  have : IsDomain R := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  set Mm := LinearMap.range (Matrix.mulVecLin Aᵀ) with hMm
  set N := (LinearMap.range (Matrix.mulVecLin B)).map (Matrix.mulVecLin Ht) with hN
  have hfgM : Mm.FG := by
    rw [hMm, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map _
  have hfgN : N.FG := by
    rw [hN, LinearMap.range_eq_map]; exact (Module.Finite.fg_top.map _).map _
  set S := Mm ⊔ N with hS
  have hfgS : S.FG := hfgM.sup hfgN
  have : Module.Finite R S := Module.Finite.iff_fg.2 hfgS
  have : Module.Free R S := L2.SecondCohomologyLattice.free_of_finite_torsionFree S (by
    rintro r ⟨x, hx⟩ hr h
    apply Subtype.ext
    funext i
    have := congrFun (congrArg Subtype.val h) i
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left hr)
  set bS := (Module.Free.chooseBasis R S).reindex (Fintype.equivFin _) with hbS
  set e := bS.equivFun with he
  set N' := N.comap S.subtype with hN'
  have hfgN' : N'.FG := by
    apply Submodule.fg_of_fg_map_injective S.subtype S.injective_subtype
    rw [hN', Submodule.map_comap_subtype, inf_eq_right.2 le_sup_right]
    exact hfgN
  set K := N'.map e.toLinearMap with hK
  have hfgK : K.FG := hfgN'.map _
  obtain ⟨n, gK, hgK⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfgK
  obtain ⟨c, ⟨ec⟩⟩ := Smith.smith_gen hv _ gK
  refine ⟨∏ i, v (algebraMap R C (c i)), _, c, ⟨?_⟩, rfl⟩
  have h1 : N.comap Mm.subtype = Mm.comap Mm.subtype ⊓ N.comap Mm.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  exact (Submodule.quotEquivOfEq _ _ h1).trans ((LinearMap.quotientInfEquivSupQuotient Mm N).trans
    ((Submodule.Quotient.equiv N' K e rfl).trans ((Submodule.quotEquivOfEq _ _ hgK.symm).trans ec)))

end ReciprocityTheory.PGsh.Up
