import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Coprod
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Take `⟨n, z, hz⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (maximalIdeal R))`. Establish `hm : ∀ s, z s ∈ maximalIdeal R` using `fun s => hz ▸ Submodule.subset_span ⟨s, rfl⟩`. Use `haveI : IsCO O (MvPowerSeries (Fin n) O) := co_mvps O O (Fin n)`. Take `⟨F, ⟨-, hF⟩, -⟩` from `co_ev O O R (Fin n) (Algebra.ofId _ _) z hm`. Use `⟨⟨Fin n, fun _ => (), F, ?_, ?_⟩, fun s => ?_⟩` and prove the remaining obligations.

Use `co_surj O _ R _ (le_trans ?_ le_sup_left)` and prove the remaining obligations. Rewrite using `[← hz, Submodule.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[← hF s]`. Use `Ideal.mem_map_of_mem _ fun hu => ?_` and prove the remaining obligations.

Simplify using `using MvPowerSeries.isUnit_constantCoeff _ hu`. Introduce `g hg j`. Establish `: wcomp O (fun _ : Fin n => ()) j g = g`. Use extensionality with `a`. Rewrite using `[coeff_wcomp, if_pos (Subsingleton.elim _ _)]`.

Rewrite using `[this]` and apply the resulting hypothesis. Use `show F (MvPowerSeries.X s) ∈ _`. Rewrite using `[hF]`. Conclude with `hm s`.
-/
private theorem co_coprod_pres (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] :
    ∃ W : WPres O Unit R, ∀ s, W.z s ∈ maximalIdeal R := by
  obtain ⟨n, z, hz⟩ := Submodule.fg_iff_exists_fin_generating_family.1
    (IsNoetherian.noetherian (maximalIdeal R))
  have hm : ∀ s, z s ∈ maximalIdeal R := fun s => hz ▸ Submodule.subset_span ⟨s, rfl⟩
  haveI : IsCO O (MvPowerSeries (Fin n) O) := co_mvps O O (Fin n)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O R (Fin n) (Algebra.ofId _ _) z hm
  refine ⟨⟨Fin n, fun _ => (), F, ?_, ?_⟩, fun s => ?_⟩
  · refine co_surj O _ R _ (le_trans ?_ le_sup_left)
    rw [← hz, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    rw [← hF s]
    refine Ideal.mem_map_of_mem _ fun hu => ?_
    simpa using MvPowerSeries.isUnit_constantCoeff _ hu
  · intro g hg j
    have : wcomp O (fun _ : Fin n => ()) j g = g := by
      ext a
      rw [coeff_wcomp, if_pos (Subsingleton.elim _ _)]
    rwa [this]
  · show F (MvPowerSeries.X s) ∈ _
    rw [hF]
    exact hm s

/- English proof (translation)
Introduce `O _ _ _ _ T _ B _ _ _`. Use `haveI := Fintype.ofFinite T`. Use `choose WB hWB using fun t => co_coprod_pres O (B t)`. Take `⟨R, i1, i2, i3, i, _, _, h, -⟩` from `coprod O Unit T B WB hWB`. Conclude with `⟨R, i1, i2, i3, i, h⟩`.
-/
theorem UpperTheory.V.CA.co_coprod :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (T : Type) [Finite T] (B : T → Type) [∀ t, CommRing (B t)] [∀ t, Algebra O (B t)] [∀ t, IsCO O (B t)], ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (j : ∀ t, B t →ₐ[O] R), ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : ∀ t, B t →ₐ[O] R'), ∃! g : R →ₐ[O] R', ∀ t, g.comp (j t) = f t := by
  intro O _ _ _ _ T _ B _ _ _
  haveI := Fintype.ofFinite T
  choose WB hWB using fun t => co_coprod_pres O (B t)
  obtain ⟨R, i1, i2, i3, i, _, _, h, -⟩ := coprod O Unit T B WB hWB
  exact ⟨R, i1, i2, i3, i, h⟩
