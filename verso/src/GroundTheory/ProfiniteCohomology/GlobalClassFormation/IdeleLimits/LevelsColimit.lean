import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Levels
import GroundTheory.ProfiniteCohomology.FilteredHomology
import GroundTheory.ProfiniteCohomology.Factor
import GroundTheory.ProfiniteCohomology.InflationRestriction.DegreeOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  FiniteSubfield IdeleLimit

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable (K : FiniteSubfield)

instance compactSpace_fixingSubgroup : CompactSpace K.1.fixingSubgroup :=
  isCompact_iff_compactSpace.1 K.1.fixingSubgroup_isClosed.isCompact

variable {K}

abbrev levelCochainsInfl (p : GLevel K) :
    cochainsComplex (ideleRep K.1 p.1.1) ⟶ cochainsComplex (limitRep K) :=
  cochainsMapAlong restrictHom continuous_restrictHom (levelMor K p.1)

abbrev levelCochainsMap {p q : GLevel K} (h : p ≤ q) :
    cochainsComplex (ideleRep K.1 p.1.1) ⟶ cochainsComplex (ideleRep K.1 q.1.1) :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  cochainsMapAlong (levelRestrict K p.1 q.1) continuous_levelRestrict (levelMap K p.1 q.1)

/- English proof (translation)
The claim follows from `haveI : Fact (p.1 ≤ q.1) := ⟨h⟩ levelCochains_comp`.
-/
theorem levelCochainsMap_comp_levelCochainsInfl {p q : GLevel K} (h : p ≤ q) :
    levelCochainsMap h ≫ levelCochainsInfl q = levelCochainsInfl p :=
  haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
  levelCochains_comp

/- English proof (translation)
Introduce `y y' h`. Apply `(ModuleCat.mono_iff_injective ((cochainsComplexι (ideleRep K.1 p.1.1)).f m)).1 inferInstance` to reduce the goal to its premises. Use function extensionality and compare the values at `τ`. Set `σ : Fin m → K.1.fixingSubgroup` to `fun i => Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)`. Establish `hσ : (fun i => restrictHom (E` using `p.1) (σ i)) = τ :=`.

Use function extensionality and compare the values at `fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)`. Establish `h1` using `congrFun (congrArg (fun c => ((cochainsComplexι (limitRep K)).f m).hom c) h) σ`. Simplify using `only [cochainsComplexι_cochainsMapAlong_apply] at h1`. Express the relevant statement in the definitionally equal form `Additive.ofMul (of p.1 (((cochainsComplexι _).f m).hom y (fun i => restrictHom (E := p.1) (σ i))).toMul) = Additive.ofMul (of p.1 (((cochainsComplexι _).f m).hom y' (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1`. Rewrite `h1` using `[hσ]`.

Conclude with `congrArg Additive.ofMul (of_injective p.1 (congrArg Additive.toMul h1))`.
-/
theorem levelCochains_injective (p : GLevel K) (m : ℕ) :
    Function.Injective ((levelCochainsInfl p).f m).hom := by
  intro y y' h
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (ideleRep K.1 p.1.1)).f m)).1 inferInstance
  funext τ
  let σ : Fin m → K.1.fixingSubgroup := fun i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have hσ : (fun i => restrictHom (E := p.1) (σ i)) = τ :=
    funext fun i => Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  have h1 := congrFun (congrArg (fun c => ((cochainsComplexι (limitRep K)).f m).hom c) h) σ
  simp only [cochainsComplexι_cochainsMapAlong_apply] at h1
  change Additive.ofMul (of p.1 (((cochainsComplexι _).f m).hom y
      (fun i => restrictHom (E := p.1) (σ i))).toMul) =
    Additive.ofMul (of p.1 (((cochainsComplexι _).f m).hom y'
      (fun i => restrictHom (E := p.1) (σ i))).toMul) at h1
  rw [hσ] at h1
  exact congrArg Additive.ofMul (of_injective p.1 (congrArg Additive.toMul h1))

/- English proof (translation)
Establish `hx : IsLocallyConstant (((cochainsComplexι (limitRep K)).f m).hom x : (Fin m → K.1.fixingSubgroup) → limitRep K)` using `(show locallyConstantCochains (limitRep K) m from x).2`. Use `set f := ((cochainsComplexι (limitRep K)).f m).hom x with hf`. Take `⟨U, hU⟩` from `exists_openNormalSubgroup_fin_of_isLocallyConstant hx`. Take `⟨t, ht, htU⟩` from `isOpen_induced_iff.1 U.isOpen`. Establish `h1t : (1 : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ t`.

Establish `: (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t`. Rewrite using `[htU]`. Conclude with `U.one_mem`. Conclude with `this`. Take `⟨E₀, hE₀fin, hE₀⟩` from `(krullTopology_mem_nhds_one_iff ℚ ℚ̄ t).1 (ht.mem_nhds h1t)`.

Establish `hfin : (Set.range f).Finite` using `hx.range_finite`. Use `choose idx x' hx' using fun a : limitRep K => exists_of (Additive.toMul a)`. Use `choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E`. Take `⟨p, hp⟩` from `Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪ {lev ⟨E₀, hE₀fin⟩})`. Establish `hpE₀ : E₀ ≤ p.1.1` using `(hlev ⟨E₀, hE₀fin⟩).trans (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))`.

Establish `hker : ∀ g : K.1.fixingSubgroup, restrictHom (E` using `p.1) g = 1 → g ∈ U := by`. Introduce `g hg`. Establish `hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup`. Rewrite using `[← ker_restrictHom, MonoidHom.mem_ker]`. Conclude with `hg`.

Rewrite `hg'` using `[Subgroup.mem_subgroupOf]`. Establish `: g ∈ Subtype.val ⁻¹' t` using `hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')`. Rewrite `this` using `[htU]`. Conclude with `this`. Establish `hval : ∀ g, ∃ z : IdeleGroup p.1.1, of p.1 z = Additive.toMul (f g)`.

Introduce `g`. Establish `hmem : f g ∈ hfin.toFinset` using `by simp`. Establish `hle : idx (f g) ≤ p.1` using `(hlev (idx (f g))).trans (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))`. Conclude with `⟨ideleMap hle (x' (f g)), by rw [of_ideleMap]; exact hx' _⟩`. Use `choose z hz using hval`.

Set `lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup` to `fun τ i => Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)`. Use `⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩` and prove the remaining obligations. Apply `(ModuleCat.mono_iff_injective ((cochainsComplexι (limitRep K)).f m)).1 inferInstance` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Express the relevant statement in the definitionally equal form `Additive.ofMul (of p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g`.

Rewrite using `[hz]`. Use `hU _ _ fun i => hker _ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)), inv_mul_cancel]`.
-/
theorem exists_levelCochains_eq (m : ℕ) (x : (cochainsComplex (limitRep K)).X m) :
    ∃ (p : GLevel K) (y : (cochainsComplex (ideleRep K.1 p.1.1)).X m),
      ((levelCochainsInfl p).f m).hom y = x := by
  classical
  have hx : IsLocallyConstant (((cochainsComplexι (limitRep K)).f m).hom x :
      (Fin m → K.1.fixingSubgroup) → limitRep K) :=
    (show locallyConstantCochains (limitRep K) m from x).2
  set f := ((cochainsComplexι (limitRep K)).f m).hom x with hf
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_fin_of_isLocallyConstant hx
  obtain ⟨t, ht, htU⟩ := isOpen_induced_iff.1 U.isOpen
  have h1t : (1 : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ t := by
    have : (1 : K.1.fixingSubgroup) ∈ Subtype.val ⁻¹' t := by
      rw [htU]
      exact U.one_mem
    exact this
  obtain ⟨E₀, hE₀fin, hE₀⟩ := (krullTopology_mem_nhds_one_iff ℚ ℚ̄ t).1 (ht.mem_nhds h1t)
  have hfin : (Set.range f).Finite := hx.range_finite
  choose idx x' hx' using fun a : limitRep K => exists_of (Additive.toMul a)
  choose lev hlev using fun E : FiniteSubfield => GLevel.exists_le (K := K) E
  obtain ⟨p, hp⟩ := Finset.exists_le ((hfin.toFinset.image fun a => lev (idx a)) ∪
    {lev ⟨E₀, hE₀fin⟩})
  have hpE₀ : E₀ ≤ p.1.1 := (hlev ⟨E₀, hE₀fin⟩).trans
    (hp _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)))
  have hker : ∀ g : K.1.fixingSubgroup, restrictHom (E := p.1) g = 1 → g ∈ U := by
    intro g hg
    have hg' : g ∈ p.1.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup := by
      rw [← ker_restrictHom, MonoidHom.mem_ker]
      exact hg
    rw [Subgroup.mem_subgroupOf] at hg'
    have : g ∈ Subtype.val ⁻¹' t := hE₀ (IntermediateField.fixingSubgroup_le hpE₀ hg')
    rw [htU] at this
    exact this
  have hval : ∀ g, ∃ z : IdeleGroup p.1.1, of p.1 z = Additive.toMul (f g) := by
    intro g
    have hmem : f g ∈ hfin.toFinset := by simp
    have hle : idx (f g) ≤ p.1 := (hlev (idx (f g))).trans
      (hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hmem)))
    exact ⟨ideleMap hle (x' (f g)), by rw [of_ideleMap]; exact hx' _⟩
  choose z hz using hval
  let lift : (Fin m → (p.1.1 ≃ₐ[K.1] p.1.1)) → Fin m → K.1.fixingSubgroup := fun τ i =>
    Function.surjInv (restrictHom_surjective (F := K) (E := p.1)) (τ i)
  refine ⟨p, ⟨fun τ => Additive.ofMul (z (lift τ)), IsLocallyConstant.of_discrete _⟩, ?_⟩
  apply (ModuleCat.mono_iff_injective ((cochainsComplexι (limitRep K)).f m)).1 inferInstance
  funext g
  change Additive.ofMul (of p.1 (z (lift fun i => restrictHom (E := p.1) (g i)))) = f g
  rw [hz]
  refine hU _ _ fun i => hker _ ?_
  rw [map_mul, map_inv, Function.surjInv_eq (restrictHom_surjective (F := K) (E := p.1)),
    inv_mul_cancel]

/- English proof (translation)
Take `⟨z, rfl⟩` from `(ModuleCat.epi_iff_surjective ((cochainsComplex (limitRep K)).homologyπ n)).1 inferInstance x`. Take `⟨p, y₀, hy₀⟩` from `exists_levelCochains_eq n (((cochainsComplex (limitRep K)).iCycles n).hom z)`. Establish `hd : ((cochainsComplex (ideleRep K.1 p.1.1)).d n (n + 1)).hom y₀ = 0`. Apply `levelCochains_injective p (n + 1)` to reduce the goal to its premises. Rewrite using `[map_zero, hom_f_d_apply, hy₀]`.

Conclude with `iCycles_d_apply _ n (n + 1) z`. Take `⟨w, hw⟩` from `exists_iCycles_eq_of_d_eq_zero _ n y₀ hd`. Use `⟨p, ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n).hom w, ?_⟩` and prove the remaining obligations. Use `(homologyMap_homologyπ_apply (levelCochainsInfl p) n w).trans (congrArg _ ?_)` and prove the remaining obligations. Apply `(ModuleCat.mono_iff_injective ((cochainsComplex (limitRep K)).iCycles n)).1 inferInstance` to reduce the goal to its premises.

Rewrite using `[iCycles_cyclesMap_apply, hw, hy₀]`.
-/
theorem exists_levelInfl_eq (n : ℕ) (x : cohomology (limitRep K) n) :
    ∃ (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n), (levelInfl K p.1 n).hom y = x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((cochainsComplex (limitRep K)).homologyπ n)).1 inferInstance x
  obtain ⟨p, y₀, hy₀⟩ := exists_levelCochains_eq n (((cochainsComplex (limitRep K)).iCycles n).hom z)
  have hd : ((cochainsComplex (ideleRep K.1 p.1.1)).d n (n + 1)).hom y₀ = 0 := by
    apply levelCochains_injective p (n + 1)
    rw [map_zero, hom_f_d_apply, hy₀]
    exact iCycles_d_apply _ n (n + 1) z
  obtain ⟨w, hw⟩ := exists_iCycles_eq_of_d_eq_zero _ n y₀ hd
  refine ⟨p, ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n).hom w, ?_⟩
  refine (homologyMap_homologyπ_apply (levelCochainsInfl p) n w).trans (congrArg _ ?_)
  apply (ModuleCat.mono_iff_injective ((cochainsComplex (limitRep K)).iCycles n)).1 inferInstance
  rw [iCycles_cyclesMap_apply, hw, hy₀]

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨w, hw⟩ : ∃ w, ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n).hom w = y` from `(ModuleCat.epi_iff_surjective ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n)).1 inferInstance y`. Substitute `hw` using the available equality. Establish `hy'` using `(homologyMap_homologyπ_apply (levelCochainsInfl p) n w).symm.trans hy`. Take `⟨u, hu⟩` from `(homologyπ_eq_zero_iff _ _).1 hy'`. Rewrite `hu` using `[iCycles_cyclesMap_apply]`.

Take `⟨q, u', hu'⟩` from `exists_levelCochains_eq _ u`. Take `⟨r, hpr, hqr⟩` from `GLevel.exists_ge p q`. Use `⟨r, hpr, (homologyMap_homologyπ_apply (levelCochainsMap hpr) n w).trans ((homologyπ_eq_zero_iff _ _).2 ⟨((levelCochainsMap hqr).f _).hom u', ?_⟩)⟩` and prove the remaining obligations. Rewrite using `[iCycles_cyclesMap_apply]`. Apply `levelCochains_injective r n` to reduce the goal to its premises.

Rewrite using `[hom_f_d_apply]`. Establish `e1` using `congrArg (fun φ => (φ.f _).hom u') (levelCochainsMap_comp_levelCochainsInfl hqr)`. Establish `e2` using `congrArg (fun φ => (φ.f n).hom (((cochainsComplex (ideleRep K.1 p.1.1)).iCycles n).hom w)) (levelCochainsMap_comp_levelCochainsInfl hpr)`. Simplify using `only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2`. Rewrite using `[e1, e2, hu', hu]`.
-/
theorem exists_levelTransition_eq_zero (n : ℕ) (p : GLevel K) (y : cohomology (ideleRep K.1 p.1.1) n)
    (hy : (levelInfl K p.1 n).hom y = 0) :
    ∃ (q : GLevel K) (h : p ≤ q),
      (HomologicalComplex.homologyMap (levelCochainsMap h) n).hom y = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n).hom w = y :=
    (ModuleCat.epi_iff_surjective ((cochainsComplex (ideleRep K.1 p.1.1)).homologyπ n)).1
      inferInstance y
  subst hw
  have hy' := (homologyMap_homologyπ_apply (levelCochainsInfl p) n w).symm.trans hy
  obtain ⟨u, hu⟩ := (homologyπ_eq_zero_iff _ _).1 hy'
  rw [iCycles_cyclesMap_apply] at hu
  obtain ⟨q, u', hu'⟩ := exists_levelCochains_eq _ u
  obtain ⟨r, hpr, hqr⟩ := GLevel.exists_ge p q
  refine ⟨r, hpr, (homologyMap_homologyπ_apply (levelCochainsMap hpr) n w).trans
    ((homologyπ_eq_zero_iff _ _).2 ⟨((levelCochainsMap hqr).f _).hom u', ?_⟩)⟩
  rw [iCycles_cyclesMap_apply]
  apply levelCochains_injective r n
  rw [hom_f_d_apply]
  have e1 := congrArg (fun φ => (φ.f _).hom u') (levelCochainsMap_comp_levelCochainsInfl hqr)
  have e2 := congrArg (fun φ => (φ.f n).hom (((cochainsComplex (ideleRep K.1 p.1.1)).iCycles n).hom w))
    (levelCochainsMap_comp_levelCochainsInfl hpr)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at e1 e2
  rw [e1, e2, hu', hu]

end

end GroundTheory.ProfCoh
