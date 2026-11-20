import Mathlib
import GroundTheory.ProfiniteCohomology.CyclicCupProf
import GroundTheory.ProfiniteCohomology.GaloisCohomology.BrauerInflation
import GroundTheory.ProfiniteCohomology.InflationRestriction
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology GroundTheory.GroupCoh IntermediateField

section Generic

universe u

variable {k G : Type u} [CommRing k] [Group G]

/- English proof (translation)
Establish `e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Fin.fin_one_eq_zero i]`. Both sides reduce to the same expression. Establish `e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[Fin.fin_one_eq_zero i]`. Simplify using `[Fin.contractNth]`. Establish `e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0`. Use function extensionality and compare the values at `i`.

Rewrite using `[Fin.fin_one_eq_zero i]`. Simplify using `[Fin.contractNth]`. Simplify using `only [inhomogeneousCochains.d_hom_apply]`. Simplify using `only [e1]`. Simplify using the standard rewrite rules.

Rewrite using `[e2, e3]`. Normalize the expressions using the abelian group laws.
-/
theorem inhomogeneousCochains_d_one_apply (A : Rep.{u} k G) (f : (Fin 1 → G) → A) (g : Fin 2 → G) :
    (inhomogeneousCochains.d A 1).hom f g =
      A.ρ (g 0) (f (fun _ => g 1)) - f (fun _ => g 0 * g 1) + f (fun _ => g 0) := by
  have e1 : (fun i : Fin 1 => g i.succ) = fun _ => g 1 := by
    funext i; rw [Fin.fin_one_eq_zero i]; rfl
  have e2 : Fin.contractNth 0 (· * ·) g = fun _ => g 0 * g 1 := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  have e3 : Fin.contractNth 1 (· * ·) g = fun _ => g 0 := by
    funext i; rw [Fin.fin_one_eq_zero i]; simp [Fin.contractNth]
  simp only [inhomogeneousCochains.d_hom_apply]
  simp only [e1]
  simp
  rw [e2, e3]
  abel

variable [TopologicalSpace G] [IsTopologicalGroup G]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(inflation A U 2).hom ((groupCohomology.π _ 2).hom ((isoCocycles₂ _).inv z)) = 0 ↔ _`. Rewrite using `[inflation_π]`. Express the relevant statement in the definitionally equal form `((cochainsComplex A).homologyπ 2).hom _ = 0 ↔ _`. Rewrite using `[homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]`. Establish `hR : ∀ v : Fin 2 → G, cochainOf A (((cochainsComplex A).iCycles 2).hom ((HomologicalComplex.cyclesMap (inflationCochains A U) 2) ((isoCocycles₂ _).inv z))) v = (z ((v 0 : G ⧸ (U : Subgroup G)), (v 1 : G ⧸ (U : Subgroup G))) : A)`.

Introduce `v`. Establish `e` using `congrFun (cochainOf_cocycleι_cyclesMap_inflationCochains U A ((isoCocycles₂ _).inv z)) v`. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[isoCocycles₂_inv_comp_iCocycles_apply]`. Both sides reduce to the same expression.

Establish `hL : ∀ (w : (cochainsComplex A).X 1) (v : Fin 2 → G), cochainOf A (((cochainsComplex A).d 1 2).hom w) v = A.ρ (v 0) (cochainOf A w (fun _ => v 1)) - cochainOf A w (fun _ => v 0 * v 1) + cochainOf A w (fun _ => v 0)`. Introduce `w v`. Establish `e` using `congrFun (cochainOf_d (A := A) w) v`. Conclude with `e.trans (inhomogeneousCochains_d_one_apply A _ v)`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw⟩`. Use `⟨fun g => cochainOf A w (fun _ => g), (isLocallyConstant_cochainOf w).comp_continuous (continuous_pi fun _ => continuous_id), fun g h => ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (fun c => cochainOf A c ![g, h]) hw`. Simplify using `only at e`. Rewrite `e` using `[hL, hR]`.

Conclude with `e`. Introduce and unpack `⟨f, hf, hfz⟩`. Use `⟨mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0)), ?_⟩` and prove the remaining obligations. Apply `cochainOf_injective` to reduce the goal to its premises. Use function extensionality and compare the values at `v`.

Rewrite using `[hL, hR]`. Conclude with `hfz (v 0) (v 1)`.
-/
theorem inflation_H2π_eq_zero_iff (A : Rep.{u} k G) [IsDiscreteRep A] (U : OpenNormalSubgroup G)
    (z : cocycles₂ (A.quotientToInvariants (U : Subgroup G))) :
    (inflation A U 2).hom (H2π _ z) = 0 ↔
      ∃ f : G → A, IsLocallyConstant f ∧ ∀ g h : G,
        A.ρ g (f h) - f (g * h) + f g = (z ((g : G ⧸ (U : Subgroup G)), (h : G ⧸ (U : Subgroup G))) : A) := by
  change (inflation A U 2).hom ((groupCohomology.π _ 2).hom ((isoCocycles₂ _).inv z)) = 0 ↔ _
  rw [inflation_π]
  change ((cochainsComplex A).homologyπ 2).hom _ = 0 ↔ _
  rw [homologyπ_eq_zero_iff, CochainComplex.prev_nat_succ]
  have hR : ∀ v : Fin 2 → G, cochainOf A (((cochainsComplex A).iCycles 2).hom
      ((HomologicalComplex.cyclesMap (inflationCochains A U) 2) ((isoCocycles₂ _).inv z))) v =
        (z ((v 0 : G ⧸ (U : Subgroup G)), (v 1 : G ⧸ (U : Subgroup G))) : A) := by
    intro v
    have e := congrFun (cochainOf_cocycleι_cyclesMap_inflationCochains U A ((isoCocycles₂ _).inv z)) v
    refine e.trans ?_
    rw [isoCocycles₂_inv_comp_iCocycles_apply]
    rfl
  have hL : ∀ (w : (cochainsComplex A).X 1) (v : Fin 2 → G),
      cochainOf A (((cochainsComplex A).d 1 2).hom w) v =
        A.ρ (v 0) (cochainOf A w (fun _ => v 1)) - cochainOf A w (fun _ => v 0 * v 1) +
          cochainOf A w (fun _ => v 0) := by
    intro w v
    have e := congrFun (cochainOf_d (A := A) w) v
    exact e.trans (inhomogeneousCochains_d_one_apply A _ v)
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨fun g => cochainOf A w (fun _ => g),
      (isLocallyConstant_cochainOf w).comp_continuous (continuous_pi fun _ => continuous_id),
      fun g h => ?_⟩
    have e := congrArg (fun c => cochainOf A c ![g, h]) hw
    simp only at e
    rw [hL, hR] at e
    exact e
  · rintro ⟨f, hf, hfz⟩
    refine ⟨mkCochain A (fun v : Fin 1 → G => f (v 0)) (hf.comp_continuous (continuous_apply 0)), ?_⟩
    apply cochainOf_injective
    funext v
    rw [hL, hR]
    exact hfz (v 0) (v 1)

end Generic

def charKerOpen {G : Type} [Group G] [TopologicalSpace G] (χ : Additive G →ₜ+ QZ) :
    OpenNormalSubgroup G where
  toSubgroup := charKer (charAdd χ)
  isOpen' := by
    have e : (charKer (charAdd χ) : Set G) = (fun g : G => χ (Additive.ofMul g)) ⁻¹' {0} := by
      ext g
      exact mem_charKer
    change IsOpen (charKer (charAdd χ) : Set G)
    rw [e]
    exact (isOpen_discrete _).preimage (χ.continuous_toFun.comp continuous_ofMul)
  isNormal' := inferInstance

section Galois

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/- English proof (translation)
Rewrite using `[inflation_galUnits_eq, ModuleCat.hom_comp, LinearMap.coe_comp]`. Conclude with `(unitsInflation_fixedField_two_injective U).comp ((ModuleCat.mono_iff_injective _).1 inferInstance)`.
-/
theorem galUnits_inflation_two_injective (U : OpenNormalSubgroup Gal(L/K)) :
    Function.Injective (inflation (galUnits.{0} K L) U 2).hom := by
  rw [inflation_galUnits_eq, ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (unitsInflation_fixedField_two_injective U).comp
    ((ModuleCat.mono_iff_injective _).1 inferInstance)

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Proceed by induction on `x using H2_induction_on with`. Consider the case `h z`. Take `⟨f, hf, hfz⟩` from `(inflation_H2π_eq_zero_iff _ U z).1 hx`.

Set `z' : cocycles₂ ((galUnits.{0} K L).quotientToInvariants (U : Subgroup Gal(L/K)))` to `⟨fun p => ⟨(z p : Additive Lˣ), (z p).2⟩, (mem_cocycles₂_iff _).2 fun g h j => by`. Proceed by induction on `g using QuotientGroup.induction_on with`. Consider the case `H g`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e` using `congrArg Subtype.val ((mem_cocycles₂_iff z).1 z.2 (g : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) h j)`.

Conclude with `e⟩`. Establish `h' : (inflation (galUnits.{0} K L) U 2).hom (H2π _ z') = 0` using `(inflation_H2π_eq_zero_iff _ U z').2 ⟨f, hf, fun g h => hfz g h⟩`. Rewrite `h'` using `[← map_zero (inflation (galUnits.{0} K L) U 2).hom]`. Establish `h0` using `galUnits_inflation_two_injective U h'`. Take `⟨F, hF⟩` from `(H2π_eq_zero_iff z').1 h0`.

Rewrite using `[H2π_eq_zero_iff]`. Use `⟨fun q => ⟨(F q : Additive Lˣ), (F q).2⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Take `⟨q, q'⟩` from `p`. Proceed by induction on `q using QuotientGroup.induction_on with`.

Consider the case `H g`. Establish `e` using `congrArg Subtype.val (congrFun hF ((g : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))), q'))`. Conclude with `Subtype.ext e`.
-/
theorem galUnitsZ_inflation_two_injective (U : OpenNormalSubgroup Gal(L/K)) :
    Function.Injective (inflation (galUnitsZ K L) U 2).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using H2_induction_on with
  | h z =>
  obtain ⟨f, hf, hfz⟩ := (inflation_H2π_eq_zero_iff _ U z).1 hx
  let z' : cocycles₂ ((galUnits.{0} K L).quotientToInvariants (U : Subgroup Gal(L/K))) :=
    ⟨fun p => ⟨(z p : Additive Lˣ), (z p).2⟩, (mem_cocycles₂_iff _).2 fun g h j => by
      induction g using QuotientGroup.induction_on with
      | H g =>
        apply Subtype.ext
        have e := congrArg Subtype.val ((mem_cocycles₂_iff z).1 z.2 (g : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) h j)
        exact e⟩
  have h' : (inflation (galUnits.{0} K L) U 2).hom (H2π _ z') = 0 :=
    (inflation_H2π_eq_zero_iff _ U z').2 ⟨f, hf, fun g h => hfz g h⟩
  rw [← map_zero (inflation (galUnits.{0} K L) U 2).hom] at h'
  have h0 := galUnits_inflation_two_injective U h'
  obtain ⟨F, hF⟩ := (H2π_eq_zero_iff z').1 h0
  rw [H2π_eq_zero_iff]
  refine ⟨fun q => ⟨(F q : Additive Lˣ), (F q).2⟩, ?_⟩
  funext p
  obtain ⟨q, q'⟩ := p
  induction q using QuotientGroup.induction_on with
  | H g =>
    have e := congrArg Subtype.val (congrFun hF ((g : Gal(L/K) ⧸ (U : Subgroup Gal(L/K))), q'))
    exact Subtype.ext e

/- English proof (translation)
Establish `: FiniteDimensional K (fixedField (U : Subgroup Gal(L/K)))` using `inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)`. Establish `: IsGalois K (fixedField (U : Subgroup Gal(L/K)))` using `inferInstanceAs (IsGalois K (fixedFiniteGalois U).toIntermediateField)`. Use `set y : fixedField (U : Subgroup Gal(L/K)) := ⟨((Additive.toMul m.1 : Lˣ) : L), mem_fixedField_of_mem_invariants_galUnits (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩ with hy`. Establish `hq : ∀ q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)), ((Additive.toMul ((((galUnitsZ K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q m : Representation.invariants ((galUnitsZ K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) : Additive Lˣ) : Lˣ) : L) = ((quotientEquivGal U q y : fixe …`. Introduce `q`.

Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H σ`. Rewrite using `[quotientEquivGal_mk_apply]`. Conclude with `coe_galUnitsHom_apply K L σ _`. Rewrite using `[Representation.norm, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum, toMul_sum, Units.coe_prod]`.

Repeatedly rewrite using `[hq]`. Rewrite using `[Fintype.prod_equiv (quotientEquivGal U).toEquiv (fun q => ((quotientEquivGal U q y : fixedField (U : Subgroup Gal(L/K))) : L)) (fun τ => ((τ y : fixedField (U : Subgroup Gal(L/K))) : L)) (fun _ => rfl), ← IntermediateField.coe_prod, ← Algebra.norm_eq_prod_automorphisms]`. Both sides reduce to the same expression.
-/
theorem coe_norm_quotientToInvariants_galUnitsZ (U : OpenNormalSubgroup Gal(L/K))
    [Fintype (Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))]
    (m : Representation.invariants ((galUnitsZ K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
    ((Additive.toMul
        ((((galUnitsZ K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ.norm m :
          Representation.invariants ((galUnitsZ K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
            Additive Lˣ) : Lˣ) : L) =
      algebraMap K L (Algebra.norm K (⟨((Additive.toMul m.1 : Lˣ) : L),
        mem_fixedField_of_mem_invariants_galUnits (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩ :
          fixedField (U : Subgroup Gal(L/K)))) := by
  have : FiniteDimensional K (fixedField (U : Subgroup Gal(L/K))) :=
    inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)
  have : IsGalois K (fixedField (U : Subgroup Gal(L/K))) :=
    inferInstanceAs (IsGalois K (fixedFiniteGalois U).toIntermediateField)
  set y : fixedField (U : Subgroup Gal(L/K)) := ⟨((Additive.toMul m.1 : Lˣ) : L),
    mem_fixedField_of_mem_invariants_galUnits (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩ with hy
  have hq : ∀ q : Gal(L/K) ⧸ (U : Subgroup Gal(L/K)),
      ((Additive.toMul ((((galUnitsZ K L).quotientToInvariants (U : Subgroup Gal(L/K))).ρ q m :
        Representation.invariants ((galUnitsZ K L).ρ.comp (U : Subgroup Gal(L/K)).subtype)) :
          Additive Lˣ) : Lˣ) : L) = ((quotientEquivGal U q y : fixedField (U : Subgroup Gal(L/K))) : L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H σ =>
      rw [quotientEquivGal_mk_apply]
      exact coe_galUnitsHom_apply K L σ _
  rw [Representation.norm, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum, toMul_sum,
    Units.coe_prod]
  simp_rw [hq]
  rw [Fintype.prod_equiv (quotientEquivGal U).toEquiv
      (fun q => ((quotientEquivGal U q y : fixedField (U : Subgroup Gal(L/K))) : L))
      (fun τ => ((τ y : fixedField (U : Subgroup Gal(L/K))) : L)) (fun _ => rfl),
    ← IntermediateField.coe_prod, ← Algebra.norm_eq_prod_automorphisms]
  rfl

/- English proof (translation)
Use `set U : OpenNormalSubgroup Gal(L/K) := charKerOpen χ with hU`. Use `Fintype.ofFinite (Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))` as an intermediate fact. Set `ψ : Additive (Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) →+ AddCircle (1 : ℚ)` to `charBar (charAdd χ)`. Establish `hψinj : Function.Injective ψ` using `charBar_injective _`. Establish `: FiniteDimensional K (fixedField (charKer (charAdd χ)))` using `inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)`.

Establish `hψ : charAdd χ = charComp (U : Subgroup Gal(L/K)) ψ` using `(charComp_charBar (charAdd χ)).symm`. Use `isCyclic_of_injective_char ψ hψinj` as an intermediate fact. Rewrite using `[galCupClass, cupCharClassProf_eq_inflation (galUnitsZ K L) χ U ψ hψ, ← map_zero (inflation (galUnitsZ K L) U 2).hom, (galUnitsZ_inflation_two_injective U).eq_iff, cupCharClass_eq_zero_iff ψ hψinj, mem_normRangeInvariants_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`.

Use `⟨⟨((Additive.toMul m.1 : Lˣ) : L), mem_fixedField_of_mem_invariants_galUnits (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩, ?_⟩` and prove the remaining obligations. Apply `(algebraMap K L).injective` to reduce the goal to its premises. Establish `h` using `coe_norm_quotientToInvariants_galUnitsZ U m`. Rewrite `h` using `[hm]`. Conclude with `h.symm.trans rfl`.

Introduce and unpack `⟨y, hy⟩`. Establish `hy0 : (y : L) ≠ 0`. Introduce `h0`. Establish `: y = 0` using `Subtype.ext h0`. Rewrite `hy` using `[this, Algebra.norm_zero]`.

Conclude with `a.ne_zero hy.symm`. Use `⟨⟨Additive.ofMul (Units.mk0 (y : L) hy0), fun σ => ?_⟩, ?_⟩` and prove the remaining obligations. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(coe_galUnitsHom_apply K L σ.1 _).trans (y.2 σ)`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Additive.toMul.injective` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(coe_norm_quotientToInvariants_galUnitsZ U _).trans (congrArg (algebraMap K L) hy)`.
-/
theorem galCupClass_eq_zero_iff (χ : Additive Gal(L/K) →ₜ+ QZ) (a : Kˣ) :
    galCupClass K L χ a = 0 ↔ ∃ y : fixedField (charKer (charAdd χ)), Algebra.norm K y = (a : K) := by
  set U : OpenNormalSubgroup Gal(L/K) := charKerOpen χ with hU
  have := Fintype.ofFinite (Gal(L/K) ⧸ (U : Subgroup Gal(L/K)))
  let ψ : Additive (Gal(L/K) ⧸ (U : Subgroup Gal(L/K))) →+ AddCircle (1 : ℚ) :=
    charBar (charAdd χ)
  have hψinj : Function.Injective ψ := charBar_injective _
  have : FiniteDimensional K (fixedField (charKer (charAdd χ))) :=
    inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)
  have hψ : charAdd χ = charComp (U : Subgroup Gal(L/K)) ψ :=
    (charComp_charBar (charAdd χ)).symm
  have := isCyclic_of_injective_char ψ hψinj
  rw [galCupClass, cupCharClassProf_eq_inflation (galUnitsZ K L) χ U ψ hψ,
    ← map_zero (inflation (galUnitsZ K L) U 2).hom,
    (galUnitsZ_inflation_two_injective U).eq_iff, cupCharClass_eq_zero_iff ψ hψinj,
    mem_normRangeInvariants_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨⟨((Additive.toMul m.1 : Lˣ) : L),
      mem_fixedField_of_mem_invariants_galUnits (U : Subgroup Gal(L/K)) (v := m.1) m.2⟩, ?_⟩
    apply (algebraMap K L).injective
    have h := coe_norm_quotientToInvariants_galUnitsZ U m
    rw [hm] at h
    exact h.symm.trans rfl
  · rintro ⟨y, hy⟩
    have hy0 : (y : L) ≠ 0 := by
      intro h0
      have : y = 0 := Subtype.ext h0
      rw [this, Algebra.norm_zero] at hy
      exact a.ne_zero hy.symm
    refine ⟨⟨Additive.ofMul (Units.mk0 (y : L) hy0), fun σ => ?_⟩, ?_⟩
    · apply Additive.toMul.injective
      apply Units.ext
      exact (coe_galUnitsHom_apply K L σ.1 _).trans (y.2 σ)
    · apply Subtype.ext
      apply Additive.toMul.injective
      apply Units.ext
      exact (coe_norm_quotientToInvariants_galUnitsZ U _).trans (congrArg (algebraMap K L) hy)

/- English proof (translation)
The claim follows from `galCupClass_eq_zero_iff χ a`.
-/
theorem galCupClass_eq_zero_iff_of_isSepClosure {Ksep : Type} [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (χ : Additive Gal(Ksep/K) →ₜ+ QZ) (a : Kˣ) :
    galCupClass K Ksep χ a = 0 ↔
      ∃ y : fixedField (charKer (charAdd χ)), Algebra.norm K y = (a : K) :=
  galCupClass_eq_zero_iff χ a

end Galois

end GroundTheory.ProfCoh
