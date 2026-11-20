import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CompleteDvrDominatingValuationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricPowerFreeFunctorialStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PelUniformisedGeometricFreeStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.GtBaseChange
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ModelFib

section Topo

/- English proof (translation)
Take `⟨o, ho, hne, hle⟩` from `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hg`. Take `⟨u, huo, huS⟩` from `hS.inter_open_nonempty o ho hne`. Conclude with `⟨u, huS, specializes_iff_mem_closure.mpr (hle huo)⟩`.
-/
theorem exists_specializes_of_dense {T : Type*} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] {S : Set T}
    (hS : Dense S) {g : T} (hg : closure {g} ∈ irreducibleComponents T) : ∃ u ∈ S, g ⤳ u := by
  obtain ⟨o, ho, hne, hle⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hg
  obtain ⟨u, huo, huS⟩ := hS.inter_open_nonempty o ho hne
  exact ⟨u, huS, specializes_iff_mem_closure.mpr (hle huo)⟩

/- English proof (translation)
Use `⟨isIrreducible_singleton.closure, fun C hC hle => ?_⟩` and prove the remaining obligations. Establish `hg : closure {hC.genericPoint} = closure C` using `hC.isGenericPoint_genericPoint_closure`. Establish `ha : a ∈ C` using `hle (subset_closure rfl)`. Establish `h1 : hC.genericPoint ⤳ a` using `specializes_iff_mem_closure.mpr (by rw [hg]; exact subset_closure ha)`. Establish `h2 : a ⤳ hC.genericPoint` using `hmin _ (h1.trans hz)`.

Introduce `c hc`. Establish `h3 : hC.genericPoint ⤳ c` using `specializes_iff_mem_closure.mpr (by rw [hg]; exact subset_closure hc)`. Conclude with `specializes_iff_mem_closure.mp (h2.trans h3)`.
-/
theorem closure_mem_irreducibleComponents {T : Type*} [TopologicalSpace T] [QuasiSober T] {a z : T} (hz : a ⤳ z)
    (hmin : ∀ g : T, g ⤳ z → a ⤳ g) : closure {a} ∈ irreducibleComponents T := by
  refine ⟨isIrreducible_singleton.closure, fun C hC hle => ?_⟩
  have hg : closure {hC.genericPoint} = closure C := hC.isGenericPoint_genericPoint_closure
  have ha : a ∈ C := hle (subset_closure rfl)
  have h1 : hC.genericPoint ⤳ a := specializes_iff_mem_closure.mpr (by rw [hg]; exact subset_closure ha)
  have h2 : a ⤳ hC.genericPoint := hmin _ (h1.trans hz)
  intro c hc
  have h3 : hC.genericPoint ⤳ c := specializes_iff_mem_closure.mpr (by rw [hg]; exact subset_closure hc)
  exact specializes_iff_mem_closure.mp (h2.trans h3)

end Topo

def stalkGen (X : Scheme.{0}) (z : X) [IsDomain (X.presheaf.stalk z)] : X :=
  X.fromSpecStalk z ⟨⊥, Ideal.isPrime_bot⟩

/- English proof (translation)
Establish `h : stalkGen X z ∈ Set.range (X.fromSpecStalk z)` using `⟨_, rfl⟩`. Rewrite `h` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis.
-/
theorem stalkGen_specializes (X : Scheme.{0}) (z : X) [IsDomain (X.presheaf.stalk z)] : stalkGen X z ⤳ z := by
  have h : stalkGen X z ∈ Set.range (X.fromSpecStalk z) := ⟨_, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at h

/- English proof (translation)
Establish `h : g ∈ Set.range (X.fromSpecStalk z)`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hg`. Take `⟨q, rfl⟩` from `h`. Establish `hq : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk z)) ⤳ q` using `(PrimeSpectrum.le_iff_specializes _ _).mp bot_le`.

Conclude with `hq.map (X.fromSpecStalk z).continuous`.
-/
theorem stalkGen_generises (X : Scheme.{0}) (z : X) [IsDomain (X.presheaf.stalk z)] (g : X) (hg : g ⤳ z) :
    stalkGen X z ⤳ g := by
  have h : g ∈ Set.range (X.fromSpecStalk z) := by
    rw [Scheme.range_fromSpecStalk]; exact hg
  obtain ⟨q, rfl⟩ := h
  have hq : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.presheaf.stalk z)) ⤳ q :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  exact hq.map (X.fromSpecStalk z).continuous

section Model

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

/- English proof (translation)
Establish `hprop : IsProper Y.s`. Take `⟨N, i, hi, e⟩` from `Y.proj`. Use `isProper_str O N` as an intermediate fact. Rewrite using `[← e]`. Use `infer_instance`.

Establish `: IsLocallyNoetherian Y.X` using `LocallyOfFiniteType.isLocallyNoetherian Y.s`. Establish `: CompactSpace Y.X` using `QuasiCompact.compactSpace_of_compactSpace Y.s`. Establish `: IsNoetherian Y.X` using `{}`. Establish `hq : IsProper (pullback.snd Y.s (spMap β))` using `inferInstance`. Establish `: IsLocallyNoetherian (pullback Y.s (spMap β))` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap β))`.

Establish `: CompactSpace ↥(pullback Y.s (spMap β) : Scheme.{0})` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap β))`. Establish `: IsNoetherian (pullback Y.s (spMap β))` using `{}`. Establish `ha1` using `stalkGen_specializes Y.X z`. Establish `ha2` using `stalkGen_generises Y.X z`. Take `⟨u, ⟨w₀, rfl⟩, hau⟩` from `exists_specializes_of_dense hd (closure_mem_irreducibleComponents ha1 ha2)`.

Establish `hjs : ∀ y : ↥(pullback Y.s (spMap β) : Scheme.{0}), Y.s (pullback.fst Y.s (spMap β) y) = (spMap β) (pullback.snd Y.s (spMap β) y)` using `fun y => by`. Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]`. Set `pt : Sp c.F` to `pullback.snd Y.s (spMap β) (Y.jQ w₀)`. Establish `hpt : ∀ x : Sp c.F, x = pt` using `fun x => Subsingleton.elim (α := PrimeSpectrum c.F) x pt`. Establish `hP : ∀ w, Y.s (Y.j w) = (spMap β) pt` using `fun w => by`.

Establish `: Y.j w = pullback.fst Y.s (spMap β) (Y.jQ w)` using `by show (Y.jQ ≫ pullback.fst _ _) w = _`. Rewrite using `[Scheme.Hom.comp_apply]`. Rewrite using `[this, hjs, hpt (pullback.snd Y.s (spMap β) (Y.jQ w))]`. Establish `hs : ∀ x, (spMap β) pt ⤳ Y.s x` using `fun x => by`. Establish `h1 : Y.s x ∈ closure {(spMap β) pt}` using `map_mem_closure Y.s.continuous (hd x) (by rintro _ ⟨w, rfl⟩; exact hP w)`.

Conclude with `specializes_iff_mem_closure.mpr h1`. Establish `hsa : Y.s (stalkGen Y.X z) = (spMap β) pt`. Establish `h1` using `hau.map Y.s.continuous`. Rewrite `h1` using `[hP]`. Conclude with `(h1.antisymm (hs _)).eq`.

Take `⟨y, hy1, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := Y.s) (g := spMap β) _ pt hsa`. Establish `hC : IsIrreducible (irreducibleComponent y)` using `isIrreducible_irreducibleComponent`. Establish `hgC : closure {hC.genericPoint} = irreducibleComponent y` using `hC.isGenericPoint_genericPoint_closure.trans isClosed_irreducibleComponent.closure_eq`. Establish `hgy : hC.genericPoint ⤳ y` using `specializes_iff_mem_closure.mpr (by rw [hgC]; exact mem_irreducibleComponent)`. Establish `hfg` using `hgy.map (pullback.fst Y.s (spMap β)).continuous`.

Rewrite `hfg` using `[hy1]`. Establish `hfe : pullback.fst Y.s (spMap β) hC.genericPoint = stalkGen Y.X z` using `(hfg.antisymm (ha2 _ (hfg.trans ha1))).eq`. Take `⟨_, ⟨w, rfl⟩, hgu⟩` from `exists_specializes_of_dense Y.jQ_dense (by rw [hgC]; exact irreducibleComponent_mem_irreducibleComponents y)`. Use `Y.jQ_open` as an intermediate fact. Take `⟨w', hw'⟩` from `hgu.mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨w, rfl⟩`.

Use `⟨w', ?_⟩` and prove the remaining obligations. Use `show (Y.jQ ≫ pullback.fst _ _) w' = _`. Rewrite using `[Scheme.Hom.comp_apply, hw', hfe]`.
-/
theorem stalkGen_mem_range [IsNoetherianRing O] (Y : Model Xo c β) (hd : Dense (Set.range Y.j)) (z : Y.X)
    [IsDomain (Y.X.presheaf.stalk z)] : ∃ w, Y.j w = stalkGen Y.X z := by
  have hprop : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str O N
    rw [← e]; infer_instance
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : CompactSpace Y.X := QuasiCompact.compactSpace_of_compactSpace Y.s
  have : IsNoetherian Y.X := {}
  have hq : IsProper (pullback.snd Y.s (spMap β)) := inferInstance
  have : IsLocallyNoetherian (pullback Y.s (spMap β)) := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Y.s (spMap β))
  have : CompactSpace ↥(pullback Y.s (spMap β) : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd Y.s (spMap β))
  have : IsNoetherian (pullback Y.s (spMap β)) := {}
  have ha1 := stalkGen_specializes Y.X z
  have ha2 := stalkGen_generises Y.X z
  obtain ⟨u, ⟨w₀, rfl⟩, hau⟩ := exists_specializes_of_dense hd (closure_mem_irreducibleComponents ha1 ha2)
  have hjs : ∀ y : ↥(pullback Y.s (spMap β) : Scheme.{0}), Y.s (pullback.fst Y.s (spMap β) y) = (spMap β) (pullback.snd Y.s (spMap β) y) := fun y => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  let pt : Sp c.F := pullback.snd Y.s (spMap β) (Y.jQ w₀)
  have hpt : ∀ x : Sp c.F, x = pt := fun x => Subsingleton.elim (α := PrimeSpectrum c.F) x pt
  have hP : ∀ w, Y.s (Y.j w) = (spMap β) pt := fun w => by
    have : Y.j w = pullback.fst Y.s (spMap β) (Y.jQ w) := by
      show (Y.jQ ≫ pullback.fst _ _) w = _
      rw [Scheme.Hom.comp_apply]
    rw [this, hjs, hpt (pullback.snd Y.s (spMap β) (Y.jQ w))]
  have hs : ∀ x, (spMap β) pt ⤳ Y.s x := fun x => by
    have h1 : Y.s x ∈ closure {(spMap β) pt} :=
      map_mem_closure Y.s.continuous (hd x) (by rintro _ ⟨w, rfl⟩; exact hP w)
    exact specializes_iff_mem_closure.mpr h1
  have hsa : Y.s (stalkGen Y.X z) = (spMap β) pt := by
    have h1 := hau.map Y.s.continuous
    rw [hP] at h1
    exact (h1.antisymm (hs _)).eq
  obtain ⟨y, hy1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Y.s) (g := spMap β) _ pt hsa
  have hC : IsIrreducible (irreducibleComponent y) := isIrreducible_irreducibleComponent
  have hgC : closure {hC.genericPoint} = irreducibleComponent y :=
    hC.isGenericPoint_genericPoint_closure.trans isClosed_irreducibleComponent.closure_eq
  have hgy : hC.genericPoint ⤳ y := specializes_iff_mem_closure.mpr (by rw [hgC]; exact mem_irreducibleComponent)
  have hfg := hgy.map (pullback.fst Y.s (spMap β)).continuous
  rw [hy1] at hfg
  have hfe : pullback.fst Y.s (spMap β) hC.genericPoint = stalkGen Y.X z :=
    (hfg.antisymm (ha2 _ (hfg.trans ha1))).eq
  obtain ⟨_, ⟨w, rfl⟩, hgu⟩ := exists_specializes_of_dense Y.jQ_dense
    (by rw [hgC]; exact irreducibleComponent_mem_irreducibleComponents y)
  have := Y.jQ_open
  obtain ⟨w', hw'⟩ := hgu.mem_open Y.jQ.isOpenEmbedding.isOpen_range ⟨w, rfl⟩
  refine ⟨w', ?_⟩
  show (Y.jQ ≫ pullback.fst _ _) w' = _
  rw [Scheme.Hom.comp_apply, hw', hfe]

/- English proof (translation)
Set `f : CommRingCat.of c.F ⟶ (Xo.XF c).presheaf.stalk w` to `Spec.preimage ((Xo.XF c).fromSpecStalk w ≫ pullback.snd _ _)`. Establish `: CharZero ((Xo.XF c).presheaf.stalk w)` using `charZero_of_injective_ringHom f.hom.injective`. Conclude with `RingHom.charZero ((Y.j.stalkMap w).hom.comp (Y.X.presheaf.stalkSpecializes h).hom)`.
-/
theorem charZero_stalk (Y : Model Xo c β) (z : Y.X) (w : Xo.XF c) (h : Y.j w ⤳ z) :
    CharZero (Y.X.presheaf.stalk z) := by
  let f : CommRingCat.of c.F ⟶ (Xo.XF c).presheaf.stalk w :=
    Spec.preimage ((Xo.XF c).fromSpecStalk w ≫ pullback.snd _ _)
  have : CharZero ((Xo.XF c).presheaf.stalk w) := charZero_of_injective_ringHom f.hom.injective
  exact RingHom.charZero ((Y.j.stalkMap w).hom.comp (Y.X.presheaf.stalkSpecializes h).hom)

end Model

open IsLocalRing in

/- English proof (translation)
Take `⟨V, hV, hA1, hA2⟩` from `GroundTheory.Heights₂.Heights.Model.DominatingDVR.full A hA (FractionRing A)`. Use `haveI := hV`. Set `g₀ : A →+* V` to `(algebraMap A (FractionRing A)).codRestrict V hA1`. Establish `hg₀ : Function.Injective g₀` using `fun a b h => IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h)`. Use `haveI : IsLocalHom g₀ := ⟨fun a ha => by`.

Assume the negation of the conclusion as `hu`. Conclude with `(hA2 a).mpr hu ha⟩`. Set `_ : Algebra (ResidueField A) (ResidueField V)` to `(ResidueField.map g₀).toAlgebra`. Set `Ω` to `AlgebraicClosure (ResidueField V)`. Set `σ : k →ₐ[ResidueField A] Ω` to `IsAlgClosed.lift`.

Set `bs` to `Module.finBasis (ResidueField A) k`. Set `k'` to `IntermediateField.adjoin (ResidueField V) (Set.range fun i => σ (bs i))`. Use `haveI : FiniteDimensional (ResidueField V) k' := IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)`. Establish `hmem : ∀ x : k, σ x ∈ k'` using `fun x => by`. Rewrite using `[← bs.sum_repr x, map_sum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply (ResidueField A) (ResidueField V) Ω]`. Conclude with `mul_mem (k'.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)`. Take `⟨R, iR, iD, iV, f, iL, s, hc, hf, hs⟩` from `GlobalTheory.T.complete_dvr_dominating_valuation V k'`. Use `⟨R, iR, iD, iV, f.comp g₀, inferInstance, s.comp (σ.toRingHom.codRestrict k'.toSubring hmem), hc, hf.comp hg₀, ?_⟩` and prove the remaining obligations.

Establish `e₁ : (σ.toRingHom.codRestrict k'.toSubring hmem).comp (algebraMap (ResidueField A) k) = (algebraMap (ResidueField V) k').comp (ResidueField.map g₀)`. Use extensionality with `x`. Conclude with `σ.commutes x`. Rewrite using `[RingHom.comp_assoc, e₁, ← RingHom.comp_assoc, hs, ResidueField.map_comp]`.
-/
theorem exists_complete_dvr (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (hA : ¬ IsField A)
    (k : Type) [Field k] [Algebra (ResidueField A) k] [FiniteDimensional (ResidueField A) k] :
    ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R) (g : A →+* R) (_ : IsLocalHom g)
      (s : k →+* ResidueField R), IsAdicComplete (maximalIdeal R) R ∧ Function.Injective g ∧
        s.comp (algebraMap _ k) = ResidueField.map g := by
  obtain ⟨V, hV, hA1, hA2⟩ := GroundTheory.Heights₂.Heights.Model.DominatingDVR.full A hA (FractionRing A)
  haveI := hV
  let g₀ : A →+* V := (algebraMap A (FractionRing A)).codRestrict V hA1
  have hg₀ : Function.Injective g₀ := fun a b h =>
    IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h)
  haveI : IsLocalHom g₀ := ⟨fun a ha => by
    by_contra hu
    exact (hA2 a).mpr hu ha⟩
  let _ : Algebra (ResidueField A) (ResidueField V) := (ResidueField.map g₀).toAlgebra
  let Ω := AlgebraicClosure (ResidueField V)
  let σ : k →ₐ[ResidueField A] Ω := IsAlgClosed.lift
  let bs := Module.finBasis (ResidueField A) k
  let k' := IntermediateField.adjoin (ResidueField V) (Set.range fun i => σ (bs i))
  haveI : FiniteDimensional (ResidueField V) k' :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  have hmem : ∀ x : k, σ x ∈ k' := fun x => by
    rw [← bs.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply (ResidueField A) (ResidueField V) Ω]
    exact mul_mem (k'.algebraMap_mem _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  obtain ⟨R, iR, iD, iV, f, iL, s, hc, hf, hs⟩ := GlobalTheory.T.complete_dvr_dominating_valuation V k'
  refine ⟨R, iR, iD, iV, f.comp g₀, inferInstance, s.comp (σ.toRingHom.codRestrict k'.toSubring hmem), hc,
    hf.comp hg₀, ?_⟩
  have e₁ : (σ.toRingHom.codRestrict k'.toSubring hmem).comp (algebraMap (ResidueField A) k) =
      (algebraMap (ResidueField V) k').comp (ResidueField.map g₀) := by
    ext x
    exact σ.commutes x
  rw [RingHom.comp_assoc, e₁, ← RingHom.comp_assoc, hs, ResidueField.map_comp]

open IsLocalRing in

/- English proof (translation)
Establish `e : (s.comp (algebraMap (X.residueField z) k)).comp (residue (X.presheaf.stalk z)) = (residue R).comp g`. Rewrite using `[hs]`. Both sides reduce to the same expression. Establish `a₁ : spMap s ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField z) k)) ≫ spMap (residue (X.presheaf.stalk z)) = spMap (residue R) ≫ spMap g`. Simplify using `only [← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Conclude with `congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) e`. Use `show _ ≫ _ ≫ (spMap (residue (X.presheaf.stalk z)) ≫ X.fromSpecStalk z) = _`. Rewrite using `[← Category.assoc (spMap (residue R)), ← a₁]`. Simplify using `only [Category.assoc]`. Both sides reduce to the same expression.
-/
theorem key_sq (X : Scheme.{0}) (z : X) (k R : Type) [Field k] [Algebra (X.residueField z) k] [CommRing R]
    [IsLocalRing R] (g : X.presheaf.stalk z →+* R) [IsLocalHom g] (s : k →+* ResidueField R)
    (hs : s.comp (algebraMap (X.residueField z) k) = ResidueField.map g) :
    spMap s ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField z) k)) ≫ X.fromSpecResidueField z =
      spMap (residue R) ≫ spMap g ≫ X.fromSpecStalk z := by
  have e : (s.comp (algebraMap (X.residueField z) k)).comp
      (residue (X.presheaf.stalk z)) = (residue R).comp g := by
    rw [hs]; rfl
  have a₁ : spMap s ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField z) k)) ≫
      spMap (residue (X.presheaf.stalk z)) = spMap (residue R) ≫ spMap g := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) e
  show _ ≫ _ ≫ (spMap (residue (X.presheaf.stalk z)) ≫ X.fromSpecStalk z) = _
  rw [← Category.assoc (spMap (residue R)), ← a₁]
  simp only [Category.assoc]
  rfl

/- English proof (translation)
The claim follows from `IsLocalRing.comap_closedPoint f`.
-/
theorem spMap_closedPoint {R S : Type} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (f : R →+* S)
    [IsLocalHom f] : spMap f (IsLocalRing.closedPoint S) = IsLocalRing.closedPoint R :=
  IsLocalRing.comap_closedPoint f

/- English proof (translation)
Substitute `h₁ h₂` using the available equality. Conclude with `Scheme.Hom.comp_apply f g x`.
-/
theorem pt_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) {x : X} {y : Y} {w : Z} (h₁ : f x = y)
    (h₂ : g y = w) : (f ≫ g) x = w := by
  subst h₁ h₂
  exact Scheme.Hom.comp_apply f g x

open IsLocalRing in

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ _ β Y hd hS h3 p hp z hz`. Take `⟨hdom, hic⟩` from `Y.normal z`. Use `haveI := hdom`. Take `⟨w, hw⟩` from `stalkGen_mem_range Y hd z`. Establish `hwz : Y.j w ⤳ z` using `hw ▸ stalkGen_specializes Y.X z`.

Use `haveI : CharZero (Y.X.presheaf.stalk z) := charZero_stalk Y z w hwz`. Establish `hprop : IsProper Y.s`. Take `⟨N, i, hi, e⟩` from `Y.proj`. Use `isProper_str O N` as an intermediate fact. Rewrite using `[← e]`.

Use `infer_instance`. Use `haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s`. Establish `hnf : ¬ IsField (Y.X.presheaf.stalk z)` using `fun hf => by`. Establish `hp0 : (p : Y.X.presheaf.stalk z) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Take `⟨b, hb⟩` from `hf.mul_inv_cancel hp0`.

Establish `hu : IsUnit (p : Y.X.presheaf.stalk z)` using `IsUnit.of_mul_eq_one _ hb`. Establish `hm : residue (Y.X.presheaf.stalk z) (p : Y.X.presheaf.stalk z) = 0`. Rewrite using `[map_natCast]`. Conclude with `hz`. Conclude with `((residue_eq_zero_iff _).mp hm) hu`.

Take `⟨k, ik, ia, hfin, -, S, hGt⟩` from `hS z`. Use `letI : Algebra (ResidueField (Y.X.presheaf.stalk z)) k := ia`. Use `haveI : FiniteDimensional (ResidueField (Y.X.presheaf.stalk z)) k := hfin`. Take `⟨R, iR, iD, iV, g, iL, s, hc, hg, hs⟩` from `exists_complete_dvr (Y.X.presheaf.stalk z) hnf k`. Set `ξ : Sp R ⟶ Y.X` to `spMap g ≫ Y.X.fromSpecStalk z`.

Use `haveI : CharZero R := charZero_of_injective_ringHom hg`. Take `⟨PP', cub, sym, adj, prim, m, -⟩` from `sabPull Out.proved_CubePullSt ξ Y.t`. Set `t : SAB H (Sp R)` to `⟨(Over.pullback ξ).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi, OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩`. Set `m' : SABMap t Y.t ξ` to `m`. Establish `habs : (ξ ⁻¹' abLocus Y.t.G).Nonempty`.

Set `pt₀ : Sp R` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)`. Use `⟨pt₀, ?_⟩` and prove the remaining obligations. Establish `h1 : ξ pt₀ = stalkGen Y.X z` using `pt_comp (spMap g) (Y.X.fromSpecStalk z) (y := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Y.X.presheaf.stalk z))) (PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)) rfl`. Establish `h2 : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G`. Rewrite using `[Y.ab_gen]`.

Conclude with `⟨_, rfl⟩`. Establish `h4 : Y.j w = pullback.fst Y.s (spMap β) (Y.jQ w)` using `by show (Y.jQ ≫ pullback.fst _ _) w = _`. Rewrite using `[Scheme.Hom.comp_apply]`. Use `show ξ pt₀ ∈ abLocus Y.t.G`. Rewrite using `[h1, ← hw, h4]`.

Conclude with `h2`. Establish `key : spMap s ≫ Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField z) k)) ≫ Y.X.fromSpecResidueField z = spMap (residue R) ≫ ξ` using `key_sq Y.X z k R g s hs`. Take `⟨S', -, -, -, -, hGt'⟩` from `Out.GtBCPf.gtBaseChange _ _ (spMap s) S _ hGt`. Establish `hsplit : ∃ S : SplitExt (Sp (ResidueField R)), S.IsGt ((Over.pullback (spMap (residue R))).obj t.G)`. Use `⟨S', ?_⟩` and prove the remaining obligations.

Establish `: IsMonHom (pullCompIso (spMap s) (Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField z) k)) ≫ Y.X.fromSpecResidueField z) Y.t.G).symm.hom` using `by show IsMonHom (pullCompIso _ _ _).inv infer_instance`. Establish `h₀` using `isGt_of_iso (pullCompIso (spMap s) _ Y.t.G).symm hGt'`. Rewrite `h₀` using `[key]`. Conclude with `isGt_of_iso (pullCompIso (spMap (residue R)) ξ Y.t.G) h₀`. Take `⟨P, -, -⟩` from `h3 R inferInstance inferInstance hc ξ t m' habs hsplit`.

Establish `g₁` using `GlobalTheory.T.pel_uniformised_geometric_free E H R t P`. Take `⟨hb₁, hb₂⟩` from `GlobalTheory.T.geometric_power_free_functorial E H Y.X Y.t`. Establish `g₂` using `(hb₂ (Sp R) t ξ m' (ResidueField R) (spMap (residue R))).mp g₁`. Establish `g₃` using `hb₁ _ (AlgebraicClosure (ResidueField R)) (algebraMap _ _) _ g₂`. Use `⟨AlgebraicClosure (ResidueField R), inferInstance, inferInstance, _, ?_, g₃⟩` and prove the remaining obligations.

Conclude with `pt_comp _ _ (spMap_closedPoint _) (pt_comp _ _ (spMap_closedPoint _) (pt_comp _ _ (spMap_closedPoint g) Scheme.fromSpecStalk_closedPoint))`.
-/
theorem model_fibPF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), Dense (Set.range Y.j) → Y.SplitFibres → Y.N3 → ∀ (p : ℕ), p.Prime → ∀ z : Y.X, (p : Y.X.residueField z) = 0 → FibPF Y.t z := by
  intro E _ _ _ H D l Xo c O _ _ β Y hd hS h3 p hp z hz
  obtain ⟨hdom, hic⟩ := Y.normal z
  haveI := hdom
  obtain ⟨w, hw⟩ := stalkGen_mem_range Y hd z
  have hwz : Y.j w ⤳ z := hw ▸ stalkGen_specializes Y.X z
  haveI : CharZero (Y.X.presheaf.stalk z) := charZero_stalk Y z w hwz
  have hprop : IsProper Y.s := by
    obtain ⟨N, i, hi, e⟩ := Y.proj
    have := isProper_str O N
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have hnf : ¬ IsField (Y.X.presheaf.stalk z) := fun hf => by
    have hp0 : (p : Y.X.presheaf.stalk z) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel hp0
    have hu : IsUnit (p : Y.X.presheaf.stalk z) := IsUnit.of_mul_eq_one _ hb
    have hm : residue (Y.X.presheaf.stalk z) (p : Y.X.presheaf.stalk z) = 0 := by
      rw [map_natCast]; exact hz
    exact ((residue_eq_zero_iff _).mp hm) hu
  obtain ⟨k, ik, ia, hfin, -, S, hGt⟩ := hS z
  letI : Algebra (ResidueField (Y.X.presheaf.stalk z)) k := ia
  haveI : FiniteDimensional (ResidueField (Y.X.presheaf.stalk z)) k := hfin
  obtain ⟨R, iR, iD, iV, g, iL, s, hc, hg, hs⟩ := exists_complete_dvr (Y.X.presheaf.stalk z) hnf k
  let ξ : Sp R ⟶ Y.X := spMap g ≫ Y.X.fromSpecStalk z
  haveI : CharZero R := charZero_of_injective_ringHom hg
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt ξ Y.t
  let t : SAB H (Sp R) := ⟨(Over.pullback ξ).obj Y.t.G, IsSemiAbelian.pullback _ Y.t.G Y.t.semi,
    OAct.pullback _ Y.t.G Y.t.act, PP', cub, sym, adj, prim⟩
  let m' : SABMap t Y.t ξ := m
  have habs : (ξ ⁻¹' abLocus Y.t.G).Nonempty := by
    let pt₀ : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
    refine ⟨pt₀, ?_⟩
    have h1 : ξ pt₀ = stalkGen Y.X z :=
      pt_comp (spMap g) (Y.X.fromSpecStalk z) (y := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Y.X.presheaf.stalk z)))
        (PrimeSpectrum.ext (Ideal.comap_bot_of_injective g hg)) rfl
    have h2 : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨_, rfl⟩
    have h4 : Y.j w = pullback.fst Y.s (spMap β) (Y.jQ w) := by
      show (Y.jQ ≫ pullback.fst _ _) w = _
      rw [Scheme.Hom.comp_apply]
    show ξ pt₀ ∈ abLocus Y.t.G
    rw [h1, ← hw, h4]
    exact h2
  have key : spMap s ≫ Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField z) k)) ≫
      Y.X.fromSpecResidueField z = spMap (residue R) ≫ ξ := key_sq Y.X z k R g s hs
  obtain ⟨S', -, -, -, -, hGt'⟩ := Out.GtBCPf.gtBaseChange _ _ (spMap s) S _ hGt
  have hsplit : ∃ S : SplitExt (Sp (ResidueField R)),
      S.IsGt ((Over.pullback (spMap (residue R))).obj t.G) := by
    refine ⟨S', ?_⟩
    have : IsMonHom (pullCompIso (spMap s) (Spec.map (CommRingCat.ofHom (algebraMap (Y.X.residueField z) k)) ≫
        Y.X.fromSpecResidueField z) Y.t.G).symm.hom := by
      show IsMonHom (pullCompIso _ _ _).inv
      infer_instance
    have h₀ := isGt_of_iso (pullCompIso (spMap s) _ Y.t.G).symm hGt'
    rw [key] at h₀
    exact isGt_of_iso (pullCompIso (spMap (residue R)) ξ Y.t.G) h₀
  obtain ⟨P, -, -⟩ := h3 R inferInstance inferInstance hc ξ t m' habs hsplit
  have g₁ := GlobalTheory.T.pel_uniformised_geometric_free E H R t P
  obtain ⟨hb₁, hb₂⟩ := GlobalTheory.T.geometric_power_free_functorial E H Y.X Y.t
  have g₂ := (hb₂ (Sp R) t ξ m' (ResidueField R) (spMap (residue R))).mp g₁
  have g₃ := hb₁ _ (AlgebraicClosure (ResidueField R)) (algebraMap _ _) _ g₂
  refine ⟨AlgebraicClosure (ResidueField R), inferInstance, inferInstance, _, ?_, g₃⟩
  exact pt_comp _ _ (spMap_closedPoint _) (pt_comp _ _ (spMap_closedPoint _) (pt_comp _ _ (spMap_closedPoint g)
    Scheme.fromSpecStalk_closedPoint))

end GlobalTheory.CompanionTheory.Ar.ModelFib
