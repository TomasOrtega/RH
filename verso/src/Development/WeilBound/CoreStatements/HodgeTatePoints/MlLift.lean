import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenOfFibreId
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfApplyEqGenericPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Ml

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

/- English proof (translation)
Use `Spec.map_injective h` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

/- English proof (translation)
Establish `hz : z.asIdeal = ⊥` using `Ideal.eq_bot_of_prime _ (h := z.2)`. Use `show Ideal.comap δ z.asIdeal = _`. Rewrite using `[hz]`. Both sides reduce to the same expression.
-/
theorem spMap_field_pt {R K : Type} [CommRing R] [Field K] (δ : R →+* K) (z : Sp K) :
    (spMap δ z).asIdeal = RingHom.ker δ := by
  have hz : z.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := z.2)
  show Ideal.comap δ z.asIdeal = _
  rw [hz]; rfl

/- English proof (translation)
Use `letI := β.toAlgebra`. Use `haveI := h`. Conclude with `IsPreimmersion.of_isLocalization (nonZeroDivisors O)`.
-/
theorem preimm_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) : IsPreimmersion (spMap β) := by
  letI := β.toAlgebra
  haveI := h
  exact IsPreimmersion.of_isLocalization (nonZeroDivisors O)

/- English proof (translation)
Use `haveI : IsPreimmersion (spMap β) := preimm_frac β h`. Take `⟨⟨p, a⟩, rfl⟩` from `(X.SpecToEquivOfField K).symm.surjective x`. Establish `hp : p ∈ Set.range (pullback.fst s (spMap β))`. Apply `hx` to reduce the goal to its premises. Conclude with `⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply p _⟩`.

Take `⟨q, rfl⟩` from `hp`. Establish `hsurj : Function.Surjective (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q)`. Establish `h1 : Function.Surjective (Scheme.Hom.stalkMap (pullback.fst s (spMap β)) q ≫ (pullback s (spMap β)).residue q)` using `((pullback s (spMap β)).residue_surjective q).comp (Scheme.Hom.stalkMap_surjective (pullback.fst s (spMap β)) q)`. Rewrite `h1` using `[← Scheme.residue_residueFieldMap]`. Introduce `b`.

Take `⟨c, hc⟩` from `h1 b`. Conclude with `⟨X.residue _ c, hc⟩`. Use `haveI : IsIso (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by`. Rewrite using `[ConcreteCategory.isIso_iff_bijective]`. Conclude with `⟨(Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q).hom.injective, hsurj⟩`.

Use `⟨Spec.map (inv (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) ≫ a) ≫ (pullback s (spMap β)).fromSpecResidueField q, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp]`. Simplify using `[Scheme.SpecToEquivOfField]`.
-/
theorem lift_frac {O F : Type} [CommRing O] [Field F] (β : O →+* F)
    (h : letI := β.toAlgebra; IsFractionRing O F) {X : Scheme.{0}} (s : X ⟶ Sp O) {K : Type} [Field K]
    (x : Sp K ⟶ X) (hx : Set.range x ⊆ Set.range (pullback.fst s (spMap β))) :
    ∃ y : Sp K ⟶ pullback s (spMap β), y ≫ pullback.fst _ _ = x := by
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  obtain ⟨⟨p, a⟩, rfl⟩ := (X.SpecToEquivOfField K).symm.surjective x
  have hp : p ∈ Set.range (pullback.fst s (spMap β)) := by
    apply hx
    exact ⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply p _⟩
  obtain ⟨q, rfl⟩ := hp
  have hsurj : Function.Surjective (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    have h1 : Function.Surjective
        (Scheme.Hom.stalkMap (pullback.fst s (spMap β)) q ≫ (pullback s (spMap β)).residue q) :=
      ((pullback s (spMap β)).residue_surjective q).comp
        (Scheme.Hom.stalkMap_surjective (pullback.fst s (spMap β)) q)
    rw [← Scheme.residue_residueFieldMap] at h1
    intro b
    obtain ⟨c, hc⟩ := h1 b
    exact ⟨X.residue _ c, hc⟩
  haveI : IsIso (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨(Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q).hom.injective, hsurj⟩
  refine ⟨Spec.map (inv (Scheme.Hom.residueFieldMap (pullback.fst s (spMap β)) q) ≫ a) ≫
    (pullback s (spMap β)).fromSpecResidueField q, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp]
  simp [Scheme.SpecToEquivOfField]

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y h K _ x hx`. Use `haveI : IsPreimmersion (spMap β) := preimm_frac β h`. Use `haveI := Y.jQ_open`. Establish `hx' : Set.range x ⊆ Set.range (pullback.fst Y.s (spMap β))`. Use `hx.trans ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `⟨Y.jQ w, by simp [Model.j]⟩`. Take `⟨y1, hy1⟩` from `lift_frac β h Y.s x hx'`. Establish `hr : Set.range y1 ⊆ Set.range Y.jQ`. Introduce and unpack `_ ⟨z, rfl⟩`.

Take `⟨w, hw⟩` from `hx ⟨z, rfl⟩`. Use `⟨w, (pullback.fst Y.s (spMap β)).isEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[← hy1]`. Simplify `hw` using `[Model.j]`. Use `⟨IsOpenImmersion.lift Y.jQ y1 hr, ?_⟩` and prove the remaining obligations.

Simplify using `[Model.j, hy1]`.
-/
theorem lift_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  intro E _ _ _ H D l Xo c O _ β Y h K _ x hx
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  haveI := Y.jQ_open
  have hx' : Set.range x ⊆ Set.range (pullback.fst Y.s (spMap β)) := by
    refine hx.trans ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨Y.jQ w, by simp [Model.j]⟩
  obtain ⟨y1, hy1⟩ := lift_frac β h Y.s x hx'
  have hr : Set.range y1 ⊆ Set.range Y.jQ := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨w, hw⟩ := hx ⟨z, rfl⟩
    refine ⟨w, (pullback.fst Y.s (spMap β)).isEmbedding.injective ?_⟩
    rw [← hy1] at hw
    simpa [Model.j] using hw
  refine ⟨IsOpenImmersion.lift Y.jQ y1 hr, ?_⟩
  simp [Model.j, hy1]

/- English proof (translation)
Establish `h1 : closure {v} ⊆ closure {v'}` using `specializes_iff_closure_subset.1 hs`. Establish `h2 : closure {v'} ⊆ closure {v}` using `h.2 isIrreducible_singleton.closure h1`. Conclude with `(hs.antisymm (specializes_iff_closure_subset.2 h2)).eq`.
-/
theorem generic_max {X : Type} [TopologicalSpace X] [T0Space X] {v v' : X} (h : v ∈ genericPoints X)
    (hs : v' ⤳ v) : v' = v := by
  have h1 : closure {v} ⊆ closure {v'} := specializes_iff_closure_subset.1 hs
  have h2 : closure {v'} ⊆ closure {v} := h.2 isIrreducible_singleton.closure h1
  exact (hs.antisymm (specializes_iff_closure_subset.2 h2)).eq

/- English proof (translation)
Establish `hC` using `irreducibleComponent_mem_irreducibleComponents z`. Take `⟨o, hoo, ⟨u, hu⟩, hoC⟩` from `TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC`. Take `⟨w, hwo, hwU⟩` from `hd.inter_open_nonempty o hoo ⟨u, hu⟩`. Establish `hg` using `hC.1.isGenericPoint_genericPoint_closure`. Rewrite `hg` using `[(isClosed_of_mem_irreducibleComponents _ hC).closure_eq]`.

Establish `hgz : hC.1.genericPoint = z` using `hz _ (hg.specializes mem_irreducibleComponent)`. Establish `hzw : z ⤳ w` using `hgz ▸ hg.specializes (hoC hwo)`. Conclude with `hzw.mem_open ho hwU`.
-/
theorem mem_of_dense_of_max {X : Type} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    {U : Set X} (ho : IsOpen U) (hd : Dense U) {z : X} (hz : ∀ z', z' ⤳ z → z' = z) : z ∈ U := by
  have hC := irreducibleComponent_mem_irreducibleComponents z
  obtain ⟨o, hoo, ⟨u, hu⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hC
  obtain ⟨w, hwo, hwU⟩ := hd.inter_open_nonempty o hoo ⟨u, hu⟩
  have hg := hC.1.isGenericPoint_genericPoint_closure
  rw [(isClosed_of_mem_irreducibleComponents _ hC).closure_eq] at hg
  have hgz : hC.1.genericPoint = z := hz _ (hg.specializes mem_irreducibleComponent)
  have hzw : z ⤳ w := hgz ▸ hg.specializes (hoC hwo)
  exact hzw.mem_open ho hwU

/- English proof (translation)
Take `⟨N, i, hi, hs⟩` from `hp`. Use `haveI := hi`. Use `haveI : Algebra.FiniteType ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0) (MvPolynomial (Fin (N + 1)) O) := haveI : IsScalarTower O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0) (MvPolynomial (Fin (N + 1)) O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl) Alg …`. Establish `hsurj : Function.Surjective (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0))`. Introduce and unpack `⟨p, hp⟩`.

Establish `h0 : p.totalDegree = 0` using `(MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p)).mpr ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)`. Use `⟨p.coeff 0, Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `(MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0).symm`. Use `haveI : LocallyOfFiniteType (spMap (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0))) := by`. Rewrite using `[spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]`.

Conclude with `RingHom.FiniteType.of_surjective _ hsurj`. Use `haveI : LocallyOfFiniteType (PSpace.str O N) := by`. Unfold `PSpace.str`. Use `infer_instance`. Use `haveI : QuasiCompact (PSpace.str O N) := by`.

Unfold `PSpace.str`. Use `infer_instance`. Use `haveI : LocallyOfFiniteType s := by`. Rewrite using `[← hs]`. Use `infer_instance`.

Use `haveI : QuasiCompact s := by`. Rewrite using `[← hs]`. Use `infer_instance`. Use `haveI : IsLocallyNoetherian (pullback s (spMap β)) := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))`. Use `haveI : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))`.

Use `haveI : IsNoetherian (pullback s (spMap β)) := {}`. Use `infer_instance`.
-/
private theorem isLocallyNoetherian_of_closedImmersion_pSpace (O F : Type) [CommRing O] [Field F] (β : O →+* F) (X : Scheme.{0}) (s : X ⟶ Sp O)
    (hp : IsProjOver s) : TopologicalSpace.NoetherianSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) := by
  obtain ⟨N, i, hi, hs⟩ := hp
  haveI := hi
  haveI : Algebra.FiniteType ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
      (MvPolynomial (Fin (N + 1)) O) :=
    haveI : IsScalarTower O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)
        (MvPolynomial (Fin (N + 1)) O) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    Algebra.FiniteType.of_restrictScalars_finiteType O _ _
  have hsurj : Function.Surjective
      (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0)) := by
    rintro ⟨p, hp⟩
    have h0 : p.totalDegree = 0 := (MvPolynomial.totalDegree_zero_iff_isHomogeneous (p := p)).mpr
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp)
    refine ⟨p.coeff 0, Subtype.ext ?_⟩
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0).symm
  haveI : LocallyOfFiniteType (spMap (algebraMap O ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) O) 0))) := by
    rw [spMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ hsurj
  haveI : LocallyOfFiniteType (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : QuasiCompact (PSpace.str O N) := by
    unfold PSpace.str
    infer_instance
  haveI : LocallyOfFiniteType s := by
    rw [← hs]
    infer_instance
  haveI : QuasiCompact s := by
    rw [← hs]
    infer_instance
  haveI : IsLocallyNoetherian (pullback s (spMap β)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap β))
  haveI : CompactSpace ↥(pullback (C := Scheme.{0}) s (spMap β)) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd s (spMap β))
  haveI : IsNoetherian (pullback s (spMap β)) := {}
  infer_instance

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y hO h v hv`. Use `haveI : IsPreimmersion (spMap β) := preimm_frac β h`. Use `haveI := Y.flat`. Use `haveI := Y.jQ_open`. Use `haveI := isLocallyNoetherian_of_closedImmersion_pSpace O c.F β Y.X Y.s Y.proj`.

Establish `hβ : Function.Injective β`. Use `letI := β.toAlgebra`. Conclude with `IsFractionRing.injective O c.F`. Set `z0 : Sp c.F` to `IsLocalRing.closedPoint c.F`. Establish `hgen : (spMap β z0).asIdeal = ⊥`.

Rewrite using `[spMap_field_pt]`. Conclude with `(RingHom.injective_iff_ker_eq_bot β).mp hβ`. Establish `hle : (spMap β z0).asIdeal ≤ (Y.s v).asIdeal`. Rewrite using `[hgen]`. Conclude with `bot_le`.

Establish `hspec : spMap β z0 ⤳ Y.s v` using `(PrimeSpectrum.le_iff_specializes _ _).mp hle`. Take `⟨v', hv'v, hv'⟩` from `Flat.generalizingMap Y.s hspec`. Rewrite `hv'` using `[generic_max hv hv'v]`. Take `⟨q, hq, -⟩` from `Scheme.Pullback.exists_preimage_pullback v z0 hv'`. Establish `hqmax : ∀ q', q' ⤳ q → q' = q`.

Introduce `q' hq'`. Apply `(pullback.fst Y.s (spMap β)).isEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hq]`. Conclude with `generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)`. Take `⟨w, hw⟩` from `mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite using `[← hq, ← hw]`. Simplify using `[Model.j]`.
-/
theorem generic_points_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO h v hv
  haveI : IsPreimmersion (spMap β) := preimm_frac β h
  haveI := Y.flat
  haveI := Y.jQ_open
  haveI := isLocallyNoetherian_of_closedImmersion_pSpace O c.F β Y.X Y.s Y.proj
  have hβ : Function.Injective β := by
    letI := β.toAlgebra
    exact IsFractionRing.injective O c.F
  let z0 : Sp c.F := IsLocalRing.closedPoint c.F
  have hgen : (spMap β z0).asIdeal = ⊥ := by
    rw [spMap_field_pt]
    exact (RingHom.injective_iff_ker_eq_bot β).mp hβ
  have hle : (spMap β z0).asIdeal ≤ (Y.s v).asIdeal := by
    rw [hgen]
    exact bot_le
  have hspec : spMap β z0 ⤳ Y.s v := (PrimeSpectrum.le_iff_specializes _ _).mp hle
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback v z0 hv'
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  refine ⟨w, ?_⟩
  rw [← hq, ← hw]
  simp [Model.j]

end PositivityTheory.HtPt.Ml
