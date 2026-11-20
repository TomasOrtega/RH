import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

/- English proof (translation)
Establish `sq : IsPullback a h' h b` using `IsPullback.of_bot hH w hX`. Take `⟨t, ht⟩` from `hx`. Take `⟨z, hz, -⟩` from `Scheme.exists_preimage_of_isPullback hX (h x) t ht.symm`. Take `⟨x', rfl, hx'⟩` from `Scheme.exists_preimage_of_isPullback sq x z hz.symm`. Take `⟨y', rfl, hy'⟩` from `Scheme.exists_preimage_of_isPullback sq y z (hxy.symm.trans hz.symm)`.

Rewrite using `[hinj (hx'.trans hy'.symm)]`.
-/
theorem eq_of_injective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') (h ≫ s) q) (w : a ≫ h = h' ≫ b)
    (hinj : Function.Injective h') {x y : H} (hxy : h x = h y) (hx : s (h x) ∈ Set.range q) : x = y := by
  have sq : IsPullback a h' h b := IsPullback.of_bot hH w hX
  obtain ⟨t, ht⟩ := hx
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hX (h x) t ht.symm
  obtain ⟨x', rfl, hx'⟩ := Scheme.exists_preimage_of_isPullback sq x z hz.symm
  obtain ⟨y', rfl, hy'⟩ := Scheme.exists_preimage_of_isPullback sq y z (hxy.symm.trans hz.symm)
  rw [hinj (hx'.trans hy'.symm)]

/- English proof (translation)
Take `⟨t, ht⟩` from `hz`. Take `⟨z', rfl, -⟩` from `Scheme.exists_preimage_of_isPullback hX z t ht.symm`. Take `⟨x, rfl⟩` from `hsurj z'`. Conclude with `⟨a x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩`.
-/
theorem mem_range_of_surjective_baseChange {S S' H X H' X' : Scheme.{0}} {q : S' ⟶ S} {s : X ⟶ S} {h : H ⟶ X}
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (w : a ≫ h = h' ≫ b)
    (hsurj : Function.Surjective h') {z : X} (hz : s z ∈ Set.range q) : z ∈ Set.range h := by
  obtain ⟨t, ht⟩ := hz
  obtain ⟨z', rfl, -⟩ := Scheme.exists_preimage_of_isPullback hX z t ht.symm
  obtain ⟨x, rfl⟩ := hsurj z'
  exact ⟨a x, by rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]⟩

/- English proof (translation)
Establish `hJ : JacobsonSpace X` using `LocallyOfFiniteType.jacobsonSpace s`. Rewrite using `[← Set.range_eq_univ]`. Assume the negation of the conclusion as `hne`. Take `⟨x, hx, hx'⟩` from `nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne) h.isClosedEmbedding.isClosed_range.isOpen_compl.isLocallyClosed`. Take `⟨c, hc⟩` from `hs _ (pointOfClosedPoint_comp s x hx')`.

Set `a : Sp k` to `IsLocalRing.closedPoint k`. Use `hx ⟨c a, ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, hc]`. Conclude with `pointOfClosedPoint_apply s x hx' _`.
-/
theorem surjective_of_isClosedImmersion_of_points {k : Type} [Field k] [IsAlgClosed k] {H X : Scheme.{0}}
    (h : H ⟶ X) [IsClosedImmersion h] (s : X ⟶ Sp k) [LocallyOfFiniteType s]
    (hs : ∀ x : Sp k ⟶ X, x ≫ s = 𝟙 _ → ∃ c : Sp k ⟶ H, c ≫ h = x) : Function.Surjective h := by
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace s
  rw [← Set.range_eq_univ]
  by_contra hne
  obtain ⟨x, hx, hx'⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
    h.isClosedEmbedding.isClosed_range.isOpen_compl.isLocallyClosed
  obtain ⟨c, hc⟩ := hs _ (pointOfClosedPoint_comp s x hx')
  let a : Sp k := IsLocalRing.closedPoint k
  refine hx ⟨c a, ?_⟩
  rw [← Scheme.Hom.comp_apply, hc]
  exact pointOfClosedPoint_apply s x hx' _

/- English proof (translation)
Distinguish the cases in `hx : PrimeSpectrum.asIdeal x = ⊥`. Use `Or.inr ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Conclude with `(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)`. Use `Or.inl (PrimeSpectrum.ext ?_)` and prove the remaining obligations.

Conclude with `IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime x).isMaximal hx)`.
-/
theorem eq_closedPoint_or_mem_range (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (x : Sp T) :
    x = IsLocalRing.closedPoint T ∨ x ∈ Set.range (spMap (algebraMap T K)) := by
  by_cases hx : PrimeSpectrum.asIdeal x = ⊥
  · refine Or.inr ⟨(⊥ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [hx]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective T K)
  · refine Or.inl (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal ((PrimeSpectrum.isPrime x).isMaximal hx)

/- English proof (translation)
Substitute `hu` using the available equality. Set `t` to `spMap (algebraMap T K)`. Establish `: IsOpenImmersion t` using `isOpenImmersion_spMap_of_isDiscreteValuationRing T K`. Establish `: ConnectedSpace ↥(pullback s t)` using `hK.isoPullback.hom.surjective.connectedSpace hK.isoPullback.hom.continuous`. Take `⟨hXi, hN⟩` from `isIntegral_and_isNormalScheme_of_smooth T K s`.

Take `⟨hHi, -⟩` from `isIntegral_and_isNormalScheme_of_smooth T K (h ≫ s)`. Establish `: IsSeparated h` using `IsSeparated.of_comp h s`. Establish `: QuasiCompact h` using `QuasiCompact.of_comp h s`. Establish `: LocallyOfFiniteType h` using `locallyOfFiniteType_of_comp h s`. Set `j` to `pullback.fst (h ≫ s) t`.

Establish `hj : IsPullback j (𝟙 _ ≫ pullback.snd (h ≫ s) t) (h ≫ s) t`. Rewrite using `[Category.id_comp]`. Conclude with `.of_hasPullback _ _`. Establish `hinj : Function.Injective h` using `fun x y hxy ↦ by`. Break down `eq_closedPoint_or_mem_range T K (s (h x)) with hx | hx` into its components or cases.

Conclude with `eq_of_injective_baseChange hX hH w hbij.1 hxy (hx ▸ hq)`. Conclude with `eq_of_injective_baseChange hK hj (Category.id_comp _).symm (fun _ _ e ↦ e) hxy hx`. Establish `hsurj : Function.Surjective h` using `fun z ↦ by`. Break down `eq_closedPoint_or_mem_range T K (s z) with hx | hx` into its components or cases. Conclude with `mem_range_of_surjective_baseChange hX w hbij.2 (hx ▸ hq)`.

Conclude with `mem_range_of_surjective_baseChange (h' := 𝟙 _) hK (Category.id_comp _).symm (fun e ↦ ⟨e, rfl⟩) hx`. Establish `: LocallyQuasiFinite h` using `LocallyQuasiFinite.of_injective hinj`. Establish `: IsOpenImmersion (j ≫ h)` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip ‹_›`. Establish `: IsOpenImmersion (j.opensRange.ι ≫ h)`. Rewrite using `[← j.isoOpensRange_inv_comp, Category.assoc]`.

Use `infer_instance`. Establish `: IsOpenImmersion h` using `isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict h (fun y ↦ (hN y).2) j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩`. Conclude with `(isIso_iff_isOpenImmersion_and_surjective h).mpr ⟨this, ⟨hsurj⟩⟩`.
-/
theorem isIso_of_genericFibre_of_specialFibre (T K : Type) [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K]
    {H X S' H' X' : Scheme.{0}} (h : H ⟶ X) (s : X ⟶ Sp T) (u : H ⟶ Sp T) (hu : h ≫ s = u)
    [Smooth s] [IsSeparated s] [Smooth u] [IsSeparated u] [QuasiCompact u]
    [ConnectedSpace ↥(pullback u (spMap (algebraMap T K)))]
    (hK : IsPullback (pullback.fst u (spMap (algebraMap T K)) ≫ h) (pullback.snd u (spMap (algebraMap T K)))
      s (spMap (algebraMap T K)))
    {q : S' ⟶ Sp T} (hq : IsLocalRing.closedPoint T ∈ Set.range q)
    {b : X' ⟶ X} {s' : X' ⟶ S'} {a : H' ⟶ H} {h' : H' ⟶ X'}
    (hX : IsPullback b s' s q) (hH : IsPullback a (h' ≫ s') u q) (w : a ≫ h = h' ≫ b)
    (hbij : Function.Bijective h') : IsIso h := by
  subst hu
  let t := spMap (algebraMap T K)
  have : IsOpenImmersion t := isOpenImmersion_spMap_of_isDiscreteValuationRing T K
  have : ConnectedSpace ↥(pullback s t) :=
    hK.isoPullback.hom.surjective.connectedSpace hK.isoPullback.hom.continuous
  obtain ⟨hXi, hN⟩ := isIntegral_and_isNormalScheme_of_smooth T K s
  obtain ⟨hHi, -⟩ := isIntegral_and_isNormalScheme_of_smooth T K (h ≫ s)
  have : IsSeparated h := IsSeparated.of_comp h s
  have : QuasiCompact h := QuasiCompact.of_comp h s
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h s
  let j := pullback.fst (h ≫ s) t
  have hj : IsPullback j (𝟙 _ ≫ pullback.snd (h ≫ s) t) (h ≫ s) t := by
    rw [Category.id_comp]; exact .of_hasPullback _ _
  have hinj : Function.Injective h := fun x y hxy ↦ by
    rcases eq_closedPoint_or_mem_range T K (s (h x)) with hx | hx
    · exact eq_of_injective_baseChange hX hH w hbij.1 hxy (hx ▸ hq)
    · exact eq_of_injective_baseChange hK hj (Category.id_comp _).symm
        (fun _ _ e ↦ e) hxy hx
  have hsurj : Function.Surjective h := fun z ↦ by
    rcases eq_closedPoint_or_mem_range T K (s z) with hx | hx
    · exact mem_range_of_surjective_baseChange hX w hbij.2 (hx ▸ hq)
    · exact mem_range_of_surjective_baseChange (h' := 𝟙 _) hK (Category.id_comp _).symm
        (fun e ↦ ⟨e, rfl⟩) hx
  have : LocallyQuasiFinite h := LocallyQuasiFinite.of_injective hinj
  have : IsOpenImmersion (j ≫ h) := MorphismProperty.of_isPullback (P := @IsOpenImmersion) hK.flip ‹_›
  have : IsOpenImmersion (j.opensRange.ι ≫ h) := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc]
    infer_instance
  have : IsOpenImmersion h :=
    isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict h (fun y ↦ (hN y).2)
      j.opensRange ⟨⟨j (Classical.arbitrary _), _, rfl⟩⟩
  exact (isIso_iff_isOpenImmersion_and_surjective h).mpr ⟨this, ⟨hsurj⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨by rw [← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _ (fun c ↦ h.lift (c.fst ≫ i) c.snd (by rw [Category.assoc, c.condition])) (fun c ↦ by rw [← cancel_mono i, Category.assoc, h.lift_fst]) (fun c ↦ h.lift_snd _ _ _) (fun c m h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, ← Category …`.
-/
theorem isPullback_of_comp_mono {𝒞 : Type*} [Category 𝒞] {A G P U Z : 𝒞} {a : A ⟶ G} {i : G ⟶ P} [Mono i]
    {s : A ⟶ U} {t : P ⟶ Z} {u : U ⟶ Z} (h : IsPullback (a ≫ i) s t u) : IsPullback a s (i ≫ t) u :=
  ⟨⟨by rw [← Category.assoc, h.w]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ h.lift (c.fst ≫ i) c.snd (by rw [Category.assoc, c.condition]))
    (fun c ↦ by rw [← cancel_mono i, Category.assoc, h.lift_fst]) (fun c ↦ h.lift_snd _ _ _)
    (fun c m h₁ h₂ ↦ h.hom_ext (by rw [h.lift_fst, ← Category.assoc, h₁]) (by rw [h.lift_snd, h₂]))⟩⟩

/- English proof (translation)
The claim follows from `GlobalTheory.NormIntegers.isAlgClosed_residueField (Valuation.valuationSubring.integers (Valued.v : Valuation (PadicAlgCl p) NNReal))`.
-/
theorem isAlgClosed_residueField_OO (p : ℕ) [Fact p.Prime] : IsAlgClosed (kb p) :=
  GlobalTheory.NormIntegers.isAlgClosed_residueField
    (Valuation.valuationSubring.integers (Valued.v : Valuation (PadicAlgCl p) NNReal))

/- English proof (translation)
Introduce `C hF hS p _ y τ`. Use `isAlgClosed_residueField_OO p` as an intermediate fact. Use `C.proper` as an intermediate fact. Use `τ.smooth` as an intermediate fact. Use `τ.sep` as an intermediate fact.

Use `τ.qc` as an intermediate fact. Use `τ.j_loc` as an intermediate fact. Establish `: Smooth C.GG.hom` using `SmoothOfRelativeDimension.smooth C.g _`. Establish `: Smooth τ.H.hom` using `SmoothOfRelativeDimension.smooth C.g _`. Establish `: IsSeparated C.GG.hom` using `inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))`.

Set `K` to `FractionRing τ.V`. Set `t : Sp K ⟶ Sp τ.V` to `spMap (algebraMap τ.V K)`. Set `q : Sp (kb p) ⟶ Sp τ.V` to `rPt p ≫ spMap τ.j`. Establish `hqy : q ≫ τ.y₀ = rPt p ≫ y` using `by rw [Category.assoc, τ.fac]`. Set `h : τ.H.left ⟶ pullback C.GG.hom τ.y₀` to `pullback.lift τ.f τ.H.hom τ.f_over`.

Establish `h₁ : h ≫ pullback.fst _ _ = τ.f` using `pullback.lift_fst _ _ _`. Establish `h₂ : h ≫ pullback.snd _ _ = τ.H.hom` using `pullback.lift_snd _ _ _`. Establish `hA : IsPullback C.a C.A.hom C.GG.hom C.U.ι` using `isPullback_of_comp_mono C.cart`. Establish `hφ : IsPullback τ.φ (pullback.snd τ.H.hom t) C.A.hom τ.yK` using `τ.φ_cart.1`. Use `C.ab.geomConnected` as an intermediate fact.

Establish `: ConnectedSpace ↥(pullback τ.H.hom t)` using `GeometricallyConnected.geometrically_connectedSpace _ _ _ hφ`. Establish `hK : IsPullback (pullback.fst τ.H.hom t ≫ h) (pullback.snd τ.H.hom t) (pullback.snd C.GG.hom τ.y₀) t`. Use `IsPullback.of_right ?_ (by rw [Category.assoc, h₂, pullback.condition]) (IsPullback.of_hasPullback C.GG.hom τ.y₀)` and prove the remaining obligations. Use `hφ.paste_horiz hA` as an intermediate fact. Rewrite `this` using `[τ.φ_f, τ.yK_fac]`.

Rewrite using `[Category.assoc, h₁]`. Conclude with `this`. Set `h' : pullback τ.H.hom q ⟶ pullback C.GG.hom (rPt p ≫ y)` to `pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by`. Rewrite using `[Category.assoc, τ.f_over, pullback.condition_assoc, hqy])`. Establish `h₁' : h' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f` using `pullback.lift_fst _ _ _`.

Establish `h₂' : h' ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Establish `: IsClosedImmersion h'` using `τ.imm h' h₁' h₂'`. Set `b : pullback C.GG.hom (rPt p ≫ y) ⟶ pullback C.GG.hom τ.y₀` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by`. Rewrite using `[Category.assoc, hqy, pullback.condition])`. Establish `b₁ : b ≫ pullback.fst _ _ = pullback.fst _ _` using `pullback.lift_fst _ _ _`.

Establish `b₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q` using `pullback.lift_snd _ _ _`. Establish `hX : IsPullback b (pullback.snd _ _) (pullback.snd C.GG.hom τ.y₀) q`. Use `IsPullback.of_right ?_ b₂ (IsPullback.of_hasPullback C.GG.hom τ.y₀)` and prove the remaining obligations. Rewrite using `[b₁, hqy]`. Conclude with `.of_hasPullback _ _`.

Establish `hsurj : Function.Surjective h'`. Use `surjective_of_isClosedImmersion_of_points h' (pullback.snd _ _) fun x hx ↦ ?_` and prove the remaining obligations. Take `⟨c, hc₁, hc₂⟩` from `hF p y τ (x ≫ pullback.fst _ _) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])`. Use `⟨pullback.lift c (𝟙 _) (by rw [Category.id_comp]; exact hc₁), pullback.hom_ext ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, h₁', pullback.lift_fst_assoc, hc₂]`. Rewrite using `[Category.assoc, h₂', pullback.lift_snd, hx]`. Establish `hq : IsLocalRing.closedPoint τ.V ∈ Set.range q`. Use `⟨IsLocalRing.closedPoint (kb p), ?_⟩` and prove the remaining obligations. Conclude with `IsLocalRing.comap_closedPoint ((IsLocalRing.residue (OO p)).comp τ.j)`.

Establish `: IsIso h` using `isIso_of_genericFibre_of_specialFibre τ.V K h (pullback.snd _ _) τ.H.hom h₂ hK hq hX (a := pullback.fst _ _) (h' := h') (by rw [h₂']; exact .of_hasPullback _ _) (pullback.hom_ext (by simp only [Category.assoc, h₁, b₁, h₁']) (by simp only [Category.assoc, h₂, b₂, reassoc_of% h₂', …`. Conclude with `IsPullback.of_iso_pullback ⟨τ.f_over⟩ (asIso h) h₁ h₂`.
-/
theorem Core.testCart_of_fib :
    ∀ C : Core, C.Fib → SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart := by
  intro C hF hS p _ y τ
  have := isAlgClosed_residueField_OO p
  have := C.proper
  have := τ.smooth
  have := τ.sep
  have := τ.qc
  have := τ.j_loc
  have : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  let K := FractionRing τ.V
  let t : Sp K ⟶ Sp τ.V := spMap (algebraMap τ.V K)
  let q : Sp (kb p) ⟶ Sp τ.V := rPt p ≫ spMap τ.j
  have hqy : q ≫ τ.y₀ = rPt p ≫ y := by rw [Category.assoc, τ.fac]
  let h : τ.H.left ⟶ pullback C.GG.hom τ.y₀ := pullback.lift τ.f τ.H.hom τ.f_over
  have h₁ : h ≫ pullback.fst _ _ = τ.f := pullback.lift_fst _ _ _
  have h₂ : h ≫ pullback.snd _ _ = τ.H.hom := pullback.lift_snd _ _ _

  have hA : IsPullback C.a C.A.hom C.GG.hom C.U.ι :=
    isPullback_of_comp_mono C.cart
  have hφ : IsPullback τ.φ (pullback.snd τ.H.hom t) C.A.hom τ.yK := τ.φ_cart.1
  have := C.ab.geomConnected
  have : ConnectedSpace ↥(pullback τ.H.hom t) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ hφ
  have hK : IsPullback (pullback.fst τ.H.hom t ≫ h) (pullback.snd τ.H.hom t) (pullback.snd C.GG.hom τ.y₀) t := by
    refine IsPullback.of_right ?_ (by rw [Category.assoc, h₂, pullback.condition])
      (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    have := hφ.paste_horiz hA
    rw [τ.φ_f, τ.yK_fac] at this
    rw [Category.assoc, h₁]
    exact this

  let h' : pullback τ.H.hom q ⟶ pullback C.GG.hom (rPt p ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
      rw [Category.assoc, τ.f_over, pullback.condition_assoc, hqy])
  have h₁' : h' ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h₂' : h' ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  have : IsClosedImmersion h' := τ.imm h' h₁' h₂'
  let b : pullback C.GG.hom (rPt p ≫ y) ⟶ pullback C.GG.hom τ.y₀ :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ q) (by
      rw [Category.assoc, hqy, pullback.condition])
  have b₁ : b ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have b₂ : b ≫ pullback.snd _ _ = pullback.snd _ _ ≫ q := pullback.lift_snd _ _ _
  have hX : IsPullback b (pullback.snd _ _) (pullback.snd C.GG.hom τ.y₀) q := by
    refine IsPullback.of_right ?_ b₂ (IsPullback.of_hasPullback C.GG.hom τ.y₀)
    rw [b₁, hqy]
    exact .of_hasPullback _ _
  have hsurj : Function.Surjective h' := by
    refine surjective_of_isClosedImmersion_of_points h' (pullback.snd _ _) fun x hx ↦ ?_
    obtain ⟨c, hc₁, hc₂⟩ := hF p y τ (x ≫ pullback.fst _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
    refine ⟨pullback.lift c (𝟙 _) (by rw [Category.id_comp]; exact hc₁), pullback.hom_ext ?_ ?_⟩
    · rw [Category.assoc, h₁', pullback.lift_fst_assoc, hc₂]
    · rw [Category.assoc, h₂', pullback.lift_snd, hx]
  have hq : IsLocalRing.closedPoint τ.V ∈ Set.range q := by
    refine ⟨IsLocalRing.closedPoint (kb p), ?_⟩
    exact IsLocalRing.comap_closedPoint ((IsLocalRing.residue (OO p)).comp τ.j)
  have : IsIso h := isIso_of_genericFibre_of_specialFibre τ.V K h (pullback.snd _ _) τ.H.hom h₂ hK hq hX
    (a := pullback.fst _ _) (h' := h') (by rw [h₂']; exact .of_hasPullback _ _)
    (pullback.hom_ext (by simp only [Category.assoc, h₁, b₁, h₁'])
      (by simp only [Category.assoc, h₂, b₂, reassoc_of% h₂', pullback.condition]))
    ⟨h'.isClosedEmbedding.injective, hsurj⟩
  exact IsPullback.of_iso_pullback ⟨τ.f_over⟩ (asIso h) h₁ h₂

end GlobalTheory.ZJ
