import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitFinitePart

/- English proof (translation)
Establish `: IsAffine N` using `isAffine_of_isAffineHom g`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (N.isoSpec.inv ≫ g)`. Take `⟨c, hc⟩` from `Spec.map_surjective (γ ≫ N.isoSpec.hom)`. Establish `h1 : IsIntegralHom (Spec.map ψ)` using `by rw [hψ]; infer_instance`. Establish `hint : ψ.hom.IsIntegral` using `IsIntegralHom.SpecMap_iff.mp h1`.

Establish `h2 : ψ ≫ c = CommRingCat.ofHom (algebraMap R K)`. Apply `Spec.map_injective` to reduce the goal to its premises. Rewrite using `[Spec.map_comp, hc, hψ, Category.assoc, Iso.hom_inv_id_assoc, hγ]`. Establish `h3 : c.hom.comp ψ.hom = algebraMap R K` using `congrArg CommRingCat.Hom.hom h2`. Establish `h4 : ∀ b, ∃ a : R, algebraMap R K a = c.hom b` using `fun b => by`.

Use `IsIntegrallyClosed.isIntegral_iff.mp ?_` and prove the remaining obligations. Use `(hint b).map c.hom` as an intermediate fact. Rewrite `this` using `[h3]`. Then use the resulting hypothesis. Use `choose σ hσ using h4`. Establish `hi` using `IsFractionRing.injective R K`.

Set `σ' : Γ(N, ⊤) →+* R` to `{ toFun := σ map_one' := hi (by simp [hσ]) map_mul' := fun a b => hi (by simp [hσ]) map_zero' := hi (by simp [hσ]) map_add' := fun a b => hi (by simp [hσ]) }`. Use `⟨spMap σ' ≫ N.isoSpec.inv, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use extensionality with `a`.

Conclude with `hi ((hσ _).trans (congrArg (fun φ : R →+* K => φ a) h3))`. Rewrite using `[← Category.assoc, Iso.comp_inv_eq, ← hc, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`. Conclude with `hσ a`.
-/
theorem exists_section_of_isIntegralHom {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {N : Scheme.{0}} (g : N ⟶ Sp R) [IsIntegralHom g] (γ : Sp K ⟶ N)
    (hγ : γ ≫ g = spMap (algebraMap R K)) : ∃ s : Sp R ⟶ N, s ≫ g = 𝟙 _ ∧ spMap (algebraMap R K) ≫ s = γ := by
  have : IsAffine N := isAffine_of_isAffineHom g
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (N.isoSpec.inv ≫ g)
  obtain ⟨c, hc⟩ := Spec.map_surjective (γ ≫ N.isoSpec.hom)
  have h1 : IsIntegralHom (Spec.map ψ) := by rw [hψ]; infer_instance
  have hint : ψ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp h1
  have h2 : ψ ≫ c = CommRingCat.ofHom (algebraMap R K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hc, hψ, Category.assoc, Iso.hom_inv_id_assoc, hγ]
  have h3 : c.hom.comp ψ.hom = algebraMap R K := congrArg CommRingCat.Hom.hom h2
  have h4 : ∀ b, ∃ a : R, algebraMap R K a = c.hom b := fun b => by
    refine IsIntegrallyClosed.isIntegral_iff.mp ?_
    have := (hint b).map c.hom
    rwa [h3] at this
  choose σ hσ using h4
  have hi := IsFractionRing.injective R K
  let σ' : Γ(N, ⊤) →+* R :=
    { toFun := σ
      map_one' := hi (by simp [hσ])
      map_mul' := fun a b => hi (by simp [hσ])
      map_zero' := hi (by simp [hσ])
      map_add' := fun a b => hi (by simp [hσ]) }
  refine ⟨spMap σ' ≫ N.isoSpec.inv, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext a
    exact hi ((hσ _).trans (congrArg (fun φ : R →+* K => φ a) h3))
  · rw [← Category.assoc, Iso.comp_inv_eq, ← hc, ← Spec.map_comp]
    congr 1
    ext a
    exact hσ a

/- English proof (translation)
Set `j` to `π.toNormalization`. Set `g` to `π.fromNormalization`. Establish `hjg : j ≫ g = π` using `π.toNormalization_fromNormalization`. Establish `hjg' : ∀ z, g (j z) = π z` using `fun z => by rw [← Scheme.Hom.comp_apply, hjg]`. Set `I : Type` to `π ⁻¹' {genericPoint (Sp R)}`.

Establish `: Finite I` using `π.finite_preimage_singleton _`. Use `choose γ hγ hγ' using fun i : I => hs i.1 i.2`. Use `choose s hs1 hs2 using fun i : I => exists_section_of_isIntegralHom g (γ i ≫ j) (by rw [Category.assoc, hjg, hγ])`. Establish `hgs : ∀ i y, g (s i y) = y` using `fun i y => by rw [← Scheme.Hom.comp_apply, hs1]; rfl`. Establish `hcl : ∀ i, IsClosed (Set.range (s i))` using `fun i => by`.

Establish `: IsClosedImmersion (s i ≫ g)` using `by rw [hs1]; infer_instance`. Establish `: IsClosedImmersion (s i)` using `IsClosedImmersion.of_comp _ g`. Conclude with `(s i).isClosedEmbedding.isClosed_range`. Establish `hcov : ∀ z : Z, ∃ i, s i (π z) = j z` using `fun z => by`. Take `⟨z', hz', e⟩` from `Flat.generalizingMap π (genericPoint_specializes (π z))`.

Take `⟨a, ha⟩` from `hγ' ⟨z', e⟩`. Establish `h1 : j z' ∈ Set.range (s ⟨z', e⟩)` using `⟨spMap (algebraMap R K) a, by rw [← Scheme.Hom.comp_apply, hs2, Scheme.Hom.comp_apply, ha]⟩`. Take `⟨y, hy⟩` from `(hz'.map j.continuous).mem_closed (hcl _) h1`. Use `⟨⟨z', e⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hjg', ← hy, hgs]`.

Set `good : I → Prop` to `fun i => s i p ∈ Set.range j`. Set `U : π.normalization.Opens` to `⟨Set.range j \ ⋃ i : {i // ¬ good i}, Set.range (s i.1), j.isOpenEmbedding.isOpen_range.sdiff (isClosed_iUnion_of_finite fun i => hcl i.1)⟩`. Set `W : (Sp R).Opens` to `⟨⋂ i : {i // good i}, s i.1 ⁻¹' U, isOpen_iInter_of_finite fun i => U.isOpen.preimage (s i.1).continuous⟩`. Establish `hU : ∀ n, n ∈ Set.range j → g n = p → n ∈ U` using `fun n hn hp => ⟨hn, fun h => by`. Take `⟨i, y, hy⟩` from `Set.mem_iUnion.mp h`.

Apply `i.2` to reduce the goal to its premises. Establish `: y = p` using `by rw [← hp, ← hy, hgs]`. Substitute `this` using the available equality. Express the relevant statement in the definitionally equal form `s i.1 y ∈ Set.range j`. Rewrite using `[hy]`.

Conclude with `hn⟩`. Establish `hpW : p ∈ W` using `Set.mem_iInter.mpr fun i => hU _ i.2 (hgs _ _)`. Establish `hgood : ∀ i y, s i y ∈ U → good i` using `fun i y h => by`. Assume the negation of the conclusion as `hn`. Conclude with `h.2 (Set.mem_iUnion.mpr ⟨⟨i, hn⟩, y, rfl⟩)`.

Establish `hWU : ∀ i, good i → ∀ y ∈ W, s i y ∈ U` using `fun i hi y hy => Set.mem_iInter.mp hy ⟨i, hi⟩`. Set `H : Z.Opens` to `j ⁻¹ᵁ U ⊓ π ⁻¹ᵁ W`. Establish `hle : H ≤ j ⁻¹ᵁ (g ⁻¹ᵁ W)` using `fun z hz => by`. Express the relevant statement in the definitionally equal form `g (j z) ∈ W`. Rewrite using `[hjg']`.

Conclude with `hz.2`. Set `a` to `j.resLE _ H hle`. Establish `ha : a ≫ (g ⁻¹ᵁ W).ι = H.ι ≫ j` using `j.resLE_comp_ι hle`. Establish `ha' : ∀ z, (a z).1 = j z.1` using `fun z => by`. Use `congrArg (fun φ : H.toScheme ⟶ _ => φ z) ha` as an intermediate fact.

Conclude with `this`. Establish `: IsOpenImmersion (a ≫ (g ⁻¹ᵁ W).ι)` using `by rw [ha]; infer_instance`. Establish `: IsOpenImmersion a` using `IsOpenImmersion.of_comp _ (g ⁻¹ᵁ W).ι`. Establish `hr : Set.range a = (g ⁻¹ᵁ W).ι ⁻¹' ⋃ i : {i // good i}, Set.range (s i.1)`. Use extensionality with `n`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Take `⟨i, hi⟩` from `hcov z.1`. Conclude with `Set.mem_iUnion.mpr ⟨⟨i, hgood i _ (by rw [hi]; exact z.2.1)⟩, π z.1, hi.trans (ha' z).symm⟩`. Introduce `hn`.

Take `⟨i, y, hy⟩` from `Set.mem_iUnion.mp hn`. Establish `hy' : s i y = n.1` using `hy`. Establish `hyW : y ∈ W`. Rewrite using `[← hgs i y, hy']`. Conclude with `n.2`.

Establish `h1` using `hWU i.1 i.2 y hyW`. Take `⟨z, hz⟩` from `h1.1`. Use `⟨⟨z, show j z ∈ U from hz ▸ h1, show π z ∈ W by rw [← hjg', hz, hgs]; exact hyW⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `(ha' _).trans (hz.trans hy')`. Establish `: IsClosedImmersion a` using `IsClosedImmersion.of_isPreimmersion _ (by`.

Rewrite using `[hr]`. Conclude with `(isClosed_iUnion_of_finite fun i : {i // good i} => hcl i.1).preimage (g ⁻¹ᵁ W).ι.continuous)`. Establish `hρ : (a ≫ g ∣_ W) ≫ W.ι = H.ι ≫ π`. Rewrite using `[Category.assoc, morphismRestrict_ι, reassoc_of% ha, hjg]`. Use `⟨W, H, a ≫ g ∣_ W, hpW, hρ, ?_, fun z hz => ⟨hU _ ⟨z, rfl⟩ ((hjg' z).trans hz), show π z ∈ W from hz ▸ hpW⟩, fun z hz => ?_⟩` and prove the remaining obligations.

Establish `: LocallyOfFiniteType ((a ≫ g ∣_ W) ≫ W.ι)` using `by rw [hρ]; infer_instance`. Establish `: LocallyOfFiniteType (a ≫ g ∣_ W)` using `locallyOfFiniteType_of_comp _ W.ι`. Conclude with `(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, this⟩`. Take `⟨i, hi⟩` from `hcov z`. Establish `hg` using `hgood i (π z) (by rw [hi]; exact hz.1)`.

Establish `hsub : Set.range (W.ι ≫ s i) ⊆ Set.range j`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `(hWU i hg w.1 w.2).1`. Establish `hl` using `IsOpenImmersion.lift_fac j (W.ι ≫ s i) hsub`. Establish `hl' : ∀ w : W.toScheme, j (IsOpenImmersion.lift j (W.ι ≫ s i) hsub w) = s i w.1` using `fun w => by`.

Rewrite using `[← Scheme.Hom.comp_apply, hl]`. Both sides reduce to the same expression. Use `⟨IsOpenImmersion.lift j (W.ι ≫ s i) hsub, ?_, fun w => ⟨?_, ?_⟩, ⟨π z, hz.2⟩, ?_⟩` and prove the remaining obligations. Use `(congrArg (_ ≫ ·) hjg.symm).trans ?_` and prove the remaining obligations. Simplify using `only [reassoc_of% hl, hs1, Category.comp_id]`.

Express the relevant statement in the definitionally equal form `j _ ∈ U`. Rewrite using `[hl']`. Conclude with `hWU i hg w.1 w.2`. Express the relevant statement in the definitionally equal form `π _ ∈ W`. Rewrite using `[← hjg', hl', hgs]`.

Conclude with `w.2`. Apply `j.isOpenEmbedding.injective` to reduce the goal to its premises. Conclude with `(hl' _).trans hi`.
-/
theorem exists_finite_open {R K : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K]
    [Algebra R K] [IsFractionRing R K] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [LocallyQuasiFinite π]
    [IsSeparated π] [QuasiCompact π] [LocallyOfFiniteType π]
    (hs : ∀ z : Z, π z = genericPoint (Sp R) →
      ∃ γ : Sp K ⟶ Z, γ ≫ π = spMap (algebraMap R K) ∧ z ∈ Set.range γ) (p : Sp R) :
    ∃ (W : (Sp R).Opens) (H : Z.Opens) (ρ : H.toScheme ⟶ W.toScheme), p ∈ W ∧ ρ ≫ W.ι = H.ι ≫ π ∧ IsFinite ρ ∧
      (∀ z : Z, π z = p → z ∈ H) ∧
      ∀ z ∈ H, ∃ s : W.toScheme ⟶ Z, s ≫ π = W.ι ∧ (∀ w, s w ∈ H) ∧ z ∈ Set.range s := by
  let j := π.toNormalization
  let g := π.fromNormalization
  have hjg : j ≫ g = π := π.toNormalization_fromNormalization
  have hjg' : ∀ z, g (j z) = π z := fun z => by rw [← Scheme.Hom.comp_apply, hjg]
  let I : Type := π ⁻¹' {genericPoint (Sp R)}
  have : Finite I := π.finite_preimage_singleton _
  choose γ hγ hγ' using fun i : I => hs i.1 i.2
  choose s hs1 hs2 using fun i : I => exists_section_of_isIntegralHom g (γ i ≫ j) (by rw [Category.assoc, hjg, hγ])
  have hgs : ∀ i y, g (s i y) = y := fun i y => by rw [← Scheme.Hom.comp_apply, hs1]; rfl
  have hcl : ∀ i, IsClosed (Set.range (s i)) := fun i => by
    have : IsClosedImmersion (s i ≫ g) := by rw [hs1]; infer_instance
    have : IsClosedImmersion (s i) := IsClosedImmersion.of_comp _ g
    exact (s i).isClosedEmbedding.isClosed_range
  have hcov : ∀ z : Z, ∃ i, s i (π z) = j z := fun z => by
    obtain ⟨z', hz', e⟩ := Flat.generalizingMap π (genericPoint_specializes (π z))
    obtain ⟨a, ha⟩ := hγ' ⟨z', e⟩
    have h1 : j z' ∈ Set.range (s ⟨z', e⟩) :=
      ⟨spMap (algebraMap R K) a, by rw [← Scheme.Hom.comp_apply, hs2, Scheme.Hom.comp_apply, ha]⟩
    obtain ⟨y, hy⟩ := (hz'.map j.continuous).mem_closed (hcl _) h1
    refine ⟨⟨z', e⟩, ?_⟩
    rw [← hjg', ← hy, hgs]
  let good : I → Prop := fun i => s i p ∈ Set.range j
  let U : π.normalization.Opens := ⟨Set.range j \ ⋃ i : {i // ¬ good i}, Set.range (s i.1),
    j.isOpenEmbedding.isOpen_range.sdiff (isClosed_iUnion_of_finite fun i => hcl i.1)⟩
  let W : (Sp R).Opens := ⟨⋂ i : {i // good i}, s i.1 ⁻¹' U,
    isOpen_iInter_of_finite fun i => U.isOpen.preimage (s i.1).continuous⟩
  have hU : ∀ n, n ∈ Set.range j → g n = p → n ∈ U := fun n hn hp => ⟨hn, fun h => by
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp h
    apply i.2
    have : y = p := by rw [← hp, ← hy, hgs]
    subst this
    change s i.1 y ∈ Set.range j
    rw [hy]; exact hn⟩
  have hpW : p ∈ W := Set.mem_iInter.mpr fun i => hU _ i.2 (hgs _ _)
  have hgood : ∀ i y, s i y ∈ U → good i := fun i y h => by
    by_contra hn
    exact h.2 (Set.mem_iUnion.mpr ⟨⟨i, hn⟩, y, rfl⟩)
  have hWU : ∀ i, good i → ∀ y ∈ W, s i y ∈ U := fun i hi y hy => Set.mem_iInter.mp hy ⟨i, hi⟩
  let H : Z.Opens := j ⁻¹ᵁ U ⊓ π ⁻¹ᵁ W
  have hle : H ≤ j ⁻¹ᵁ (g ⁻¹ᵁ W) := fun z hz => by
    change g (j z) ∈ W
    rw [hjg']; exact hz.2
  let a := j.resLE _ H hle
  have ha : a ≫ (g ⁻¹ᵁ W).ι = H.ι ≫ j := j.resLE_comp_ι hle
  have ha' : ∀ z, (a z).1 = j z.1 := fun z => by
    have := congrArg (fun φ : H.toScheme ⟶ _ => φ z) ha
    exact this
  have : IsOpenImmersion (a ≫ (g ⁻¹ᵁ W).ι) := by rw [ha]; infer_instance
  have : IsOpenImmersion a := IsOpenImmersion.of_comp _ (g ⁻¹ᵁ W).ι
  have hr : Set.range a = (g ⁻¹ᵁ W).ι ⁻¹' ⋃ i : {i // good i}, Set.range (s i.1) := by
    ext n
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨i, hi⟩ := hcov z.1
      exact Set.mem_iUnion.mpr ⟨⟨i, hgood i _ (by rw [hi]; exact z.2.1)⟩, π z.1, hi.trans (ha' z).symm⟩
    · intro hn
      obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hn
      have hy' : s i y = n.1 := hy
      have hyW : y ∈ W := by
        rw [← hgs i y, hy']; exact n.2
      have h1 := hWU i.1 i.2 y hyW
      obtain ⟨z, hz⟩ := h1.1
      refine ⟨⟨z, show j z ∈ U from hz ▸ h1, show π z ∈ W by rw [← hjg', hz, hgs]; exact hyW⟩, Subtype.ext ?_⟩
      exact (ha' _).trans (hz.trans hy')
  have : IsClosedImmersion a := IsClosedImmersion.of_isPreimmersion _ (by
    rw [hr]
    exact (isClosed_iUnion_of_finite fun i : {i // good i} => hcl i.1).preimage (g ⁻¹ᵁ W).ι.continuous)
  have hρ : (a ≫ g ∣_ W) ≫ W.ι = H.ι ≫ π := by
    rw [Category.assoc, morphismRestrict_ι, reassoc_of% ha, hjg]
  refine ⟨W, H, a ≫ g ∣_ W, hpW, hρ, ?_, fun z hz => ⟨hU _ ⟨z, rfl⟩ ((hjg' z).trans hz), show π z ∈ W from hz ▸ hpW⟩,
    fun z hz => ?_⟩
  · have : LocallyOfFiniteType ((a ≫ g ∣_ W) ≫ W.ι) := by rw [hρ]; infer_instance
    have : LocallyOfFiniteType (a ≫ g ∣_ W) := locallyOfFiniteType_of_comp _ W.ι
    exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, this⟩
  · obtain ⟨i, hi⟩ := hcov z
    have hg := hgood i (π z) (by rw [hi]; exact hz.1)
    have hsub : Set.range (W.ι ≫ s i) ⊆ Set.range j := by
      rintro _ ⟨w, rfl⟩
      exact (hWU i hg w.1 w.2).1
    have hl := IsOpenImmersion.lift_fac j (W.ι ≫ s i) hsub
    have hl' : ∀ w : W.toScheme, j (IsOpenImmersion.lift j (W.ι ≫ s i) hsub w) = s i w.1 := fun w => by
      rw [← Scheme.Hom.comp_apply, hl]; rfl
    refine ⟨IsOpenImmersion.lift j (W.ι ≫ s i) hsub, ?_, fun w => ⟨?_, ?_⟩, ⟨π z, hz.2⟩, ?_⟩
    · refine (congrArg (_ ≫ ·) hjg.symm).trans ?_
      simp only [reassoc_of% hl, hs1, Category.comp_id]
    · change j _ ∈ U
      rw [hl']; exact hWU i hg w.1 w.2
    · change π _ ∈ W
      rw [← hjg', hl', hgs]; exact w.2
    · apply j.isOpenEmbedding.injective
      exact (hl' _).trans hi

/- English proof (translation)
Rewrite using `[← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]`.
-/
theorem range_of_isPullback {P X Y S : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  rw [← Scheme.Pullback.range_fst, ← h.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, h.isoPullback.hom.surjective.range_eq, Set.image_univ]

/- English proof (translation)
Use `set A := Localization.Away f₀`. Use `Module.FinitePresentation.of_finite_of_finitePresentation A B` as an intermediate fact. Choose the witnesses or unpack the hypotheses as in `⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by`. Rewrite using `[PrimeSpectrum.localization_away_comap_range A f₀]`. Conclude with `hp`.

Establish `: Module.Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl B)` using `Module.free_of_flat_of_isLocalRing`. Take `⟨r, hr, hf, -⟩` from `Module.FinitePresentation.exists_free_localizedModule_powers q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl B) (Localization.AtPrime q.asIdeal)`. Take `⟨⟨r', u⟩, hu⟩` from `IsLocalization.surj (Submonoid.powers f₀) r`. Establish `hu' : IsUnit (algebraMap R A u)` using `IsLocalization.map_units A u`. Establish `hass : Associated r (algebraMap R A r')` using `⟨hu'.unit, hu⟩`.

Establish `hr' : r' ∉ (PrimeSpectrum.comap (algebraMap R A) q).asIdeal` using `fun h => by`. Establish `h' : algebraMap R A r' ∈ q.asIdeal` using `h`. Rewrite `h'` using `[← show r * algebraMap R A u = algebraMap R A r' from hu]`. Conclude with `(q.isPrime.mem_or_mem h').elim hr fun h'' => q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem h'' hu')`. Set `T` to `Localization.Away r`.

Establish `: IsLocalization.Away (algebraMap R A r') T` using `IsLocalization.Away.of_associated hass`. Establish `: IsLocalization.Away (f₀ * r') T` using `IsLocalization.Away.mul' A T f₀ r'`. Set `e : T ≃ₐ[R] Localization.Away (f₀ * r')` to `IsLocalization.algEquiv (Submonoid.powers (f₀ * r')) _ _`. Use `letI : Algebra T (Localization.Away (f₀ * r')) := e.toRingHom.toAlgebra`. Use `letI : Algebra A (Localization.Away (f₀ * r')) := (e.toRingHom.comp (algebraMap A T)).toAlgebra`.

Establish `: IsScalarTower A T (Localization.Away (f₀ * r'))` using `IsScalarTower.of_algebraMap_eq' rfl`. Establish `: Module.Free T (T ⊗[A] B)` using `Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) B)`. Use `⟨f₀ * r', inferInstance, fun h => ((PrimeSpectrum.comap (algebraMap R A) q).isPrime.mem_or_mem h).elim hp hr', IsScalarTower.of_algebraMap_eq fun x => ?_, Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A T (Localization.Away (f₀ * r')) (Localization.Away …` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = e (algebraMap A T (algebraMap R A x))`. Rewrite using `[← IsScalarTower.algebraMap_apply, e.commutes]`.
-/
theorem exists_free_away {R : Type} [CommRing R] (f₀ : R) (p : PrimeSpectrum R) (hp : f₀ ∉ p.asIdeal) (B : Type)
    [CommRing B] [Algebra (Localization.Away f₀) B] [Module.Finite (Localization.Away f₀) B]
    [Module.Flat (Localization.Away f₀) B] [Algebra.FinitePresentation (Localization.Away f₀) B] :
    ∃ (f : R) (_ : Algebra (Localization.Away f₀) (Localization.Away f)), f ∉ p.asIdeal ∧
      IsScalarTower R (Localization.Away f₀) (Localization.Away f) ∧
      Module.Free (Localization.Away f) (Localization.Away f ⊗[Localization.Away f₀] B) := by
  set A := Localization.Away f₀
  have := Module.FinitePresentation.of_finite_of_finitePresentation A B
  obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A)) := by
    rw [PrimeSpectrum.localization_away_comap_range A f₀]; exact hp
  have : Module.Free (Localization.AtPrime q.asIdeal) (LocalizedModule q.asIdeal.primeCompl B) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨r, hr, hf, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    q.asIdeal.primeCompl (LocalizedModule.mkLinearMap q.asIdeal.primeCompl B) (Localization.AtPrime q.asIdeal)
  obtain ⟨⟨r', u⟩, hu⟩ := IsLocalization.surj (Submonoid.powers f₀) r
  have hu' : IsUnit (algebraMap R A u) := IsLocalization.map_units A u
  have hass : Associated r (algebraMap R A r') := ⟨hu'.unit, hu⟩
  have hr' : r' ∉ (PrimeSpectrum.comap (algebraMap R A) q).asIdeal := fun h => by
    have h' : algebraMap R A r' ∈ q.asIdeal := h
    rw [← show r * algebraMap R A u = algebraMap R A r' from hu] at h'
    exact (q.isPrime.mem_or_mem h').elim hr fun h'' => q.isPrime.ne_top (q.asIdeal.eq_top_of_isUnit_mem h'' hu')
  let T := Localization.Away r
  have : IsLocalization.Away (algebraMap R A r') T := IsLocalization.Away.of_associated hass
  have : IsLocalization.Away (f₀ * r') T := IsLocalization.Away.mul' A T f₀ r'
  let e : T ≃ₐ[R] Localization.Away (f₀ * r') := IsLocalization.algEquiv (Submonoid.powers (f₀ * r')) _ _
  letI : Algebra T (Localization.Away (f₀ * r')) := e.toRingHom.toAlgebra
  letI : Algebra A (Localization.Away (f₀ * r')) := (e.toRingHom.comp (algebraMap A T)).toAlgebra
  have : IsScalarTower A T (Localization.Away (f₀ * r')) := IsScalarTower.of_algebraMap_eq' rfl
  have : Module.Free T (T ⊗[A] B) := Module.Free.of_equiv (LocalizedModule.equivTensorProduct (Submonoid.powers r) B)
  refine ⟨f₀ * r', inferInstance, fun h => ((PrimeSpectrum.comap (algebraMap R A) q).isPrime.mem_or_mem h).elim hp hr',
    IsScalarTower.of_algebraMap_eq fun x => ?_, Module.Free.of_equiv (TensorProduct.AlgebraTensorModule.cancelBaseChange A T
      (Localization.Away (f₀ * r')) (Localization.Away (f₀ * r')) B)⟩
  change _ = e (algebraMap A T (algebraMap R A x))
  rw [← IsScalarTower.algebraMap_apply, e.commutes]

/- English proof (translation)
Take `⟨_, ⟨f₀, rfl⟩, hp, hsub⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show p ∈ (W ⊓ W').1 from ⟨hW, hW'⟩) (W ⊓ W').isOpen`. Set `A` to `Localization.Away f₀`. Establish `hA : Set.range (spMap (algebraMap R A)) ⊆ (W : Set (Sp R)) ∩ W'` using `(PrimeSpectrum.localization_away_comap_range A f₀).subset.trans hsub`. Establish `hA' : Set.range (spMap (algebraMap R A)) ⊆ Set.range W.ι`. Rewrite using `[Scheme.Opens.range_ι]`.

Conclude with `fun x hx => (hA hx).1`. Set `a` to `IsOpenImmersion.lift W.ι (spMap (algebraMap R A)) hA'`. Establish `ha : a ≫ W.ι = spMap (algebraMap R A)` using `IsOpenImmersion.lift_fac _ _ _`. Establish `P₀ : IsPullback (𝟙 _) ρ (H.ι ≫ π) W.ι` using `IsPullback.of_horiz_isIso_mono ⟨by rw [hρ, Category.id_comp]⟩`. Establish `: Flat ρ` using `MorphismProperty.of_isPullback (P := @Flat) P₀ inferInstance`.

Establish `: LocallyOfFinitePresentation ρ` using `MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) P₀ inferInstance`. Establish `: IsAffine (pullback ρ a)` using `isAffine_of_isAffineHom (pullback.snd ρ a)`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective ((pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a)`. Set `B₀ : Type` to `Γ(pullback ρ a, ⊤)`. Use `letI : Algebra A B₀ := ψ.hom.toAlgebra`.

Establish `: Module.Finite A B₀` using `(IsFinite.SpecMap_iff ψ).mp (by rw [hψ]; infer_instance)`. Establish `: Module.Flat A B₀` using `Flat.SpecMap_iff.mp (show Flat (Spec.map ψ) by rw [hψ]; infer_instance)`. Establish `: Algebra.FinitePresentation A B₀` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp (show LocallyOfFinitePresentation (Spec.map ψ) by rw [hψ]; infer_instance)`. Take `⟨f, _, hf, hT, hfree⟩` from `exists_free_away f₀ p hp B₀`. Set `A'` to `Localization.Away f`.

Establish `e : spMap (algebraMap A A') ≫ spMap (algebraMap R A) = spMap (algebraMap R A')`. Rewrite using `[← Spec.map_comp, IsScalarTower.algebraMap_eq R A A']`. Both sides reduce to the same expression. Establish `P₁` using `isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A A' B₀)`. Establish `P₂ : IsPullback ((pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) (spMap (algebraMap A B₀)) ρ a`.

Establish `h : spMap (algebraMap A B₀) = (pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a` using `hψ`. Rewrite using `[h]`. Conclude with `IsPullback.of_iso (IsPullback.of_hasPullback ρ a) (pullback ρ a).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)`. Establish `P₃` using `P₁.flip.paste_horiz P₂`. Establish `e' : (spMap (algebraMap A A') ≫ a) ≫ W.ι = spMap (algebraMap R A')` using `by rw [Category.assoc, ha, e]`.

Establish `: IsOpenImmersion (spMap (algebraMap R A'))` using `IsOpenImmersion.of_isLocalization f`. Establish `: IsOpenImmersion ((spMap (algebraMap A A') ≫ a) ≫ W.ι)` using `by rw [e']; infer_instance`. Establish `ho : IsOpenImmersion (spMap (algebraMap A A') ≫ a)` using `IsOpenImmersion.of_comp _ W.ι`. Establish `ho'` using `MorphismProperty.of_isPullback (P := @IsOpenImmersion) P₃.flip ho`. Establish `hr` using `range_of_isPullback P₃`.

Establish `hw` using `P₃.w`. Generalize the expression as in `(Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B₀)).toRingHom) ≫ (pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) = j at ho' hr hw`. Establish `hρ' : ∀ z, (ρ z).1 = π z.1` using `fun z => congrArg (fun φ : H.toScheme ⟶ _ => φ z) hρ`. Use `⟨f, A' ⊗[A] B₀, inferInstance, inferInstance, j ≫ H.ι, hf, inferInstance, hfree, inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hρ, reassoc_of% hw, ← e']`.

Both sides reduce to the same expression. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `hA ⟨spMap (algebraMap A A') y, by rw [← Scheme.Hom.comp_apply, e]⟩`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, rfl⟩`. Take `⟨w, hw'⟩` from `hr.subset ⟨y, rfl⟩`. Use `⟨(j y).2, w, ?_⟩` and prove the remaining obligations. Rewrite using `[← e', Scheme.Hom.comp_apply, hw']`. Conclude with `hρ' _`.

Introduce and unpack `⟨hz, w, hw'⟩`. Take `⟨y, hy⟩` from `hr.superset (show (⟨z, hz⟩ : H.toScheme) ∈ ρ ⁻¹' Set.range (spMap (algebraMap A A') ≫ a) from ⟨w, Subtype.ext (by`. Use `Eq.trans ?_ (hρ' ⟨z, hz⟩).symm` and prove the remaining obligations. Use `Eq.trans ?_ hw'` and prove the remaining obligations. Rewrite using `[← e']`.

Use the proof step `rfl)⟩)`. Conclude with `⟨y, by rw [Scheme.Hom.comp_apply, hy]; rfl⟩`.
-/
theorem exists_free_chart {R : Type} [CommRing R] {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π]
    [LocallyOfFinitePresentation π] (p : PrimeSpectrum R) (W W' : (Sp R).Opens) (H : Z.Opens)
    (ρ : H.toScheme ⟶ W.toScheme) (hW : p ∈ W) (hW' : p ∈ W') (hρ : ρ ≫ W.ι = H.ι ≫ π) [IsFinite ρ] :
    ∃ (f : R) (B : Type) (_ : CommRing B) (_ : Algebra (Localization.Away f) B) (j : Sp B ⟶ Z), f ∉ p.asIdeal ∧
      Module.Finite (Localization.Away f) B ∧ Module.Free (Localization.Away f) B ∧ IsOpenImmersion j ∧
      j ≫ π = spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap R (Localization.Away f)) ∧
      Set.range (spMap (algebraMap R (Localization.Away f))) ⊆ (W : Set (Sp R)) ∩ W' ∧
      Set.range j = (H : Set Z) ∩ π ⁻¹' Set.range (spMap (algebraMap R (Localization.Away f))) := by
  obtain ⟨_, ⟨f₀, rfl⟩, hp, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (W ⊓ W').1 from ⟨hW, hW'⟩) (W ⊓ W').isOpen
  let A := Localization.Away f₀
  have hA : Set.range (spMap (algebraMap R A)) ⊆ (W : Set (Sp R)) ∩ W' :=
    (PrimeSpectrum.localization_away_comap_range A f₀).subset.trans hsub
  have hA' : Set.range (spMap (algebraMap R A)) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]; exact fun x hx => (hA hx).1
  let a := IsOpenImmersion.lift W.ι (spMap (algebraMap R A)) hA'
  have ha : a ≫ W.ι = spMap (algebraMap R A) := IsOpenImmersion.lift_fac _ _ _
  have P₀ : IsPullback (𝟙 _) ρ (H.ι ≫ π) W.ι := IsPullback.of_horiz_isIso_mono ⟨by rw [hρ, Category.id_comp]⟩
  have : Flat ρ := MorphismProperty.of_isPullback (P := @Flat) P₀ inferInstance
  have : LocallyOfFinitePresentation ρ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) P₀ inferInstance
  have : IsAffine (pullback ρ a) := isAffine_of_isAffineHom (pullback.snd ρ a)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a)
  let B₀ : Type := Γ(pullback ρ a, ⊤)
  letI : Algebra A B₀ := ψ.hom.toAlgebra
  have : Module.Finite A B₀ := (IsFinite.SpecMap_iff ψ).mp (by rw [hψ]; infer_instance)
  have : Module.Flat A B₀ := Flat.SpecMap_iff.mp (show Flat (Spec.map ψ) by rw [hψ]; infer_instance)
  have : Algebra.FinitePresentation A B₀ := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
    (show LocallyOfFinitePresentation (Spec.map ψ) by rw [hψ]; infer_instance)
  obtain ⟨f, _, hf, hT, hfree⟩ := exists_free_away f₀ p hp B₀
  let A' := Localization.Away f
  have e : spMap (algebraMap A A') ≫ spMap (algebraMap R A) = spMap (algebraMap R A') := by
    rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R A A']; rfl
  have P₁ := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A A' B₀)
  have P₂ : IsPullback ((pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) (spMap (algebraMap A B₀)) ρ a := by
    have h : spMap (algebraMap A B₀) = (pullback ρ a).isoSpec.inv ≫ pullback.snd ρ a := hψ
    rw [h]
    exact IsPullback.of_iso (IsPullback.of_hasPullback ρ a) (pullback ρ a).isoSpec (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  have P₃ := P₁.flip.paste_horiz P₂
  have e' : (spMap (algebraMap A A') ≫ a) ≫ W.ι = spMap (algebraMap R A') := by rw [Category.assoc, ha, e]
  have : IsOpenImmersion (spMap (algebraMap R A')) := IsOpenImmersion.of_isLocalization f
  have : IsOpenImmersion ((spMap (algebraMap A A') ≫ a) ≫ W.ι) := by rw [e']; infer_instance
  have ho : IsOpenImmersion (spMap (algebraMap A A') ≫ a) := IsOpenImmersion.of_comp _ W.ι
  have ho' := MorphismProperty.of_isPullback (P := @IsOpenImmersion) P₃.flip ho
  have hr := range_of_isPullback P₃
  have hw := P₃.w
  generalize (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := A') (B := B₀)).toRingHom) ≫
    (pullback ρ a).isoSpec.inv ≫ pullback.fst ρ a) = j at ho' hr hw
  have hρ' : ∀ z, (ρ z).1 = π z.1 := fun z => congrArg (fun φ : H.toScheme ⟶ _ => φ z) hρ
  refine ⟨f, A' ⊗[A] B₀, inferInstance, inferInstance, j ≫ H.ι, hf, inferInstance, hfree, inferInstance, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hρ, reassoc_of% hw, ← e']
    rfl
  · rintro _ ⟨y, rfl⟩
    exact hA ⟨spMap (algebraMap A A') y, by rw [← Scheme.Hom.comp_apply, e]⟩
  · ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨w, hw'⟩ := hr.subset ⟨y, rfl⟩
      refine ⟨(j y).2, w, ?_⟩
      rw [← e', Scheme.Hom.comp_apply, hw']
      exact hρ' _
    · rintro ⟨hz, w, hw'⟩
      obtain ⟨y, hy⟩ := hr.superset (show (⟨z, hz⟩ : H.toScheme) ∈ ρ ⁻¹' Set.range (spMap (algebraMap A A') ≫ a) from
        ⟨w, Subtype.ext (by
          refine Eq.trans ?_ (hρ' ⟨z, hz⟩).symm
          refine Eq.trans ?_ hw'
          rw [← e']; rfl)⟩)
      exact ⟨y, by rw [Scheme.Hom.comp_apply, hy]; rfl⟩

/- English proof (translation)
Establish `hc : IsClosed (ρ '' (U : Set P)ᶜ)` using `ρ.isClosedMap _ U.isOpen.isClosed_compl`. Use `⟨⟨W.ι '' (ρ '' (U : Set P)ᶜ)ᶜ, W.ι.isOpenEmbedding.isOpenMap _ hc.isOpen_compl⟩, ⟨⟨p, hp⟩, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy, e⟩`. Conclude with `hy (hU y (congrArg Subtype.val e))`. Introduce and unpack `y ⟨w, hw, e⟩`.

Assume the negation of the conclusion as `hy`. Conclude with `hw ⟨y, hy, Subtype.ext e.symm⟩`.
-/
theorem exists_open_fibres_subset {P S : Scheme.{0}} (W : S.Opens) (ρ : P ⟶ W.toScheme) [UniversallyClosed ρ]
    (U : P.Opens) (p : S) (hp : p ∈ W) (hU : ∀ y : P, (ρ y).1 = p → y ∈ U) :
    ∃ W' : S.Opens, p ∈ W' ∧ ∀ y : P, (ρ y).1 ∈ W' → y ∈ U := by
  have hc : IsClosed (ρ '' (U : Set P)ᶜ) := ρ.isClosedMap _ U.isOpen.isClosed_compl
  refine ⟨⟨W.ι '' (ρ '' (U : Set P)ᶜ)ᶜ, W.ι.isOpenEmbedding.isOpenMap _ hc.isOpen_compl⟩, ⟨⟨p, hp⟩, ?_, rfl⟩, ?_⟩
  · rintro ⟨y, hy, e⟩
    exact hy (hU y (congrArg Subtype.val e))
  · rintro y ⟨w, hw, e⟩
    by_contra hy
    exact hw ⟨y, hy, Subtype.ext e.symm⟩

/- English proof (translation)
Take `⟨Q, hQ⟩` from `h`. Use extensionality with `b`. Establish `h1 : b - algebraMap A B (σ b) ∈ (spMap σ.toRingHom Q).asIdeal`. Express the relevant statement in the definitionally equal form `σ (b - algebraMap A B (σ b)) ∈ Q.asIdeal`. Simplify using the standard rewrite rules.

Rewrite `h1` using `[hQ]`. Establish `h2 : β (b - algebraMap A B (σ b)) ∈ y.asIdeal` using `h1`. Rewrite `h2` using `[(Ideal.eq_bot_of_prime y.asIdeal (h := y.isPrime)), Ideal.mem_bot, map_sub, sub_eq_zero]`. Conclude with `h2`.
-/
theorem eq_comp_section {A B k : Type} [CommRing A] [CommRing B] [Algebra A B] [Field k] (β : B →+* k)
    (σ : B →ₐ[A] A) (y : Sp k) (h : spMap β y ∈ Set.range (spMap σ.toRingHom)) :
    β = (β.comp (algebraMap A B)).comp σ.toRingHom := by
  obtain ⟨Q, hQ⟩ := h
  ext b
  have h1 : b - algebraMap A B (σ b) ∈ (spMap σ.toRingHom Q).asIdeal := by
    change σ (b - algebraMap A B (σ b)) ∈ Q.asIdeal
    simp
  rw [hQ] at h1
  have h2 : β (b - algebraMap A B (σ b)) ∈ y.asIdeal := h1
  rw [(Ideal.eq_bot_of_prime y.asIdeal (h := y.isPrime)), Ideal.mem_bot, map_sub, sub_eq_zero] at h2
  exact h2

/- English proof (translation)
Establish `: IsDominant (spMap (algebraMap R K))`. Rewrite using `[isDominant_iff]`. Use `(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr ?_` and prove the remaining obligations. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]`. Conclude with `bot_le`.

Use `IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))` as an intermediate fact. Conclude with `IsSchemeTheoreticallyDominant.isReduced (pullback.fst π (spMap (algebraMap R K)))`.
-/
theorem isReduced_of_generic {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {Z : Scheme.{0}} (π : Z ⟶ Sp R) [Flat π] [IsReduced (pullback π (spMap (algebraMap R K)))] : IsReduced Z := by
  have : IsDominant (spMap (algebraMap R K)) := by
    rw [isDominant_iff]
    refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap R K)).mpr ?_
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.fst π (spMap (algebraMap R K)))

/- English proof (translation)
Take `⟨𝔪, h𝔪, hle⟩` from `Ideal.exists_le_maximal s.asIdeal s.isPrime.ne_top`. Use `h𝔪.isPrime` as an intermediate fact. Establish `h1` using `h 𝔪 h𝔪 ⟨⊥, Ideal.isPrime_bot⟩`. Use `Specializes.mem_open ((PrimeSpectrum.le_iff_specializes _ _).mp ?_) U.isOpen h1` and prove the remaining obligations. Introduce `a ha`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha)`.
-/
theorem mem_of_forall_maximal {S : Type} [CommRing S] (U : (Sp S).Opens)
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → ∀ y, spMap (Ideal.Quotient.mk 𝔪) y ∈ U) (s : Sp S) : s ∈ U := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal s.asIdeal s.isPrime.ne_top
  have := h𝔪.isPrime
  have h1 := h 𝔪 h𝔪 ⟨⊥, Ideal.isPrime_bot⟩
  refine Specializes.mem_open ((PrimeSpectrum.le_iff_specializes _ _).mp ?_) U.isOpen h1
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha)

/- English proof (translation)
Establish `: Flat (spMap σ)` using `inferInstance`. Establish `: Surjective (spMap σ)` using `⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩`. Conclude with `Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_spMap {K L : Type} [Field K] [Field L] (σ : K →+* L) : Epi (spMap σ) := by
  have : Flat (spMap σ) := inferInstance
  have : Surjective (spMap σ) := ⟨fun u => ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

end GlobalTheory.SplitFinitePart
