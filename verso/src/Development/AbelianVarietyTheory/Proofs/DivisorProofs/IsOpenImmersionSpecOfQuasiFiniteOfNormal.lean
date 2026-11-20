import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Use `haveI := hA P`. Set `K` to `RingHom.ker (algebraMap A (Localization.AtPrime P))`. Establish `hK : K.IsPrime` using `RingHom.ker_isPrime _`. Establish `hle : ∀ Q : Ideal A, Q.IsPrime → Q ≤ P → K ≤ Q`. Introduce `Q hQ hQP`.

Establish `h` using `IsLocalization.comap_map_of_isPrime_disjoint P.primeCompl (Localization.AtPrime P) hQ (Set.disjoint_left.2 fun x hx hxQ ↦ hx (hQP hxQ))`. Rewrite using `[← h]`. Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Simplify using `[Ideal.mem_comap, hx]`.

Establish `h1 : K = p` using `le_antisymm (hle p hp.1.1 hpP) (hp.2 ⟨hK, bot_le⟩ (hle p hp.1.1 hpP))`. Establish `h2 : K = q` using `le_antisymm (hle q hq.1.1 hqP) (hq.2 ⟨hK, bot_le⟩ (hle q hq.1.1 hqP))`. Conclude with `h1.symm.trans h2`.
-/
theorem eq_of_minimalPrimes_le_of_isDomain_localization {A : Type} [CommRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {P p q : Ideal A} [P.IsPrime] (hp : p ∈ minimalPrimes A) (hq : q ∈ minimalPrimes A)
    (hpP : p ≤ P) (hqP : q ≤ P) : p = q := by
  haveI := hA P
  let K := RingHom.ker (algebraMap A (Localization.AtPrime P))
  have hK : K.IsPrime := RingHom.ker_isPrime _
  have hle : ∀ Q : Ideal A, Q.IsPrime → Q ≤ P → K ≤ Q := by
    intro Q hQ hQP
    have h := IsLocalization.comap_map_of_isPrime_disjoint P.primeCompl (Localization.AtPrime P) hQ
      (Set.disjoint_left.2 fun x hx hxQ ↦ hx (hQP hxQ))
    rw [← h]
    intro x hx
    rw [RingHom.mem_ker] at hx
    simp [Ideal.mem_comap, hx]
  have h1 : K = p := le_antisymm (hle p hp.1.1 hpP) (hp.2 ⟨hK, bot_le⟩ (hle p hp.1.1 hpP))
  have h2 : K = q := le_antisymm (hle q hq.1.1 hqP) (hq.2 ⟨hK, bot_le⟩ (hle q hq.1.1 hqP))
  exact h1.symm.trans h2

/- English proof (translation)
Establish `hfin` using `(minimalPrimes.finite_of_isNoetherianRing A).subset (Set.diff_subset (t := {p}))`. Establish `heq : (PrimeSpectrum.zeroLocus (p : Set A))ᶜ = ⋃ q ∈ minimalPrimes A \ {p}, PrimeSpectrum.zeroLocus (q : Set A)`. Use extensionality with `x`. Simplify using `only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, exists_prop]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Take `⟨q, hq, hqx⟩` from `Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le`. Use `⟨q, ⟨hq, ?_⟩, hqx⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hx hqx`.

Introduce and unpack `⟨q, ⟨hq, hne⟩, hqx⟩ hpx`. Conclude with `hne (eq_of_minimalPrimes_le_of_isDomain_localization hA hq hp hqx hpx)`. Rewrite using `[← isClosed_compl_iff, heq]`. Conclude with `hfin.isClosed_biUnion fun q _ ↦ PrimeSpectrum.isClosed_zeroLocus _`.
-/
theorem isOpen_zeroLocus_of_mem_minimalPrimes {A : Type} [CommRing A] [IsNoetherianRing A]
    (hA : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P))
    {p : Ideal A} (hp : p ∈ minimalPrimes A) : IsOpen (PrimeSpectrum.zeroLocus (p : Set A)) := by
  have hfin := (minimalPrimes.finite_of_isNoetherianRing A).subset (Set.diff_subset (t := {p}))
  have heq : (PrimeSpectrum.zeroLocus (p : Set A))ᶜ =
      ⋃ q ∈ minimalPrimes A \ {p}, PrimeSpectrum.zeroLocus (q : Set A) := by
    ext x
    simp only [Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
      Set.mem_iUnion, Set.mem_diff, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hx
      obtain ⟨q, hq, hqx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
      refine ⟨q, ⟨hq, ?_⟩, hqx⟩
      rintro rfl
      exact hx hqx
    · rintro ⟨q, ⟨hq, hne⟩, hqx⟩ hpx
      exact hne (eq_of_minimalPrimes_le_of_isDomain_localization hA hq hp hqx hpx)
  rw [← isClosed_compl_iff, heq]
  exact hfin.isClosed_biUnion fun q _ ↦ PrimeSpectrum.isClosed_zeroLocus _

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Take `⟨V, hVne, hVo⟩` from `hV`. Use `set f := Spec.map (CommRingCat.ofHom φ) with hf`. Establish `hAd : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P)` using `fun P _ ↦ (hA P).1`. Establish `hft : LocallyOfFiniteType f` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hφ`. Set `η` to `genericPoint (Spec (CommRingCat.of B))`.

Establish `hηV : η ∈ V` using `((genericPoint_spec _).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)`. Set `y₀ : PrimeSpectrum A` to `f η`. Establish `hsp : ∀ x, y₀ ⤳ f x` using `fun x ↦ (genericPoint_specializes x).map f.continuous`. Establish `hW : IsOpen (Set.range (V.ι ≫ f))` using `(V.ι ≫ f).isOpenEmbedding.isOpen_range`. Establish `hy₀W : y₀ ∈ Set.range (V.ι ≫ f)` using `⟨⟨η, hηV⟩, rfl⟩`.

Establish `hmin : y₀.asIdeal ∈ minimalPrimes A`. Use `⟨⟨y₀.isPrime, bot_le⟩, fun q hq hle ↦ ?_⟩` and prove the remaining obligations. Set `z : PrimeSpectrum A` to `⟨q, hq.1⟩`. Establish `hz : z ⤳ y₀` using `(PrimeSpectrum.le_iff_specializes z y₀).1 hle`. Take `⟨v, hv⟩` from `hz.mem_open hW hy₀W`.

Establish `h2 : y₀ ≤ z`. Rewrite using `[← hv, Scheme.Hom.comp_apply]`. Conclude with `(PrimeSpectrum.le_iff_specializes _ _).2 (hsp _)`. Conclude with `h2`. Establish `hZo : IsOpen (closure ({y₀} : Set (PrimeSpectrum A)))`.

Rewrite using `[PrimeSpectrum.closure_singleton]`. Conclude with `isOpen_zeroLocus_of_mem_minimalPrimes hAd hmin`. Set `Z : (Spec (CommRingCat.of A)).Opens` to `⟨closure ({y₀} : Set (PrimeSpectrum A)), hZo⟩`. Establish `hrange : Set.range f ⊆ Set.range Z.ι`. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `specializes_iff_mem_closure.1 (hsp x)`. Set `g : Spec (CommRingCat.of B) ⟶ Z.toScheme` to `IsOpenImmersion.lift Z.ι f hrange`. Establish `hgf : g ≫ Z.ι = f` using `IsOpenImmersion.lift_fac _ _ _`. Use `haveI : _root_.IsReduced A := isReduced_ofLocalizationMaximal A fun P _ ↦ by haveI := hAd P; infer_instance`.

Use `haveI : Nonempty Z.toScheme := ⟨⟨y₀, subset_closure rfl⟩⟩`. Use `haveI : IrreducibleSpace Z.toScheme := Subtype.irreducibleSpace (isIrreducible_singleton (x := y₀)).closure`. Use `haveI : IsIntegral Z.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _`. Establish `hZ : ∀ z : Z.toScheme, IsIntegrallyClosed (Z.toScheme.presheaf.stalk z)`. Introduce `z`.

Establish `e₁` using `asIso (Z.ι.stalkMap z)`. Set `x : PrimeSpectrum A` to `Z.ι z`. Establish `hloc : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk x) x.asIdeal` using `StructureSheaf.IsLocalization.to_stalk A x`. Establish `e₂` using `IsLocalization.algEquiv x.asIdeal.primeCompl ((Spec.structureSheaf A).presheaf.stalk x) (Localization.AtPrime x.asIdeal)`. Use `haveI := (hA x.asIdeal).2`.

Establish `hic : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk x)` using `IsIntegrallyClosed.of_equiv e₂.symm.toRingEquiv`. Use `haveI : IsIntegrallyClosed ((Spec (CommRingCat.of A)).presheaf.stalk (Z.ι z)) := hic`. Conclude with `IsIntegrallyClosed.of_equiv (e₁.commRingCatIsoToRingEquiv)`. Use `haveI : IsSeparated g := IsSeparated.of_comp g Z.ι`. Use `haveI : QuasiCompact g := QuasiCompact.of_comp g Z.ι`.

Use `haveI : LocallyOfFiniteType (g ≫ Z.ι) := by rw [hgf]; exact hft`. Use `haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g Z.ι`. Use `haveI : LocallyQuasiFinite (g ≫ Z.ι) := by rw [hgf]; exact hqf`. Use `haveI : LocallyQuasiFinite g := LocallyQuasiFinite.of_comp g Z.ι`. Use `haveI : IsOpenImmersion ((V.ι ≫ g) ≫ Z.ι) := by rw [Category.assoc, hgf]; exact hVo`.

Use `haveI : IsOpenImmersion (V.ι ≫ g) := IsOpenImmersion.of_comp _ Z.ι`. Use `isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict g hZ V hVne` as an intermediate fact. Rewrite using `[← hgf]`. Use `infer_instance`.
-/
theorem isOpenImmersion_spec_of_quasiFinite_of_normal {A B : Type} [CommRing A] [CommRing B]
    [IsDomain B] [IsNoetherianRing A] (φ : A →+* B)
    (hA : ∀ (𝔭 : Ideal A) [𝔭.IsPrime],
      IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭))
    (hφ : φ.FiniteType) (hqf : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom φ)))
    (hV : ∃ V : (Spec (CommRingCat.of B)).Opens, Nonempty V ∧
      IsOpenImmersion (V.ι ≫ Spec.map (CommRingCat.ofHom φ))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨V, hVne, hVo⟩ := hV
  set f := Spec.map (CommRingCat.ofHom φ) with hf
  have hAd : ∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) :=
    fun P _ ↦ (hA P).1
  have hft : LocallyOfFiniteType f :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr hφ
  let η := genericPoint (Spec (CommRingCat.of B))
  have hηV : η ∈ V :=
    ((genericPoint_spec _).mem_open_set_iff V.isOpen).mpr (by simpa using hVne)
  let y₀ : PrimeSpectrum A := f η
  have hsp : ∀ x, y₀ ⤳ f x := fun x ↦ (genericPoint_specializes x).map f.continuous

  have hW : IsOpen (Set.range (V.ι ≫ f)) := (V.ι ≫ f).isOpenEmbedding.isOpen_range
  have hy₀W : y₀ ∈ Set.range (V.ι ≫ f) := ⟨⟨η, hηV⟩, rfl⟩
  have hmin : y₀.asIdeal ∈ minimalPrimes A := by
    refine ⟨⟨y₀.isPrime, bot_le⟩, fun q hq hle ↦ ?_⟩
    let z : PrimeSpectrum A := ⟨q, hq.1⟩
    have hz : z ⤳ y₀ := (PrimeSpectrum.le_iff_specializes z y₀).1 hle
    obtain ⟨v, hv⟩ := hz.mem_open hW hy₀W
    have h2 : y₀ ≤ z := by
      rw [← hv, Scheme.Hom.comp_apply]
      exact (PrimeSpectrum.le_iff_specializes _ _).2 (hsp _)
    exact h2

  have hZo : IsOpen (closure ({y₀} : Set (PrimeSpectrum A))) := by
    rw [PrimeSpectrum.closure_singleton]
    exact isOpen_zeroLocus_of_mem_minimalPrimes hAd hmin
  let Z : (Spec (CommRingCat.of A)).Opens := ⟨closure ({y₀} : Set (PrimeSpectrum A)), hZo⟩
  have hrange : Set.range f ⊆ Set.range Z.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact specializes_iff_mem_closure.1 (hsp x)
  let g : Spec (CommRingCat.of B) ⟶ Z.toScheme := IsOpenImmersion.lift Z.ι f hrange
  have hgf : g ≫ Z.ι = f := IsOpenImmersion.lift_fac _ _ _

  haveI : _root_.IsReduced A := isReduced_ofLocalizationMaximal A fun P _ ↦ by
    haveI := hAd P; infer_instance
  haveI : Nonempty Z.toScheme := ⟨⟨y₀, subset_closure rfl⟩⟩
  haveI : IrreducibleSpace Z.toScheme :=
    Subtype.irreducibleSpace (isIrreducible_singleton (x := y₀)).closure
  haveI : IsIntegral Z.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hZ : ∀ z : Z.toScheme, IsIntegrallyClosed (Z.toScheme.presheaf.stalk z) := by
    intro z
    have e₁ := asIso (Z.ι.stalkMap z)
    let x : PrimeSpectrum A := Z.ι z
    have hloc : IsLocalization.AtPrime ((Spec.structureSheaf A).presheaf.stalk x) x.asIdeal :=
      StructureSheaf.IsLocalization.to_stalk A x
    have e₂ := IsLocalization.algEquiv x.asIdeal.primeCompl
      ((Spec.structureSheaf A).presheaf.stalk x) (Localization.AtPrime x.asIdeal)
    haveI := (hA x.asIdeal).2
    have hic : IsIntegrallyClosed ((Spec.structureSheaf A).presheaf.stalk x) :=
      IsIntegrallyClosed.of_equiv e₂.symm.toRingEquiv
    haveI : IsIntegrallyClosed ((Spec (CommRingCat.of A)).presheaf.stalk (Z.ι z)) := hic
    exact IsIntegrallyClosed.of_equiv (e₁.commRingCatIsoToRingEquiv)

  haveI : IsSeparated g := IsSeparated.of_comp g Z.ι
  haveI : QuasiCompact g := QuasiCompact.of_comp g Z.ι
  haveI : LocallyOfFiniteType (g ≫ Z.ι) := by rw [hgf]; exact hft
  haveI : LocallyOfFiniteType g := locallyOfFiniteType_of_comp g Z.ι
  haveI : LocallyQuasiFinite (g ≫ Z.ι) := by rw [hgf]; exact hqf
  haveI : LocallyQuasiFinite g := LocallyQuasiFinite.of_comp g Z.ι
  haveI : IsOpenImmersion ((V.ι ≫ g) ≫ Z.ι) := by rw [Category.assoc, hgf]; exact hVo
  haveI : IsOpenImmersion (V.ι ≫ g) := IsOpenImmersion.of_comp _ Z.ι
  have := isOpenImmersion_of_quasiFinite_of_isOpenImmersion_restrict g hZ V hVne
  rw [← hgf]
  infer_instance

end GlobalTheory
