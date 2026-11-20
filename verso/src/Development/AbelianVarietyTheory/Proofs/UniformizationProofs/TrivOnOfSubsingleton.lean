import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKerIffMinors
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsIsGenTranslDiffComp

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TrivRep

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Establish `hne : LinearMap.ker (LinearMap.mulRight S x) ≠ ⊤` using `fun e => hx (by`. Establish `: (1 : S) ∈ LinearMap.ker (LinearMap.mulRight S x)` using `e ▸ Submodule.mem_top`. Simplify using `using this)`. Take `⟨m, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Take `⟨s, hs, h0⟩` from `h ⟨m, hm.isPrime⟩`. Take `⟨⟨_, n, rfl⟩, hc⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ x).1 h0`. Conclude with `hs (hm.isPrime.mem_of_pow_mem n (hle hc))`.
-/
theorem eq_zero_of_away {S : Type} [CommRing S] (x : S)
    (h : ∀ q : PrimeSpectrum S, ∃ s ∉ q.asIdeal, algebraMap S (Localization.Away s) x = 0) : x = 0 := by
  by_contra hx
  have hne : LinearMap.ker (LinearMap.mulRight S x) ≠ ⊤ := fun e => hx (by
    have : (1 : S) ∈ LinearMap.ker (LinearMap.mulRight S x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, h0⟩ := h ⟨m, hm.isPrime⟩
  obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ x).1 h0
  exact hs (hm.isPrime.mem_of_pow_mem n (hle hc))

/- English proof (translation)
Use `choose r hr J hJ using H`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun p => (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R))) (fun p => (PrimeSpectrum.basicOpen (r p)).isOpen) (fun p _ => Set.mem_iUnion.2 ⟨p, hr p⟩)`. Establish `ht' : ∀ (S : Type) [CommRing S] (g : R →+* S) (q : PrimeSpectrum S), ∃ i ∈ t, g (r i) ∉ q.asIdeal`. Introduce `S _ g q`. Take `⟨i, hi, h⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ (PrimeSpectrum.comap g q)))`.

Conclude with `⟨i, hi, h⟩`. Set `T` to `fun i => Localization.Away (r i) ⧸ (J i).map (algebraMap R (Localization.Away (r i)))`. Set `φ : ∀ i, R →+* T i` to `fun i => (Ideal.Quotient.mk _).comp (algebraMap R (Localization.Away (r i)))`. Establish `hφ : ∀ i, P _ (φ i)` using `fun i => (hJ i _ (φ i) ((IsLocalization.Away.algebraMap_isUnit (r i)).map (Ideal.Quotient.mk _))).2 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)`. Establish `hk : ∀ i (S : Type) [CommRing S] (g : R →+* S), IsUnit (g (r i)) → P S g → RingHom.ker (φ i) ≤ RingHom.ker g`.

Introduce `i S _ g hu hg a ha`. Establish `h₁ : (J i).map (algebraMap R (Localization.Away (r i))) ≤ RingHom.ker (IsLocalization.Away.lift (S` using `Localization.Away (r i)) (r i) hu) := by`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `b hb`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, IsLocalization.Away.lift_eq]`.

Conclude with `(hJ i S g hu).1 hg hb`. Establish `h₂` using `h₁ (Ideal.Quotient.eq_zero_iff_mem.1 ha)`. Rewrite `h₂` using `[RingHom.mem_ker, IsLocalization.Away.lift_eq]`. Then use the resulting hypothesis. Use `⟨⨅ i ∈ t, RingHom.ker (φ i), fun S _ g => ⟨fun h a ha => ?_, fun h q => ?_⟩⟩` and prove the remaining obligations. Use `eq_zero_of_away (g a) fun q => ?_` and prove the remaining obligations.

Take `⟨s, hs, hPs⟩` from `h q`. Take `⟨i, hi, hq⟩` from `ht' S g q`. Establish `hu : IsUnit (algebraMap S (Localization.Away (s * g (r i))) (s * g (r i)))` using `IsLocalization.Away.algebraMap_isUnit _`. Rewrite `hu` using `[map_mul, IsUnit.mul_iff]`. Establish `h₁` using `hP _ _ _ (IsLocalization.Away.lift (S := Localization.Away s) s hu.1) hPs`.

Rewrite `h₁` using `[← RingHom.comp_assoc, IsLocalization.Away.lift_comp]`. Use `⟨s * g (r i), fun hm => (q.isPrime.mem_or_mem hm).elim hs hq, ?_⟩` and prove the remaining obligations. Conclude with `hk i _ _ hu.2 h₁ ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ha i) hi)`. Take `⟨i, hi, hq⟩` from `ht' S g q`. Establish `hu : IsUnit (algebraMap S (Localization.Away (g (r i))) (g (r i)))` using `IsLocalization.Away.algebraMap_isUnit _`.

Use `⟨g (r i), hq, (hJ i _ _ hu).2 fun a ha => ?_⟩` and prove the remaining obligations. Establish `h₁ : ∀ j, ∃ n : ℕ, φ j (r i ^ n * a) = 0` using `fun j => by`. Establish `h₂` using `(hJ i _ _ (IsLocalization.Away.algebraMap_isUnit (φ j (r i)))).1 (hP _ _ _ (algebraMap (T j) (Localization.Away (φ j (r i)))) (hφ j)) ha`. Take `⟨⟨_, n, rfl⟩, hc⟩` from `(IsLocalization.map_eq_zero_iff (Submonoid.powers (φ j (r i))) _ _).1 h₂`. Conclude with `⟨n, by rw [map_mul, map_pow]; exact hc⟩`.

Use `choose n hn using h₁`. Establish `h₃ : r i ^ (∑ j ∈ t, n j) * a ∈ ⨅ i ∈ t, RingHom.ker (φ i)`. Use `(Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => ?_` and prove the remaining obligations. Rewrite using `[← Finset.add_sum_erase t n hj, add_comm, pow_add, _root_.mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (hn j)`.

Establish `h₄ : g (r i ^ (∑ j ∈ t, n j) * a) = 0` using `h h₃`. Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, ← (hu.pow (∑ j ∈ t, n j)).mul_right_eq_zero, ← map_pow, ← map_mul, ← map_pow, ← map_mul, h₄, map_zero]`.
-/
theorem exists_ideal {R : Type} [CommRing R] (P : ∀ (S : Type) [CommRing S], (R →+* S) → Prop)
    (hP : ∀ (S : Type) [CommRing S] (g : R →+* S) (T : Type) [CommRing T] (h : S →+* T), P S g → P T (h.comp g))
    (H : ∀ p : PrimeSpectrum R, ∃ r ∉ p.asIdeal, ∃ I : Ideal R, ∀ (S : Type) [CommRing S] (g : R →+* S),
      IsUnit (g r) → (P S g ↔ I ≤ RingHom.ker g)) :
    ∃ I : Ideal R, ∀ (S : Type) [CommRing S] (g : R →+* S),
      (∀ q : PrimeSpectrum S, ∃ s ∉ q.asIdeal, P _ ((algebraMap S (Localization.Away s)).comp g)) ↔
        I ≤ RingHom.ker g := by
  classical
  choose r hr J hJ using H
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (PrimeSpectrum.basicOpen (r p) : Set (PrimeSpectrum R)))
    (fun p => (PrimeSpectrum.basicOpen (r p)).isOpen) (fun p _ => Set.mem_iUnion.2 ⟨p, hr p⟩)
  have ht' : ∀ (S : Type) [CommRing S] (g : R →+* S) (q : PrimeSpectrum S), ∃ i ∈ t, g (r i) ∉ q.asIdeal := by
    intro S _ g q
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (PrimeSpectrum.comap g q)))
    exact ⟨i, hi, h⟩
  let T := fun i => Localization.Away (r i) ⧸ (J i).map (algebraMap R (Localization.Away (r i)))
  let φ : ∀ i, R →+* T i := fun i => (Ideal.Quotient.mk _).comp (algebraMap R (Localization.Away (r i)))
  have hφ : ∀ i, P _ (φ i) := fun i =>
    (hJ i _ (φ i) ((IsLocalization.Away.algebraMap_isUnit (r i)).map (Ideal.Quotient.mk _))).2 fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have hk : ∀ i (S : Type) [CommRing S] (g : R →+* S), IsUnit (g (r i)) → P S g →
      RingHom.ker (φ i) ≤ RingHom.ker g := by
    intro i S _ g hu hg a ha
    have h₁ : (J i).map (algebraMap R (Localization.Away (r i))) ≤
        RingHom.ker (IsLocalization.Away.lift (S := Localization.Away (r i)) (r i) hu) := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, IsLocalization.Away.lift_eq]
      exact (hJ i S g hu).1 hg hb
    have h₂ := h₁ (Ideal.Quotient.eq_zero_iff_mem.1 ha)
    rwa [RingHom.mem_ker, IsLocalization.Away.lift_eq] at h₂
  refine ⟨⨅ i ∈ t, RingHom.ker (φ i), fun S _ g => ⟨fun h a ha => ?_, fun h q => ?_⟩⟩
  · refine eq_zero_of_away (g a) fun q => ?_
    obtain ⟨s, hs, hPs⟩ := h q
    obtain ⟨i, hi, hq⟩ := ht' S g q
    have hu : IsUnit (algebraMap S (Localization.Away (s * g (r i))) (s * g (r i))) :=
      IsLocalization.Away.algebraMap_isUnit _
    rw [map_mul, IsUnit.mul_iff] at hu
    have h₁ := hP _ _ _ (IsLocalization.Away.lift (S := Localization.Away s) s hu.1) hPs
    rw [← RingHom.comp_assoc, IsLocalization.Away.lift_comp] at h₁
    refine ⟨s * g (r i), fun hm => (q.isPrime.mem_or_mem hm).elim hs hq, ?_⟩
    exact hk i _ _ hu.2 h₁ ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ha i) hi)
  · obtain ⟨i, hi, hq⟩ := ht' S g q
    have hu : IsUnit (algebraMap S (Localization.Away (g (r i))) (g (r i))) :=
      IsLocalization.Away.algebraMap_isUnit _
    refine ⟨g (r i), hq, (hJ i _ _ hu).2 fun a ha => ?_⟩
    have h₁ : ∀ j, ∃ n : ℕ, φ j (r i ^ n * a) = 0 := fun j => by
      have h₂ := (hJ i _ _ (IsLocalization.Away.algebraMap_isUnit (φ j (r i)))).1
        (hP _ _ _ (algebraMap (T j) (Localization.Away (φ j (r i)))) (hφ j)) ha
      obtain ⟨⟨_, n, rfl⟩, hc⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ j (r i))) _ _).1 h₂
      exact ⟨n, by rw [map_mul, map_pow]; exact hc⟩
    choose n hn using h₁
    have h₃ : r i ^ (∑ j ∈ t, n j) * a ∈ ⨅ i ∈ t, RingHom.ker (φ i) := by
      refine (Submodule.mem_iInf _).2 fun j => (Submodule.mem_iInf _).2 fun hj => ?_
      rw [← Finset.add_sum_erase t n hj, add_comm, pow_add, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hn j)
    have h₄ : g (r i ^ (∑ j ∈ t, n j) * a) = 0 := h h₃
    rw [RingHom.mem_ker, RingHom.comp_apply, ← (hu.pow (∑ j ∈ t, n j)).mul_right_eq_zero, ← map_pow,
      ← map_mul, ← map_pow, ← map_mul, h₄, map_zero]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (F : LB X)

def TrivOn (S : Type) [CommRing S] (g : R →+* S) : Prop :=
  Triv (F.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g))))

/- English proof (translation)
The claim follows from `CubeOpen.triv_comp (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom h)) (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])) (pullback.lift_fst _ _ _) H`.
-/
theorem TrivOn.comp (S : Type) [CommRing S] (g : R →+* S) (T : Type) [CommRing T] (h : S →+* T)
    (H : TrivOn f F S g) : TrivOn f F T (h.comp g) :=
  CubeOpen.triv_comp (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom h))
    (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]))
    (pullback.lift_fst _ _ _) H

/- English proof (translation)
Establish `he : IsEmpty (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0})` using `⟨fun x => (inferInstance : IsEmpty (PrimeSpectrum S)).elim ((pullback.snd f (Spec.map (CommRingCat.ofHom g))) x)⟩`. Establish `hs : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0}).Opens, Subsingleton Γ(pullback f (Spec.map (CommRingCat.ofHom g)), U)` using `fun U => by`. Establish `: U = ⊥` using `TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)`. Substitute `this` using the available equality. Use `infer_instance`.

Conclude with `⟨⟨fun _ => 1⟩, fun i j => Units.ext (Subsingleton.elim _ _)⟩`.
-/
theorem trivOn_of_subsingleton (S : Type) [CommRing S] [Subsingleton S] (g : R →+* S) : TrivOn f F S g := by
  have he : IsEmpty (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0}) :=
    ⟨fun x => (inferInstance : IsEmpty (PrimeSpectrum S)).elim
      ((pullback.snd f (Spec.map (CommRingCat.ofHom g))) x)⟩
  have hs : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom g)) : Scheme.{0}).Opens,
      Subsingleton Γ(pullback f (Spec.map (CommRingCat.ofHom g)), U) := fun U => by
    have : U = ⊥ := TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)
    subst this
    infer_instance
  exact ⟨⟨fun _ => 1⟩, fun i j => Units.ext (Subsingleton.elim _ _)⟩

/- English proof (translation)
Establish `hr : ∀ s : S, Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) = (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S))` using `fun s => PrimeSpectrum.localization_away_comap_range (Localization.Away s) s`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨U, hq, t, ht⟩`. Take `⟨_, ⟨s, rfl⟩, hs, hU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (u := U.1) hq U.isOpen`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations.

Establish `ht' : Triv (F.pull ((f' ⁻¹ᵁ U).ι ≫ π))` using `exists_isGen_linComb_of_pull F _ _ _ t ht`. Set `l` to `h.lift (pullback.fst f (Spec.map (CommRingCat.ofHom ((algebraMap S (Localization.Away s)).comp g)))) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])`. Establish `hl : Set.range l ⊆ Set.range (f' ⁻¹ᵁ U).ι`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`.

Apply `hU` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(l ≫ f') y ∈ _`. Rewrite using `[h.lift_snd]`. Conclude with `(hr s).le ⟨_, rfl⟩`. Use `CubeOpen.triv_comp (IsOpenImmersion.lift _ l hl) ?_ ht'` and prove the remaining obligations.

Rewrite using `[IsOpenImmersion.lift_fac_assoc]`. Conclude with `h.lift_fst _ _ _`. Introduce and unpack `⟨s, hs, ht⟩`. Use `⟨PrimeSpectrum.basicOpen s, hs, CubeOpen.triv_pull_pull _ _ ?_⟩` and prove the remaining obligations. Use `haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) := IsOpenImmersion.of_isLocalization s`.

Establish `hsub : Set.range ((f' ⁻¹ᵁ (PrimeSpectrum.basicOpen s)).ι ≫ f') ⊆ Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))))`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[hr]`. Conclude with `y.2`. Use `CubeOpen.triv_comp (pullback.lift _ (IsOpenImmersion.lift _ _ hsub) ?_) (pullback.lift_fst _ _ _) ht` and prove the remaining obligations.

Rewrite using `[CommRingCat.ofHom_comp g, Spec.map_comp, IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, h.w]`.
-/
theorem loc_iff {S : Type} [CommRing S] {g : R →+* S} {X' : Scheme.{0}} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of S)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (q : PrimeSpectrum S) :
    (∃ U : (Spec (CommRingCat.of S)).Opens, q ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔
      ∃ s ∉ q.asIdeal, TrivOn f F _ ((algebraMap S (Localization.Away s)).comp g) := by
  have hr : ∀ s : S, Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) =
      (PrimeSpectrum.basicOpen s : Set (PrimeSpectrum S)) := fun s =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away s) s
  constructor
  · rintro ⟨U, hq, t, ht⟩
    obtain ⟨_, ⟨s, rfl⟩, hs, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (u := U.1) hq U.isOpen
    refine ⟨s, hs, ?_⟩
    have ht' : Triv (F.pull ((f' ⁻¹ᵁ U).ι ≫ π)) := exists_isGen_linComb_of_pull F _ _ _ t ht
    let l := h.lift (pullback.fst f (Spec.map (CommRingCat.ofHom ((algebraMap S (Localization.Away s)).comp g))))
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s))))
      (by rw [pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
    have hl : Set.range l ⊆ Set.range (f' ⁻¹ᵁ U).ι := by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      apply hU
      change (l ≫ f') y ∈ _
      rw [h.lift_snd]
      exact (hr s).le ⟨_, rfl⟩
    refine CubeOpen.triv_comp (IsOpenImmersion.lift _ l hl) ?_ ht'
    rw [IsOpenImmersion.lift_fac_assoc]
    exact h.lift_fst _ _ _
  · rintro ⟨s, hs, ht⟩
    refine ⟨PrimeSpectrum.basicOpen s, hs, CubeOpen.triv_pull_pull _ _ ?_⟩
    haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) :=
      IsOpenImmersion.of_isLocalization s
    have hsub : Set.range ((f' ⁻¹ᵁ (PrimeSpectrum.basicOpen s)).ι ≫ f') ⊆
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) := by
      rintro _ ⟨y, rfl⟩
      rw [hr]
      exact y.2
    refine CubeOpen.triv_comp (pullback.lift _ (IsOpenImmersion.lift _ _ hsub) ?_) (pullback.lift_fst _ _ _) ht
    rw [CommRingCat.ofHom_comp g, Spec.map_comp, IsOpenImmersion.lift_fac_assoc, Category.assoc, Category.assoc, h.w]

/- English proof (translation)
Introduce `hG R _ B _ hB hproj F hF`. Use `haveI := hB.proper`. Use `haveI := hB.geomConnected`. Establish `hP` using `GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj F hF`. Establish `hQ` using `GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj _ (isLB_pw hF (-1))`.

Establish `hC` using `GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)`. Take `⟨I, hI⟩` from `exists_ideal (TrivOn B.hom F) (TrivOn.comp B.hom F) (fun p => by`. Distinguish the cases in `hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}`. Take `⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩` from `hp`. Take `⟨r, I, hr, -, H⟩` from `GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀ h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht`.

Conclude with `⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩`. Take `⟨_, ⟨r, rfl⟩, hr, hU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (Set.mem_compl hp) hC.isOpen_compl`. Use `⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Break down `subsingleton_or_nontrivial S with _ | _` into its components or cases. Conclude with `fun a _ => Subsingleton.elim _ _`.

Take `⟨m, hm⟩` from `Ideal.exists_maximal S`. Use `letI := Ideal.Quotient.field m`. Set `g'` to `(Ideal.Quotient.mk m).comp g`. Use `(hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim` and prove the remaining obligations. Conclude with `⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩`.

Use `haveI : Subsingleton S := subsingleton_of_zero_eq_one ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))`. Conclude with `trivOn_of_subsingleton B.hom F S g)`. Use `⟨I, fun S _ g X' π f' h => ?_⟩` and prove the remaining obligations. Rewrite using `[← hI S g]`. Conclude with `forall_congr' fun q => loc_iff B.hom F h q`.
-/
theorem exists_ideal_locTriv : GlobalFnsSt → ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ F : LB B.left, F.IsLB → ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) → ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧ Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  intro hG R _ B _ hB hproj F hF
  haveI := hB.proper
  haveI := hB.geomConnected
  have hP := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj F hF
  have hQ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ B.hom hB.smooth hproj _ (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := exists_ideal (TrivOn B.hom F) (TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => loc_iff B.hom F h q

end GlobalTheory.TrivRep
