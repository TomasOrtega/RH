import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.FracPts

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Set `f : S →+* R` to `(S.val : S →+* Ω).codRestrict R (fun s => h s s.2)`. Use `⟨(IsLocalRing.maximalIdeal R).comap f, Ideal.IsPrime.comap f, fun s => ?_⟩` and prove the remaining obligations. Establish `hs : (f s : Ω) = (s : Ω)` using `rfl`. Rewrite using `[Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal]`. Prove the components needed by the constructor for the conclusion.

Introduce `hu`. Take `⟨u, hu⟩` from `hu`. Establish `h1 : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1`. Rewrite using `[← Subring.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression.

Establish `hu' : ((u : R) : Ω) = (s : Ω)` using `by rw [hu, hs]`. Rewrite `h1` using `[hu']`. Establish `h0 : (s : Ω) ≠ 0` using `left_ne_zero_of_mul_eq_one h1`. Use `⟨h0, h s s.2, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_eq_of_mul_eq_one_right h1]`.

Conclude with `(((u⁻¹ : Rˣ) : R)).2`. Introduce and unpack `⟨h0, h1, h2⟩`. Use `IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : R) (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(s : Ω) * (s : Ω)⁻¹ = 1`. Conclude with `mul_inv_cancel₀ h0`.
-/
theorem exists_prime_of_subset {k : Type} [CommRing k] [Algebra k Ω] (S : Subalgebra k Ω) (R : Subring Ω)
    (hR : IsLocalRing R) (h : ∀ s ∈ S, s ∈ R) :
    ∃ I : Ideal S, I.IsPrime ∧ ∀ s : S, s ∉ I ↔ ((s : Ω) ≠ 0 ∧ (s : Ω) ∈ R ∧ (s : Ω)⁻¹ ∈ R) := by
  let f : S →+* R := (S.val : S →+* Ω).codRestrict R (fun s => h s s.2)
  refine ⟨(IsLocalRing.maximalIdeal R).comap f, Ideal.IsPrime.comap f, fun s => ?_⟩
  have hs : (f s : Ω) = (s : Ω) := rfl
  rw [Ideal.mem_comap, IsLocalRing.notMem_maximalIdeal]
  constructor
  · intro hu
    obtain ⟨u, hu⟩ := hu
    have h1 : ((u : R) : Ω) * (((u⁻¹ : Rˣ) : R) : Ω) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    have hu' : ((u : R) : Ω) = (s : Ω) := by rw [hu, hs]
    rw [hu'] at h1
    have h0 : (s : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one h1
    refine ⟨h0, h s s.2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact (((u⁻¹ : Rˣ) : R)).2
  · rintro ⟨h0, h1, h2⟩
    refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, h2⟩ : R) (Subtype.ext ?_)
    change (s : Ω) * (s : Ω)⁻¹ = 1
    exact mul_inv_cancel₀ h0

variable {X : Scheme.{0}}

/- English proof (translation)
Establish `: a = s⁻¹ * (s * a)` using `by rw [inv_mul_cancel_left₀ hs.1]`. Rewrite using `[this]`. Conclude with `(regAt ξ p).mul_mem hs.2.2 h`.
-/
theorem mem_regAt_of_unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (h : s * a ∈ regAt ξ p) : a ∈ regAt ξ p := by
  have : a = s⁻¹ * (s * a) := by rw [inv_mul_cancel_left₀ hs.1]
  rw [this]
  exact (regAt ξ p).mul_mem hs.2.2 h

/- English proof (translation)
Use `⟨mul_ne_zero hs.1 ha.1, (regAt ξ p).mul_mem hs.2.1 ha.2.1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv]`. Conclude with `(regAt ξ p).mul_mem hs.2.2 ha.2.2`.
-/
theorem unitAt_mul {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} {s a : Ω} (hs : unitAt ξ p s)
    (ha : unitAt ξ p a) : unitAt ξ p (s * a) := by
  refine ⟨mul_ne_zero hs.1 ha.1, (regAt ξ p).mul_mem hs.2.1 ha.2.1, ?_⟩
  rw [mul_inv]
  exact (regAt ξ p).mul_mem hs.2.2 ha.2.2

variable (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F]
  [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω]

include F in

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply o F Ω]`. Conclude with `(map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)`.
-/
theorem algebraMap_ne_zero {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

/- English proof (translation)
Establish `: Algebra.adjoin o S ≤ (Algebra.adjoin F S).restrictScalars o` using `Algebra.adjoin_le Algebra.subset_adjoin`. Conclude with `fun a ha => this ha`.
-/
theorem adjoin_subset (S : Set Ω) : ∀ a ∈ Algebra.adjoin o S, a ∈ Algebra.adjoin F S := by
  have : Algebra.adjoin o S ≤ (Algebra.adjoin F S).restrictScalars o :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact fun a ha => this ha

/- English proof (translation)
Proceed by induction on `hb using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩`. Consider the case `algebraMap r`. Take `⟨n, d, hd, rfl⟩` from `IsFractionRing.div_surjective (A := o) r`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`.

Use `⟨d, hd0, ?_⟩` and prove the remaining obligations. Establish `hF : algebraMap o F d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd0`. Establish `: algebraMap o Ω d * algebraMap F Ω (algebraMap o F n / algebraMap o F d) = algebraMap o Ω n`. Rewrite using `[IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, mul_div_cancel₀ _ hF, ← IsScalarTower.algebraMap_apply]`. Rewrite using `[this]`.

Conclude with `Subalgebra.algebraMap_mem _ n`. Consider the case `add x y _ _ hx hy`. Take `⟨d, hd, h⟩` from `hx`. Take `⟨e, he, h'⟩` from `hy`. Use `⟨d * e, mul_ne_zero hd he, ?_⟩` and prove the remaining obligations.

Establish `: algebraMap o Ω (d * e) * (x + y) = algebraMap o Ω e * (algebraMap o Ω d * x) + algebraMap o Ω d * (algebraMap o Ω e * y)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `add_mem (mul_mem (Subalgebra.algebraMap_mem _ e) h) (mul_mem (Subalgebra.algebraMap_mem _ d) h')`.

Consider the case `mul x y _ _ hx hy`. Take `⟨d, hd, h⟩` from `hx`. Take `⟨e, he, h'⟩` from `hy`. Use `⟨d * e, mul_ne_zero hd he, ?_⟩` and prove the remaining obligations. Establish `: algebraMap o Ω (d * e) * (x * y) = (algebraMap o Ω d * x) * (algebraMap o Ω e * y)`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `mul_mem h h'`.
-/
theorem exists_mul_mem_adjoin (S : Set Ω) (b : Ω) (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ algebraMap o Ω d * b ∈ Algebra.adjoin o S := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin hx⟩
  | algebraMap r =>
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := o) r
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    refine ⟨d, hd0, ?_⟩
    have hF : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd0
    have : algebraMap o Ω d * algebraMap F Ω (algebraMap o F n / algebraMap o F d) = algebraMap o Ω n := by
      rw [IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, mul_div_cancel₀ _ hF,
        ← IsScalarTower.algebraMap_apply]
    rw [this]
    exact Subalgebra.algebraMap_mem _ n
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x + y) =
        algebraMap o Ω e * (algebraMap o Ω d * x) + algebraMap o Ω d * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ e) h) (mul_mem (Subalgebra.algebraMap_mem _ d) h')
  | mul x y _ _ hx hy =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨e, he, h'⟩ := hy
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    have : algebraMap o Ω (d * e) * (x * y) = (algebraMap o Ω d * x) * (algebraMap o Ω e * y) := by
      rw [map_mul]; ring
    rw [this]
    exact mul_mem h h'

variable {W : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ W}
  {κ : Type} {t : κ → Ω}

/- English proof (translation)
Establish `hF0 : algebraMap o F d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd`. Establish `hmem : ∀ r : F, algebraMap F Ω r ∈ regAt ξ' p'` using `fun r => (hF.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc`. Use `⟨algebraMap_ne_zero o F hd, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply o F Ω]`. Conclude with `hmem _`.

Rewrite using `[IsScalarTower.algebraMap_apply o F Ω, ← map_inv₀]`. Conclude with `hmem _`.
-/
theorem unitAt_algebraMap (hF : CoordTie F ξ' t) {c : κ} {p' : Cpt ξ'} (hc : InChart ξ' t c p') {d : o}
    (hd : d ≠ 0) : unitAt ξ' p' (algebraMap o Ω d) := by
  have hF0 : algebraMap o F d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd
  have hmem : ∀ r : F, algebraMap F Ω r ∈ regAt ξ' p' := fun r =>
    (hF.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  refine ⟨algebraMap_ne_zero o F hd, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_apply o F Ω]
    exact hmem _
  · rw [IsScalarTower.algebraMap_apply o F Ω, ← map_inv₀]
    exact hmem _

/- English proof (translation)
Establish `hB : ∀ b ∈ Algebra.adjoin F (Set.range fun j => t j / t c), b ∈ regAt ξ' p'` using `fun b hb => (hF.ring c hc'.1 b).1 hb p' hc'`. Establish `hA' : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ' p'` using `fun b hb => hB b (adjoin_subset o F _ b hb)`. Establish `hAp : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ p` using `fun b hb => (hA.ring c hc.1 b).1 hb p hc`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Take `⟨s, hs, hsu, hsa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).1 ha`. Conclude with `mem_regAt_of_unitAt_mul ((hu s hs).1 hsu) (hA' _ hsa)`. Introduce `ha`. Take `⟨s, hs, hsu, hsa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization W Ω ξ' F κ t hF c p' hc' a).1 ha`.

Take `⟨d, hd, hds⟩` from `exists_mul_mem_adjoin o F _ s hs`. Take `⟨e, he, hes⟩` from `exists_mul_mem_adjoin o F _ _ hsa`. Establish `hunit : unitAt ξ' p' (algebraMap o Ω e * (algebraMap o Ω d * s))` using `unitAt_mul (unitAt_algebraMap o F hF hc' he) (unitAt_mul (unitAt_algebraMap o F hF hc' hd) hsu)`. Establish `hmemA : algebraMap o Ω e * (algebraMap o Ω d * s) ∈ Algebra.adjoin o (Set.range fun j => t j / t c)` using `mul_mem (Subalgebra.algebraMap_mem _ e) hds`. Use `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).2 ⟨_, hmemA, (hu _ hmemA).2 hunit, ?_⟩` and prove the remaining obligations.

Establish `: algebraMap o Ω e * (algebraMap o Ω d * s) * a = algebraMap o Ω d * (algebraMap o Ω e * (s * a))` using `by ring`. Rewrite using `[this]`. Conclude with `mul_mem (Subalgebra.algebraMap_mem _ d) hes`.
-/
theorem regAt_eq_of_units (hA : CoordTie o ξ t) (hF : CoordTie F ξ' t) {c : κ} {p : Cpt ξ} {p' : Cpt ξ'}
    (hc : InChart ξ t c p) (hc' : InChart ξ' t c p')
    (hu : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), unitAt ξ p s ↔ unitAt ξ' p' s) :
    regAt ξ p = regAt ξ' p' := by
  have hB : ∀ b ∈ Algebra.adjoin F (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    (hF.ring c hc'.1 b).1 hb p' hc'
  have hA' : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ' p' := fun b hb =>
    hB b (adjoin_subset o F _ b hb)
  have hAp : ∀ b ∈ Algebra.adjoin o (Set.range fun j => t j / t c), b ∈ regAt ξ p := fun b hb =>
    (hA.ring c hc.1 b).1 hb p hc
  ext a
  constructor
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).1 ha
    exact mem_regAt_of_unitAt_mul ((hu s hs).1 hsu) (hA' _ hsa)
  · intro ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization W Ω ξ' F κ t hF c p' hc' a).1 ha
    obtain ⟨d, hd, hds⟩ := exists_mul_mem_adjoin o F _ s hs
    obtain ⟨e, he, hes⟩ := exists_mul_mem_adjoin o F _ _ hsa
    have hunit : unitAt ξ' p' (algebraMap o Ω e * (algebraMap o Ω d * s)) :=
      unitAt_mul (unitAt_algebraMap o F hF hc' he) (unitAt_mul (unitAt_algebraMap o F hF hc' hd) hsu)
    have hmemA : algebraMap o Ω e * (algebraMap o Ω d * s) ∈
        Algebra.adjoin o (Set.range fun j => t j / t c) :=
      mul_mem (Subalgebra.algebraMap_mem _ e) hds
    refine (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ o κ t hA c p hc a).2
      ⟨_, hmemA, (hu _ hmemA).2 hunit, ?_⟩
    have : algebraMap o Ω e * (algebraMap o Ω d * s) * a =
        algebraMap o Ω d * (algebraMap o Ω e * (s * a)) := by ring
    rw [this]
    exact mul_mem (Subalgebra.algebraMap_mem _ d) hes

/- English proof (translation)
Introduce `o F _ _ _ _ _ Ω _ _ _ _ X W ξ ξ' κ t hA hF`. Prove the components needed by the constructor for the conclusion. Introduce `p'`. Take `⟨c, hc⟩` from `hF.cover p'`. Establish `hloc : IsLocalRing (regAt ξ' p')` using `(regAt_isLocalRing_isFractionRing_stalk W Ω ξ' hF.gen p').1`.

Establish `hsub : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), s ∈ regAt ξ' p'` using `fun s hs => (hF.ring c hc.1 s).1 (adjoin_subset o F _ s hs) p' hc`. Take `⟨I, hI, hIu⟩` from `exists_prime_of_subset _ (regAt ξ' p') hloc hsub`. Take `⟨p, ⟨hp, hpu⟩, -⟩` from `GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ o κ t hA c hc.1 I hI`. Use `⟨p, regAt_eq_of_units o F hA hF hp hc fun s hs => ?_⟩` and prove the remaining obligations. Conclude with `(hpu ⟨s, hs⟩).symm.trans (hIu ⟨s, hs⟩)`.

Introduce `p hd`. Take `⟨c, hc⟩` from `hA.cover p`. Establish `hloc : IsLocalRing (regAt ξ p)` using `(regAt_isLocalRing_isFractionRing_stalk X Ω ξ hA.gen p).1`. Establish `hsub : ∀ s ∈ Algebra.adjoin F (Set.range fun j => t j / t c), s ∈ regAt ξ p` using `fun s hs => by`. Take `⟨d, hd0, hds⟩` from `exists_mul_mem_adjoin o F _ s hs`.

Conclude with `mem_regAt_of_unitAt_mul (hd d hd0) ((hA.ring c hc.1 _).1 hds p hc)`. Take `⟨I, hI, hIu⟩` from `exists_prime_of_subset _ (regAt ξ p) hloc hsub`. Take `⟨p', ⟨hp', hpu⟩, -⟩` from `GlobalTheory.T.prime_chart_existsUnique_point W Ω ξ' F κ t hF c hc.1 I hI`. Use `⟨p', regAt_eq_of_units o F hA hF hc hp' fun s hs => ?_⟩` and prove the remaining obligations. Establish `hsB` using `adjoin_subset o F _ s hs`.

Conclude with `(hIu ⟨s, hsB⟩).symm.trans (hpu ⟨s, hsB⟩)`.
-/
theorem regAt_frac :
    ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type) [Field Ω]
      [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (X W : Scheme.{0}) (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ W) (κ : Type)
      (t : κ → Ω), CoordTie o ξ t → CoordTie F ξ' t →
      (∀ p' : Cpt ξ', ∃ p : Cpt ξ, regAt ξ p = regAt ξ' p') ∧
        ∀ p : Cpt ξ, (∀ d : o, d ≠ 0 → unitAt ξ p (algebraMap o Ω d)) → ∃ p' : Cpt ξ', regAt ξ p = regAt ξ' p' := by
  intro o F _ _ _ _ _ Ω _ _ _ _ X W ξ ξ' κ t hA hF
  constructor
  · intro p'
    obtain ⟨c, hc⟩ := hF.cover p'
    have hloc : IsLocalRing (regAt ξ' p') := (regAt_isLocalRing_isFractionRing_stalk W Ω ξ' hF.gen p').1
    have hsub : ∀ s ∈ Algebra.adjoin o (Set.range fun j => t j / t c), s ∈ regAt ξ' p' := fun s hs =>
      (hF.ring c hc.1 s).1 (adjoin_subset o F _ s hs) p' hc
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ' p') hloc hsub
    obtain ⟨p, ⟨hp, hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ o κ t hA c hc.1 I hI
    refine ⟨p, regAt_eq_of_units o F hA hF hp hc fun s hs => ?_⟩
    exact (hpu ⟨s, hs⟩).symm.trans (hIu ⟨s, hs⟩)
  · intro p hd
    obtain ⟨c, hc⟩ := hA.cover p
    have hloc : IsLocalRing (regAt ξ p) := (regAt_isLocalRing_isFractionRing_stalk X Ω ξ hA.gen p).1
    have hsub : ∀ s ∈ Algebra.adjoin F (Set.range fun j => t j / t c), s ∈ regAt ξ p := fun s hs => by
      obtain ⟨d, hd0, hds⟩ := exists_mul_mem_adjoin o F _ s hs
      exact mem_regAt_of_unitAt_mul (hd d hd0) ((hA.ring c hc.1 _).1 hds p hc)
    obtain ⟨I, hI, hIu⟩ := exists_prime_of_subset _ (regAt ξ p) hloc hsub
    obtain ⟨p', ⟨hp', hpu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point W Ω ξ' F κ t hF c hc.1 I hI
    refine ⟨p', regAt_eq_of_units o F hA hF hc hp' fun s hs => ?_⟩
    have hsB := adjoin_subset o F _ s hs
    exact (hIu ⟨s, hsB⟩).symm.trans (hpu ⟨s, hsB⟩)

end GlobalTheory.CompanionTheory.Ar.SncBase.FracPts
