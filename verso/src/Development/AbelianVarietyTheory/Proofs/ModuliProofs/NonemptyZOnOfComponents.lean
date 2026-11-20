import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaConstantsUniqueUpToUnit
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaPointsVanishingIdealRadicalHomogeneous
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCoverStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamilyModel

/- English proof (translation)
Establish `hmin : p ∈ minimalPrimes R` using `⟨⟨hp, bot_le⟩, fun q hq hle => (hm q hq.1 hle).ge⟩`. Establish `hfin` using `(minimalPrimes.finite_of_isNoetherianRing R).subset (Set.diff_subset (t := {p}))`. Establish `hnle : ¬ (hfin.toFinset.inf id ≤ p)`. Rewrite using `[Ideal.IsPrime.inf_le' hp]`. Introduce and unpack `⟨q, hq, hle⟩`.

Rewrite `hq` using `[Set.Finite.mem_toFinset]`. Conclude with `hq.2 (hm q hq.1.1.1 hle)`. Take `⟨f, hf, hfp⟩` from `SetLike.not_le_iff_exists.1 hnle`. Establish `hz : ∀ a ∈ p, f * a = 0` using `fun a ha => by`. Establish `: f * a ∈ sInf (minimalPrimes R)` using `Ideal.mem_sInf.2 fun {q} hq => by`.

Distinguish the cases in `h : q = p`. Conclude with `h ▸ p.mul_mem_left f ha`. Conclude with `q.mul_mem_right a ((Finset.inf_le (f := id) (hfin.mem_toFinset.2 ⟨hq, h⟩) : _ ≤ q) hf)`. Rewrite `this` using `[minimalPrimes, Ideal.sInf_minimalPrimes]`. Conclude with `IsNilpotent.eq_zero (mem_nilradical.1 this)`.

Establish `hk : ∀ a, algebraMap R (Localization.Away f) a = 0 ↔ a ∈ p` using `fun a => by`. Rewrite using `[IsLocalization.map_eq_zero_iff (Submonoid.powers f)]`. Use `⟨?_, fun ha => ⟨⟨f, Submonoid.mem_powers f⟩, hz a ha⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨⟨_, k, rfl⟩, h⟩`. Conclude with `(hp.mem_or_mem (h ▸ p.zero_mem)).resolve_left fun h => hfp (hp.mem_of_pow_mem k h)`.

Establish `: Nontrivial (Localization.Away f)` using `⟨1, 0, fun h => hp.one_notMem ((hk 1).1 (by rw [map_one, h]))⟩`. Establish `: NoZeroDivisors (Localization.Away f)` using `⟨fun {x y} h => by`. Take `⟨a, s, rfl⟩` from `IsLocalization.exists_mk'_eq (Submonoid.powers f) x`. Take `⟨b, t, rfl⟩` from `IsLocalization.exists_mk'_eq (Submonoid.powers f) y`. Rewrite `h` using `[← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff, ← IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f), hk]`.

Simplify using `only [IsLocalization.mk'_eq_zero_iff, ← IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f), hk]`. Conclude with `hp.mem_or_mem h⟩`. Conclude with `⟨f, hfp, NoZeroDivisors.to_isDomain _⟩`.
-/
theorem exists_isDomain_away {R : Type} [CommRing R] [IsNoetherianRing R] [_root_.IsReduced R] (p : Ideal R) [hp : p.IsPrime]
    (hm : ∀ q : Ideal R, q.IsPrime → q ≤ p → q = p) : ∃ f ∉ p, IsDomain (Localization.Away f) := by
  have hmin : p ∈ minimalPrimes R := ⟨⟨hp, bot_le⟩, fun q hq hle => (hm q hq.1 hle).ge⟩
  have hfin := (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.diff_subset (t := {p}))
  have hnle : ¬ (hfin.toFinset.inf id ≤ p) := by
    rw [Ideal.IsPrime.inf_le' hp]
    rintro ⟨q, hq, hle⟩
    rw [Set.Finite.mem_toFinset] at hq
    exact hq.2 (hm q hq.1.1.1 hle)
  obtain ⟨f, hf, hfp⟩ := SetLike.not_le_iff_exists.1 hnle
  have hz : ∀ a ∈ p, f * a = 0 := fun a ha => by
    have : f * a ∈ sInf (minimalPrimes R) := Ideal.mem_sInf.2 fun {q} hq => by
      by_cases h : q = p
      · exact h ▸ p.mul_mem_left f ha
      · exact q.mul_mem_right a ((Finset.inf_le (f := id) (hfin.mem_toFinset.2 ⟨hq, h⟩) : _ ≤ q) hf)
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at this
    exact IsNilpotent.eq_zero (mem_nilradical.1 this)
  have hk : ∀ a, algebraMap R (Localization.Away f) a = 0 ↔ a ∈ p := fun a => by
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers f)]
    refine ⟨?_, fun ha => ⟨⟨f, Submonoid.mem_powers f⟩, hz a ha⟩⟩
    rintro ⟨⟨_, k, rfl⟩, h⟩
    exact (hp.mem_or_mem (h ▸ p.zero_mem)).resolve_left fun h => hfp (hp.mem_of_pow_mem k h)
  have : Nontrivial (Localization.Away f) := ⟨1, 0, fun h => hp.one_notMem ((hk 1).1 (by rw [map_one, h]))⟩
  have : NoZeroDivisors (Localization.Away f) := ⟨fun {x y} h => by
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) x
    obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) y
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff,
      ← IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f), hk] at h
    simp only [IsLocalization.mk'_eq_zero_iff, ← IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f), hk]
    exact hp.mem_or_mem h⟩
  exact ⟨f, hfp, NoZeroDivisors.to_isDomain _⟩

/- English proof (translation)
The claim follows from `have : Module.Flat o R := RingHom.flat_algebraMap_iff.1 h FaithfulSMul.algebraMap_injective o R`.
-/
theorem injective_of_flat {o R : Type} [CommRing o] [IsDomain o] [CommRing R] [Nontrivial R] [Algebra o R]
    (h : (algebraMap o R).Flat) : Function.Injective (algebraMap o R) :=
  have : Module.Flat o R := RingHom.flat_algebraMap_iff.1 h
  FaithfulSMul.algebraMap_injective o R

/- English proof (translation)
The claim follows from `(Spec.map_comp (CommRingCat.ofHom y) (CommRingCat.ofHom φ)).symm`.
-/
theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (y : R →+* R') (φ : R' →+* R'') :
    spMap φ ≫ spMap y = spMap (φ.comp y) := (Spec.map_comp (CommRingCat.ofHom y) (CommRingCat.ofHom φ)).symm

/- English proof (translation)
Take `⟨β, hβ⟩` from `Spec.map_surjective (x ≫ s)`. Take `⟨p, rfl⟩` from `hx`. Establish `hft : β.hom.FiniteType`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hβ]`. Use `infer_instance`.

Use `letI : Algebra o R₀ := β.hom.toAlgebra`. Establish `: Algebra.FiniteType o R₀` using `hft`. Establish `: IsNoetherianRing R₀` using `Algebra.FiniteType.isNoetherianRing o R₀`. Establish `: IsReduced (Sp R₀)` using `isReduced_of_isOpenImmersion x`. Establish `: _root_.IsReduced R₀` using `(affine_isReduced_iff (CommRingCat.of R₀)).1 this`.

Take `⟨f, hf, hd⟩` from `exists_isDomain_away (show PrimeSpectrum R₀ from p).asIdeal fun q hq hle => by`. Establish `h1 : (show Sp R₀ from (⟨q, hq⟩ : PrimeSpectrum R₀)) ⤳ p` using `(PrimeSpectrum.le_iff_specializes _ _).1 hle`. Conclude with `congrArg PrimeSpectrum.asIdeal (x.isOpenEmbedding.injective (eq_of_specializes_of_mem_genericPoints hξ (h1.map x.continuous)))`. Set `L` to `Localization.Away f`. Set `Ω` to `FractionRing L`.

Set `j` to `IsScalarTower.toAlgHom o L Ω`. Set `e : L ≃ₐ[o] j.range` to `AlgEquiv.ofInjective j (IsFractionRing.injective L Ω)`. Establish `hiso : IsIso (spMap (e : L →+* j.range))`. Establish `: IsIso (CommRingCat.ofHom (e : L →+* j.range))` using `e.toRingEquiv.toCommRingCatIso.isIso_hom`. Use `infer_instance`.

Establish `ho : IsOpenImmersion (spMap ((e : L →+* j.range).comp (algebraMap R₀ L)) ≫ x)`. Rewrite using `[← spMap_comp]`. Use `infer_instance`. Establish `hs : (spMap ((e : L →+* j.range).comp (algebraMap R₀ L)) ≫ x) ≫ s = spMap (algebraMap o j.range)`. Rewrite using `[Category.assoc, ← hβ]`.

Use `(spMap_comp β.hom _).trans (congrArg spMap (RingHom.ext fun a => ?_))` and prove the remaining obligations. Conclude with `e.commutes a`. Use `⟨Ω, inferInstance, inferInstance, j.range, _, ho, ?_, hs, ?_, fun z => ?_, ?_⟩` and prove the remaining obligations. Take `⟨q, hq⟩` from `(PrimeSpectrum.localization_away_comap_range L f).ge hf`. Take `⟨q', rfl⟩` from `(spMap (e : L →+* j.range)).surjective q`.

Use `⟨q', ?_⟩` and prove the remaining obligations. Rewrite using `[← spMap_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Conclude with `congrArg x hq`. Establish `: Algebra.FiniteType o L` using `Algebra.FiniteType.trans (S := R₀) inferInstance inferInstance`. Conclude with `(Subalgebra.fg_iff_finiteType _).2 (this.equiv e)`.

Take `⟨a, c, -, rfl⟩` from `IsFractionRing.div_surjective (A := L) z`. Conclude with `⟨_, ⟨a, rfl⟩, _, ⟨c, rfl⟩, rfl⟩`. Establish `hfl : Flat (spMap (algebraMap o j.range))` using `by rw [← hs]; infer_instance`. Establish `h2 : (algebraMap o j.range).Flat` using `(HasRingHomProperty.Spec_iff (P := @Flat)).1 hfl`. Establish `h3` using `injective_of_flat h2`.

Conclude with `fun a b h => h3 (Subtype.ext h)`.
-/
theorem exists_integral_chart {o : Type} [CommRing o] [IsDomain o] [IsNoetherianRing o] {X : Scheme.{0}} [IsReduced X]
    (s : X ⟶ Sp o) [LocallyOfFiniteType s] [Flat s] {ξ : X} (hξ : ξ ∈ genericPoints X)
    {R₀ : Type} [CommRing R₀] (x : Sp R₀ ⟶ X) [IsOpenImmersion x] (hx : ξ ∈ Set.range x) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra o Ω) (R : Subalgebra o Ω) (φ : R₀ →+* R),
      IsOpenImmersion (spMap φ ≫ x) ∧ ξ ∈ Set.range (spMap φ ≫ x) ∧ (spMap φ ≫ x) ≫ s = spMap (algebraMap o R) ∧ R.FG ∧
      (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ Function.Injective (algebraMap o Ω) := by
  obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ s)
  obtain ⟨p, rfl⟩ := hx
  have hft : β.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hβ]; infer_instance
  letI : Algebra o R₀ := β.hom.toAlgebra
  have : Algebra.FiniteType o R₀ := hft
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing o R₀
  have : IsReduced (Sp R₀) := isReduced_of_isOpenImmersion x
  have : _root_.IsReduced R₀ := (affine_isReduced_iff (CommRingCat.of R₀)).1 this
  obtain ⟨f, hf, hd⟩ := exists_isDomain_away (show PrimeSpectrum R₀ from p).asIdeal fun q hq hle => by
    have h1 : (show Sp R₀ from (⟨q, hq⟩ : PrimeSpectrum R₀)) ⤳ p := (PrimeSpectrum.le_iff_specializes _ _).1 hle
    exact congrArg PrimeSpectrum.asIdeal
      (x.isOpenEmbedding.injective (eq_of_specializes_of_mem_genericPoints hξ (h1.map x.continuous)))
  let L := Localization.Away f
  let Ω := FractionRing L
  let j := IsScalarTower.toAlgHom o L Ω
  let e : L ≃ₐ[o] j.range := AlgEquiv.ofInjective j (IsFractionRing.injective L Ω)
  have hiso : IsIso (spMap (e : L →+* j.range)) := by
    have : IsIso (CommRingCat.ofHom (e : L →+* j.range)) := e.toRingEquiv.toCommRingCatIso.isIso_hom
    infer_instance
  have ho : IsOpenImmersion (spMap ((e : L →+* j.range).comp (algebraMap R₀ L)) ≫ x) := by
    rw [← spMap_comp]; infer_instance
  have hs : (spMap ((e : L →+* j.range).comp (algebraMap R₀ L)) ≫ x) ≫ s = spMap (algebraMap o j.range) := by
    rw [Category.assoc, ← hβ]
    refine (spMap_comp β.hom _).trans (congrArg spMap (RingHom.ext fun a => ?_))
    exact e.commutes a
  refine ⟨Ω, inferInstance, inferInstance, j.range, _, ho, ?_, hs, ?_, fun z => ?_, ?_⟩
  · obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range L f).ge hf
    obtain ⟨q', rfl⟩ := (spMap (e : L →+* j.range)).surjective q
    refine ⟨q', ?_⟩
    rw [← spMap_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg x hq
  · have : Algebra.FiniteType o L := Algebra.FiniteType.trans (S := R₀) inferInstance inferInstance
    exact (Subalgebra.fg_iff_finiteType _).2 (this.equiv e)
  · obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := L) z
    exact ⟨_, ⟨a, rfl⟩, _, ⟨c, rfl⟩, rfl⟩
  · have hfl : Flat (spMap (algebraMap o j.range)) := by rw [← hs]; infer_instance
    have h2 : (algebraMap o j.range).Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1 hfl
    have h3 := injective_of_flat h2
    exact fun a b h => h3 (Subtype.ext h)

/- English proof (translation)
Introduce `F hF`. Establish `key : ∀ (e : ℕ) (P : MvPolynomial σ o), P.IsHomogeneous e → MvPolynomial.eval₂ β (fun a => c * v a) P = c ^ e * MvPolynomial.eval₂ β v P` using `fun e P hP => by`. Rewrite using `[MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `h1 : ∑ i ∈ d.support, d i = e`.

Use `hP (MvPolynomial.mem_support_iff.1 hd)` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]`.

Use `Finset.sum_eq_zero fun e _ => ?_` and prove the remaining obligations. Rewrite using `[key e _ (MvPolynomial.homogeneousComponent_isHomogeneous e F), hv _ (hI F hF e), mul_zero]`.
-/
theorem eval₂_mul_eq_zero {o R σ : Type} [CommRing o] [CommRing R] {I : Ideal (MvPolynomial σ o)}
    (hI : ∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) (β : o →+* R) {v : σ → R}
    (hv : ∀ F ∈ I, MvPolynomial.eval₂ β v F = 0) (c : R) : ∀ F ∈ I, MvPolynomial.eval₂ β (fun a => c * v a) F = 0 := by
  intro F hF
  have key : ∀ (e : ℕ) (P : MvPolynomial σ o), P.IsHomogeneous e →
      MvPolynomial.eval₂ β (fun a => c * v a) P = c ^ e * MvPolynomial.eval₂ β v P := fun e P hP => by
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have h1 : ∑ i ∈ d.support, d i = e := by
      have := hP (MvPolynomial.mem_support_iff.1 hd)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h1]
    ring
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [key e _ (MvPolynomial.homogeneousComponent_isHomogeneous e F), hv _ (hI F hF e), mul_zero]

/- English proof (translation)
Use `set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)}) with hK`. Establish `hI` using `(GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1`. Set `ρ : R →+* Ω` to `R.val.toRingHom`. Establish `hx : (spMap ρ ≫ i) ≫ F.s = spMap (algebraMap o Ω)`. Rewrite using `[Category.assoc, hi, spMap_comp]`.

Both sides reduce to the same expression. Establish `hvΩ` using `T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ _ F.univ R Ω ρ i v hv`. Take `⟨v', hv', he, hc⟩` from `F.loc Ω _ _ hx`. Take `⟨u, hu⟩` from `ThetaUniq.exists_unit_local h₁.globalFns F.univ _ hvΩ hv'`. Take `⟨c₀, hc₀⟩` from `hc ⊥ Ideal.isPrime_bot 0`.

Take `⟨a₀, ha₀⟩ : ∃ a₀, v' a₀ ≠ 0` from `⟨_, hc₀⟩`. Set `w : GlobalTheory.ZM.Ix g (N' ^ 2) → K` to `fun a => ⟨v a / v a₀, Subfield.subset_closure (Or.inr ⟨a, a₀, rfl⟩)⟩`. Establish `hw : ∀ a, K.subtype (w a) = (v' a₀)⁻¹ * v' a` using `fun a => by`. Rewrite using `[hu a, hu a₀]`. Use `u.ne_zero` as an intermediate fact.

Use `show (v a : Ω) / v a₀ = (u * (v a₀ : Ω))⁻¹ * (u * (v a : Ω))`. Rewrite using `[mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel₀ this, _root_.one_mul, div_eq_inv_mul]`. Set `β : o →+* K` to `(algebraMap o Ω).codRestrict K fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)`. Establish `hβ : K.subtype.comp β = algebraMap o Ω` using `rfl`. Establish `he'` using `eval₂_mul_eq_zero hI _ he (v' a₀)⁻¹`.

Establish `hc' : ∀ a, ∃ c, (v' a₀)⁻¹ * v' (a + (N' / n) • c) ≠ 0` using `fun a => (hc ⊥ Ideal.isPrime_bot a).imp fun c h => mul_ne_zero (inv_ne_zero ha₀) h`. Establish `mΩ : InMM n N' (thIdeal em C) (algebraMap o Ω) (fun a => (v' a₀)⁻¹ * v' a)` using `⟨he', fun q hq a => by rw [Ideal.eq_bot_of_prime q]; exact hc' a⟩`. Establish `mK : InMM n N' (thIdeal em C) β w`. Use `⟨fun P hP => K.subtype.injective ?_, fun q hq a => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_comp_left, map_zero, hβ, show K.subtype ∘ w = _ from funext hw]`.

Conclude with `he' P hP`. Rewrite using `[Ideal.eq_bot_of_prime q]`. Conclude with `(hc' a).imp fun c h h0 => h (by rw [← hw, Ideal.mem_bot.1 h0, map_zero])`. Take `⟨y, ⟨hy, hty⟩, -⟩` from `F.pts K β w mK`. Establish `hxy : spMap K.subtype ≫ y = spMap ρ ≫ i`.

Use `(F.pts Ω _ _ mΩ).unique ⟨?_, ?_⟩ ⟨hx, ThetaClosed.hasTh_unit_mul F.univ (Units.mk0 _ (inv_ne_zero ha₀)) hv'⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hy, spMap_comp, hβ]`. Use `T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ _ F.univ K Ω K.subtype y w hty` as an intermediate fact. Simplify `this` using `only [hw]`. Establish `hle : Set.range y ⊆ Set.range i`.

Introduce and unpack `_ ⟨p, rfl⟩`. Set `q : Sp Ω` to `(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)`. Take `rfl : p = spMap K.subtype q` from `Subsingleton.elim (α := PrimeSpectrum K) _ _`. Conclude with `⟨spMap ρ q, by rw [← Scheme.Hom.comp_apply, ← hxy, Scheme.Hom.comp_apply]⟩`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (IsOpenImmersion.lift i y hle)`.

Establish `h3 : K.subtype.comp ψ.hom = ρ`. Establish `h4 : spMap (K.subtype.comp ψ.hom) = spMap ρ`. Rewrite using `[← cancel_mono i, ← hxy, ← spMap_comp, Category.assoc]`. Use `congr 1`. Conclude with `(congrArg (· ≫ i) hψ).trans (IsOpenImmersion.lift_fac _ _ _)`.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h4)`. Establish `h5 : ∀ a ∈ R, a ∈ K` using `fun a ha => by`. Establish `: a = (ψ.hom ⟨a, ha⟩ : K)`. Establish `h6` using `(DFunLike.congr_fun h3 (⟨a, ha⟩ : R)).symm`. Conclude with `h6`.

Rewrite using `[this]`. Conclude with `Subtype.property _`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨a, ha, c, hc, rfl⟩` from `hR z`. Conclude with `K.div_mem (h5 a ha) (h5 c hc)`.
-/
theorem closure_ratios_eq_top (h₁ : Out.Laws) (h₂ : Out.Laws2) {o : Type} [CommRing o] {g n N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {em : o →+* ℂ} (hem : Function.Injective em) {C : TObj g (N' ^ 2) J b (spMap em) → Prop}
    (F : ThetaFam n em C) {Ω : Type} [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (i : Sp R ⟶ F.MM) [IsOpenImmersion i]
    (hi : i ≫ F.s = spMap (algebraMap o R)) (hR : ∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c)
    (v : GlobalTheory.ZM.Ix g (N' ^ 2) → R) (hv : F.univ.HasTh i v) :
    Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)}) = ⊤ := by
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)}) with hK
  have hI := (GlobalTheory.ZM.ThIdeal.thIdeal_radical_homogeneous_torsionFree o g N' J b em C hem).2.1
  let ρ : R →+* Ω := R.val.toRingHom
  have hx : (spMap ρ ≫ i) ≫ F.s = spMap (algebraMap o Ω) := by
    rw [Category.assoc, hi, spMap_comp]; rfl
  have hvΩ := T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ _ F.univ R Ω ρ i v hv
  obtain ⟨v', hv', he, hc⟩ := F.loc Ω _ _ hx
  obtain ⟨u, hu⟩ := ThetaUniq.exists_unit_local h₁.globalFns F.univ _ hvΩ hv'
  obtain ⟨c₀, hc₀⟩ := hc ⊥ Ideal.isPrime_bot 0
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, v' a₀ ≠ 0 := ⟨_, hc₀⟩
  let w : GlobalTheory.ZM.Ix g (N' ^ 2) → K := fun a => ⟨v a / v a₀, Subfield.subset_closure (Or.inr ⟨a, a₀, rfl⟩)⟩
  have hw : ∀ a, K.subtype (w a) = (v' a₀)⁻¹ * v' a := fun a => by
    rw [hu a, hu a₀]
    have := u.ne_zero
    show (v a : Ω) / v a₀ = (u * (v a₀ : Ω))⁻¹ * (u * (v a : Ω))
    rw [mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel₀ this, _root_.one_mul, div_eq_inv_mul]
  let β : o →+* K := (algebraMap o Ω).codRestrict K fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  have hβ : K.subtype.comp β = algebraMap o Ω := rfl
  have he' := eval₂_mul_eq_zero hI _ he (v' a₀)⁻¹
  have hc' : ∀ a, ∃ c, (v' a₀)⁻¹ * v' (a + (N' / n) • c) ≠ 0 := fun a =>
    (hc ⊥ Ideal.isPrime_bot a).imp fun c h => mul_ne_zero (inv_ne_zero ha₀) h
  have mΩ : InMM n N' (thIdeal em C) (algebraMap o Ω) (fun a => (v' a₀)⁻¹ * v' a) :=
    ⟨he', fun q hq a => by rw [Ideal.eq_bot_of_prime q]; exact hc' a⟩
  have mK : InMM n N' (thIdeal em C) β w := by
    refine ⟨fun P hP => K.subtype.injective ?_, fun q hq a => ?_⟩
    · rw [MvPolynomial.eval₂_comp_left, map_zero, hβ, show K.subtype ∘ w = _ from funext hw]
      exact he' P hP
    · rw [Ideal.eq_bot_of_prime q]
      exact (hc' a).imp fun c h h0 => h (by rw [← hw, Ideal.mem_bot.1 h0, map_zero])
  obtain ⟨y, ⟨hy, hty⟩, -⟩ := F.pts K β w mK
  have hxy : spMap K.subtype ≫ y = spMap ρ ≫ i := by
    refine (F.pts Ω _ _ mΩ).unique ⟨?_, ?_⟩ ⟨hx, ThetaClosed.hasTh_unit_mul F.univ (Units.mk0 _ (inv_ne_zero ha₀)) hv'⟩
    · rw [Category.assoc, hy, spMap_comp, hβ]
    · have := T.hasThetaConstants_ring_baseChange h₂ o g N' J b _ _ F.univ K Ω K.subtype y w hty
      simpa only [hw] using this
  have hle : Set.range y ⊆ Set.range i := by
    rintro _ ⟨p, rfl⟩
    let q : Sp Ω := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Ω)
    obtain rfl : p = spMap K.subtype q := Subsingleton.elim (α := PrimeSpectrum K) _ _
    exact ⟨spMap ρ q, by rw [← Scheme.Hom.comp_apply, ← hxy, Scheme.Hom.comp_apply]⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift i y hle)
  have h3 : K.subtype.comp ψ.hom = ρ := by
    have h4 : spMap (K.subtype.comp ψ.hom) = spMap ρ := by
      rw [← cancel_mono i, ← hxy, ← spMap_comp, Category.assoc]
      congr 1
      exact (congrArg (· ≫ i) hψ).trans (IsOpenImmersion.lift_fac _ _ _)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h4)
  have h5 : ∀ a ∈ R, a ∈ K := fun a ha => by
    have : a = (ψ.hom ⟨a, ha⟩ : K) := by
      have h6 := (DFunLike.congr_fun h3 (⟨a, ha⟩ : R)).symm
      exact h6
    rw [this]; exact Subtype.property _
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨a, ha, c, hc, rfl⟩ := hR z
  exact K.div_mem (h5 a ha) (h5 c hc)

/- English proof (translation)
Take `⟨u, hu⟩` from `tObj_pull o g k J b S S' s s' f t hf`. Choose the witnesses or unpack the hypotheses as in `⟨t₀, ⟨m⟩⟩ : ∃ t₀ : SAB H S', Nonempty (SABMap t₀ τ f) := by`. Take `⟨_, _, _, _, _, m, -⟩` from `sabPull Out.CubePf.cubePull f τ`. Conclude with `⟨_, ⟨m⟩⟩`. Establish `hu'` using `hu`.

Take `⟨ψ, hψ, hLu, -⟩` from `hu'`. Take `⟨e, he, hc⟩` from `grpPullback_iso ((m.cart.comp (isGrpPullback_of_iso φ)).congr (Category.comp_id _) rfl) hψ`. Establish `hm : LBIso t₀.PP.L (τ.PP.L.pull m.φ)` using `m.lin.imp fun _ h => h.1`. Use `⟨u, t₀, m, e, hu, he, ?_⟩` and prove the remaining obligations. Use `LBIso.trans t₀.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB u.isLB _) hm ?_` and prove the remaining obligations.

Conclude with `LBIso.trans (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (pull_isLB u.isLB _) (GenSpread.lbIso_pull_of_lbIso hL _ rfl) (GenSpread.lbIso_pull_of_lbIso hLu _ hc.symm).symm`.
-/
theorem exists_pull {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {o : Type} [CommRing o] {g k : ℕ}
    {J : Type} {b : TBase o k} {S S' : Scheme.{0}} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} (t : TObj g k J b s) (τ : SAB H S)
    (φ : τ.G ≅ t.A) [IsMonHom φ.hom] (hL : LBIso τ.PP.L (t.L.pull φ.hom.left)) (f : S' ⟶ S) (hf : f ≫ s = s') :
    ∃ (u : TObj g k J b s') (t₀ : SAB H S') (_ : SABMap t₀ τ f) (e : t₀.G ≅ u.A),
      TMap u t f ∧ IsMonHom e.hom ∧ LBIso t₀.PP.L (u.L.pull e.hom.left) := by
  obtain ⟨u, hu⟩ := tObj_pull o g k J b S S' s s' f t hf
  obtain ⟨t₀, ⟨m⟩⟩ : ∃ t₀ : SAB H S', Nonempty (SABMap t₀ τ f) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f τ
    exact ⟨_, ⟨m⟩⟩
  have hu' := hu
  obtain ⟨ψ, hψ, hLu, -⟩ := hu'
  obtain ⟨e, he, hc⟩ := grpPullback_iso ((m.cart.comp (isGrpPullback_of_iso φ)).congr (Category.comp_id _) rfl) hψ
  have hm : LBIso t₀.PP.L (τ.PP.L.pull m.φ) := m.lin.imp fun _ h => h.1
  refine ⟨u, t₀, m, e, hu, he, ?_⟩
  refine LBIso.trans t₀.PP.isLB (pull_isLB τ.PP.isLB _) (pull_isLB u.isLB _) hm ?_
  exact LBIso.trans (pull_isLB τ.PP.isLB _) (pull_isLB t.isLB _) (pull_isLB u.isLB _)
    (GenSpread.lbIso_pull_of_lbIso hL _ rfl) (GenSpread.lbIso_pull_of_lbIso hLu _ hc.symm).symm

/- English proof (translation)
Introduce `h₁ h₂ h₃ h₄ h₅ h₆ E _ _ _ H D n _ hn ho`. Take `⟨k, j₀, hz⟩` from `hcomp h₁ h₂ h₃ h₄ h₅ h₆ E H (Module.finrank ℤ D.La / 2) n hn ho`. Use `⟨k, j₀, ?_⟩` and prove the remaining obligations. Introduce and unpack `j hj _ rfl g J _ a bas b F τ - - - - ⟨φ, hφ, hL, -⟩ -`. Choose the witnesses or unpack the hypotheses as in `rfl : g = Module.finrank ℤ D.La / 2 := by`.

Use `bas.finrank_eq` as an intermediate fact. Rewrite `this` using `[Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Establish `hded : IsDedekindDomain (RZ H n ((n ^ j) ^ 2))` using `BaseRing.isDedekindDomain_RZ (HostModel.level H ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)) (e := j * 2) hn.pos (by rw [pow_mul]; exact dvd_rfl)`. Take `⟨N, q, hq₀, hqc, hs⟩` from `F.qproj`.

Establish `hp : IsProper (PSpace.str (RZ H n ((n ^ j) ^ 2)) N)` using `isProper_str _ _`. Establish `hft : LocallyOfFiniteType F.s` using `by rw [← hs]; infer_instance`. Establish `hq : QuasiCompact F.s` using `by rw [← hs]; infer_instance`. Establish `hg` using `isGrpPullback_of_iso φ`. Take `⟨hab, hamp, hk⟩` from `pol_pull _ _ _ _ _ _ _ _ F.univ.isLB τ.PP.isLB F.univ.ab hg hL`.

Use `T.generic_points_open_integral_cover E H _ _ F.s τ _ F.reduced hft hq (fun ξ hξ => ?_) ⟨_, (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 F.univ.dim⟩ h₁ h₂ hab.proper (hamp F.univ.ample) (hk F.univ.ktriv)` and prove the remaining obligations. Take `⟨R₀, _, x, v₀, hx, hξx, hv₀⟩` from `ThetaLocal.exists_hasTh h₁ h₂ _ _ _ J b _ _ F.univ ho.pow ξ`. Use `F.reduced` as an intermediate fact. Use `F.flat` as an intermediate fact. Take `⟨Ω, _, _, R, ψ, hi, hξi, his, hfg, hfr, hinj⟩` from `exists_integral_chart F.s hξ x hξx`.

Establish `hv` using `T.hasThetaConstants_ring_baseChange h₂ _ _ _ J b _ _ F.univ R₀ R ψ x v₀ hv₀`. Establish `: GlobalTheory.ZH.ArithBase (RZ H n ((n ^ j) ^ 2)) Ω` using `⟨hded, BaseRing.finiteType_RZ H _ _, charZero_of_injective_algebraMap hinj, hinj⟩`. Take `⟨u, t₀, m, e, hu, he, hLe⟩` from `exists_pull F.univ τ φ hL _ his`. Establish `htop` using `closure_ratios_eq_top h₁ h₂ Subtype.val_injective F R _ his hfr _ hv`. Establish `hC` using `hz j hj _ Ω R J b u t₀ e (fun a => ψ (v₀ a)) hfg hfr he hLe ((hasTh_iff_of_tmap _ _ _ J b _ _ F.univ _ _ u _ R (𝟙 _) _ hu).2 (by rw [Category.id_comp]; exact hv)) (Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun z => ⟨⟨z, by rw [htop]; trivial⟩, rfl⟩)`.

Rewrite `hC` using `[← his]`. Take `⟨C, hC⟩` from `hC`. Conclude with `⟨_, _, t₀, m, C, hi, hξi, inferInstance, hC⟩`.
-/
theorem nonempty_zOn_of_components (hcomp : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g n : ℕ), n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((n ^ j) ^ 2)) (u : TObj g ((n ^ j) ^ 2) J b (spMap (algebraMap o R))) (t₀ : SAB H (Sp R)) (e : t₀.G ≅ u.A) (v : GlobalTheory.ZM.Ix g ((n ^ j) ^ 2) → R), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) → IsMonHom e.hom → LBIso t₀.PP.L (u.L.pull e.hom.left) → u.HasTh (𝟙 _) v → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i i', x = (v i : Ω) / (v i' : Ω)})) Ω → ∃ C : ZOn (spMap (algebraMap o R)) t₀ (n ^ k), IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L ((n ^ k) ^ 2), A.r = r ∧ A.s = 1) : Out.Laws → Out.Laws2 → GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ThmUSt → GlobalTheory.ZH.UTorsSt → GlobalTheory.ZH.ZHGeoSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n : ℕ), 1 ≤ D.p + D.q → n.Prime → Odd n → ∃ k j₀ : ℕ, ∀ j ≥ j₀, ∀ N' : ℕ, N' = n ^ j → ∀ (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → Nonempty (ZOn F.s τ (n ^ k)) := by
  intro h₁ h₂ h₃ h₄ h₅ h₆ E _ _ _ H D n _ hn ho
  obtain ⟨k, j₀, hz⟩ := hcomp h₁ h₂ h₃ h₄ h₅ h₆ E H (Module.finrank ℤ D.La / 2) n hn ho
  refine ⟨k, j₀, ?_⟩
  rintro j hj _ rfl g J _ a bas b F τ - - - - ⟨φ, hφ, hL, -⟩ -
  obtain rfl : g = Module.finrank ℤ D.La / 2 := by
    have := bas.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  have hded : IsDedekindDomain (RZ H n ((n ^ j) ^ 2)) :=
    BaseRing.isDedekindDomain_RZ (HostModel.level H ((n ^ j) ^ 2) (pow_pos (pow_pos hn.pos j) 2)) (e := j * 2) hn.pos
      (by rw [pow_mul]; exact dvd_rfl)
  obtain ⟨N, q, hq₀, hqc, hs⟩ := F.qproj
  have hp : IsProper (PSpace.str (RZ H n ((n ^ j) ^ 2)) N) := isProper_str _ _
  have hft : LocallyOfFiniteType F.s := by rw [← hs]; infer_instance
  have hq : QuasiCompact F.s := by rw [← hs]; infer_instance
  have hg := isGrpPullback_of_iso φ
  obtain ⟨hab, hamp, hk⟩ := pol_pull _ _ _ _ _ _ _ _ F.univ.isLB τ.PP.isLB F.univ.ab hg hL
  refine T.generic_points_open_integral_cover E H _ _ F.s τ _ F.reduced hft hq (fun ξ hξ => ?_)
    ⟨_, (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hg.1 F.univ.dim⟩ h₁ h₂ hab.proper
    (hamp F.univ.ample) (hk F.univ.ktriv)
  obtain ⟨R₀, _, x, v₀, hx, hξx, hv₀⟩ := ThetaLocal.exists_hasTh h₁ h₂ _ _ _ J b _ _ F.univ ho.pow ξ
  have := F.reduced
  have := F.flat
  obtain ⟨Ω, _, _, R, ψ, hi, hξi, his, hfg, hfr, hinj⟩ := exists_integral_chart F.s hξ x hξx
  have hv := T.hasThetaConstants_ring_baseChange h₂ _ _ _ J b _ _ F.univ R₀ R ψ x v₀ hv₀
  have : GlobalTheory.ZH.ArithBase (RZ H n ((n ^ j) ^ 2)) Ω :=
    ⟨hded, BaseRing.finiteType_RZ H _ _, charZero_of_injective_algebraMap hinj, hinj⟩
  obtain ⟨u, t₀, m, e, hu, he, hLe⟩ := exists_pull F.univ τ φ hL _ his
  have htop := closure_ratios_eq_top h₁ h₂ Subtype.val_injective F R _ his hfr _ hv
  have hC := hz j hj _ Ω R J b u t₀ e (fun a => ψ (v₀ a)) hfg hfr he hLe
    ((hasTh_iff_of_tmap _ _ _ J b _ _ F.univ _ _ u _ R (𝟙 _) _ hu).2 (by rw [Category.id_comp]; exact hv))
    (Module.Finite.of_surjective (Algebra.linearMap _ Ω) fun z => ⟨⟨z, by rw [htop]; trivial⟩, rfl⟩)
  rw [← his] at hC
  obtain ⟨C, hC⟩ := hC
  exact ⟨_, _, t₀, m, C, hi, hξi, inferInstance, hC⟩

end GlobalTheory.FamilyModel
