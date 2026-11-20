import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DedekindConstantsDegreeOneStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlaceStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

namespace GlobalTheory.CompanionTheory.Ar.Num.LatFlag

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩`.
-/
theorem unitAt_mul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ} {a b : Ω}
    (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩`.
-/
theorem unitAt_pow {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ} {a : Ω}
    (ha : unitAt ξ q a) (n : ℕ) : unitAt ξ q (a ^ n) :=
  ⟨pow_ne_zero n ha.1, pow_mem ha.2.1 n, by rw [← inv_pow]; exact pow_mem ha.2.2 n⟩

/- English proof (translation)
Take `⟨v, rfl⟩` from `hu`. Use `⟨(v.isUnit.map (algebraMap O Ω)).ne_zero, hO _, ?_⟩` and prove the remaining obligations. Establish `: (algebraMap O Ω (v : O))⁻¹ = algebraMap O Ω ((v⁻¹ : Oˣ) : O)`. Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Rewrite using `[this]`. Conclude with `hO _`.
-/
theorem unitAt_algebraMap {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}
    {O : Type} [CommRing O] [Algebra O Ω] (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) {u : O} (hu : IsUnit u) :
    unitAt ξ q (algebraMap O Ω u) := by
  obtain ⟨v, rfl⟩ := hu
  refine ⟨(v.isUnit.map (algebraMap O Ω)).ne_zero, hO _, ?_⟩
  have : (algebraMap O Ω (v : O))⁻¹ = algebraMap O Ω ((v⁻¹ : Oˣ) : O) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← map_mul, Units.mul_inv, map_one]
  rw [this]
  exact hO _

end GlobalTheory.CompanionTheory.Ar.Num.LatFlag

namespace GlobalTheory.CompanionTheory.Ar.Num.LatFlag

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem a ha => exact Algebra.subset_adjoin ha`. Consider the case `algebraMap n`. Establish `: algebraMap ℤ Ω n = algebraMap O Ω (n : O)` using `by simp`. Rewrite using `[this]`.

Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `mul a b _ _ ha hb => exact mul_mem ha hb`.
-/
theorem chartRing_int_le (Ω : Type) [Field Ω] (κ : Type) (x : κ → Ω) (O : Type) [CommRing O] [Algebra O Ω] (c : κ)
    {a : Ω} (ha : a ∈ chartRing ℤ x c) : a ∈ chartRing O x c := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap n =>
    have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

/- English proof (translation)
Set `R` to `Algebra.adjoin ℤ (Set.range fun j => x j / x c)`. Set `ι : R →+* chartRing O x c` to `{ toFun := fun a => ⟨a, chartRing_int_le Ω κ x O c a.2⟩ map_one' := Subtype.ext (by simp) map_mul' := fun _ _ => Subtype.ext (by simp) map_zero' := Subtype.ext (by simp) map_add' := fun _ _ => Subtype.ext (by simp) }`. Take `⟨q, ⟨hq, hqu⟩, -⟩` from `GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ ℤ κ x hT c hc (P.comap ι) (Ideal.comap_isPrime ι P)`. Conclude with `⟨q, hq, fun a ha => by`. Use `hqu ⟨a, ha⟩` as an intermediate fact.

Rewrite `this` using `[Ideal.mem_comap]`. Conclude with `this⟩`.
-/
theorem chart_point_of_prime_alt (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω)
    (O : Type) [CommRing O] [Algebra O Ω] (hT : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    (P : Ideal (chartRing O x c)) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ ∀ a (ha : a ∈ chartRing ℤ x c),
      (⟨a, chartRing_int_le Ω κ x O c ha⟩ : chartRing O x c) ∉ P ↔ unitAt ξ q a := by
  let R := Algebra.adjoin ℤ (Set.range fun j => x j / x c)
  let ι : R →+* chartRing O x c :=
    { toFun := fun a => ⟨a, chartRing_int_le Ω κ x O c a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  obtain ⟨q, ⟨hq, hqu⟩, -⟩ := GlobalTheory.CompanionTheory.Ar.chart_point_of_prime X Ω ξ ℤ κ x hT c hc (P.comap ι) (Ideal.comap_isPrime ι P)
  exact ⟨q, hq, fun a ha => by
    have := hqu ⟨a, ha⟩
    rw [Ideal.mem_comap] at this
    exact this⟩

end GlobalTheory.CompanionTheory.Ar.Num.LatFlag

namespace GlobalTheory.CompanionTheory.Ar.Num.LatFlag

/- English proof (translation)
Assemble the required witnesses or components as `⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩`.
-/
theorem unitAt_inv {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ} {a : Ω}
    (ha : unitAt ξ q a) : unitAt ξ q a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

/- English proof (translation)
Establish `hone : algebraMap A Ω 1 = 1` using `map_one _`. Proceed by induction on `hs using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Use `⟨1, fun h => (inferInstance : m.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩` and prove the remaining obligations. Rewrite using `[hone, one_mul]`.

Conclude with `Algebra.subset_adjoin ha`. Consider the case `algebraMap o`. Take `⟨⟨a, t⟩, h⟩` from `IsLocalization.surj m.primeCompl o`. Use `⟨t, t.2, ?_⟩` and prove the remaining obligations. Establish `h' : algebraMap A Ω t * algebraMap O Ω o = algebraMap A Ω a`.

Rewrite using `[IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω, ← map_mul, mul_comm]`. Conclude with `congrArg _ h`. Rewrite using `[h']`. Conclude with `hA a`. Consider the case `add a b _ _ ha hb`.

Take `⟨t, ht, hta⟩` from `ha`. Take `⟨u, hu, hub⟩` from `hb`. Use `⟨t * u, fun h => ((inferInstance : m.IsPrime).mem_or_mem h).elim ht hu, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap A Ω (t * u) * (a + b) = algebraMap A Ω u * (algebraMap A Ω t * a) + algebraMap A Ω t * (algebraMap A Ω u * b)`. Rewrite using `[map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `add_mem (mul_mem (hA u) hta) (mul_mem (hA t) hub)`. Consider the case `mul a b _ _ ha hb`. Take `⟨t, ht, hta⟩` from `ha`.

Take `⟨u, hu, hub⟩` from `hb`. Use `⟨t * u, fun h => ((inferInstance : m.IsPrime).mem_or_mem h).elim ht hu, ?_⟩` and prove the remaining obligations. Establish `e : algebraMap A Ω (t * u) * (a * b) = (algebraMap A Ω t * a) * (algebraMap A Ω u * b)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `mul_mem hta hub`.
-/
theorem exists_den (Ω : Type) [Field Ω] (κ : Type) (x : κ → Ω) (A : Type) [CommRing A] [Algebra A Ω] (m : Ideal A)
    [m.IsPrime] (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] (c : κ) (hA : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ x c) {s : Ω}
    (hs : s ∈ chartRing O x c) : ∃ t : A, t ∉ m ∧ algebraMap A Ω t * s ∈ chartRing ℤ x c := by
  have hone : algebraMap A Ω 1 = 1 := map_one _
  induction hs using Algebra.adjoin_induction with
  | mem a ha =>
    refine ⟨1, fun h => (inferInstance : m.IsPrime).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [hone, one_mul]
    exact Algebra.subset_adjoin ha
  | algebraMap o =>
    obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj m.primeCompl o
    refine ⟨t, t.2, ?_⟩
    have h' : algebraMap A Ω t * algebraMap O Ω o = algebraMap A Ω a := by
      rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω, ← map_mul, mul_comm]
      exact congrArg _ h
    rw [h']
    exact hA a
  | add a b _ _ ha hb =>
    obtain ⟨t, ht, hta⟩ := ha
    obtain ⟨u, hu, hub⟩ := hb
    refine ⟨t * u, fun h => ((inferInstance : m.IsPrime).mem_or_mem h).elim ht hu, ?_⟩
    have e : algebraMap A Ω (t * u) * (a + b) =
        algebraMap A Ω u * (algebraMap A Ω t * a) + algebraMap A Ω t * (algebraMap A Ω u * b) := by
      rw [map_mul]; ring
    rw [e]
    exact add_mem (mul_mem (hA u) hta) (mul_mem (hA t) hub)
  | mul a b _ _ ha hb =>
    obtain ⟨t, ht, hta⟩ := ha
    obtain ⟨u, hu, hub⟩ := hb
    refine ⟨t * u, fun h => ((inferInstance : m.IsPrime).mem_or_mem h).elim ht hu, ?_⟩
    have e : algebraMap A Ω (t * u) * (a * b) = (algebraMap A Ω t * a) * (algebraMap A Ω u * b) := by
      rw [map_mul]; ring
    rw [e]
    exact mul_mem hta hub

/- English proof (translation)
Take `⟨q, hq, hqu⟩` from `chart_point_of_prime_alt X Ω ξ κ x O hT c hc P hP`. Establish `hRreg : ∀ a ∈ chartRing ℤ x c, a ∈ regAt ξ q` using `fun a ha => (hT.ring c hc a).1 ha q hq`. Establish `hAu : ∀ t : A, t ∉ m → (⟨_, chartRing_int_le Ω κ x O c (hA t)⟩ : chartRing O x c) ∉ P`. Introduce `t ht hmem`. Take `⟨v, hv⟩` from `IsLocalization.map_units O (⟨t, ht⟩ : m.primeCompl)`.

Establish `hv' : (v : O) = algebraMap A O t` using `hv`. Set `i : chartRing O x c` to `⟨algebraMap O Ω ((v⁻¹ : Oˣ) : O), Subalgebra.algebraMap_mem _ _⟩`. Establish `h1 : i * (⟨_, chartRing_int_le Ω κ x O c (hA t)⟩ : chartRing O x c) = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[MulMemClass.coe_mul, OneMemClass.coe_one]`.

Use `show algebraMap O Ω ((v⁻¹ : Oˣ) : O) * algebraMap A Ω t = 1`. Rewrite using `[IsScalarTower.algebraMap_apply A O Ω, ← hv', ← map_mul, Units.inv_mul, map_one]`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.mul_mem_left i hmem))`. Establish `hden` using `fun (s : chartRing O x c) => exists_den Ω κ x A m O c hA s.2`. Establish `hreg : ∀ s : chartRing O x c, (s : Ω) ∈ regAt ξ q`.

Introduce `s`. Take `⟨t, ht, hts⟩` from `hden s`. Establish `hu` using `(hqu _ (hA t)).1 (hAu t ht)`. Establish `e : (s : Ω) = (algebraMap A Ω t)⁻¹ * (algebraMap A Ω t * s)`. Rewrite using `[inv_mul_cancel_left₀ hu.1]`.

Rewrite using `[e]`. Conclude with `mul_mem hu.2.2 (hRreg _ hts)`. Use `⟨q, hq, fun o => hreg ⟨_, Subalgebra.algebraMap_mem _ o⟩, fun s hs => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Take `⟨t, ht, hts⟩` from `hden s`. Establish `hn` using `hAu t ht`.

Establish `hu` using `(hqu _ (hA t)).1 hn`. Establish `hnot : (⟨_, chartRing_int_le Ω κ x O c hts⟩ : chartRing O x c) ∉ P`. Introduce `hmem`. Establish `h3 : (⟨_, chartRing_int_le Ω κ x O c hts⟩ : chartRing O x c) = (⟨_, chartRing_int_le Ω κ x O c (hA t)⟩ : chartRing O x c) * s` using `Subtype.ext (by rw [MulMemClass.coe_mul])`. Rewrite `hmem` using `[h3]`.

Conclude with `(hP.mem_or_mem hmem).elim hn hs`. Establish `hu2 : unitAt ξ q (algebraMap A Ω t * s)` using `(hqu _ hts).1 hnot`. Establish `e : (s : Ω) = (algebraMap A Ω t)⁻¹ * (algebraMap A Ω t * s)`. Rewrite using `[inv_mul_cancel_left₀ hu.1]`. Rewrite using `[e]`.

Conclude with `unitAt_mul (unitAt_inv hu) hu2`. Take `⟨s, hs, hsu, hsa⟩` from `(GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c q hq a).1 ha`. Conclude with `⟨⟨s, chartRing_int_le Ω κ x O c hs⟩, (hqu s hs).2 hsu, chartRing_int_le Ω κ x O c hsa⟩`.
-/
theorem chart_point (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω)
    (A : Type) [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O]
    [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (hT : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    (hA : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ x c) (P : Ideal (chartRing O x c)) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, InChart ξ x c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧
      (∀ s : chartRing O x c, s ∉ P → unitAt ξ q (s : Ω)) ∧
      ∀ a ∈ regAt ξ q, ∃ s : chartRing O x c, s ∉ P ∧ (s : Ω) * a ∈ chartRing O x c := by
  classical
  obtain ⟨q, hq, hqu⟩ := chart_point_of_prime_alt X Ω ξ κ x O hT c hc P hP
  have hRreg : ∀ a ∈ chartRing ℤ x c, a ∈ regAt ξ q := fun a ha => (hT.ring c hc a).1 ha q hq
  have hAu : ∀ t : A, t ∉ m → (⟨_, chartRing_int_le Ω κ x O c (hA t)⟩ : chartRing O x c) ∉ P := by
    intro t ht hmem
    obtain ⟨v, hv⟩ := IsLocalization.map_units O (⟨t, ht⟩ : m.primeCompl)
    have hv' : (v : O) = algebraMap A O t := hv
    let i : chartRing O x c := ⟨algebraMap O Ω ((v⁻¹ : Oˣ) : O), Subalgebra.algebraMap_mem _ _⟩
    have h1 : i * (⟨_, chartRing_int_le Ω κ x O c (hA t)⟩ : chartRing O x c) = 1 := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, OneMemClass.coe_one]
      show algebraMap O Ω ((v⁻¹ : Oˣ) : O) * algebraMap A Ω t = 1
      rw [IsScalarTower.algebraMap_apply A O Ω, ← hv', ← map_mul, Units.inv_mul, map_one]
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (h1 ▸ P.mul_mem_left i hmem))
  have hden := fun (s : chartRing O x c) => exists_den Ω κ x A m O c hA s.2
  have hreg : ∀ s : chartRing O x c, (s : Ω) ∈ regAt ξ q := by
    intro s
    obtain ⟨t, ht, hts⟩ := hden s
    have hu := (hqu _ (hA t)).1 (hAu t ht)
    have e : (s : Ω) = (algebraMap A Ω t)⁻¹ * (algebraMap A Ω t * s) := by
      rw [inv_mul_cancel_left₀ hu.1]
    rw [e]
    exact mul_mem hu.2.2 (hRreg _ hts)
  refine ⟨q, hq, fun o => hreg ⟨_, Subalgebra.algebraMap_mem _ o⟩, fun s hs => ?_, fun a ha => ?_⟩
  · obtain ⟨t, ht, hts⟩ := hden s
    have hn := hAu t ht
    have hu := (hqu _ (hA t)).1 hn
    have hnot : (⟨_, chartRing_int_le Ω κ x O c hts⟩ : chartRing O x c) ∉ P := by
      intro hmem
      have h3 : (⟨_, chartRing_int_le Ω κ x O c hts⟩ : chartRing O x c) =
          (⟨_, chartRing_int_le Ω κ x O c (hA t)⟩ : chartRing O x c) * s :=
        Subtype.ext (by rw [MulMemClass.coe_mul])
      rw [h3] at hmem
      exact (hP.mem_or_mem hmem).elim hn hs
    have hu2 : unitAt ξ q (algebraMap A Ω t * s) := (hqu _ hts).1 hnot
    have e : (s : Ω) = (algebraMap A Ω t)⁻¹ * (algebraMap A Ω t * s) := by
      rw [inv_mul_cancel_left₀ hu.1]
    rw [e]
    exact unitAt_mul (unitAt_inv hu) hu2
  · obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction X Ω ξ ℤ κ x hT c q hq a).1 ha
    exact ⟨⟨s, chartRing_int_le Ω κ x O c hs⟩, (hqu s hs).2 hsu, chartRing_int_le Ω κ x O c hsa⟩

/- English proof (translation)
Establish `h1 : (p : O) ∈ IsLocalRing.maximalIdeal O`. Use `(IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hm` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hco : IsCoprime (p : ℤ) (p' : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 hne.symm)`. Take `⟨a, b, hab⟩` from `hco.map (Int.castRingHom O)`.

Assume the negation of the conclusion as `hu`. Establish `h2 : (p' : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hu`. Establish `h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← hab]`. Simplify using `only [eq_intCast, Int.cast_natCast]`.

Conclude with `add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)`.
-/
theorem isUnit_natCast_of_ne (A : Type) [CommRing A] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] (p p' : ℕ) (hp : p.Prime) (hp' : p'.Prime)
    (hne : p' ≠ p) (hm : (p : A) ∈ m) : IsUnit (p' : O) := by
  have h1 : (p : O) ∈ IsLocalRing.maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hm
    rwa [map_natCast] at this
  have hco : IsCoprime (p : ℤ) (p' : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hp').2 hne.symm)
  obtain ⟨a, b, hab⟩ := hco.map (Int.castRingHom O)
  by_contra hu
  have h2 : (p' : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hu
  have h3 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← hab]
    simp only [eq_intCast, Int.cast_natCast]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)

/- English proof (translation)
Establish `hp0 : (p : O) ≠ 0`. Introduce `h0`. Establish `hA0 : (p : A) = 0` using `hinj (by rw [map_natCast, h0, map_zero])`. Use `haveI : Finite A := Module.finite_of_fg_torsion A (fun x => ⟨⟨(p : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp.ne_zero)⟩, by show (p : ℤ) • x = 0`. Rewrite using `[← Int.cast_smul_eq_zsmul A, Int.cast_natCast, hA0, zero_smul]⟩)`.

Establish `hF : IsField A` using `Finite.isField_of_domain A`. Take `⟨⟨a, t⟩, h⟩` from `IsLocalization.surj m.primeCompl ϖ`. Establish `hu : IsUnit (algebraMap A O t)` using `IsLocalization.map_units O t`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`.

Rewrite `h` using `[map_zero]`. Conclude with `hu.ne_zero ((mul_eq_zero.1 h).resolve_left hϖ.ne_zero)`. Establish `hua : IsUnit a`. Take `⟨b, hb⟩` from `hF.mul_inv_cancel ha`. Conclude with `IsUnit.of_mul_eq_one _ hb`.

Establish `: IsUnit (ϖ * algebraMap A O t)`. Establish `h' : ϖ * algebraMap A O t = algebraMap A O a` using `h`. Rewrite using `[h']`. Conclude with `hua.map _`. Conclude with `hϖ.not_isUnit (isUnit_of_mul_isUnit_left this)`.

Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ`. Use `⟨n, ((u⁻¹ : Oˣ) : O), (u⁻¹).isUnit, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]`.
-/
theorem exists_natCast_eq (A : Type) [CommRing A] [IsDomain A] [Module.Finite ℤ A] (m : Ideal A) [m.IsPrime]
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m]
    (hinj : Function.Injective (algebraMap A O)) (p : ℕ) (hp : p.Prime) (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (n : ℕ) (u : O), IsUnit u ∧ (p : O) = u * ϖ ^ n := by
  have hp0 : (p : O) ≠ 0 := by
    intro h0
    have hA0 : (p : A) = 0 := hinj (by rw [map_natCast, h0, map_zero])
    haveI : Finite A := Module.finite_of_fg_torsion A (fun x => ⟨⟨(p : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hp.ne_zero)⟩, by
      show (p : ℤ) • x = 0
      rw [← Int.cast_smul_eq_zsmul A, Int.cast_natCast, hA0, zero_smul]⟩)
    have hF : IsField A := Finite.isField_of_domain A
    obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj m.primeCompl ϖ
    have hu : IsUnit (algebraMap A O t) := IsLocalization.map_units O t
    have ha : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at h
      exact hu.ne_zero ((mul_eq_zero.1 h).resolve_left hϖ.ne_zero)
    have hua : IsUnit a := by
      obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha
      exact IsUnit.of_mul_eq_one _ hb
    have : IsUnit (ϖ * algebraMap A O t) := by
      have h' : ϖ * algebraMap A O t = algebraMap A O a := h
      rw [h']; exact hua.map _
    exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left this)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hp0 hϖ
  refine ⟨n, ((u⁻¹ : Oˣ) : O), (u⁻¹).isUnit, ?_⟩
  rw [← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]

end GlobalTheory.CompanionTheory.Ar.Num.LatFlag

namespace GlobalTheory.CompanionTheory.Ar.Num.LatFlag

/- English proof (translation)
Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)`. Establish `H : ∀ i : ℕ, i ≤ r → ∀ z : E, (∀ j : Fin r, i ≤ (j : ℕ) → (w.unitsSMul e).repr z j = 0) → (∀ q, good q → z ∈ L q) → ∃ n : ℕ, f ^ n • z ∈ B.lat c`. Introduce `i`. Proceed by induction on `i with`. Consider the case `zero`.

Introduce `_ z h0 _`. Establish `hz0 : z = 0`. Apply `(w.unitsSMul e).repr.map_eq_zero_iff.1` to reduce the goal to its premises. Use extensionality with `j`. Simplify using `using h0 j (Nat.zero_le _)`.

Conclude with `⟨0, by simp [hz0, zero_mem]⟩`. Consider the case `succ i ih`. Introduce `hi z h0 hzL`. Use `set v := w.unitsSMul e with hv`. Set `ii : Fin r` to `⟨i, hi⟩`.

Take `⟨Y, hY⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ x ii k` from `⟨_, rfl⟩`. Establish `hY0 : Y ≠ 0`. Rewrite using `[hY]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)`. Take `⟨s, hs⟩ : ∃ s : Ω, s = v.repr z ii` from `⟨_, rfl⟩`.

Establish `hreg : ∀ q, good q → s / Y ∈ regAt ξ q`. Introduce `q hq`. Establish `hflagm : z - (s * (e ii : Ω)) • w ii ∈ flagStep Ω (⇑w) ii`. Establish `hsum : z = ∑ j, v.repr z j • v j` using `(v.sum_repr z).symm`. Establish `hz2 : z - (s * (e ii : Ω)) • w ii = ∑ j ∈ Finset.univ.erase ii, v.repr z j • v j` using `by conv_lhs => rw [hsum]`.

Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ ii), ← hs, hv, Module.Basis.unitsSMul_apply]`. Rewrite using `[Units.smul_def, smul_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hz2]`. Use `Submodule.sum_mem _ fun j hj => ?_` and prove the remaining obligations.

Distinguish the cases in `hji : (i : ℕ) ≤ j`. Establish `hne : (j : ℕ) ≠ i` using `fun h => (Finset.ne_of_mem_erase hj) (Fin.ext h)`. Rewrite using `[h0 j (by omega), zero_smul]`. Conclude with `zero_mem _`. Rewrite using `[hv, Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, (not_le.1 hji : (j : ℕ) < i), rfl⟩)`. Establish `hmem : s * (e ii : Ω) ∈ (L.gr w ii) q` using `Submodule.subset_span ⟨z, hzL q hq, hflagm⟩`. Rewrite `hmem` using `[hgr q hq ii, ← hY]`. Take `⟨ρ, hρ⟩` from `Submodule.mem_span_singleton.1 hmem`. Establish `hρ' : (ρ : Ω) * (Y * (e ii : Ω)) = s * (e ii : Ω)` using `hρ`.

Establish `: s / Y = ρ`. Establish `he` using `(e ii).ne_zero`. Rewrite using `[div_eq_iff hY0]`. Conclude with `(mul_right_cancel₀ he (by rw [← hρ']; ring))`. Rewrite using `[this]`.

Conclude with `ρ.2`. Take `⟨n, hn⟩` from `hpow (s / Y) hreg`. Establish `hdeg : f ^ n * s ∈ GroundTheory.Heights₂.Heights.NumbersDVR.degLat O y (x ii) c`. Use `⟨_, hn, ?_⟩` and prove the remaining obligations. Rewrite using `[← hY]`.

Clear the denominators using the available nonvanishing facts. Rewrite `hdeg` using `[← hflag.graded c hc ii]`. Take `⟨u, hu, hu0, hus⟩` from `hdeg`. Take `⟨n', hn'⟩` from `ih (by omega) (f ^ n • z - u) (fun j hj => by`. Rewrite using `[map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply]`.

Distinguish the cases in `hji : (j : ℕ) = i`. Establish `: j = ii` using `Fin.ext hji`. Rewrite using `[this, hus, hs, smul_eq_mul, sub_self]`. Establish `hlt : ii < j` using `by show i < (j : ℕ)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h0 j (by omega), hu0 j hlt, smul_zero, sub_zero]) (fun q hq => by`. Use `sub_mem ?_ (hB u hu q hq)` and prove the remaining obligations. Conclude with `(L q).smul_mem (⟨f ^ n, pow_mem (hfr q hq) n⟩ : regAt ξ q) (hzL q hq))`. Use `⟨n' + n, ?_⟩` and prove the remaining obligations. Establish `e1 : f ^ (n' + n) • z = f ^ n' • (f ^ n • z - u) + f ^ n' • u`.

Rewrite using `[smul_sub, sub_add_cancel, smul_smul, pow_add]`. Rewrite using `[e1]`. Conclude with `add_mem hn' (B.stable c _ (pow_mem hf n') u hu)`. Conclude with `H r le_rfl z (fun j hj => absurd j.2 (not_lt.2 hj)) hz`.
-/
theorem flag_sections (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    (J : K → Type) (y : (Σ k, J k) → Ω) (O : Type) [CommRing O] [Algebra O Ω] (E : Type) [AddCommGroup E]
    [Module Ω E] (r : ℕ) (w : Module.Basis (Fin r) Ω E) (e : Fin r → Ωˣ) (x : Fin r → K → ℤ)
    (B : ChartBundle O (segreVec y) r E) (L : Lat ξ E) (c : (k : K) → J k) (hc : segreVec y c ≠ 0)
    (good : Cpt ξ → Prop) (f : Ω) (hf : f ∈ chartRing O (segreVec y) c)
    (hflag : IsFlagFrame y B (w.unitsSMul e) x) (hB : ∀ z ∈ B.lat c, ∀ q, good q → z ∈ L q)
    (hfr : ∀ q, good q → f ∈ regAt ξ q)
    (hgr : ∀ q, good q → ∀ i, (L.gr w i) q = Submodule.span (regAt ξ q) {(∏ k, y ⟨k, c k⟩ ^ x i k) * (e i : Ω)})
    (hpow : ∀ a : Ω, (∀ q, good q → a ∈ regAt ξ q) → ∃ n : ℕ, f ^ n * a ∈ chartRing O (segreVec y) c)
    (z : E) (hz : ∀ q, good q → z ∈ L q) : ∃ n : ℕ, f ^ n • z ∈ B.lat c := by
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have H : ∀ i : ℕ, i ≤ r → ∀ z : E, (∀ j : Fin r, i ≤ (j : ℕ) → (w.unitsSMul e).repr z j = 0) →
      (∀ q, good q → z ∈ L q) → ∃ n : ℕ, f ^ n • z ∈ B.lat c := by
    intro i
    induction i with
    | zero =>
      intro _ z h0 _
      have hz0 : z = 0 := by
        apply (w.unitsSMul e).repr.map_eq_zero_iff.1
        ext j
        simpa using h0 j (Nat.zero_le _)
      exact ⟨0, by simp [hz0, zero_mem]⟩
    | succ i ih =>
      intro hi z h0 hzL
      set v := w.unitsSMul e with hv
      let ii : Fin r := ⟨i, hi⟩
      obtain ⟨Y, hY⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ x ii k := ⟨_, rfl⟩
      have hY0 : Y ≠ 0 := by
        rw [hY]; exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
      obtain ⟨s, hs⟩ : ∃ s : Ω, s = v.repr z ii := ⟨_, rfl⟩
      have hreg : ∀ q, good q → s / Y ∈ regAt ξ q := by
        intro q hq
        have hflagm : z - (s * (e ii : Ω)) • w ii ∈ flagStep Ω (⇑w) ii := by
          have hsum : z = ∑ j, v.repr z j • v j := (v.sum_repr z).symm
          have hz2 : z - (s * (e ii : Ω)) • w ii =
              ∑ j ∈ Finset.univ.erase ii, v.repr z j • v j := by
            conv_lhs => rw [hsum]
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ii), ← hs, hv, Module.Basis.unitsSMul_apply]
            rw [Units.smul_def, smul_smul]
            abel
          rw [hz2]
          refine Submodule.sum_mem _ fun j hj => ?_
          by_cases hji : (i : ℕ) ≤ j
          · have hne : (j : ℕ) ≠ i := fun h => (Finset.ne_of_mem_erase hj) (Fin.ext h)
            rw [h0 j (by omega), zero_smul]
            exact zero_mem _
          · rw [hv, Module.Basis.unitsSMul_apply, Units.smul_def, smul_smul]
            exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, (not_le.1 hji : (j : ℕ) < i), rfl⟩)
        have hmem : s * (e ii : Ω) ∈ (L.gr w ii) q :=
          Submodule.subset_span ⟨z, hzL q hq, hflagm⟩
        rw [hgr q hq ii, ← hY] at hmem
        obtain ⟨ρ, hρ⟩ := Submodule.mem_span_singleton.1 hmem
        have hρ' : (ρ : Ω) * (Y * (e ii : Ω)) = s * (e ii : Ω) := hρ
        have : s / Y = ρ := by
          have he := (e ii).ne_zero
          rw [div_eq_iff hY0]
          exact (mul_right_cancel₀ he (by rw [← hρ']; ring))
        rw [this]
        exact ρ.2
      obtain ⟨n, hn⟩ := hpow (s / Y) hreg
      have hdeg : f ^ n * s ∈ GroundTheory.Heights₂.Heights.NumbersDVR.degLat O y (x ii) c := by
        refine ⟨_, hn, ?_⟩
        rw [← hY]
        field_simp
      rw [← hflag.graded c hc ii] at hdeg
      obtain ⟨u, hu, hu0, hus⟩ := hdeg
      obtain ⟨n', hn'⟩ := ih (by omega) (f ^ n • z - u) (fun j hj => by
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply]
        by_cases hji : (j : ℕ) = i
        · have : j = ii := Fin.ext hji
          rw [this, hus, hs, smul_eq_mul, sub_self]
        · have hlt : ii < j := by
            show i < (j : ℕ)
            omega
          rw [h0 j (by omega), hu0 j hlt, smul_zero, sub_zero]) (fun q hq => by
        refine sub_mem ?_ (hB u hu q hq)
        exact (L q).smul_mem (⟨f ^ n, pow_mem (hfr q hq) n⟩ : regAt ξ q) (hzL q hq))
      refine ⟨n' + n, ?_⟩
      have e1 : f ^ (n' + n) • z = f ^ n' • (f ^ n • z - u) + f ^ n' • u := by
        rw [smul_sub, sub_add_cancel, smul_smul, pow_add]
      rw [e1]
      exact add_mem hn' (B.stable c _ (pow_mem hf n') u hu)
  exact H r le_rfl z (fun j hj => absurd j.2 (not_lt.2 hj)) hz

end GlobalTheory.CompanionTheory.Ar.Num.LatFlag

namespace GlobalTheory.CompanionTheory.Ar.Num.LatFlag

open GroundTheory.Heights₂.Heights.NumbersDVR (pointConeMap blockWeight IsRelevant IsVerticalDivisor)

section Cone

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} {Ω : Type} [Field Ω]
  (y : (Σ k, J k) → Ω)

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg`. Rewrite using `[Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), hf, hg, map_add, map_mul]`. Simplify using `only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `single p n`. Rewrite using `[Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), Finsupp.weight_single, mul_pow, map_pow]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single p.1]`.

Simplify using `[blockWeight]`. Introduce `k _ hk`. Simplify using `[blockWeight, hk]`. Simplify using the standard rewrite rules.
-/
theorem cone_prod (d : (Σ k, J k) →₀ ℕ) :
    (d.prod fun p n => (C (y p) * X p.1 : MvPolynomial K Ω) ^ n) =
      C (d.prod fun p n => y p ^ n) * ∏ k, X k ^ (Finsupp.weight (blockWeight J) d k) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]), Finsupp.prod_add_index' (by simp) (by intros; rw [pow_add]),
      hf, hg, map_add, map_mul]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | single p n =>
    rw [Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp), Finsupp.weight_single, mul_pow, map_pow]
    congr 1
    rw [Finset.prod_eq_single p.1]
    · simp [blockWeight]
    · intro k _ hk
      simp [blockWeight, hk]
    · simp

variable {O : Type} [CommRing O] [Algebra O Ω]

/- English proof (translation)
Use `conv_lhs => rw [← support_sum_monomial_coeff h]`. Use `conv_rhs => rw [← support_sum_monomial_coeff h]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hw : Finsupp.weight (blockWeight J) d = b` using `hh (mem_support_iff.1 hd)`.

Rewrite using `[GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, aeval_monomial, aeval_monomial, cone_prod, hw, map_mul]`. Simplify using `only [MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, _root_.mul_assoc]`.
-/
theorem cone_eq {h : MvPolynomial (Σ k, J k) O} {b : K → ℕ}
    (hh : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h b) :
    pointConeMap O y h = C (aeval y h) * ∏ k, X k ^ b k := by
  classical
  conv_lhs => rw [← support_sum_monomial_coeff h]
  conv_rhs => rw [← support_sum_monomial_coeff h]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWeight J) d = b := hh (mem_support_iff.1 hd)
  rw [GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, aeval_monomial, aeval_monomial, cone_prod, hw, map_mul]
  simp only [MvPolynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, _root_.mul_assoc]

/- English proof (translation)
Rewrite using `[pointIdeal, RingHom.mem_ker, map_sub, cone_eq y hh, cone_eq y hh', he, sub_self]`.
-/
theorem sub_mem_pointIdeal {h h' : MvPolynomial (Σ k, J k) O} {b : K → ℕ}
    (hh : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h b) (hh' : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h' b)
    (he : aeval y h = aeval y h') : h - h' ∈ pointIdeal O y := by
  rw [pointIdeal, RingHom.mem_ker, map_sub, cone_eq y hh, cone_eq y hh', he, sub_self]

/- English proof (translation)
Introduce `hm`. Rewrite `hm` using `[pointIdeal, RingHom.mem_ker, cone_eq y hh]`. Break down `mul_eq_zero.1 hm with h1 | h1` into its components or cases. Conclude with `h0 (C_eq_zero.1 h1)`. Conclude with `(Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) h1`.
-/
theorem not_mem_pointIdeal {h : MvPolynomial (Σ k, J k) O} {b : K → ℕ}
    (hh : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h b) (h0 : aeval y h ≠ 0) : h ∉ pointIdeal O y := by
  intro hm
  rw [pointIdeal, RingHom.mem_ker, cone_eq y hh] at hm
  rcases mul_eq_zero.1 hm with h1 | h1
  · exact h0 (C_eq_zero.1 h1)
  · exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (X_ne_zero k)) h1

/- English proof (translation)
The claim follows from `IsWeightedHomogeneous.mul hf hg`.
-/
theorem mh_mul {f g : MvPolynomial (Σ k, J k) O} {a b : K → ℕ} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a)
    (hg : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g b) : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (f * g) (a + b) :=
  IsWeightedHomogeneous.mul hf hg

/- English proof (translation)
The claim follows from `h ▸ mh_mul hf hg`.
-/
theorem mh_mul' {f g : MvPolynomial (Σ k, J k) O} {a b c : K → ℕ} (h : c = a + b)
    (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a)
    (hg : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g b) : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (f * g) c :=
  h ▸ mh_mul hf hg

/- English proof (translation)
The claim follows from `IsWeightedHomogeneous.add hf hg`.
-/
theorem mh_add {f g : MvPolynomial (Σ k, J k) O} {a : K → ℕ} (hf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f a)
    (hg : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g a) : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (f + g) a :=
  IsWeightedHomogeneous.add hf hg

/- English proof (translation)
Establish `h` using `IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O)) (fun k => b k • blockWeight J ⟨k, c k⟩) (fun k _ => (isWeightedHomogeneous_X O (blockWeight J) ⟨k, c k⟩).pow (b k))`. Establish `e : ∑ k, b k • blockWeight J ⟨k, c k⟩ = b`. Use function extensionality and compare the values at `k'`. Simplify using `[blockWeight, Finset.sum_apply, Pi.single_apply]`. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
theorem isMultiHomog_coord (c : (k : K) → J k) (b : K → ℕ) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (∏ k, X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O) b := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O))
    (fun k => b k • blockWeight J ⟨k, c k⟩) (fun k _ => (isWeightedHomogeneous_X O (blockWeight J) ⟨k, c k⟩).pow (b k))
  have e : ∑ k, b k • blockWeight J ⟨k, c k⟩ = b := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]`.
-/
theorem Y_add (c : (k : K) → J k) (a b : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (a + b) k = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ b k := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]

/- English proof (translation)
Simplify using `[map_prod]`.
-/
theorem aeval_coord (c : (k : K) → J k) (b : K → ℕ) :
    aeval y (∏ k, X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O) = ∏ k, y ⟨k, c k⟩ ^ b k := by
  simp [map_prod]

/- English proof (translation)
Use `⟨mh_add (mh_mul hh1 (isMultiHomog_coord (O := O) c b2)) (mh_mul' (add_comm b1 b2) hh2 (isMultiHomog_coord (O := O) c b1)), ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, aeval_coord, aeval_coord, hv1, hv2, Y_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_add (c : (k : K) → J k) {s t : Ω} {b1 b2 : K → ℕ} {h1 h2 : MvPolynomial (Σ k, J k) O}
    (hh1 : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h1 b1) (hh2 : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h2 b2)
    (hv1 : aeval y h1 = s * ∏ k, y ⟨k, c k⟩ ^ b1 k) (hv2 : aeval y h2 = t * ∏ k, y ⟨k, c k⟩ ^ b2 k) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog
        (h1 * (∏ k, X ⟨k, c k⟩ ^ b2 k) + h2 * (∏ k, X ⟨k, c k⟩ ^ b1 k) : MvPolynomial (Σ k, J k) O) (b1 + b2) ∧
      aeval y (h1 * (∏ k, X ⟨k, c k⟩ ^ b2 k) + h2 * (∏ k, X ⟨k, c k⟩ ^ b1 k) : MvPolynomial (Σ k, J k) O) =
        (s + t) * ∏ k, y ⟨k, c k⟩ ^ (b1 + b2) k := by
  refine ⟨mh_add (mh_mul hh1 (isMultiHomog_coord (O := O) c b2))
    (mh_mul' (add_comm b1 b2) hh2 (isMultiHomog_coord (O := O) c b1)), ?_⟩
  rw [map_add, map_mul, map_mul, aeval_coord, aeval_coord, hv1, hv2, Y_add]
  ring

/- English proof (translation)
Rewrite using `[map_mul, hv1, hv2, Y_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_mul (c : (k : K) → J k) {s t : Ω} {b1 b2 : K → ℕ} {h1 h2 : MvPolynomial (Σ k, J k) O}
    (hv1 : aeval y h1 = s * ∏ k, y ⟨k, c k⟩ ^ b1 k) (hv2 : aeval y h2 = t * ∏ k, y ⟨k, c k⟩ ^ b2 k) :
    aeval y (h1 * h2) = (s * t) * ∏ k, y ⟨k, c k⟩ ^ (b1 + b2) k := by
  rw [map_mul, hv1, hv2, Y_add]
  ring

/- English proof (translation)
Proceed by induction on `hs using Algebra.adjoin_induction with`. Consider the case `mem a ha`. Take `⟨j, rfl⟩` from `ha`. Establish `h1` using `isMultiHomog_coord (O := O) j (fun _ => 1)`. Use `⟨_, _, h1, ?_⟩` and prove the remaining obligations.

Rewrite using `[aeval_coord]`. Simplify using `only [pow_one]`. Conclude with `(div_mul_cancel₀ _ hc).symm`. Consider the case `algebraMap o`. Establish `h1 : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C o : MvPolynomial (Σ k, J k) O) 0` using `isWeightedHomogeneous_C _ o`.

Use `⟨_, _, h1, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_C]`. Simplify using `only [Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one]`. Consider the case `add a b _ _ ha hb`. Take `⟨b1, h1, hh1, hv1⟩` from `ha`.

Take `⟨b2, h2, hh2, hv2⟩` from `hb`. Take `⟨h3, h4⟩` from `form_add y c hh1 hh2 hv1 hv2`. Conclude with `⟨_, _, h3, h4⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨b1, h1, hh1, hv1⟩` from `ha`.

Take `⟨b2, h2, hh2, hv2⟩` from `hb`. Conclude with `⟨_, _, mh_mul hh1 hh2, form_mul y c hv1 hv2⟩`.
-/
theorem exists_form (c : (k : K) → J k) (hc : segreVec y c ≠ 0) {s : Ω} (hs : s ∈ chartRing O (segreVec y) c) :
    ∃ (b : K → ℕ) (h : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h b ∧
      aeval y h = s * ∏ k, y ⟨k, c k⟩ ^ b k := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨j, rfl⟩ := ha
    have h1 := isMultiHomog_coord (O := O) j (fun _ => 1)
    refine ⟨_, _, h1, ?_⟩
    rw [aeval_coord]
    simp only [pow_one]
    exact (div_mul_cancel₀ _ hc).symm
  | algebraMap o =>
    have h1 : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C o : MvPolynomial (Σ k, J k) O) 0 :=
      isWeightedHomogeneous_C _ o
    refine ⟨_, _, h1, ?_⟩
    rw [aeval_C]
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, mul_one]
  | add a b _ _ ha hb =>
    obtain ⟨b1, h1, hh1, hv1⟩ := ha
    obtain ⟨b2, h2, hh2, hv2⟩ := hb
    obtain ⟨h3, h4⟩ := form_add y c hh1 hh2 hv1 hv2
    exact ⟨_, _, h3, h4⟩
  | mul a b _ _ ha hb =>
    obtain ⟨b1, h1, hh1, hv1⟩ := ha
    obtain ⟨b2, h2, hh2, hv2⟩ := hb
    exact ⟨_, _, mh_mul hh1 hh2, form_mul y c hv1 hv2⟩

def formIdeal (c : (k : K) → J k) (hc : segreVec y c ≠ 0) (W : Ideal (MvPolynomial (Σ k, J k) O)) :
    Ideal (chartRing O (segreVec y) c) where
  carrier := {r | ∃ (b : K → ℕ) (h : MvPolynomial (Σ k, J k) O), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h b ∧
    aeval y h = (r : Ω) * (∏ k, y ⟨k, c k⟩ ^ b k) ∧ h ∈ W}
  add_mem' := by
    rintro a b ⟨b1, h1, hh1, hv1, hm1⟩ ⟨b2, h2, hh2, hv2, hm2⟩
    obtain ⟨h3, h4⟩ := form_add y c hh1 hh2 hv1 hv2
    exact ⟨_, _, h3, by rw [h4, AddMemClass.coe_add], add_mem (W.mul_mem_right _ hm1) (W.mul_mem_right _ hm2)⟩
  zero_mem' := by
    have h0 : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (0 : MvPolynomial (Σ k, J k) O) (0 : K → ℕ) :=
      isWeightedHomogeneous_zero _ _ _
    refine ⟨_, _, h0, ?_, W.zero_mem⟩
    rw [map_zero, ZeroMemClass.coe_zero, zero_mul]
  smul_mem' := by
    rintro a b ⟨b1, h1, hh1, hv1, hm1⟩
    obtain ⟨b2, h2, hh2, hv2⟩ := exists_form y c hc a.2
    exact ⟨_, _, mh_mul hh2 hh1, by rw [form_mul y c hv2 hv1, smul_eq_mul, MulMemClass.coe_mul],
      W.mul_mem_left _ hm1⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_formIdeal {c : (k : K) → J k} {hc : segreVec y c ≠ 0} {W : Ideal (MvPolynomial (Σ k, J k) O)}
    {r : chartRing O (segreVec y) c} : r ∈ formIdeal y c hc W ↔ ∃ (b : K → ℕ) (h : MvPolynomial (Σ k, J k) O),
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h b ∧ aeval y h = (r : Ω) * (∏ k, y ⟨k, c k⟩ ^ b k) ∧ h ∈ W :=
  Iff.rfl

/- English proof (translation)
Use `sub_mem hm (hPW (sub_mem_pointIdeal y hh hh' he))` as an intermediate fact. Simplify using `using this`.
-/
theorem mem_of_aeval_eq {W : Ideal (MvPolynomial (Σ k, J k) O)} (hPW : pointIdeal O y ≤ W)
    {h h' : MvPolynomial (Σ k, J k) O} {b : K → ℕ} (hh : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h b)
    (hh' : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog h' b) (he : aeval y h = aeval y h') (hm : h ∈ W) : h' ∈ W := by
  have := sub_mem hm (hPW (sub_mem_pointIdeal y hh hh' he))
  simpa using this

/- English proof (translation)
Use `⟨fun htop => ?_, fun {r1 r2} hab => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : chartRing O (segreVec y) c) ∈ formIdeal y c hc W` using `htop ▸ Submodule.mem_top`. Take `⟨b, h, hh, hv, hm⟩` from `(mem_formIdeal y).1 h1`. Use `hxW b (mem_of_aeval_eq y hPW hh (isMultiHomog_coord (O := O) c b) ?_ hm)` and prove the remaining obligations. Rewrite using `[hv, aeval_coord, OneMemClass.coe_one, one_mul]`.

Take `⟨b, h, hh, hv, hm⟩` from `(mem_formIdeal y).1 hab`. Take `⟨b1, h1, hh1, hv1⟩` from `exists_form y c hc r1.2`. Take `⟨b2, h2, hh2, hv2⟩` from `exists_form y c hc r2.2`. Establish `hm2 : h1 * h2 * (∏ k, X ⟨k, c k⟩ ^ b k) ∈ W`. Establish `e1` using `mh_mul hh (isMultiHomog_coord (O := O) c (b1 + b2))`.

Establish `e2` using `mh_mul' (add_comm b (b1 + b2)) (mh_mul hh1 hh2) (isMultiHomog_coord (O := O) c b)`. Use `mem_of_aeval_eq y hPW e1 e2 ?_ (W.mul_mem_right _ hm)` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_mul, hv, hv1, hv2, aeval_coord, aeval_coord, Y_add, MulMemClass.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Break down `hW.mem_or_mem hm2 with h3 | h3` into its components or cases.

Break down `hW.mem_or_mem h3 with h4 | h4` into its components or cases. Conclude with `Or.inl ((mem_formIdeal y).2 ⟨b1, h1, hh1, hv1, h4⟩)`. Conclude with `Or.inr ((mem_formIdeal y).2 ⟨b2, h2, hh2, hv2, h4⟩)`. Conclude with `(hxW b h3).elim`.
-/
theorem formIdeal_isPrime {c : (k : K) → J k} (hc : segreVec y c ≠ 0) {W : Ideal (MvPolynomial (Σ k, J k) O)}
    (hW : W.IsPrime) (hPW : pointIdeal O y ≤ W)
    (hxW : ∀ b : K → ℕ, (∏ k, X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O) ∉ W) : (formIdeal y c hc W).IsPrime := by
  refine ⟨fun htop => ?_, fun {r1 r2} hab => ?_⟩
  · have h1 : (1 : chartRing O (segreVec y) c) ∈ formIdeal y c hc W := htop ▸ Submodule.mem_top
    obtain ⟨b, h, hh, hv, hm⟩ := (mem_formIdeal y).1 h1
    refine hxW b (mem_of_aeval_eq y hPW hh (isMultiHomog_coord (O := O) c b) ?_ hm)
    rw [hv, aeval_coord, OneMemClass.coe_one, one_mul]
  · obtain ⟨b, h, hh, hv, hm⟩ := (mem_formIdeal y).1 hab
    obtain ⟨b1, h1, hh1, hv1⟩ := exists_form y c hc r1.2
    obtain ⟨b2, h2, hh2, hv2⟩ := exists_form y c hc r2.2
    have hm2 : h1 * h2 * (∏ k, X ⟨k, c k⟩ ^ b k) ∈ W := by
      have e1 := mh_mul hh (isMultiHomog_coord (O := O) c (b1 + b2))
      have e2 := mh_mul' (add_comm b (b1 + b2)) (mh_mul hh1 hh2) (isMultiHomog_coord (O := O) c b)
      refine mem_of_aeval_eq y hPW e1 e2 ?_ (W.mul_mem_right _ hm)
      rw [map_mul, map_mul, map_mul, hv, hv1, hv2, aeval_coord, aeval_coord, Y_add, MulMemClass.coe_mul]
      ring
    rcases hW.mem_or_mem hm2 with h3 | h3
    · rcases hW.mem_or_mem h3 with h4 | h4
      · exact Or.inl ((mem_formIdeal y).2 ⟨b1, h1, hh1, hv1, h4⟩)
      · exact Or.inr ((mem_formIdeal y).2 ⟨b2, h2, hh2, hv2, h4⟩)
    · exact (hxW b h3).elim

/- English proof (translation)
Introduce `hm`. Take `⟨b, h, hh, hv, hm⟩` from `(mem_formIdeal y).1 hm`. Establish `h0 : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C ϖ : MvPolynomial (Σ k, J k) O) 0` using `isWeightedHomogeneous_C _ ϖ`. Establish `e2` using `mh_mul' (zero_add b).symm h0 (isMultiHomog_coord (O := O) c b)`. Establish `h1 : C ϖ * (∏ k, X ⟨k, c k⟩ ^ b k) ∈ W`.

Use `mem_of_aeval_eq y hPW hh e2 ?_ hm` and prove the remaining obligations. Rewrite using `[hv, hs, map_mul, aeval_coord, aeval_C]`. Break down `hW.mem_or_mem h1 with h2 | h2` into its components or cases. Conclude with `hϖW h2`. Conclude with `hxW b h2`.
-/
theorem not_mem_formIdeal_of_uniformiser {c : (k : K) → J k} (hc : segreVec y c ≠ 0)
    {W : Ideal (MvPolynomial (Σ k, J k) O)} (hW : W.IsPrime) (hPW : pointIdeal O y ≤ W)
    (hxW : ∀ b : K → ℕ, (∏ k, X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O) ∉ W) {ϖ : O}
    (hϖW : (C ϖ : MvPolynomial (Σ k, J k) O) ∉ W) (s : chartRing O (segreVec y) c)
    (hs : (s : Ω) = algebraMap O Ω ϖ) : s ∉ formIdeal y c hc W := by
  intro hm
  obtain ⟨b, h, hh, hv, hm⟩ := (mem_formIdeal y).1 hm
  have h0 : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (C ϖ : MvPolynomial (Σ k, J k) O) 0 :=
    isWeightedHomogeneous_C _ ϖ
  have e2 := mh_mul' (zero_add b).symm h0 (isMultiHomog_coord (O := O) c b)
  have h1 : C ϖ * (∏ k, X ⟨k, c k⟩ ^ b k) ∈ W := by
    refine mem_of_aeval_eq y hPW hh e2 ?_ hm
    rw [hv, hs, map_mul, aeval_coord, aeval_C]
  rcases hW.mem_or_mem h1 with h2 | h2
  · exact hϖW h2
  · exact hxW b h2

end Cone

/- English proof (translation)
Use `IsVerticalDivisor.of_unit_off_special ⟨bf, bg, hbf, hbg, rfl⟩ (not_mem_pointIdeal y hbf hf) (not_mem_pointIdeal y hbg hg) ?_` and prove the remaining obligations. Introduce `W hW hPW hrel hϖW`. Use `choose c hcW using hrel`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Introduce `k h0`.

Apply `hcW k` to reduce the goal to its premises. Apply `hPW` to reduce the goal to its premises. Rewrite using `[pointIdeal, RingHom.mem_ker]`. Simplify using `[GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, h0]`. Establish `hc : segreVec y c ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hyc k`.

Establish `hxW : ∀ b : K → ℕ, (∏ k, X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O) ∉ W`. Introduce `b hmem`. Take `⟨k, -, hk⟩` from `(hW.prod_mem_iff).1 hmem`. Conclude with `hcW k (hW.mem_of_pow_mem _ hk)`. Take `⟨s, t, hs, ht, heq⟩` from `H c hc (formIdeal y c hc W) (formIdeal_isPrime y hc hW hPW hxW) (not_mem_formIdeal_of_uniformiser y hc hW hPW hxW hϖW)`.

Take `⟨b1, hs', hhs, hvs⟩` from `exists_form y c hc s.2`. Take `⟨b2, ht', hht, hvt⟩` from `exists_form y c hc t.2`. Establish `hsW : hs' ∉ W` using `fun h => hs ((mem_formIdeal y).2 ⟨b1, hs', hhs, hvs, h⟩)`. Establish `htW : ht' ∉ W` using `fun h => ht ((mem_formIdeal y).2 ⟨b2, ht', hht, hvt, h⟩)`. Establish `hu : hs' * (∏ k, X ⟨k, c k⟩ ^ (bg + b2) k) ∉ W` using `fun h => (hW.mem_or_mem h).elim hsW (hxW (bg + b2))`.

Establish `hv : ht' * (∏ k, X ⟨k, c k⟩ ^ (bf + b1) k) ∉ W` using `fun h => (hW.mem_or_mem h).elim htW (hxW (bf + b1))`. Use `⟨_, _, hu, hv, ?_⟩` and prove the remaining obligations. Establish `hdeg : b2 + (bf + b1) + bg = b1 + (bg + b2) + bf`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply]`.

Use linear arithmetic over natural numbers and integers. Establish `e1` using `mh_mul (mh_mul hhs (isMultiHomog_coord (O := O) c (bg + b2))) hbf`. Establish `e2` using `mh_mul' hdeg.symm (mh_mul hht (isMultiHomog_coord (O := O) c (bf + b1))) hbg`. Use `sub_mem_pointIdeal y e1 e2 ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_mul, map_mul, aeval_coord, aeval_coord, hvs, hvt, Y_add, Y_add]`.

Take the linear combination `(∏ k, y ⟨k, c k⟩ ^ b1 k) * (∏ k, y ⟨k, c k⟩ ^ b2 k) * heq`.
-/
theorem vertical_of_local (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type)
    [Field Ω] (y : (Σ k, J k) → Ω) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω]
    (ϖ : O) (f g : MvPolynomial (Σ k, J k) O) (bf bg : K → ℕ)
    (hbf : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf) (hbg : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg)
    (hf : aeval y f ≠ 0) (hg : aeval y g ≠ 0)
    (H : ∀ c : (k : K) → J k, segreVec y c ≠ 0 → ∀ P : Ideal (chartRing O (segreVec y) c), P.IsPrime →
      (∀ s : chartRing O (segreVec y) c, (s : Ω) = algebraMap O Ω ϖ → s ∉ P) →
      ∃ s t : chartRing O (segreVec y) c, s ∉ P ∧ t ∉ P ∧
        (s : Ω) * (aeval y f * ∏ k, y ⟨k, c k⟩ ^ bg k) = (t : Ω) * (aeval y g * ∏ k, y ⟨k, c k⟩ ^ bf k)) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsVerticalDivisor (pointIdeal O y) ϖ (fun k => (bf k : ℤ) - bg k) f g := by
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, hbf, hbg, rfl⟩ (not_mem_pointIdeal y hbf hf)
    (not_mem_pointIdeal y hbg hg) ?_
  intro W hW hPW hrel hϖW
  choose c hcW using hrel
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hcW k
    apply hPW
    rw [pointIdeal, RingHom.mem_ker]
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.pointConeMap, h0]
  have hc : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hyc k
  have hxW : ∀ b : K → ℕ, (∏ k, X ⟨k, c k⟩ ^ b k : MvPolynomial (Σ k, J k) O) ∉ W := by
    intro b hmem
    obtain ⟨k, -, hk⟩ := (hW.prod_mem_iff).1 hmem
    exact hcW k (hW.mem_of_pow_mem _ hk)
  obtain ⟨s, t, hs, ht, heq⟩ := H c hc (formIdeal y c hc W) (formIdeal_isPrime y hc hW hPW hxW)
    (not_mem_formIdeal_of_uniformiser y hc hW hPW hxW hϖW)
  obtain ⟨b1, hs', hhs, hvs⟩ := exists_form y c hc s.2
  obtain ⟨b2, ht', hht, hvt⟩ := exists_form y c hc t.2
  have hsW : hs' ∉ W := fun h => hs ((mem_formIdeal y).2 ⟨b1, hs', hhs, hvs, h⟩)
  have htW : ht' ∉ W := fun h => ht ((mem_formIdeal y).2 ⟨b2, ht', hht, hvt, h⟩)
  have hu : hs' * (∏ k, X ⟨k, c k⟩ ^ (bg + b2) k) ∉ W := fun h => (hW.mem_or_mem h).elim hsW (hxW (bg + b2))
  have hv : ht' * (∏ k, X ⟨k, c k⟩ ^ (bf + b1) k) ∉ W := fun h => (hW.mem_or_mem h).elim htW (hxW (bf + b1))
  refine ⟨_, _, hu, hv, ?_⟩
  have hdeg : b2 + (bf + b1) + bg = b1 + (bg + b2) + bf := by
    funext k
    simp only [Pi.add_apply]
    omega
  have e1 := mh_mul (mh_mul hhs (isMultiHomog_coord (O := O) c (bg + b2))) hbf
  have e2 := mh_mul' hdeg.symm (mh_mul hht (isMultiHomog_coord (O := O) c (bf + b1))) hbg
  refine sub_mem_pointIdeal y e1 e2 ?_
  rw [map_mul, map_mul, map_mul, map_mul, aeval_coord, aeval_coord, hvs, hvt, Y_add, Y_add]
  linear_combination (∏ k, y ⟨k, c k⟩ ^ b1 k) * (∏ k, y ⟨k, c k⟩ ^ b2 k) * heq

end GlobalTheory.CompanionTheory.Ar.Num.LatFlag

namespace GlobalTheory.CompanionTheory.Ar.Num.LatFlag

/- English proof (translation)
Set `I : Ideal (chartRing O x c)` to `{ carrier := {s | (s : Ω) * a ∈ chartRing O x c} add_mem' := fun {s t} hs ht => by show ((s + t : chartRing O x c) : Ω) * a ∈ chartRing O x c`. Use `add_mem (show (s : Ω) * a ∈ chartRing O x c from hs) (show (t : Ω) * a ∈ chartRing O x c from ht)` as an intermediate fact. Simplify `this` using `[add_mul]`. Use the proof step `zero_mem' := by show ((0 : chartRing O x c) : Ω) * a ∈ chartRing O x c`. Simplify using the standard rewrite rules.

Use the proof step `smul_mem' := fun b s hs => by show ((b * s : chartRing O x c) : Ω) * a ∈ chartRing O x c`. Use `mul_mem b.2 (show (s : Ω) * a ∈ chartRing O x c from hs)` as an intermediate fact. Simplify `this }` using `[_root_.mul_assoc]`. Establish `hmem : (⟨f, hf⟩ : chartRing O x c) ∈ I.radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`.

Introduce and unpack `P ⟨hIP, hP⟩`. Assume the negation of the conclusion as `hfP`. Take `⟨q, hq, hO, hu, hfr⟩` from `chart_point X Ω ξ κ x A m O hT c hc hA P hP`. Take `⟨s, hs, hsa⟩` from `hfr a (ha q hq hO (hu _ hfP))`. Conclude with `hs (hIP hsa)`.

Take `⟨n, hn⟩` from `hmem`. Establish `hn' : (((⟨f, hf⟩ : chartRing O x c) ^ n : chartRing O x c) : Ω) * a ∈ chartRing O x c` using `hn`. Conclude with `⟨n, by simpa using hn'⟩`.
-/
theorem exists_pow_mul_mem (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type)
    (x : κ → Ω) (A : Type) [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O]
    [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (hT : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    (hA : ∀ a : A, algebraMap A Ω a ∈ chartRing ℤ x c) (f : Ω) (hf : f ∈ chartRing O x c) (a : Ω)
    (ha : ∀ q : Cpt ξ, InChart ξ x c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → unitAt ξ q f → a ∈ regAt ξ q) :
    ∃ n : ℕ, f ^ n * a ∈ chartRing O x c := by
  classical
  let I : Ideal (chartRing O x c) :=
    { carrier := {s | (s : Ω) * a ∈ chartRing O x c}
      add_mem' := fun {s t} hs ht => by
        show ((s + t : chartRing O x c) : Ω) * a ∈ chartRing O x c
        have := add_mem (show (s : Ω) * a ∈ chartRing O x c from hs) (show (t : Ω) * a ∈ chartRing O x c from ht)
        simpa [add_mul] using this
      zero_mem' := by
        show ((0 : chartRing O x c) : Ω) * a ∈ chartRing O x c
        simp
      smul_mem' := fun b s hs => by
        show ((b * s : chartRing O x c) : Ω) * a ∈ chartRing O x c
        have := mul_mem b.2 (show (s : Ω) * a ∈ chartRing O x c from hs)
        simpa [_root_.mul_assoc] using this }
  have hmem : (⟨f, hf⟩ : chartRing O x c) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hIP, hP⟩
    by_contra hfP
    obtain ⟨q, hq, hO, hu, hfr⟩ := chart_point X Ω ξ κ x A m O hT c hc hA P hP
    obtain ⟨s, hs, hsa⟩ := hfr a (ha q hq hO (hu _ hfP))
    exact hs (hIP hsa)
  obtain ⟨n, hn⟩ := hmem
  have hn' : (((⟨f, hf⟩ : chartRing O x c) ^ n : chartRing O x c) : Ω) * a ∈ chartRing O x c := hn
  exact ⟨n, by simpa using hn'⟩

/- English proof (translation)
Introduce `d hd`. Use `h ?_` and prove the remaining obligations. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[coeff_map, h0, map_zero]`.
-/
theorem isMultiHomog_map {K : Type} [DecidableEq K] {J : K → Type} {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) {f : MvPolynomial (Σ k, J k) R} {b : K → ℕ}
    (h : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f b) :
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (MvPolynomial.map φ f) b := by
  intro d hd
  refine h ?_
  intro h0
  apply hd
  rw [coeff_map, h0, map_zero]

/- English proof (translation)
Introduce `X Ω _ ξ K _ _ J _ y hT d hd A _ _ _ _ hAinj hconst p hp m _ hpm O _ _ _ _ _ _ _ ϖ hϖ E _ _ r w L L' Q hQ hoff`. Take `⟨hvb, hvb', hi⟩` from `hQ`. Use `choose e e' he he' hdeg hg0 hfg using hi`. Establish `he0 : ∀ i, e i ≠ 0` using `fun i => (he i).1`. Establish `he0' : ∀ i, e' i ≠ 0` using `fun i => (he' i).1`.

Take `⟨B, hBl, hBf⟩` from `GlobalTheory.T.dedekind_constants_degree_one X Ω ξ K J y hT d hd A hAinj hconst p hp m hpm O E r w L hvb`. Take `⟨B', hBl', hBf'⟩` from `GlobalTheory.T.dedekind_constants_degree_one X Ω ξ K J y hT d hd A hAinj hconst p hp m hpm O E r w L' hvb'`. Establish `hfr` using `hBf Q.x e he0 he`. Establish `hfr'` using `hBf' Q.x' e' he0' he'`. Take `⟨-, hmod, -⟩` from `GlobalTheory.T.localization_model_over_place K J Ω y A hAinj hconst d hd m O`.

Establish `hT' : CoordTie ℤ ξ (segreVec y)` using `hT`. Establish `hinj : Function.Injective (algebraMap A O)`. Introduce `a b hab`. Apply `hAinj` to reduce the goal to its premises. Rewrite using `[IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω, hab]`.

Establish `hover : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → q ∈ overPrime ξ p`. Introduce `q hO p' hp' hne hF`. Apply `hF` to reduce the goal to its premises. Use `unitAt_algebraMap hO (isUnit_natCast_of_ne A m O p p' hp hp' hne hpm)` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Establish `hnf : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → unitAt ξ q (algebraMap O Ω ϖ) → ¬ InFibre ξ p q`. Introduce `q hO hu hF`. Apply `hF` to reduce the goal to its premises. Take `⟨n, u, hu', hpu⟩` from `exists_natCast_eq A m O hinj p hp ϖ hϖ`. Establish `h1` using `unitAt_mul (unitAt_algebraMap hO hu') (unitAt_pow hu n)`.

Rewrite `h1` using `[← map_pow, ← map_mul, ← hpu, map_natCast]`. Conclude with `h1`. Establish `hLL : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → unitAt ξ q (algebraMap O Ω ϖ) → L q = L' q` using `fun q hO hu => hoff q (hover q hO) (hnf q hO hu)`. Set `ue : Fin r → Ωˣ` to `fun i => Units.mk0 (e i) (he0 i)`. Set `ue' : Fin r → Ωˣ` to `fun i => Units.mk0 (e' i) (he0' i)`.

Set `good : ((k : K) → J k) → Cpt ξ → Prop` to `fun c q => InChart ξ (segreVec y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ unitAt ξ q (algebraMap O Ω ϖ)`. Establish `hpow : ∀ c, segreVec y c ≠ 0 → ∀ a : Ω, (∀ q, good c q → a ∈ regAt ξ q) → ∃ n : ℕ, algebraMap O Ω ϖ ^ n * a ∈ chartRing O (segreVec y) c` using `fun c hc a ha => exists_pow_mul_mem X Ω ξ _ (segreVec y) A m O hT' c hc (hconst c hc) _ (Subalgebra.algebraMap_mem _ ϖ) a fun q hq hO hu => ha q ⟨hq, hO, hu⟩`. Establish `hsame : SameGenericFibre ϖ B B'`. Introduce `c hc`. Establish `hϖc : algebraMap O Ω ϖ ∈ chartRing O (segreVec y) c` using `Subalgebra.algebraMap_mem _ ϖ`.

Prove the components needed by the constructor for the conclusion. Introduce `z hz`. Conclude with `flag_sections X Ω ξ K J y O E r w ue' Q.x' B' L' c hc (good c) (algebraMap O Ω ϖ) hϖc hfr' (fun z hz q hq => (hBl' c hc z).1 hz q hq.1 hq.2.1) (fun q hq => hq.2.2.2.1) (fun q hq i => by simpa [ue'] using (he' i).2 q (hover q hq.2.1) c hq.1) (hpow c hc) z (fun q hq => by`. Rewrite using `[← hLL q hq.2.1 hq.2.2]`. Conclude with `(hBl c hc z).1 hz q hq.1 hq.2.1)`.

Introduce `z hz`. Conclude with `flag_sections X Ω ξ K J y O E r w ue Q.x B L c hc (good c) (algebraMap O Ω ϖ) hϖc hfr (fun z hz q hq => (hBl c hc z).1 hz q hq.1 hq.2.1) (fun q hq => hq.2.2.2.1) (fun q hq i => by simpa [ue] using (he i).2 q (hover q hq.2.1) c hq.1) (hpow c hc) z (fun q hq => by`. Rewrite using `[hLL q hq.2.1 hq.2.2]`. Conclude with `(hBl' c hc z).1 hz q hq.1 hq.2.1)`. Establish `hcoef : ∀ i j, (w.unitsSMul ue).repr ((w.unitsSMul ue') i) j = if i = j then e' i / e i else 0`.

Introduce `i j`. Rewrite using `[Module.Basis.repr_unitsSMul, Module.Basis.unitsSMul_apply]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[ue, ue', Units.smul_def, div_eq_mul_inv, mul_comm]`.

Simplify using `[ue, ue', Units.smul_def, h]`. Establish `hev : ∀ (f : MvPolynomial (Σ k, J k) ℤ), aeval y (MvPolynomial.map (Int.castRingHom O) f) = aeval y f`. Introduce `f`. Rewrite using `[← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]`. Use `⟨B, B', w.unitsSMul ue, w.unitsSMul ue', fun c hc z => ⟨hBl c hc z, hBl' c hc z⟩, hmod, hsame, ?_⟩` and prove the remaining obligations.

Use `⟨hfr, hfr', fun i j hij => ?_, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hcoef, if_neg hij.ne]`. Take `⟨bf, bg, hbf, hbg, hb⟩` from `hdeg i`. Establish `hf0 : aeval y (Q.f i) ≠ 0`. Rewrite using `[hfg i]`.

Conclude with `mul_ne_zero (div_ne_zero (he0' i) (he0 i)) (hg0 i)`. Establish `hv` using `vertical_of_local K J Ω y O ϖ (MvPolynomial.map (Int.castRingHom O) (Q.f i)) (MvPolynomial.map (Int.castRingHom O) (Q.g i)) bf bg (isMultiHomog_map _ hbf) (isMultiHomog_map _ hbg) (by rw [hev]; exact hf0) (by rw [hev]; exact hg0 i) ?_`. Rewrite `hv` using `[hb]`. Conclude with `hv`. Introduce `c hc P hP hϖP`.

Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)`. Take `⟨q, hq, hO, hu, hreg⟩` from `chart_point X Ω ξ _ (segreVec y) A m O hT' c hc (hconst c hc) P hP`. Establish `hϖu : unitAt ξ q (algebraMap O Ω ϖ)` using `hu ⟨_, Subalgebra.algebraMap_mem _ ϖ⟩ (hϖP _ rfl)`. Establish `h1` using `(he i).2 q (hover q hO) c hq`. Establish `h2` using `(he' i).2 q (hover q hO) c hq`.

Establish `hgr : (L.gr w i) q = (L'.gr w i) q`. Unfold `Lat.gr`. Rewrite using `[hLL q hO hϖu]`. Take `⟨Yx, hYx⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ Q.x i k` from `⟨_, rfl⟩`. Take `⟨Yx', hYx'⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ Q.x' i k` from `⟨_, rfl⟩`.

Take `⟨Yf, hYf⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ bf k` from `⟨_, rfl⟩`. Take `⟨Yg, hYg⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ bg k` from `⟨_, rfl⟩`. Establish `hYx0 : Yx ≠ 0`. Rewrite using `[hYx]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)`.

Establish `hYx0' : Yx' ≠ 0`. Rewrite using `[hYx']`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)`. Establish `hYf0 : Yf ≠ 0`. Rewrite using `[hYf]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)`. Establish `hYY : Yx * Yg = Yx' * Yf`. Rewrite using `[hYx, hYx', hYf, hYg, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `hk : (bf k : ℤ) - bg k = Q.x i k - Q.x' i k` using `congrFun hb k`.

Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[← hYx, smul_eq_mul]`. Rewrite `h2` using `[← hYx', smul_eq_mul]`.

Rewrite `hgr` using `[h1, h2]`. Establish `hα : Yx * e i ≠ 0` using `mul_ne_zero hYx0 (he0 i)`. Establish `hβ : Yx' * e' i ≠ 0` using `mul_ne_zero hYx0' (he0' i)`. Establish `hβm : Yx' * e' i ∈ Submodule.span (regAt ξ q) {Yx * e i}`. Rewrite using `[hgr]`.

Conclude with `Submodule.mem_span_singleton_self _`. Establish `hαm : Yx * e i ∈ Submodule.span (regAt ξ q) {Yx' * e' i}`. Rewrite using `[← hgr]`. Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨ρ, hρ⟩` from `Submodule.mem_span_singleton.1 hβm`.

Take `⟨ρ', hρ'⟩` from `Submodule.mem_span_singleton.1 hαm`. Establish `hρ1 : (ρ : Ω) = (Yx' * e' i) / (Yx * e i)`. Rewrite using `[eq_div_iff hα]`. Conclude with `hρ`. Establish `hρ2 : (ρ' : Ω) = ((Yx' * e' i) / (Yx * e i))⁻¹`.

Rewrite using `[inv_div, eq_div_iff hβ]`. Conclude with `hρ'`. Take `⟨s1, hs1, hm1⟩` from `hreg _ (hρ1 ▸ ρ.2)`. Take `⟨s2, hs2, hm2⟩` from `hreg _ (hρ2 ▸ ρ'.2)`. Use `⟨s1, ⟨_, hm1⟩, hs1, fun ht => ?_, ?_⟩` and prove the remaining obligations.

Establish `hmul : s1 * s2 = (⟨_, hm1⟩ : chartRing O (segreVec y) c) * ⟨_, hm2⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (s1 : Ω) * s2 = _ * _`. Rewrite using `[mul_mul_mul_comm, mul_inv_cancel₀ (div_ne_zero hβ hα), mul_one]`. Use `P.mul_mem_right (⟨_, hm2⟩ : chartRing O (segreVec y) c) ht` as an intermediate fact.

Rewrite `this` using `[← hmul]`. Conclude with `(hP.mem_or_mem this).elim hs1 hs2`. Use `show (s1 : Ω) * _ = (s1 : Ω) * _ * _`. Rewrite using `[hev, hev, hfg i, ← hYg, ← hYf]`. Establish `hYg' : Yg = Yx' * Yf / Yx`.

Rewrite using `[eq_div_iff hYx0]`. Take the linear combination `hYY`. Establish `hei` using `he0 i`. Rewrite using `[hYg']`. Clear the denominators using the available nonvanishing facts.

Simplify using `only [hcoef, if_true] show aeval y (MvPolynomial.map (Int.castRingHom O) (Q.f i)) = _ * aeval y (MvPolynomial.map (Int.castRingHom O) (Q.g i))`. Rewrite using `[hev, hev, hfg i]`.
-/
theorem flag_pair_of_lat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ d : ℕ, IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsDedekindDomain A] [Module.Finite ℤ A], Function.Injective (algebraMap A Ω) → HasConstants ℤ A y → ∀ (p : ℕ), p.Prime → ∀ (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (ϖ : O), Irreducible ϖ → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (w : Module.Basis (Fin r) Ω E) (L L' : Lat ξ E) (Q : LocPair J ℤ (Fin r)), IsLatFlagPair y (overPrime ξ p) L L' w Q → (∀ q : Cpt ξ, q ∈ overPrime ξ p → ¬ InFibre ξ p q → L q = L' q) → ∃ (B B' : ChartBundle O (segreVec y) r E) (v v' : Module.Basis (Fin r) Ω E), (∀ c, segreVec y c ≠ 0 → ∀ z, (z ∈ B.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → z ∈ L q) ∧ (z ∈ B'.lat c ↔ ∀ q : Cpt ξ, InChart ξ (segreVec y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → z ∈ L' q)) ∧ IsModelOver (pointIdeal O y) d ∧ SameGenericFibre ϖ B B' ∧ IsFlagPair ϖ y B B' v v' Q.x Q.x' (Q.map (Int.castRingHom O)).f (Q.map (Int.castRingHom O)).g := by
  intro X Ω _ ξ K _ _ J _ y hT d hd A _ _ _ _ hAinj hconst p hp m _ hpm O _ _ _ _ _ _ _ ϖ hϖ E _ _ r w L L' Q hQ hoff
  obtain ⟨hvb, hvb', hi⟩ := hQ
  choose e e' he he' hdeg hg0 hfg using hi
  have he0 : ∀ i, e i ≠ 0 := fun i => (he i).1
  have he0' : ∀ i, e' i ≠ 0 := fun i => (he' i).1
  obtain ⟨B, hBl, hBf⟩ := GlobalTheory.T.dedekind_constants_degree_one X Ω ξ K J y hT d hd A hAinj hconst p hp m hpm O E r w L hvb
  obtain ⟨B', hBl', hBf'⟩ := GlobalTheory.T.dedekind_constants_degree_one X Ω ξ K J y hT d hd A hAinj hconst p hp m hpm O E r w L' hvb'
  have hfr := hBf Q.x e he0 he
  have hfr' := hBf' Q.x' e' he0' he'
  obtain ⟨-, hmod, -⟩ := GlobalTheory.T.localization_model_over_place K J Ω y A hAinj hconst d hd m O
  have hT' : CoordTie ℤ ξ (segreVec y) := hT
  have hinj : Function.Injective (algebraMap A O) := by
    intro a b hab
    apply hAinj
    rw [IsScalarTower.algebraMap_apply A O Ω, IsScalarTower.algebraMap_apply A O Ω, hab]
  have hover : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → q ∈ overPrime ξ p := by
    intro q hO p' hp' hne hF
    apply hF
    have := unitAt_algebraMap hO (isUnit_natCast_of_ne A m O p p' hp hp' hne hpm)
    rwa [map_natCast] at this
  have hnf : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → unitAt ξ q (algebraMap O Ω ϖ) →
      ¬ InFibre ξ p q := by
    intro q hO hu hF
    apply hF
    obtain ⟨n, u, hu', hpu⟩ := exists_natCast_eq A m O hinj p hp ϖ hϖ
    have h1 := unitAt_mul (unitAt_algebraMap hO hu') (unitAt_pow hu n)
    rw [← map_pow, ← map_mul, ← hpu, map_natCast] at h1
    exact h1
  have hLL : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → unitAt ξ q (algebraMap O Ω ϖ) → L q = L' q :=
    fun q hO hu => hoff q (hover q hO) (hnf q hO hu)
  let ue : Fin r → Ωˣ := fun i => Units.mk0 (e i) (he0 i)
  let ue' : Fin r → Ωˣ := fun i => Units.mk0 (e' i) (he0' i)
  let good : ((k : K) → J k) → Cpt ξ → Prop := fun c q => InChart ξ (segreVec y) c q ∧
    (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ unitAt ξ q (algebraMap O Ω ϖ)
  have hpow : ∀ c, segreVec y c ≠ 0 → ∀ a : Ω, (∀ q, good c q → a ∈ regAt ξ q) →
      ∃ n : ℕ, algebraMap O Ω ϖ ^ n * a ∈ chartRing O (segreVec y) c := fun c hc a ha =>
    exists_pow_mul_mem X Ω ξ _ (segreVec y) A m O hT' c hc (hconst c hc) _ (Subalgebra.algebraMap_mem _ ϖ) a
      fun q hq hO hu => ha q ⟨hq, hO, hu⟩
  have hsame : SameGenericFibre ϖ B B' := by
    intro c hc
    have hϖc : algebraMap O Ω ϖ ∈ chartRing O (segreVec y) c := Subalgebra.algebraMap_mem _ ϖ
    constructor
    · intro z hz
      exact flag_sections X Ω ξ K J y O E r w ue' Q.x' B' L' c hc (good c) (algebraMap O Ω ϖ) hϖc hfr'
        (fun z hz q hq => (hBl' c hc z).1 hz q hq.1 hq.2.1)
        (fun q hq => hq.2.2.2.1) (fun q hq i => by simpa [ue'] using (he' i).2 q (hover q hq.2.1) c hq.1)
        (hpow c hc) z (fun q hq => by
          rw [← hLL q hq.2.1 hq.2.2]
          exact (hBl c hc z).1 hz q hq.1 hq.2.1)
    · intro z hz
      exact flag_sections X Ω ξ K J y O E r w ue Q.x B L c hc (good c) (algebraMap O Ω ϖ) hϖc hfr
        (fun z hz q hq => (hBl c hc z).1 hz q hq.1 hq.2.1)
        (fun q hq => hq.2.2.2.1) (fun q hq i => by simpa [ue] using (he i).2 q (hover q hq.2.1) c hq.1)
        (hpow c hc) z (fun q hq => by
          rw [hLL q hq.2.1 hq.2.2]
          exact (hBl' c hc z).1 hz q hq.1 hq.2.1)
  have hcoef : ∀ i j, (w.unitsSMul ue).repr ((w.unitsSMul ue') i) j =
      if i = j then e' i / e i else 0 := by
    intro i j
    rw [Module.Basis.repr_unitsSMul, Module.Basis.unitsSMul_apply]
    by_cases h : i = j
    · subst h
      simp [ue, ue', Units.smul_def, div_eq_mul_inv, mul_comm]
    · simp [ue, ue', Units.smul_def, h]
  have hev : ∀ (f : MvPolynomial (Σ k, J k) ℤ), aeval y (MvPolynomial.map (Int.castRingHom O) f) = aeval y f := by
    intro f
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap]
  refine ⟨B, B', w.unitsSMul ue, w.unitsSMul ue', fun c hc z => ⟨hBl c hc z, hBl' c hc z⟩, hmod, hsame, ?_⟩
  refine ⟨hfr, hfr', fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hcoef, if_neg hij.ne]
  · obtain ⟨bf, bg, hbf, hbg, hb⟩ := hdeg i
    have hf0 : aeval y (Q.f i) ≠ 0 := by
      rw [hfg i]
      exact mul_ne_zero (div_ne_zero (he0' i) (he0 i)) (hg0 i)
    have hv := vertical_of_local K J Ω y O ϖ (MvPolynomial.map (Int.castRingHom O) (Q.f i))
      (MvPolynomial.map (Int.castRingHom O) (Q.g i)) bf bg (isMultiHomog_map _ hbf) (isMultiHomog_map _ hbg)
      (by rw [hev]; exact hf0) (by rw [hev]; exact hg0 i) ?_
    · rw [hb] at hv
      exact hv
    intro c hc P hP hϖP
    have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
    obtain ⟨q, hq, hO, hu, hreg⟩ := chart_point X Ω ξ _ (segreVec y) A m O hT' c hc (hconst c hc) P hP
    have hϖu : unitAt ξ q (algebraMap O Ω ϖ) := hu ⟨_, Subalgebra.algebraMap_mem _ ϖ⟩ (hϖP _ rfl)
    have h1 := (he i).2 q (hover q hO) c hq
    have h2 := (he' i).2 q (hover q hO) c hq
    have hgr : (L.gr w i) q = (L'.gr w i) q := by
      unfold Lat.gr
      rw [hLL q hO hϖu]
    obtain ⟨Yx, hYx⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ Q.x i k := ⟨_, rfl⟩
    obtain ⟨Yx', hYx'⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ Q.x' i k := ⟨_, rfl⟩
    obtain ⟨Yf, hYf⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ bf k := ⟨_, rfl⟩
    obtain ⟨Yg, hYg⟩ : ∃ Y : Ω, Y = ∏ k, y ⟨k, c k⟩ ^ bg k := ⟨_, rfl⟩
    have hYx0 : Yx ≠ 0 := by
      rw [hYx]; exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
    have hYx0' : Yx' ≠ 0 := by
      rw [hYx']; exact Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
    have hYf0 : Yf ≠ 0 := by
      rw [hYf]; exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
    have hYY : Yx * Yg = Yx' * Yf := by
      rw [hYx, hYx', hYf, hYg, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hk : (bf k : ℤ) - bg k = Q.x i k - Q.x' i k := congrFun hb k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), ← zpow_add₀ (hyc k)]
      congr 1
      omega
    rw [← hYx, smul_eq_mul] at h1
    rw [← hYx', smul_eq_mul] at h2
    rw [h1, h2] at hgr
    have hα : Yx * e i ≠ 0 := mul_ne_zero hYx0 (he0 i)
    have hβ : Yx' * e' i ≠ 0 := mul_ne_zero hYx0' (he0' i)
    have hβm : Yx' * e' i ∈ Submodule.span (regAt ξ q) {Yx * e i} := by
      rw [hgr]; exact Submodule.mem_span_singleton_self _
    have hαm : Yx * e i ∈ Submodule.span (regAt ξ q) {Yx' * e' i} := by
      rw [← hgr]; exact Submodule.mem_span_singleton_self _
    obtain ⟨ρ, hρ⟩ := Submodule.mem_span_singleton.1 hβm
    obtain ⟨ρ', hρ'⟩ := Submodule.mem_span_singleton.1 hαm
    have hρ1 : (ρ : Ω) = (Yx' * e' i) / (Yx * e i) := by
      rw [eq_div_iff hα]; exact hρ
    have hρ2 : (ρ' : Ω) = ((Yx' * e' i) / (Yx * e i))⁻¹ := by
      rw [inv_div, eq_div_iff hβ]; exact hρ'
    obtain ⟨s1, hs1, hm1⟩ := hreg _ (hρ1 ▸ ρ.2)
    obtain ⟨s2, hs2, hm2⟩ := hreg _ (hρ2 ▸ ρ'.2)
    refine ⟨s1, ⟨_, hm1⟩, hs1, fun ht => ?_, ?_⟩
    · have hmul : s1 * s2 = (⟨_, hm1⟩ : chartRing O (segreVec y) c) * ⟨_, hm2⟩ := by
        apply Subtype.ext
        show (s1 : Ω) * s2 = _ * _
        rw [mul_mul_mul_comm, mul_inv_cancel₀ (div_ne_zero hβ hα), mul_one]
      have := P.mul_mem_right (⟨_, hm2⟩ : chartRing O (segreVec y) c) ht
      rw [← hmul] at this
      exact (hP.mem_or_mem this).elim hs1 hs2
    · show (s1 : Ω) * _ = (s1 : Ω) * _ * _
      rw [hev, hev, hfg i, ← hYg, ← hYf]
      have hYg' : Yg = Yx' * Yf / Yx := by
        rw [eq_div_iff hYx0]; linear_combination hYY
      have hei := he0 i
      rw [hYg']
      field_simp
  · simp only [hcoef, if_true]
    show aeval y (MvPolynomial.map (Int.castRingHom O) (Q.f i)) = _ * aeval y (MvPolynomial.map (Int.castRingHom O) (Q.g i))
    rw [hev, hev, hfg i]

end GlobalTheory.CompanionTheory.Ar.Num.LatFlag
