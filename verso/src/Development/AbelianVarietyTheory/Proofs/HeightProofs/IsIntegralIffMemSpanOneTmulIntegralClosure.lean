import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Break down `eq_or_ne c 0 with rfl | hc` into its components or cases. Conclude with `⟨0, map_zero _⟩`. Break down `ValuationRing.isInteger_or_isInteger R c with h1 | ⟨r, hr⟩` into its components or cases. Conclude with `h1`. Establish `h2 : algebraMap R R' r * r' = 1`.

Apply `IsFractionRing.injective R' F'` to reduce the goal to its premises. Rewrite using `[map_mul, h, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', hr, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]`. Establish `hu : IsUnit r` using `IsLocalHom.map_nonunit (f := algebraMap R R') r (IsUnit.of_mul_eq_one _ h2)`. Take `⟨s, hs⟩` from `hu.exists_right_inv`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Establish `h3 : c⁻¹ * algebraMap R F s = 1` using `by rw [← hr, ← map_mul, hs, map_one]`. Clear denominators, using `at h3` for the nonvanishing conditions. Conclude with `h3`.
-/
theorem mem_range_of_map_eq_of_isLocalHom {R R' F F' : Type} [CommRing R] [IsDomain R]
    [ValuationRing R] [CommRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
    [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    (c : F) (r' : R') (h : algebraMap R' F' r' = algebraMap F F' c) :
    ∃ r : R, algebraMap R F r = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger R c with h1 | ⟨r, hr⟩
  · exact h1
  have h2 : algebraMap R R' r * r' = 1 := by
    apply IsFractionRing.injective R' F'
    rw [map_mul, h, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', hr,
      ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
  have hu : IsUnit r := IsLocalHom.map_nonunit (f := algebraMap R R') r (IsUnit.of_mul_eq_one _ h2)
  obtain ⟨s, hs⟩ := hu.exists_right_inv
  refine ⟨s, ?_⟩
  have h3 : c⁻¹ * algebraMap R F s = 1 := by rw [← hr, ← map_mul, hs, map_one]
  field_simp at h3
  exact h3

/- English proof (translation)
Take `⟨p, hp⟩ : ∃ p, p = (minpoly F l).map (algebraMap F F')` from `⟨_, rfl⟩`. Rewrite using `[← hp]`. Establish `hpm : p.Monic` using `hp ▸ (minpoly.monic hl).map _`. Establish `hp0 : aeval ((1 : F') ⊗ₜ[F] l) p = 0`. Rewrite using `[hp, aeval_map_algebraMap]`.

Use `aeval_algHom_apply (Algebra.TensorProduct.includeRight (R := F) (A := F') (B := L)) l (minpoly F l)` as an intermediate fact. Rewrite `this` using `[minpoly.aeval, map_zero]`. Conclude with `this`. Establish `hr : aeval ((1 : F') ⊗ₜ[F] l) (q %ₘ p) = 0`. Rewrite using `[aeval_modByMonic_eq_self_of_root hp0, hq]`.

Establish `hdeg : (q %ₘ p).degree < ((minpoly F l).natDegree : ℕ)`. Establish `h5 : p.degree = ((minpoly F l).natDegree : ℕ)`. Rewrite using `[hp, (minpoly.monic hl).degree_map, degree_eq_natDegree (minpoly.ne_zero hl)]`. Conclude with `h5 ▸ degree_modByMonic_lt q hpm`. Establish `hli : LinearIndependent F' (fun i : Fin (minpoly F l).natDegree => (1 : F') ⊗ₜ[F] (l ^ (i : ℕ)))` using `Module.Flat.linearIndependent_one_tmul (R := F) (S := F') (linearIndependent_pow (K := F) l)`.

Rewrite using `[← modByMonic_eq_zero_iff_dvd hpm]`. Assume the negation of the conclusion as `hne`. Establish `hnd : (q %ₘ p).natDegree < (minpoly F l).natDegree` using `(natDegree_lt_iff_degree_lt hne).2 hdeg`. Rewrite `hr` using `[aeval_eq_sum_range' hnd, Finset.sum_range]`. Simplify using `only [Algebra.TensorProduct.tmul_pow, one_pow] at hr`.

Establish `h4 : (q %ₘ p).coeff (q %ₘ p).natDegree = 0` using `Fintype.linearIndependent_iff.1 hli (fun i => (q %ₘ p).coeff i) hr ⟨_, hnd⟩`. Conclude with `hne (leadingCoeff_eq_zero.1 h4)`.
-/
theorem map_minpoly_dvd_of_aeval_one_tmul {F F' L : Type} [Field F] [Field F'] [Algebra F F']
    [Field L] [Algebra F L] {l : L} (hl : IsIntegral F l) {q : F'[X]}
    (hq : aeval ((1 : F') ⊗ₜ[F] l) q = 0) : (minpoly F l).map (algebraMap F F') ∣ q := by
  obtain ⟨p, hp⟩ : ∃ p, p = (minpoly F l).map (algebraMap F F') := ⟨_, rfl⟩
  rw [← hp]
  have hpm : p.Monic := hp ▸ (minpoly.monic hl).map _
  have hp0 : aeval ((1 : F') ⊗ₜ[F] l) p = 0 := by
    rw [hp, aeval_map_algebraMap]
    have := aeval_algHom_apply (Algebra.TensorProduct.includeRight (R := F) (A := F') (B := L)) l
      (minpoly F l)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hr : aeval ((1 : F') ⊗ₜ[F] l) (q %ₘ p) = 0 := by
    rw [aeval_modByMonic_eq_self_of_root hp0, hq]
  have hdeg : (q %ₘ p).degree < ((minpoly F l).natDegree : ℕ) := by
    have h5 : p.degree = ((minpoly F l).natDegree : ℕ) := by
      rw [hp, (minpoly.monic hl).degree_map, degree_eq_natDegree (minpoly.ne_zero hl)]
    exact h5 ▸ degree_modByMonic_lt q hpm
  have hli : LinearIndependent F'
      (fun i : Fin (minpoly F l).natDegree => (1 : F') ⊗ₜ[F] (l ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul (R := F) (S := F') (linearIndependent_pow (K := F) l)
  rw [← modByMonic_eq_zero_iff_dvd hpm]
  by_contra hne
  have hnd : (q %ₘ p).natDegree < (minpoly F l).natDegree :=
    (natDegree_lt_iff_degree_lt hne).2 hdeg
  rw [aeval_eq_sum_range' hnd, Finset.sum_range] at hr
  simp only [Algebra.TensorProduct.tmul_pow, one_pow] at hr
  have h4 : (q %ₘ p).coeff (q %ₘ p).natDegree = 0 :=
    Fintype.linearIndependent_iff.1 hli (fun i => (q %ₘ p).coeff i) hr ⟨_, hnd⟩
  exact hne (leadingCoeff_eq_zero.1 h4)

/- English proof (translation)
Establish `hl : IsIntegral F l` using `Algebra.IsIntegral.isIntegral l`. Take `⟨q, hqm, hq⟩` from `h`. Establish `hq' : aeval ((1 : F') ⊗ₜ[F] l) (q.map (algebraMap R' F')) = 0`. Rewrite using `[aeval_map_algebraMap]`. Conclude with `hq`.

Establish `hd` using `map_minpoly_dvd_of_aeval_one_tmul hl hq'`. Establish `hlift` using `integralClosure.mem_lifts_of_monic_of_dvd_map F' hqm ((minpoly.monic hl).map _) hd`. Establish `hlift2 : minpoly F l ∈ lifts (algebraMap R F)`. Rewrite `hlift`, the goal using `[lifts_iff_coeff_lifts]`. Introduce `n`.

Take `⟨⟨y, hy⟩, hy2⟩` from `hlift n`. Take `⟨r', hr'⟩` from `IsIntegrallyClosed.algebraMap_eq_of_integral (R := R') (K := F') hy`. Rewrite `hy2` using `[coeff_map]`. Conclude with `mem_range_of_map_eq_of_isLocalHom _ r' (hr'.trans hy2)`. Take `⟨g, hg, -, hgm⟩` from `lifts_and_degree_eq_and_monic hlift2 (minpoly.monic hl)`.

Use `⟨g, hgm, ?_⟩` and prove the remaining obligations. Use `minpoly.aeval F l` as an intermediate fact. Rewrite `this` using `[← hg, aeval_map_algebraMap]`. Conclude with `this`.
-/
theorem isIntegral_of_isIntegral_one_tmul {R R' F F' : Type} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsLocalHom (algebraMap R R')]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
    [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra R L] [IsScalarTower R F L]
    {l : L} (h : IsIntegral R' ((1 : F') ⊗ₜ[F] l)) : IsIntegral R l := by
  have hl : IsIntegral F l := Algebra.IsIntegral.isIntegral l
  obtain ⟨q, hqm, hq⟩ := h
  have hq' : aeval ((1 : F') ⊗ₜ[F] l) (q.map (algebraMap R' F')) = 0 := by
    rw [aeval_map_algebraMap]
    exact hq
  have hd := map_minpoly_dvd_of_aeval_one_tmul hl hq'
  have hlift := integralClosure.mem_lifts_of_monic_of_dvd_map F' hqm
    ((minpoly.monic hl).map _) hd
  have hlift2 : minpoly F l ∈ lifts (algebraMap R F) := by
    rw [lifts_iff_coeff_lifts] at hlift ⊢
    intro n
    obtain ⟨⟨y, hy⟩, hy2⟩ := hlift n
    obtain ⟨r', hr'⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (R := R') (K := F') hy
    rw [coeff_map] at hy2
    exact mem_range_of_map_eq_of_isLocalHom _ r' (hr'.trans hy2)
  obtain ⟨g, hg, -, hgm⟩ := lifts_and_degree_eq_and_monic hlift2 (minpoly.monic hl)
  refine ⟨g, hgm, ?_⟩
  have := minpoly.aeval F l
  rw [← hg, aeval_map_algebraMap] at this
  exact this

/- English proof (translation)
Establish `h1 : ∀ r' : R', ∃ (r : R) (s : R'), r' = algebraMap R R' r + algebraMap R R' ϖ * s`. Introduce `r'`. Take `⟨a, ha⟩` from `hres (IsLocalRing.residue R' r')`. Take `⟨r, rfl⟩` from `IsLocalRing.residue_surjective a`. Rewrite `ha` using `[IsLocalRing.ResidueField.map_residue]`.

Establish `hm : r' - algebraMap R R' r ∈ IsLocalRing.maximalIdeal R'`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, ha, sub_self]`. Rewrite `hm` using `[hϖ, Ideal.mem_span_singleton]`. Take `⟨s, hs⟩` from `hm`. Conclude with `⟨r, s, by rw [← hs]; ring⟩`.

Proceed by induction on `n with`. Consider the case `zero => exact ⟨0, r', by simp⟩`. Consider the case `succ n ih`. Take `⟨r, s, hs⟩` from `ih`. Take `⟨r₁, s₁, hs₁⟩` from `h1 s`.

Use `⟨r + ϖ ^ n * r₁, s₁, ?_⟩` and prove the remaining obligations. Rewrite using `[hs, hs₁, map_add, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_eq_algebraMap_add_pow_mul {R R' : Type} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] {ϖ : R}
    (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' ϖ})
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R'))) (n : ℕ)
    (r' : R') : ∃ (r : R) (s : R'), r' = algebraMap R R' r + algebraMap R R' ϖ ^ n * s := by
  have h1 : ∀ r' : R', ∃ (r : R) (s : R'), r' = algebraMap R R' r + algebraMap R R' ϖ * s := by
    intro r'
    obtain ⟨a, ha⟩ := hres (IsLocalRing.residue R' r')
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    rw [IsLocalRing.ResidueField.map_residue] at ha
    have hm : r' - algebraMap R R' r ∈ IsLocalRing.maximalIdeal R' := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ha, sub_self]
    rw [hϖ, Ideal.mem_span_singleton] at hm
    obtain ⟨s, hs⟩ := hm
    exact ⟨r, s, by rw [← hs]; ring⟩
  induction n with
  | zero => exact ⟨0, r', by simp⟩
  | succ n ih =>
    obtain ⟨r, s, hs⟩ := ih
    obtain ⟨r₁, s₁, hs₁⟩ := h1 s
    refine ⟨r + ϖ ^ n * r₁, s₁, ?_⟩
    rw [hs, hs₁, map_add, map_mul, map_pow]
    ring

open NumberField in
open scoped TensorProduct in
open Polynomial in
variable (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R']
  [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F']
  [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']
  (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L] in
/- English proof (translation)
Break down `ValuationRing.isInteger_or_isInteger R c with ⟨r, hr⟩ | ⟨r, hr⟩` into its components or cases. Conclude with `⟨r, hr⟩`. Distinguish the cases in `hc : c = 0`. Conclude with `⟨0, by simp [hc]⟩`. Establish `hF : algebraMap R' F' (algebraMap R R' r * a) = algebraMap R' F' 1`.

Rewrite using `[map_mul, ← h, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', hr, ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]`. Establish `hu : IsUnit (algebraMap R R' r)` using `IsUnit.of_mul_eq_one a (IsFractionRing.injective R' F' hF)`. Take `⟨u, rfl⟩` from `(isUnit_of_map_unit (algebraMap R R') r hu)`. Use `⟨(u⁻¹ : Rˣ), ?_⟩` and prove the remaining obligations. Rewrite using `[map_units_inv, hr, inv_inv]`.
-/
private theorem exists_algebraMap_eq_of_algebraMap_eq_algebraMap {c : F} {a : R'}
    (h : algebraMap F F' c = algebraMap R' F' a) : ∃ r : R, algebraMap R F r = c := by
  rcases ValuationRing.isInteger_or_isInteger R c with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  · by_cases hc : c = 0
    · exact ⟨0, by simp [hc]⟩
    have hF : algebraMap R' F' (algebraMap R R' r * a) = algebraMap R' F' 1 := by
      rw [map_mul, ← h, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', hr,
        ← map_mul, inv_mul_cancel₀ hc, map_one, map_one]
    have hu : IsUnit (algebraMap R R' r) :=
      IsUnit.of_mul_eq_one a (IsFractionRing.injective R' F' hF)
    obtain ⟨u, rfl⟩ := (isUnit_of_map_unit (algebraMap R R') r hu)
    refine ⟨(u⁻¹ : Rˣ), ?_⟩
    rw [map_units_inv, hr, inv_inv]

open NumberField in
open scoped TensorProduct in
open Polynomial in
variable (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R']
  [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F']
  [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']
  (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L] in
/- English proof (translation)
Take `⟨p, hpm, hp⟩` from `hy`. Establish `hyF : IsIntegral F y` using `Algebra.IsIntegral.isIntegral y`. Use `set f := minpoly F y with hf`. Use `set f' : F'[X] := f.map (algebraMap F F') with hf'`. Establish `hfm : f'.Monic` using `(minpoly.monic hyF).map _`.

Use `set t : F' ⊗[F] L := (1 : F') ⊗ₜ[F] y with ht`. Establish `ht' : t = Algebra.TensorProduct.includeRight y` using `rfl`. Establish `hft : aeval t f' = 0`. Rewrite using `[hf', aeval_map_algebraMap, ht', aeval_algHom_apply, minpoly.aeval, map_zero]`. Use `set g : F'[X] := p.map (algebraMap R' F') with hg`.

Establish `hgt : aeval t g = 0`. Rewrite using `[hg, aeval_map_algebraMap, aeval_def, hp]`. Establish `hind : LinearIndependent F' fun i : Fin f.natDegree => t ^ (i : ℕ)`. Use `Module.Flat.linearIndependent_one_tmul (S := F') (linearIndependent_pow (K := F) y)` as an intermediate fact. Use `this using 2 with i` and compare the differences between its conclusion and the goal.

Rewrite using `[ht, Algebra.TensorProduct.tmul_pow, one_pow]`. Establish `hdvd : f' ∣ g`. Rewrite using `[← modByMonic_eq_zero_iff_dvd hfm]`. Use `set r := g %ₘ f' with hr`. Establish `hrt : aeval t r = 0`.

Use `modByMonic_add_div g f'` as an intermediate fact. Rewrite `this` using `[← hr]`. Establish `h2` using `congrArg (aeval t) this`. Rewrite `h2` using `[map_add, map_mul, hft, zero_mul, add_zero, hgt]`. Conclude with `h2`.

Establish `hdeg : r.degree < f.natDegree`. Use `degree_modByMonic_lt g hfm` as an intermediate fact. Rewrite `this` using `[hf', degree_map, degree_eq_natDegree (minpoly.ne_zero hyF)]`. Then use the resulting hypothesis. Establish `hcoeff : ∀ i : Fin f.natDegree, r.coeff i = 0`. Rewrite `hind` using `[Fintype.linearIndependent_iff]`.

Apply `hind` to reduce the goal to its premises. Rewrite `hrt` using `[aeval_eq_sum_range' (p := r) (n := f.natDegree) ?_]`. Rewrite using `[← hrt, Fin.sum_univ_eq_sum_range (fun i => r.coeff i • t ^ i)]`. Distinguish the cases in `h0 : r = 0`. Rewrite using `[h0, natDegree_zero]`.

Conclude with `minpoly.natDegree_pos hyF`. Conclude with `(natDegree_lt_iff_degree_lt h0).2 hdeg`. Use extensionality with `i`. Rewrite using `[coeff_zero]`. Distinguish the cases in `hi : i < f.natDegree`.

Conclude with `hcoeff ⟨i, hi⟩`. Conclude with `coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.1 hi))`. Take `⟨q, hq⟩` from `IsIntegrallyClosed.eq_map_mul_C_of_dvd F' hpm (hg ▸ hdvd)`. Rewrite `hq` using `[hfm.leadingCoeff, C_1, mul_one]`. Establish `hlift : f ∈ lifts (algebraMap R F)`.

Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `i`. Establish `: algebraMap F F' (f.coeff i) = algebraMap R' F' (q.coeff i)`. Rewrite using `[← coeff_map, ← hf', ← hq, coeff_map]`. Take `⟨r, hr⟩` from `exists_algebraMap_eq_of_algebraMap_eq_algebraMap R R' F F' this`.

Conclude with `⟨r, hr⟩`. Take `⟨q', hq'map, -, hq'm⟩` from `lifts_and_degree_eq_and_monic hlift (minpoly.monic hyF)`. Use `⟨q', hq'm, ?_⟩` and prove the remaining obligations. Rewrite using `[← aeval_def, ← aeval_map_algebraMap F, hq'map, hf, minpoly.aeval]`.
-/
private theorem isIntegral_of_isIntegral_one_tmul' {y : L}
    (hy : IsIntegral R' ((1 : F') ⊗ₜ[F] y : F' ⊗[F] L)) : IsIntegral R y := by
  obtain ⟨p, hpm, hp⟩ := hy
  have hyF : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  set f := minpoly F y with hf
  set f' : F'[X] := f.map (algebraMap F F') with hf'
  have hfm : f'.Monic := (minpoly.monic hyF).map _
  set t : F' ⊗[F] L := (1 : F') ⊗ₜ[F] y with ht
  have ht' : t = Algebra.TensorProduct.includeRight y := rfl
  have hft : aeval t f' = 0 := by
    rw [hf', aeval_map_algebraMap, ht', aeval_algHom_apply, minpoly.aeval, map_zero]
  set g : F'[X] := p.map (algebraMap R' F') with hg
  have hgt : aeval t g = 0 := by
    rw [hg, aeval_map_algebraMap, aeval_def, hp]
  have hind : LinearIndependent F' fun i : Fin f.natDegree => t ^ (i : ℕ) := by
    have := Module.Flat.linearIndependent_one_tmul (S := F') (linearIndependent_pow (K := F) y)
    convert this using 2 with i
    rw [ht, Algebra.TensorProduct.tmul_pow, one_pow]
  have hdvd : f' ∣ g := by
    rw [← modByMonic_eq_zero_iff_dvd hfm]
    set r := g %ₘ f' with hr
    have hrt : aeval t r = 0 := by
      have := modByMonic_add_div g f'
      rw [← hr] at this
      have h2 := congrArg (aeval t) this
      rw [map_add, map_mul, hft, zero_mul, add_zero, hgt] at h2
      exact h2
    have hdeg : r.degree < f.natDegree := by
      have := degree_modByMonic_lt g hfm
      rwa [hf', degree_map, degree_eq_natDegree (minpoly.ne_zero hyF)] at this
    have hcoeff : ∀ i : Fin f.natDegree, r.coeff i = 0 := by
      rw [Fintype.linearIndependent_iff] at hind
      apply hind
      rw [aeval_eq_sum_range' (p := r) (n := f.natDegree) ?_] at hrt
      · rw [← hrt, Fin.sum_univ_eq_sum_range (fun i => r.coeff i • t ^ i)]
      · by_cases h0 : r = 0
        · rw [h0, natDegree_zero]; exact minpoly.natDegree_pos hyF
        · exact (natDegree_lt_iff_degree_lt h0).2 hdeg
    ext i
    rw [coeff_zero]
    by_cases hi : i < f.natDegree
    · exact hcoeff ⟨i, hi⟩
    · exact coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg (by exact_mod_cast not_lt.1 hi))
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F' hpm (hg ▸ hdvd)
  rw [hfm.leadingCoeff, C_1, mul_one] at hq
  have hlift : f ∈ lifts (algebraMap R F) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have : algebraMap F F' (f.coeff i) = algebraMap R' F' (q.coeff i) := by
      rw [← coeff_map, ← hf', ← hq, coeff_map]
    obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_algebraMap_eq_algebraMap R R' F F' this
    exact ⟨r, hr⟩
  obtain ⟨q', hq'map, -, hq'm⟩ := lifts_and_degree_eq_and_monic hlift (minpoly.monic hyF)
  refine ⟨q', hq'm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq'map, hf, minpoly.aeval]

open NumberField in
open scoped TensorProduct in
open Polynomial in

/- English proof (translation)
Introduce `R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres L _ _ _ _ _ _ x`. Use `set M := Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L)) with hM`. Establish `hMint : ∀ z ∈ M, IsIntegral R' z`. Introduce `z hz`. Use `(Submodule.span_le (p := Subalgebra.toSubmodule (integralClosure R' (F' ⊗[F] L)))).2 ?_ hz` and prove the remaining obligations.

Introduce and unpack `_ ⟨s, hs, rfl⟩`. Establish `hs' : IsIntegral R s` using `hs`. Conclude with `(hs'.map (Algebra.TensorProduct.includeRight.restrictScalars R : L →ₐ[R] F' ⊗[F] L)).tower_top`. Use `⟨fun hx => ?_, hMint x⟩` and prove the remaining obligations. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible R`.

Use `set ϖ := algebraMap R R' π with hϖdef`. Establish `hmax' : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ}`. Rewrite using `[← hmax, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`. Establish `hϖ : Irreducible ϖ` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).2 hmax'`. Establish `happrox : ∀ a : R', ∃ r : R, ∃ b : R', a = algebraMap R R' r + ϖ * b`.

Introduce `a`. Take `⟨c, hc⟩` from `hres (IsLocalRing.residue R' a)`. Take `⟨r, rfl⟩` from `IsLocalRing.residue_surjective c`. Rewrite `hc` using `[IsLocalRing.ResidueField.map_residue]`. Establish `hmem : a - algebraMap R R' r ∈ Ideal.span {ϖ}`.

Rewrite using `[← hmax', ← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 hmem`. Conclude with `⟨r, b, eq_add_of_sub_eq' (hb.symm.trans (mul_comm _ _))⟩`. Establish `hsm : ∀ (c : R) (s : L), algebraMap R R' c • ((1 : F') ⊗ₜ[F] s) = (1 : F') ⊗ₜ[F] (algebraMap R L c * s)`. Introduce `c s`.

Rewrite using `[TensorProduct.smul_tmul', Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', Algebra.algebraMap_eq_smul_one (A := F'), TensorProduct.smul_tmul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]`. Establish `hinj : ∀ d : R, d ≠ 0 → algebraMap R R' d ≠ 0`. Introduce `d hd`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ`. Rewrite using `[map_mul, map_pow]`.

Conclude with `mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ hϖ.ne_zero)`. Establish `hstep : ∀ z ∈ M, ∃ s ∈ integralClosure R L, ∃ m ∈ M, z = (1 : F') ⊗ₜ[F] s + ϖ • m`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨s, hs, rfl⟩` from `hz`. Conclude with `⟨s, hs, 0, M.zero_mem, by rw [smul_zero, add_zero]⟩`. Consider the case `zero`. Conclude with `⟨0, (integralClosure R L).zero_mem, 0, M.zero_mem, by rw [TensorProduct.tmul_zero, smul_zero, add_zero]⟩`. Consider the case `add z w _ _ hz hw`.

Take `⟨s, hs, m, hm, rfl⟩` from `hz`. Take `⟨s', hs', m', hm', rfl⟩` from `hw`. Conclude with `⟨s + s', add_mem hs hs', m + m', add_mem hm hm', by rw [TensorProduct.tmul_add, smul_add]; abel⟩`. Consider the case `smul a z _ hz`. Take `⟨s, hs, m, hm, rfl⟩` from `hz`.

Take `⟨r, b, rfl⟩` from `happrox a`. Use `⟨algebraMap R L r * s, mul_mem (algebraMap_mem _ r) hs, b • ((1 : F') ⊗ₜ[F] s) + (algebraMap R R' r + ϖ * b) • m, add_mem (M.smul_mem _ (Submodule.subset_span ⟨s, hs, rfl⟩)) (M.smul_mem _ hm), ?_⟩` and prove the remaining obligations. Rewrite using `[← hsm]`. Use `module`. Establish `hden : ∀ z : F' ⊗[F] L, ∃ c : R', c ≠ 0 ∧ c • z ∈ M`.

Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩`. Consider the case `tmul a l`. Take `⟨n, e, he, rfl⟩` from `IsFractionRing.div_surjective (A := R') a`.

Take `⟨d, hd⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors R) l (Algebra.IsIntegral.isIntegral (R := F) l)`. Establish `hd0 : (d : R) ≠ 0` using `nonZeroDivisors.coe_ne_zero d`. Establish `he0 : e ≠ 0` using `nonZeroDivisors.ne_zero he`. Use `⟨e * algebraMap R R' d, mul_ne_zero he0 (hinj _ hd0), ?_⟩` and prove the remaining obligations. Establish `hcalc : (e * algebraMap R R' d) • ((algebraMap R' F' n / algebraMap R' F' e) ⊗ₜ[F] l) = n • (algebraMap R R' d • ((1 : F') ⊗ₜ[F] l))`.

Rewrite using `[TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one]`. Use `congr 1`. Establish `: algebraMap R' F' e ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R' F')).2 he0`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hcalc, hsm, ← Algebra.smul_def]`. Conclude with `M.smul_mem _ (Submodule.subset_span ⟨_, hd, rfl⟩)`. Consider the case `add z w hz hw`. Take `⟨c, hc, hcz⟩` from `hz`. Take `⟨c', hc', hcw⟩` from `hw`.

Use `⟨c * c', mul_ne_zero hc hc', ?_⟩` and prove the remaining obligations. Establish `: (c * c') • (z + w) = c' • (c • z) + c • (c' • w)` using `by module`. Rewrite using `[this]`. Conclude with `add_mem (M.smul_mem _ hcz) (M.smul_mem _ hcw)`. Establish `hπL : algebraMap R L π ≠ 0`.

Rewrite using `[IsScalarTower.algebraMap_apply R F L]`. Conclude with `(_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero)`. Establish `hϖF : algebraMap R' F' ϖ ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective R' F')).2 hϖ.ne_zero`. Establish `hmain : ∀ z : F' ⊗[F] L, IsIntegral R' z → ϖ • z ∈ M → z ∈ M`. Introduce `z hz hϖz`.

Take `⟨s, hs, m, hm, hzm⟩` from `hstep _ hϖz`. Establish `hy : ϖ • ((1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s)) = (1 : F') ⊗ₜ[F] s`. Rewrite using `[hϖdef, hsm, ← mul_assoc, mul_inv_cancel₀ hπL, one_mul]`. Establish `heq : z = (1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) + m`. Establish `h1 : ϖ • z = ϖ • ((1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) + m)`.

Rewrite using `[smul_add, hy, hzm]`. Rewrite `h1` using `[← algebraMap_smul F' ϖ z, ← algebraMap_smul F' ϖ (_ + m)]`. Conclude with `smul_right_injective _ hϖF h1`. Establish `hyint : IsIntegral R ((algebraMap R L π)⁻¹ * s)`. Use `isIntegral_of_isIntegral_one_tmul' R R' F F' L ?_` and prove the remaining obligations.

Establish `: (1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) = z - m` using `by rw [heq]; abel`. Rewrite using `[this]`. Conclude with `hz.sub (hMint m hm)`. Rewrite using `[heq]`. Conclude with `add_mem (Submodule.subset_span ⟨_, hyint, rfl⟩) hm`.

Establish `hpow : ∀ (k : ℕ) (z : F' ⊗[F] L), IsIntegral R' z → ϖ ^ k • z ∈ M → z ∈ M`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro z _ hz`. Rewrite `hz` using `[pow_zero, one_smul]`. Then use the resulting hypothesis.

Consider the case `succ k ih`. Introduce `z hz hkz`. Use `hmain z hz (ih _ ?_ ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `isIntegral_algebraMap.mul hz`.

Rewrite using `[smul_smul, ← pow_succ]` and apply the resulting hypothesis. Take `⟨c, hc, hcx⟩` from `hden x`. Take `⟨k, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ`. Use `hpow k x hx ?_` and prove the remaining obligations. Use `M.smul_mem (↑u⁻¹ : R') hcx` as an intermediate fact.

Rewrite `this` using `[smul_smul, ← mul_assoc, Units.inv_mul, one_mul]`. Then use the resulting hypothesis.
-/
theorem _root_.GlobalTheory.isIntegral_iff_mem_span_one_tmul_integralClosure :
    ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Algebra R L] [IsScalarTower R F L] (x : F' ⊗[F] L), IsIntegral R' x ↔ x ∈ Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L)) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres L _ _ _ _ _ _ x
  set M := Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L))
    with hM
  have hMint : ∀ z ∈ M, IsIntegral R' z := by
    intro z hz
    refine (Submodule.span_le (p := Subalgebra.toSubmodule (integralClosure R' (F' ⊗[F] L)))).2
      ?_ hz
    rintro _ ⟨s, hs, rfl⟩
    have hs' : IsIntegral R s := hs
    exact (hs'.map (Algebra.TensorProduct.includeRight.restrictScalars R :
      L →ₐ[R] F' ⊗[F] L)).tower_top
  refine ⟨fun hx => ?_, hMint x⟩
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  set ϖ := algebraMap R R' π with hϖdef
  have hmax' : IsLocalRing.maximalIdeal R' = Ideal.span {ϖ} := by
    rw [← hmax, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hϖ : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).2 hmax'
  have happrox : ∀ a : R', ∃ r : R, ∃ b : R', a = algebraMap R R' r + ϖ * b := by
    intro a
    obtain ⟨c, hc⟩ := hres (IsLocalRing.residue R' a)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective c
    rw [IsLocalRing.ResidueField.map_residue] at hc
    have hmem : a - algebraMap R R' r ∈ Ideal.span {ϖ} := by
      rw [← hmax', ← IsLocalRing.residue_eq_zero_iff, map_sub, hc, sub_self]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨r, b, eq_add_of_sub_eq' (hb.symm.trans (mul_comm _ _))⟩
  have hsm : ∀ (c : R) (s : L), algebraMap R R' c • ((1 : F') ⊗ₜ[F] s) =
      (1 : F') ⊗ₜ[F] (algebraMap R L c * s) := by
    intro c s
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R F F', Algebra.algebraMap_eq_smul_one (A := F'),
      TensorProduct.smul_tmul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  have hinj : ∀ d : R, d ≠ 0 → algebraMap R R' d ≠ 0 := by
    intro d hd
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hπ
    rw [map_mul, map_pow]
    exact mul_ne_zero (u.isUnit.map _).ne_zero (pow_ne_zero _ hϖ.ne_zero)
  have hstep : ∀ z ∈ M, ∃ s ∈ integralClosure R L, ∃ m ∈ M, z = (1 : F') ⊗ₜ[F] s + ϖ • m := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨s, hs, rfl⟩ := hz
      exact ⟨s, hs, 0, M.zero_mem, by rw [smul_zero, add_zero]⟩
    | zero =>
      exact ⟨0, (integralClosure R L).zero_mem, 0, M.zero_mem,
        by rw [TensorProduct.tmul_zero, smul_zero, add_zero]⟩
    | add z w _ _ hz hw =>
      obtain ⟨s, hs, m, hm, rfl⟩ := hz
      obtain ⟨s', hs', m', hm', rfl⟩ := hw
      exact ⟨s + s', add_mem hs hs', m + m', add_mem hm hm',
        by rw [TensorProduct.tmul_add, smul_add]; abel⟩
    | smul a z _ hz =>
      obtain ⟨s, hs, m, hm, rfl⟩ := hz
      obtain ⟨r, b, rfl⟩ := happrox a
      refine ⟨algebraMap R L r * s, mul_mem (algebraMap_mem _ r) hs,
        b • ((1 : F') ⊗ₜ[F] s) + (algebraMap R R' r + ϖ * b) • m,
        add_mem (M.smul_mem _ (Submodule.subset_span ⟨s, hs, rfl⟩)) (M.smul_mem _ hm), ?_⟩
      rw [← hsm]
      module
  have hden : ∀ z : F' ⊗[F] L, ∃ c : R', c ≠ 0 ∧ c • z ∈ M := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
    | tmul a l =>
      obtain ⟨n, e, he, rfl⟩ := IsFractionRing.div_surjective (A := R') a
      obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
        (nonZeroDivisors R) l (Algebra.IsIntegral.isIntegral (R := F) l)
      have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
      have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
      refine ⟨e * algebraMap R R' d, mul_ne_zero he0 (hinj _ hd0), ?_⟩
      have hcalc : (e * algebraMap R R' d) • ((algebraMap R' F' n / algebraMap R' F' e) ⊗ₜ[F] l) =
          n • (algebraMap R R' d • ((1 : F') ⊗ₜ[F] l)) := by
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, mul_one]
        congr 1
        have : algebraMap R' F' e ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective R' F')).2 he0
        rw [map_mul]
        field_simp
      rw [hcalc, hsm, ← Algebra.smul_def]
      exact M.smul_mem _ (Submodule.subset_span ⟨_, hd, rfl⟩)
    | add z w hz hw =>
      obtain ⟨c, hc, hcz⟩ := hz
      obtain ⟨c', hc', hcw⟩ := hw
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      have : (c * c') • (z + w) = c' • (c • z) + c • (c' • w) := by module
      rw [this]
      exact add_mem (M.smul_mem _ hcz) (M.smul_mem _ hcw)
  have hπL : algebraMap R L π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply R F L]
    exact (_root_.map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective R F)).2 hπ.ne_zero)
  have hϖF : algebraMap R' F' ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R' F')).2 hϖ.ne_zero
  have hmain : ∀ z : F' ⊗[F] L, IsIntegral R' z → ϖ • z ∈ M → z ∈ M := by
    intro z hz hϖz
    obtain ⟨s, hs, m, hm, hzm⟩ := hstep _ hϖz
    have hy : ϖ • ((1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s)) = (1 : F') ⊗ₜ[F] s := by
      rw [hϖdef, hsm, ← mul_assoc, mul_inv_cancel₀ hπL, one_mul]
    have heq : z = (1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) + m := by
      have h1 : ϖ • z = ϖ • ((1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) + m) := by
        rw [smul_add, hy, hzm]
      rw [← algebraMap_smul F' ϖ z, ← algebraMap_smul F' ϖ (_ + m)] at h1
      exact smul_right_injective _ hϖF h1
    have hyint : IsIntegral R ((algebraMap R L π)⁻¹ * s) := by
      refine isIntegral_of_isIntegral_one_tmul' R R' F F' L ?_
      have : (1 : F') ⊗ₜ[F] ((algebraMap R L π)⁻¹ * s) = z - m := by rw [heq]; abel
      rw [this]
      exact hz.sub (hMint m hm)
    rw [heq]
    exact add_mem (Submodule.subset_span ⟨_, hyint, rfl⟩) hm
  have hpow : ∀ (k : ℕ) (z : F' ⊗[F] L), IsIntegral R' z → ϖ ^ k • z ∈ M → z ∈ M := by
    intro k
    induction k with
    | zero => intro z _ hz; rwa [pow_zero, one_smul] at hz
    | succ k ih =>
      intro z hz hkz
      refine hmain z hz (ih _ ?_ ?_)
      · rw [Algebra.smul_def]
        exact isIntegral_algebraMap.mul hz
      · rwa [smul_smul, ← pow_succ]
  obtain ⟨c, hc, hcx⟩ := hden x
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine hpow k x hx ?_
  have := M.smul_mem (↑u⁻¹ : R') hcx
  rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this

end GlobalTheory
