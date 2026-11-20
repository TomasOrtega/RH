import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.CycAway
open NumberField

/- English proof (translation)
Establish `key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹}), ∃ m : ℕ, ∃ a, z * (n : Ω) ^ m = (algebraMap A T a : Ω)`. Introduce `z hz`. Proceed by induction on `hz using Subring.closure_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨a, rfl⟩ | rfl` into its components or cases.

Conclude with `⟨0, a, by simp⟩`. Conclude with `⟨1, 1, by simp [h0]⟩`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `one => exact ⟨0, 1, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨m, a, ha⟩` from `hx`. Take `⟨k, b, hb⟩` from `hy`. Use `⟨m + k, a * n ^ k + b * n ^ m, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, map_natCast]`. Use `push_cast`.

Rewrite using `[← ha, ← hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x _ hx`. Take `⟨m, a, ha⟩` from `hx`. Use `⟨m, -a, ?_⟩` and prove the remaining obligations.

Simplify using `only [map_neg]`. Use `push_cast`. Rewrite using `[← ha]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ hx hy`.

Take `⟨m, a, ha⟩` from `hx`. Take `⟨k, b, hb⟩` from `hy`. Use `⟨m + k, a * b, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul]`. Use `push_cast`.

Rewrite using `[← ha, ← hb]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨_, m, rfl⟩`. Simplify using `only [map_pow, map_natCast]`.

Use `IsUnit.pow _ (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))` and prove the remaining obligations. Simplify using `[h0]`. Introduce `z`. Take `⟨m, a, ha⟩` from `key z (hT z.2)`. Use `⟨(a, ⟨_, m, rfl⟩), Subtype.ext ?_⟩` and prove the remaining obligations.

Simplify using `only [map_pow, map_natCast]`. Use `push_cast`. Conclude with `ha`. Introduce `x y h`. Conclude with `⟨1, by rw [hinj h]⟩`.
-/
theorem isLocalization_of_le_closure {Ω : Type} [Field Ω] {n : ℕ} (h0 : (n : Ω) ≠ 0) (A : Type) [CommRing A]
    (T : Subring Ω) [Algebra A T] (hinj : Function.Injective (algebraMap A T)) (hinv : (n : Ω)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹})) :
    IsLocalization (Submonoid.powers (n : A)) T := by
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹}),
      ∃ m : ℕ, ∃ a, z * (n : Ω) ^ m = (algebraMap A T a : Ω) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | rfl
      · exact ⟨0, a, by simp⟩
      · exact ⟨1, 1, by simp [h0]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * n ^ k + b * n ^ m, ?_⟩
      simp only [map_add, map_mul, map_pow, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, a, ha⟩ := hx
      refine ⟨m, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    simp only [map_pow, map_natCast]
    refine IsUnit.pow _ (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    simp [h0]
  · intro z
    obtain ⟨m, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨_, m, rfl⟩), Subtype.ext ?_⟩
    simp only [map_pow, map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

/- English proof (translation)
Use `haveI := Fact.mk hn`. Use `haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _`. Establish `h0 : (n : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr hn.ne_zero`. Use `set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef`. Set `io : 𝓞 K →+* Ω` to `φ.comp (algebraMap _ K)`.

Establish `hio : Function.Injective io` using `φ.injective.comp RingOfIntegers.coe_injective`. Establish `hmem : ∀ x, io x ∈ T`. Introduce `x`. Take `⟨y, hy⟩` from `(IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1 (RingOfIntegers.isIntegral_coe x)`. Establish `h1 : (y : K) ∈ Subring.closure ({ζ} : Set K)`.

Conclude with `Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by`. Introduce and unpack `_ (⟨r, rfl⟩ | h)`. Conclude with `intCast_mem (Subring.closure ({ζ} : Set K)) r`. Conclude with `Subring.subset_closure h)) h`. Establish `h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ`.

Rewrite using `[Subring.closure_le]`. Introduce and unpack `_ rfl`. Conclude with `Subring.subset_closure (Or.inl rfl)`. Establish `h3 : io x = φ y` using `congrArg φ hy.symm`. Rewrite using `[h3]`.

Conclude with `h2 h1`. Use `letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra`. Establish `hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T`. Use `isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h)) (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)` and prove the remaining obligations. Introduce and unpack `x (rfl | h)`.

Conclude with `Or.inl ⟨hζ.toInteger, rfl⟩`. Conclude with `Or.inr h`. Establish `hn' : (n : 𝓞 K) ≠ 0` using `by exact_mod_cast hn.ne_zero`. Use `⟨IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _, ?_⟩` and prove the remaining obligations. Establish `h1 : Algebra.FiniteType ℤ (𝓞 K)` using `inferInstance`.

Establish `h2 : Algebra.FiniteType (𝓞 K) T`. Use `IsLocalization.Away.finitePresentation (S := T) (n : 𝓞 K)` as an intermediate fact. Use `inferInstance`. Conclude with `h1.trans h2`.
-/
theorem dedekind_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n a : ℕ} (hn : n.Prime)
    [IsCyclotomicExtension {n ^ a} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ a)) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) ∧ Algebra.FiniteType ℤ (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI := Fact.mk hn
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne_zero
  refine ⟨IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _, ?_⟩
  have h1 : Algebra.FiniteType ℤ (𝓞 K) := inferInstance
  have h2 : Algebra.FiniteType (𝓞 K) T :=
    have := IsLocalization.Away.finitePresentation (S := T) (n : 𝓞 K)
    inferInstance
  exact h1.trans h2

/- English proof (translation)
Introduce `Ω _ _ _ n a hn`. Use `haveI := Fact.mk hn`. Establish `h0 : (n : Ω) ≠ 0` using `Nat.cast_ne_zero.mpr hn.ne_zero`. Set `K` to `CyclotomicField (n ^ a) ℚ`. Use `haveI : IsCyclotomicExtension {n ^ a} ℚ K := CyclotomicField.isCyclotomicExtension (n ^ a) ℚ`.

Use `haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _`. Set `φ : K →+* Ω` to `(IsAlgClosed.lift (R := ℚ) (S := K) (M := Ω)).toRingHom`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec (n ^ a) ℚ K`. Use `set ζ := IsCyclotomicExtension.zeta (n ^ a) ℚ K`. Take `⟨hD, hF⟩` from `dedekind_closure hn φ hζ`.

Use `set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef`. Establish `hz : IsPrimitiveRoot (φ ζ) (n ^ a)` using `hζ.map_of_injective φ.injective`. Set `z : T` to `⟨φ ζ, Subring.subset_closure (Or.inl rfl)⟩`. Establish `hz' : IsPrimitiveRoot z (n ^ a)` using `IsPrimitiveRoot.of_map_of_injective (f := T.subtype) hz T.subtype_injective`. Establish `hu : IsUnit z` using `hz'.isUnit (NeZero.ne _)`.

Use `⟨T, hu.unit, hD, hF, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `IsUnit.of_mul_eq_one ⟨_, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `[h0]`. Rewrite using `[← IsPrimitiveRoot.coe_units_iff]`. Conclude with `hz`.

Both sides reduce to the same expression.
-/
theorem exists_base : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n a : ℕ), n.Prime → ∃ (o : Subring Ω) (ze : oˣ), IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧ IsUnit (n : o) ∧ IsPrimitiveRoot (Units.map o.subtype.toMonoidHom ze) (n ^ a) ∧ o = Subring.closure {((ze : o) : Ω), (n : Ω)⁻¹} := by
  intro Ω _ _ _ n a hn
  haveI := Fact.mk hn
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  let K := CyclotomicField (n ^ a) ℚ
  haveI : IsCyclotomicExtension {n ^ a} ℚ K := CyclotomicField.isCyclotomicExtension (n ^ a) ℚ
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  let φ : K →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := K) (M := Ω)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec (n ^ a) ℚ K
  set ζ := IsCyclotomicExtension.zeta (n ^ a) ℚ K
  obtain ⟨hD, hF⟩ := dedekind_closure hn φ hζ
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  have hz : IsPrimitiveRoot (φ ζ) (n ^ a) := hζ.map_of_injective φ.injective
  let z : T := ⟨φ ζ, Subring.subset_closure (Or.inl rfl)⟩
  have hz' : IsPrimitiveRoot z (n ^ a) := IsPrimitiveRoot.of_map_of_injective (f := T.subtype) hz T.subtype_injective
  have hu : IsUnit z := hz'.isUnit (NeZero.ne _)
  refine ⟨T, hu.unit, hD, hF, ?_, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ⟨_, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext ?_)
    simp [h0]
  · rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz
  · rfl

end GlobalTheory.CycAway
