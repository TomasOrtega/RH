import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldMapCompConstFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
open Polynomial

/- English proof (translation)
Introduce `K L _ _ _ φ hfin V _ hE s hs`. Use `letI : Algebra K L := φ.toAlgebra`. Use `haveI : FiniteDimensional K L := hfin`. Use `set E : ValuationSubring K := V.comap φ with hEdef`. Use `letI : Algebra E L := (φ.comp E.subtype).toAlgebra`.

Use `haveI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : IsFractionRing E K := inferInstance`. Use `haveI : Algebra.IsSeparable K L := inferInstance`. Use `haveI : IsDedekindDomain (integralClosure E L) := integralClosure.isDedekindDomain E K L`. Use `haveI : IsFractionRing (integralClosure E L) L := integralClosure.isFractionRing_of_finite_extension K L`.

Establish `hBV : ∀ x : L, IsIntegral E x → x ∈ V`. Introduce `x hx`. Use `letI : Algebra E V := ((φ.comp E.subtype).codRestrict V (fun y => y.2)).toAlgebra`. Use `haveI : IsScalarTower E V L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `h2 : IsIntegral V x` using `IsIntegral.tower_top hx`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Rewrite using `[← hy]`. Conclude with `y.2`. Establish `hpoly : ∀ x : L, IsIntegral E x → ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0`. Introduce and unpack `x ⟨p, hpm, hp⟩`.

Use `⟨p.map E.subtype, hpm.map _, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_map]`. Conclude with `(p.coeff i).2`. Rewrite using `[Polynomial.eval₂_map]`. Conclude with `hp`.

Use `set B := integralClosure E L`. Set `f : B →+* V` to `{ toFun := fun b => ⟨(b : L), hBV _ b.2⟩ map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Set `n : Ideal B` to `(IsLocalRing.maximalIdeal V).comap f`. Use `haveI hnp : n.IsPrime := Ideal.comap_isPrime _ _`. Establish `hn0 : n ≠ ⊥`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible E`. Establish `hϖ0 : (ϖ : K) ≠ 0` using `fun h => hϖ.ne_zero (Subtype.ext h)`. Introduce `hbot`. Establish `hmem : algebraMap E B ϖ ∈ n` using `by show f (algebraMap E B ϖ) ∈ IsLocalRing.maximalIdeal V`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`.

Introduce and unpack `⟨u, hu⟩`. Apply `hϖ.not_isUnit` to reduce the goal to its premises. Establish `h1 : ((u⁻¹ : Vˣ) : V) * f (algebraMap E B ϖ) = 1` using `by rw [← hu]; exact u.inv_mul`. Establish `h2 : ((((u⁻¹ : Vˣ) : V) : L)) * φ ϖ = 1` using `congrArg Subtype.val h1`. Establish `h3 : (ϖ : K)⁻¹ ∈ E` using `by show φ ((ϖ : K)⁻¹) ∈ V`.

Rewrite using `[map_inv₀, inv_eq_of_mul_eq_one_left h2]`. Conclude with `(((u⁻¹ : Vˣ) : V)).2`. Conclude with `isUnit_iff_exists_inv.2 ⟨⟨_, h3⟩, Subtype.ext (mul_inv_cancel₀ hϖ0)⟩`. Rewrite `hmem` using `[hbot, Ideal.mem_bot]`. Establish `h4 : φ (ϖ : K) = 0` using `congrArg (fun b : B => (b : L)) hmem`.

Conclude with `hϖ0 ((map_eq_zero φ).1 h4)`. Establish `hunit : ∀ d : B, d ∉ n → (d : L) ≠ 0 ∧ (d : L)⁻¹ ∈ V`. Introduce `d hd`. Establish `hu : IsUnit (f d)`. Assume the negation of the conclusion as `h`.

Conclude with `hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)`. Take `⟨u, hu⟩` from `hu`. Establish `h1 : f d * ((u⁻¹ : Vˣ) : V) = 1` using `by rw [← hu]; exact u.mul_inv`. Establish `h2 : (d : L) * ((((u⁻¹ : Vˣ) : V) : L)) = 1` using `congrArg Subtype.val h1`. Use `⟨left_ne_zero_of_mul_eq_one h2, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_eq_of_mul_eq_one_right h2]`. Conclude with `(((u⁻¹ : Vˣ) : V)).2`. Set `O` to `Localization.AtPrime n`. Use `letI : Algebra O L := IsLocalization.localizationAlgebraOfSubmonoidLe O L n.primeCompl (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)`. Use `haveI : IsScalarTower B O L := IsLocalization.localization_isScalarTower_of_submonoid_le O L n.primeCompl (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)`.

Use `haveI : IsFractionRing O L := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization n.primeCompl O L`. Use `haveI : IsDiscreteValuationRing O := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hn0 O`. Establish `hO : ∀ z : O, ∃ b d : B, d ∉ n ∧ algebraMap O L z * (d : L) = (b : L)`. Introduce `z`. Take `⟨⟨a, t⟩, rfl⟩` from `IsLocalization.mk'_surjective n.primeCompl z`.

Use `⟨a, t, t.2, ?_⟩` and prove the remaining obligations. Use `show algebraMap O L (IsLocalization.mk' O a t) * algebraMap B L t = algebraMap B L a`. Rewrite using `[IsScalarTower.algebraMap_apply B O L (t : B), IsScalarTower.algebraMap_apply B O L a, ← map_mul, IsLocalization.mk'_spec]`. Distinguish the cases in `hs0 : s = 0`. Use `⟨0, 1, ⟨hBV _ isIntegral_zero, hpoly _ isIntegral_zero⟩, ⟨hBV _ isIntegral_one, hpoly _ isIntegral_one⟩, one_ne_zero, by rw [inv_one]; exact V.one_mem, ?_⟩` and prove the remaining obligations.

Rewrite using `[hs0, zero_div]`. Break down `ValuationRing.isInteger_or_isInteger O s with ⟨z, hz⟩ | ⟨z, hz⟩` into its components or cases. Take `⟨b, d, hd, hbd⟩` from `hO z`. Use `⟨b, d, ⟨hBV _ b.2, hpoly _ b.2⟩, ⟨hBV _ d.2, hpoly _ d.2⟩, (hunit d hd).1, (hunit d hd).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, ← hbd, mul_div_cancel_right₀ _ (hunit d hd).1]`.

Take `⟨b, d, hd, hbd⟩` from `hO z`. Rewrite `hbd` using `[hz]`. Establish `hsb : s * (b : L) = d` using `by rw [← hbd, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]`. Establish `hb : b ∉ n`. Introduce `hb`.

Establish `hb' : ¬ IsUnit (f b)` using `(IsLocalRing.mem_maximalIdeal _).1 hb`. Establish `hfd : IsUnit (f d)`. Assume the negation of the conclusion as `h`. Conclude with `hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)`. Establish `hm : (⟨s, hs⟩ : V) * f b = f d` using `Subtype.ext hsb`.

Rewrite `hfd` using `[← hm]`. Conclude with `hb' (isUnit_of_mul_isUnit_right hfd)`. Use `⟨d, b, ⟨hBV _ d.2, hpoly _ d.2⟩, ⟨hBV _ b.2, hpoly _ b.2⟩, (hunit b hb).1, (hunit b hb).2, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_div_iff (hunit b hb).1, hsb]`.
-/
theorem GlobalTheory.dvr_eq_localization_integralClosure : ∀ (K L : Type) [Field K] [Field L] [CharZero K] (φ : K →+* L), (letI := φ.toAlgebra; FiniteDimensional K L) → ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V], IsDiscreteValuationRing (V.comap φ) → ∀ s ∈ V, ∃ b d : L, (b ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ b = 0) ∧ (d ∈ V ∧ ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ d = 0) ∧ d ≠ 0 ∧ d⁻¹ ∈ V ∧ s = b / d := by
  intro K L _ _ _ φ hfin V _ hE s hs
  letI : Algebra K L := φ.toAlgebra
  haveI : FiniteDimensional K L := hfin
  set E : ValuationSubring K := V.comap φ with hEdef
  letI : Algebra E L := (φ.comp E.subtype).toAlgebra
  haveI : IsScalarTower E K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsFractionRing E K := inferInstance
  haveI : Algebra.IsSeparable K L := inferInstance
  haveI : IsDedekindDomain (integralClosure E L) := integralClosure.isDedekindDomain E K L
  haveI : IsFractionRing (integralClosure E L) L := integralClosure.isFractionRing_of_finite_extension K L

  have hBV : ∀ x : L, IsIntegral E x → x ∈ V := by
    intro x hx
    letI : Algebra E V := ((φ.comp E.subtype).codRestrict V (fun y => y.2)).toAlgebra
    haveI : IsScalarTower E V L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have h2 : IsIntegral V x := IsIntegral.tower_top hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    rw [← hy]; exact y.2

  have hpoly : ∀ x : L, IsIntegral E x →
      ∃ p : K[X], p.Monic ∧ (∀ i, p.coeff i ∈ V.comap φ) ∧ p.eval₂ φ x = 0 := by
    rintro x ⟨p, hpm, hp⟩
    refine ⟨p.map E.subtype, hpm.map _, fun i => ?_, ?_⟩
    · rw [Polynomial.coeff_map]; exact (p.coeff i).2
    · rw [Polynomial.eval₂_map]; exact hp
  set B := integralClosure E L
  let f : B →+* V :=
    { toFun := fun b => ⟨(b : L), hBV _ b.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let n : Ideal B := (IsLocalRing.maximalIdeal V).comap f
  haveI hnp : n.IsPrime := Ideal.comap_isPrime _ _

  have hn0 : n ≠ ⊥ := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E
    have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    intro hbot
    have hmem : algebraMap E B ϖ ∈ n := by
      show f (algebraMap E B ϖ) ∈ IsLocalRing.maximalIdeal V
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hϖ.not_isUnit
      have h1 : ((u⁻¹ : Vˣ) : V) * f (algebraMap E B ϖ) = 1 := by rw [← hu]; exact u.inv_mul
      have h2 : ((((u⁻¹ : Vˣ) : V) : L)) * φ ϖ = 1 := congrArg Subtype.val h1
      have h3 : (ϖ : K)⁻¹ ∈ E := by
        show φ ((ϖ : K)⁻¹) ∈ V
        rw [map_inv₀, inv_eq_of_mul_eq_one_left h2]; exact (((u⁻¹ : Vˣ) : V)).2
      exact isUnit_iff_exists_inv.2 ⟨⟨_, h3⟩, Subtype.ext (mul_inv_cancel₀ hϖ0)⟩
    rw [hbot, Ideal.mem_bot] at hmem
    have h4 : φ (ϖ : K) = 0 := congrArg (fun b : B => (b : L)) hmem
    exact hϖ0 ((map_eq_zero φ).1 h4)
  have hunit : ∀ d : B, d ∉ n → (d : L) ≠ 0 ∧ (d : L)⁻¹ ∈ V := by
    intro d hd
    have hu : IsUnit (f d) := by
      by_contra h
      exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
    obtain ⟨u, hu⟩ := hu
    have h1 : f d * ((u⁻¹ : Vˣ) : V) = 1 := by rw [← hu]; exact u.mul_inv
    have h2 : (d : L) * ((((u⁻¹ : Vˣ) : V) : L)) = 1 := congrArg Subtype.val h1
    refine ⟨left_ne_zero_of_mul_eq_one h2, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h2]; exact (((u⁻¹ : Vˣ) : V)).2
  let O := Localization.AtPrime n
  letI : Algebra O L := IsLocalization.localizationAlgebraOfSubmonoidLe O L n.primeCompl
    (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsScalarTower B O L := IsLocalization.localization_isScalarTower_of_submonoid_le O L
    n.primeCompl (nonZeroDivisors B) (Ideal.primeCompl_le_nonZeroDivisors n)
  haveI : IsFractionRing O L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization n.primeCompl O L
  haveI : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hn0 O
  have hO : ∀ z : O, ∃ b d : B, d ∉ n ∧ algebraMap O L z * (d : L) = (b : L) := by
    intro z
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective n.primeCompl z
    refine ⟨a, t, t.2, ?_⟩
    show algebraMap O L (IsLocalization.mk' O a t) * algebraMap B L t = algebraMap B L a
    rw [IsScalarTower.algebraMap_apply B O L (t : B), IsScalarTower.algebraMap_apply B O L a,
      ← map_mul, IsLocalization.mk'_spec]
  by_cases hs0 : s = 0
  · refine ⟨0, 1, ⟨hBV _ isIntegral_zero, hpoly _ isIntegral_zero⟩,
      ⟨hBV _ isIntegral_one, hpoly _ isIntegral_one⟩, one_ne_zero, by rw [inv_one]; exact V.one_mem, ?_⟩
    rw [hs0, zero_div]
  rcases ValuationRing.isInteger_or_isInteger O s with ⟨z, hz⟩ | ⟨z, hz⟩
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    refine ⟨b, d, ⟨hBV _ b.2, hpoly _ b.2⟩, ⟨hBV _ d.2, hpoly _ d.2⟩, (hunit d hd).1,
      (hunit d hd).2, ?_⟩
    rw [← hz, ← hbd, mul_div_cancel_right₀ _ (hunit d hd).1]
  · obtain ⟨b, d, hd, hbd⟩ := hO z
    rw [hz] at hbd
    have hsb : s * (b : L) = d := by rw [← hbd, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    have hb : b ∉ n := by
      intro hb
      have hb' : ¬ IsUnit (f b) := (IsLocalRing.mem_maximalIdeal _).1 hb
      have hfd : IsUnit (f d) := by
        by_contra h
        exact hd (show f d ∈ IsLocalRing.maximalIdeal V from (IsLocalRing.mem_maximalIdeal _).2 h)
      have hm : (⟨s, hs⟩ : V) * f b = f d := Subtype.ext hsb
      rw [← hm] at hfd
      exact hb' (isUnit_of_mul_isUnit_right hfd)
    refine ⟨d, b, ⟨hBV _ d.2, hpoly _ d.2⟩, ⟨hBV _ b.2, hpoly _ b.2⟩, (hunit b hb).1,
      (hunit b hb).2, ?_⟩
    rw [eq_div_iff (hunit b hb).1, hsb]
