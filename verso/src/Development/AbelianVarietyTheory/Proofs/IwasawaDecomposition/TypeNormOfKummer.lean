import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E] {h : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_ne_zero, 1, by rw [one_pow, FractionalIdeal.spanSingleton_one]⟩`.
-/
theorem one_mem_pow : (1 : E) ∈ powIdealElts E h :=
  ⟨one_ne_zero, 1, by rw [one_pow, FractionalIdeal.spanSingleton_one]⟩

/- English proof (translation)
Take `⟨hx0, a, ha⟩` from `hx`. Take `⟨hy0, b, hb⟩` from `hy`. Conclude with `⟨mul_ne_zero hx0 hy0, a * b, by`. Rewrite using `[← FractionalIdeal.spanSingleton_mul_spanSingleton, ha, hb, mul_pow]⟩`.
-/
theorem mul_mem_pow {x y : E} (hx : x ∈ powIdealElts E h) (hy : y ∈ powIdealElts E h) :
    x * y ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  obtain ⟨hy0, b, hb⟩ := hy
  exact ⟨mul_ne_zero hx0 hy0, a * b, by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ha, hb, mul_pow]⟩

/- English proof (translation)
Take `⟨hx0, a, ha⟩` from `hx`. Conclude with `⟨inv_ne_zero hx0, a⁻¹, by rw [← FractionalIdeal.spanSingleton_inv, ha, inv_pow]⟩`.
-/
theorem inv_mem_pow {x : E} (hx : x ∈ powIdealElts E h) : x⁻¹ ∈ powIdealElts E h := by
  obtain ⟨hx0, a, ha⟩ := hx
  exact ⟨inv_ne_zero hx0, a⁻¹, by rw [← FractionalIdeal.spanSingleton_inv, ha, inv_pow]⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `one_mem_pow`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `mul_mem_pow ih hx`.
-/
theorem npow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℕ) : x ^ n ∈ powIdealElts E h := by
  induction n with
  | zero => rw [pow_zero]; exact one_mem_pow
  | succ n ih => rw [pow_succ]; exact mul_mem_pow ih hx

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using npow_mem_pow hx n`. Consider the case `negSucc n => rw [zpow_negSucc]`. Conclude with `inv_mem_pow (npow_mem_pow hx _)`.
-/
theorem zpow_mem_pow {x : E} (hx : x ∈ powIdealElts E h) (n : ℤ) : x ^ n ∈ powIdealElts E h := by
  cases n with
  | ofNat n => simpa using npow_mem_pow hx n
  | negSucc n => rw [zpow_negSucc]; exact inv_mem_pow (npow_mem_pow hx _)

/- English proof (translation)
The claim follows from `Finset.prod_induction f (· ∈ powIdealElts E h) (fun _ _ => mul_mem_pow) one_mem_pow hf`.
-/
theorem prod_mem_pow {ι : Type} (s : Finset ι) (f : ι → E) (hf : ∀ i ∈ s, f i ∈ powIdealElts E h) :
    ∏ i ∈ s, f i ∈ powIdealElts E h :=
  Finset.prod_induction f (· ∈ powIdealElts E h) (fun _ _ => mul_mem_pow) one_mem_pow hf

/- English proof (translation)
Take `⟨hx0, a, ha⟩` from `hx`. Establish `hle : (𝓞 E)⁰ ≤ Submonoid.comap (RingOfIntegers.mapRingHom σ) (𝓞 E')⁰` using `nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun a b hab => RingOfIntegers.ext (σ.injective (congrArg (fun y : 𝓞 E' => (y : E')) hab))`. Establish `hm : IsLocalization.map E' (RingOfIntegers.mapRingHom σ) hle = σ` using `IsLocalization.ringHom_ext (𝓞 E)⁰ (by rw [IsLocalization.map_comp]; rfl)`. Use `⟨(map_ne_zero σ).2 hx0, FractionalIdeal.extendedHom' E' hle a, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, ← ha]`.

Express the relevant statement in the definitionally equal form `_ = FractionalIdeal.extended E' _ _`. Rewrite using `[FractionalIdeal.extended_spanSingleton, hm]`.
-/
theorem map_mem_pow {E' : Type} [Field E'] [NumberField E'] (σ : E →+* E') {x : E} (hx : x ∈ powIdealElts E h) :
    σ x ∈ powIdealElts E' h := by
  obtain ⟨hx0, a, ha⟩ := hx
  have hle : (𝓞 E)⁰ ≤ Submonoid.comap (RingOfIntegers.mapRingHom σ) (𝓞 E')⁰ :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ fun a b hab =>
      RingOfIntegers.ext (σ.injective (congrArg (fun y : 𝓞 E' => (y : E')) hab))
  have hm : IsLocalization.map E' (RingOfIntegers.mapRingHom σ) hle = σ :=
    IsLocalization.ringHom_ext (𝓞 E)⁰ (by rw [IsLocalization.map_comp]; rfl)
  refine ⟨(map_ne_zero σ).2 hx0, FractionalIdeal.extendedHom' E' hle a, ?_⟩
  rw [← map_pow, ← ha]
  change _ = FractionalIdeal.extended E' _ _
  rw [FractionalIdeal.extended_spanSingleton, hm]

/- English proof (translation)
Assemble the required witnesses or components as `⟨by exact_mod_cast h0, 𝔞, by rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]⟩`.
-/
theorem mem_pow_of_span {𝔞 : Ideal (𝓞 E)} {γ : 𝓞 E} (h0 : γ ≠ 0) (hγ : 𝔞 ^ h = Ideal.span {γ}) :
    (γ : E) ∈ powIdealElts E h :=
  ⟨by exact_mod_cast h0, 𝔞, by
    rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]⟩

/- English proof (translation)
Use `letI := φ.toAlgebra`. Set `t : E →ₐ[ℚ] ℂ` to `τ.toRatAlgHom`. Conclude with `⟨t.restrictNormal' E, fun x => (t.restrictNormal_commutes E x).symm⟩`.
-/
theorem exists_aut [IsGalois ℚ E] (φ τ : E →+* ℂ) : ∃ σ : E ≃ₐ[ℚ] E, ∀ x, τ x = φ (σ x) := by
  letI := φ.toAlgebra
  let t : E →ₐ[ℚ] ℂ := τ.toRatAlgHom
  exact ⟨t.restrictNormal' E, fun x => (t.restrictNormal_commutes E x).symm⟩

/- English proof (translation)
Set `𝔠 : (Ideal (𝓞 E))⁰` to `⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩`. Establish `h1 : ClassGroup.mk0 (𝔠 ^ classNumber E) = 1`. Rewrite using `[map_pow, classNumber, pow_card_eq_one]`. Take `⟨γ, hγ⟩` from `(ClassGroup.mk0_eq_one_iff (𝔠 ^ classNumber E).2).1 h1`. Establish `hγ' : 𝔞 ^ classNumber E = Ideal.span {γ}` using `hγ`.

Use `⟨γ, ?_, hγ'⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hγ'` using `[Ideal.span_singleton_zero]`. Conclude with `pow_ne_zero _ h𝔞 hγ'`.
-/
theorem exists_gen (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) :
    ∃ γ : 𝓞 E, γ ≠ 0 ∧ 𝔞 ^ classNumber E = Ideal.span {γ} := by
  let 𝔠 : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  have h1 : ClassGroup.mk0 (𝔠 ^ classNumber E) = 1 := by
    rw [map_pow, classNumber, pow_card_eq_one]
  obtain ⟨γ, hγ⟩ := (ClassGroup.mk0_eq_one_iff (𝔠 ^ classNumber E).2).1 h1
  have hγ' : 𝔞 ^ classNumber E = Ideal.span {γ} := hγ
  refine ⟨γ, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ h𝔞 hγ'

/- English proof (translation)
Use `Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K hK) 𝔞)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Subtype.ext_iff]`. Both sides reduce to the same expression.
-/
theorem span_eq_extend (K : IntermediateField ℚ ℂ) [NumberField K] (τ : E →+* ℂ) (hK : ∀ x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) : Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} =
      extendIdealHom (τ.codRestrict K hK) 𝔞 := by
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K hK) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

/- English proof (translation)
Establish `: NumberField K` using `NumberField.mk`. Take `⟨hK, -, hV⟩` from `(kummerField_le_iff φ).1 hV`. Rewrite using `[span_eq_extend K φ hK]`. Break down `eq_or_ne 𝔞 ⊥ with rfl | h𝔞` into its components or cases. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Ideal.span_singleton_zero, extendIdealHom_span]`. Simplify using the standard rewrite rules. Take `⟨γ, h0, hγ⟩` from `exists_gen 𝔞 h𝔞`. Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq (φ (γ : E)) (classNumber_pos E)`. Set `β : K` to `⟨b, hV _ (mem_pow_of_span h0 hγ) b hb⟩`.

Establish `hβ : β ^ classNumber E = φ.codRestrict K hK (γ : E)` using `Subtype.ext hb`. Establish `hβ0 : β ≠ 0`. Introduce `h`. Rewrite `hβ` using `[h, zero_pow (classNumber_ne_zero E), eq_comm, map_eq_zero]`. Conclude with `h0 (by exact_mod_cast hβ)`.

Use `⟨β, (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ (classNumber_pos E) hβ0 (extendIdealHom_fg _ _) ?_).symm⟩` and prove the remaining obligations. Rewrite using `[← map_pow, hγ, extendIdealHom_span, hβ]`.
-/
theorem capit_of_kummer (φ : E →+* ℂ) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hV : kummerField φ (classNumber E) ≤ K) (𝔞 : Ideal (𝓞 E)) : ∃ β : K,
      Submodule.span (𝓞 K) {β} = Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = φ (a : E)} := by
  have : NumberField K := NumberField.mk
  obtain ⟨hK, -, hV⟩ := (kummerField_le_iff φ).1 hV
  rw [span_eq_extend K φ hK]
  rcases eq_or_ne 𝔞 ⊥ with rfl | h𝔞
  · refine ⟨0, ?_⟩
    rw [← Ideal.span_singleton_zero, extendIdealHom_span]
    simp
  obtain ⟨γ, h0, hγ⟩ := exists_gen 𝔞 h𝔞
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (φ (γ : E)) (classNumber_pos E)
  let β : K := ⟨b, hV _ (mem_pow_of_span h0 hγ) b hb⟩
  have hβ : β ^ classNumber E = φ.codRestrict K hK (γ : E) := Subtype.ext hb
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow (classNumber_ne_zero E), eq_comm, map_eq_zero] at hβ
    exact h0 (by exact_mod_cast hβ)
  refine ⟨β, (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ (classNumber_pos E) hβ0
    (extendIdealHom_fg _ _) ?_).symm⟩
  rw [← map_pow, hγ, extendIdealHom_span, hβ]

/- English proof (translation)
Establish `: NumberField K` using `NumberField.mk`. Take `⟨hK0, -, hV⟩` from `(kummerField_le_iff φ).1 hV`. Use `choose s hs using exists_aut φ`. Establish `hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K` using `fun τ x => by rw [hs]; exact hK0 _`. Establish `hpos` using `classNumber_pos E`.

Take `⟨γ, h0, hγ⟩` from `exists_gen 𝔞 h𝔞`. Establish `hy : ∏ τ, s τ (γ : E) ^ r τ ∈ powIdealElts E (classNumber E)` using `prod_mem_pow _ _ fun τ _ => npow_mem_pow (map_mem_pow (s τ : E →+* E) (mem_pow_of_span h0 hγ)) _`. Take `⟨b, hb⟩` from `IsAlgClosed.exists_pow_nat_eq (φ (∏ τ, s τ (γ : E) ^ r τ)) hpos`. Set `β : K` to `⟨b, hV _ hy b hb⟩`. Establish `hβ : β ^ classNumber E = ∏ τ : E →+* ℂ, τ.codRestrict K (hK τ) (γ : E) ^ r τ`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [β, SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb, map_prod, map_pow, ← hs]`. Both sides reduce to the same expression. Establish `hβ0 : β ≠ 0`. Introduce `h`.

Rewrite `hβ` using `[h, zero_pow hpos.ne']`. Use `Finset.prod_ne_zero_iff.2 (fun τ _ => pow_ne_zero _ ?_) hβ.symm` and prove the remaining obligations. Rewrite using `[map_ne_zero]`. Conclude with `h0` after adjusting the coercions. Use `⟨β, hβ0, ?_, fun σ => ?_⟩` and prove the remaining obligations.

Simplify using `only [fun τ => span_eq_extend K τ (hK τ)]`. Use `(GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ hpos hβ0 (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_).symm` and prove the remaining obligations. Rewrite using `[hβ, ← span_singleton_prod_pow, ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, mul_comm, pow_mul, ← map_pow, hγ, extendIdealHom_span]`.

Establish `h1` using `norm_typeNorm_sq_eq E r n hr K hK (γ : E) σ`. Establish `h2 : ‖σ (β ^ classNumber E)‖ ^ 2 = (Ideal.absNorm (Ideal.span {γ}) : ℝ) ^ n`. Rewrite using `[Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, hβ]`. Rewrite `h1` using `[← Algebra.coe_norm_int, Rat.cast_intCast]`. Conclude with `h1`.

Rewrite `h2` using `[← hγ, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul]`. Conclude with `(pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 h2`.
-/
theorem typeNorm_of_kummer [IsCMField E] [IsGalois ℚ E] (φ : E →+* ℂ) (r : (E →+* ℂ) → ℕ) (n : ℕ)
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (hV : kummerField φ (classNumber E) ≤ K) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} =
        ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  classical
  have : NumberField K := NumberField.mk
  obtain ⟨hK0, -, hV⟩ := (kummerField_le_iff φ).1 hV
  choose s hs using exists_aut φ
  have hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K := fun τ x => by rw [hs]; exact hK0 _
  have hpos := classNumber_pos E
  obtain ⟨γ, h0, hγ⟩ := exists_gen 𝔞 h𝔞
  have hy : ∏ τ, s τ (γ : E) ^ r τ ∈ powIdealElts E (classNumber E) :=
    prod_mem_pow _ _ fun τ _ => npow_mem_pow (map_mem_pow (s τ : E →+* E) (mem_pow_of_span h0 hγ)) _
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (φ (∏ τ, s τ (γ : E) ^ r τ)) hpos
  let β : K := ⟨b, hV _ hy b hb⟩
  have hβ : β ^ classNumber E = ∏ τ : E →+* ℂ, τ.codRestrict K (hK τ) (γ : E) ^ r τ := by
    apply Subtype.ext
    simp only [β, SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb, map_prod, map_pow, ← hs]
    rfl
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h, zero_pow hpos.ne'] at hβ
    refine Finset.prod_ne_zero_iff.2 (fun τ _ => pow_ne_zero _ ?_) hβ.symm
    rw [map_ne_zero]; exact_mod_cast h0
  refine ⟨β, hβ0, ?_, fun σ => ?_⟩
  · simp only [fun τ => span_eq_extend K τ (hK τ)]
    refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β _ hpos hβ0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_).symm
    rw [hβ, ← span_singleton_prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hγ, extendIdealHom_span]
  · have h1 := norm_typeNorm_sq_eq E r n hr K hK (γ : E) σ
    have h2 : ‖σ (β ^ classNumber E)‖ ^ 2 = (Ideal.absNorm (Ideal.span {γ}) : ℝ) ^ n := by
      rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs, hβ]
      rw [← Algebra.coe_norm_int, Rat.cast_intCast] at h1
      exact h1
    rw [← hγ, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at h2
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 h2

end GlobalTheory.Mem.FieldsEx

end
