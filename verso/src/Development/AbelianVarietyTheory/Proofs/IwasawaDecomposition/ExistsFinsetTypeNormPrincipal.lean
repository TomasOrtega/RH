import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubmoduleEqSpanOfPowEqSpanPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdNormEmbeddingsEqAbsNorm
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped nonZeroDivisors

namespace GlobalTheory.Mem

/- English proof (translation)
Rewrite using `[Ideal.map, IsLocalization.coeSubmodule_span, Set.image_image]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`.

Conclude with `⟨a, ha, rfl⟩`. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `⟨a, ha, rfl⟩`.
-/
theorem span_image_eq_coeSubmodule_map {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (𝔞 : Ideal (𝓞 E)) :
    Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, x = f (a : E)} =
      IsLocalization.coeSubmodule K (𝔞.map (RingOfIntegers.mapRingHom f)) := by
  rw [Ideal.map, IsLocalization.coeSubmodule_span, Set.image_image]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

noncomputable def extendIdealHom {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) : Ideal (𝓞 E) →* Submodule (𝓞 K) K where
  toFun 𝔞 := IsLocalization.coeSubmodule K (𝔞.map (RingOfIntegers.mapRingHom f))
  map_one' := by
    rw [Ideal.one_eq_top, Ideal.map_top, IsLocalization.coeSubmodule_top]
  map_mul' a b := by rw [Ideal.map_mul, IsLocalization.coeSubmodule_mul]

/- English proof (translation)
Use `show IsLocalization.coeSubmodule K ((Ideal.span {a}).map (RingOfIntegers.mapRingHom f)) = _`. Rewrite using `[Ideal.map_span, IsLocalization.coeSubmodule_span, Set.image_singleton, Set.image_singleton]`. Both sides reduce to the same expression.
-/
theorem extendIdealHom_span {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (a : 𝓞 E) :
    extendIdealHom f (Ideal.span {a}) = Submodule.span (𝓞 K) {f (a : E)} := by
  show IsLocalization.coeSubmodule K ((Ideal.span {a}).map (RingOfIntegers.mapRingHom f)) = _
  rw [Ideal.map_span, IsLocalization.coeSubmodule_span, Set.image_singleton, Set.image_singleton]
  rfl

/- English proof (translation)
The claim follows from `Submodule.FG.map _ (IsNoetherian.noetherian _)`.
-/
theorem extendIdealHom_fg {E K : Type} [Field E] [Field K] [NumberField K]
    (f : E →+* K) (𝔞 : Ideal (𝓞 E)) : (extendIdealHom f 𝔞).FG :=
  Submodule.FG.map _ (IsNoetherian.noetherian _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Submodule.one_eq_span]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.prod_insert hi, ih, Submodule.span_pow, Set.singleton_pow, Submodule.span_mul_span, Set.singleton_mul_singleton]`.
-/
theorem span_singleton_prod_pow {R K ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset ι) (x : ι → K) (r : ι → ℕ) :
    ∏ i ∈ s, Submodule.span R {x i} ^ r i = Submodule.span R {∏ i ∈ s, x i ^ r i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Submodule.one_eq_span]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, ih, Submodule.span_pow, Set.singleton_pow,
      Submodule.span_mul_span, Set.singleton_mul_singleton]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Submodule.one_eq_span]`. Conclude with `Submodule.fg_span_singleton _`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi]`.

Conclude with `((h i).pow _).mul ih`.
-/
theorem fg_prod_pow {R K ι : Type} [CommRing R] [CommRing K] [Algebra R K]
    (s : Finset ι) (I : ι → Submodule R K) (r : ι → ℕ) (h : ∀ i, (I i).FG) :
    (∏ i ∈ s, I i ^ r i).FG := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact ((h i).pow _).mul ih

/- English proof (translation)
Take `⟨𝔠, h𝔠⟩` from `ClassGroup.mk0_surjective c`. Establish `h1 : ClassGroup.mk0 (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))) = 1`. Rewrite using `[map_pow, pow_card_eq_one]`. Establish `h2` using `(ClassGroup.mk0_eq_one_iff (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))).2).1 h1`. Take `⟨γ, hγ⟩` from `h2`.

Establish `hγ' : (𝔠 : Ideal (𝓞 E)) ^ Fintype.card (ClassGroup (𝓞 E)) = Ideal.span {γ}` using `hγ`. Use `⟨𝔠, γ, h𝔠, ?_, hγ'⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hγ'` using `[Ideal.span_singleton_zero]`. Conclude with `pow_ne_zero _ (nonZeroDivisors.ne_zero 𝔠.2) hγ'`.
-/
theorem exists_rep_pow_classNumber (E : Type) [Field E] [NumberField E] (c : ClassGroup (𝓞 E)) :
    ∃ (𝔠 : (Ideal (𝓞 E))⁰) (γ : 𝓞 E), ClassGroup.mk0 𝔠 = c ∧ γ ≠ 0 ∧
      (𝔠 : Ideal (𝓞 E)) ^ Fintype.card (ClassGroup (𝓞 E)) = Ideal.span {γ} := by
  obtain ⟨𝔠, h𝔠⟩ := ClassGroup.mk0_surjective c
  have h1 : ClassGroup.mk0 (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 := (ClassGroup.mk0_eq_one_iff (𝔠 ^ Fintype.card (ClassGroup (𝓞 E))).2).1 h1
  obtain ⟨γ, hγ⟩ := h2
  have hγ' : (𝔠 : Ideal (𝓞 E)) ^ Fintype.card (ClassGroup (𝓞 E)) = Ideal.span {γ} := hγ
  refine ⟨𝔠, γ, h𝔠, ?_, hγ'⟩
  rintro rfl
  rw [Ideal.span_singleton_zero] at hγ'
  exact pow_ne_zero _ (nonZeroDivisors.ne_zero 𝔠.2) hγ'

/- English proof (translation)
Introduce `E _ _ _ _ r n hr`. Use `set h := Fintype.card (ClassGroup (𝓞 E)) with hh`. Establish `hpos : 0 < h` using `Fintype.card_pos`. Use `choose 𝔠 γ h𝔠 hγ0 hγ using exists_rep_pow_classNumber E`. Establish `hex : ∀ c, ∃ z : ℂ, z ^ h = ∏ τ : E →+* ℂ, τ (γ c : E) ^ r τ` using `fun c => IsAlgClosed.exists_pow_nat_eq _ hpos`.

Use `choose b hb using hex`. Use `⟨Finset.univ.image b, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`. Take `⟨c, -, rfl⟩` from `Finset.mem_image.1 hz`. Use `IsAlgebraic.of_pow hpos ?_` and prove the remaining obligations.

Rewrite using `[hb]`. Use `IsIntegral.isAlgebraic (IsIntegral.prod _ fun τ _ => IsIntegral.pow ?_ _)` and prove the remaining obligations. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℚ) (γ c : E)).map τ.toRatAlgHom`. Introduce `K _ hS hK 𝔞 h𝔞`. Establish `: NumberField K` using `NumberField.mk`.

Set `f : (E →+* ℂ) → (E →+* K)` to `fun τ => τ.codRestrict K (hK τ)`. Set `N : 𝓞 E → K` to `fun a => ∏ τ : E →+* ℂ, f τ (a : E) ^ r τ`. Establish `hN0 : ∀ a, a ≠ 0 → N a ≠ 0` using `fun a ha => Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by`. Rewrite using `[map_ne_zero]`. Conclude with `ha)` after adjusting the coercions.

Establish `hNabs : ∀ (a : 𝓞 E) (σ : K →+* ℂ), ‖σ (N a)‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) ^ n`. Introduce `a σ`. Use `norm_typeNorm_sq_eq E r n hr K hK (a : E) σ` as an intermediate fact. Rewrite using `[Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]`. Rewrite `this` using `[← Algebra.coe_norm_int]`.

Rewrite `this` using `[Rat.cast_intCast]`. Conclude with `this`. Set `Φ : Ideal (𝓞 E) → Submodule (𝓞 K) K` to `fun I => ∏ τ : E →+* ℂ, extendIdealHom (f τ) I ^ r τ`. Establish `hΦmul : ∀ I J, Φ (I * J) = Φ I * Φ J`. Introduce `I J`.

Simplify using `only [Φ, map_mul, mul_pow, Finset.prod_mul_distrib]`. Establish `hΦpow : ∀ I, Φ (I ^ h) = Φ I ^ h`. Introduce `I`. Simplify using `only [Φ, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]`. Establish `hΦspan : ∀ a, Φ (Ideal.span {a}) = Submodule.span (𝓞 K) {N a}`.

Introduce `a`. Simplify using `only [Φ, N, extendIdealHom_span, span_singleton_prod_pow]`. Establish `hgoal : ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ = Φ 𝔞`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Use `Eq.trans ?_ (span_image_eq_coeSubmodule_map (f τ) 𝔞)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_ofPred_eq, Subtype.ext_iff]`. Both sides reduce to the same expression.

Rewrite using `[hgoal]`. Set `𝔞' : (Ideal (𝓞 E))⁰` to `⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩`. Use `set c := ClassGroup.mk0 𝔞' with hc`. Take `⟨x, y, hx, hy, hxy⟩` from `ClassGroup.mk0_eq_mk0_iff.1 (hc.symm.trans (h𝔠 c).symm)`. Establish `hxy' : Ideal.span {x} * 𝔞 = Ideal.span {y} * (𝔠 c : Ideal (𝓞 E))` using `hxy`.

Set `βc : K` to `⟨b c, hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩`. Establish `hβc : βc ^ h = N (γ c)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [βc, N, SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]`. Both sides reduce to the same expression.

Establish `hβc0 : βc ≠ 0`. Introduce `h0`. Rewrite `hβc` using `[h0, zero_pow hpos.ne']`. Conclude with `hN0 _ (hγ0 c) hβc.symm`. Establish `hΦc : Φ (𝔠 c) = Submodule.span (𝓞 K) {βc}`.

Use `GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ βc h hpos hβc0 (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_` and prove the remaining obligations. Rewrite using `[← hΦpow, hγ, hΦspan, hβc]`. Establish `hcabs : ∀ σ : K →+* ℂ, ‖σ βc‖ ^ 2 = (Ideal.absNorm (𝔠 c : Ideal (𝓞 E)) : ℝ) ^ n`. Introduce `σ`. Use `hNabs (γ c) σ` as an intermediate fact.

Rewrite `this` using `[← hγ, ← hβc, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul]`. Conclude with `(pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 this`. Use `⟨(N x)⁻¹ * (N y * βc), mul_ne_zero (inv_ne_zero (hN0 x hx)) (mul_ne_zero (hN0 y hy) hβc0), ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg Φ hxy'`. Rewrite `h1` using `[hΦmul, hΦmul, hΦspan, hΦspan, hΦc]`.

Rewrite using `[← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span, ← Submodule.span_mul_span, ← h1, ← mul_assoc, Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ (hN0 x hx), ← Submodule.one_eq_span, one_mul]`. Introduce `σ`. Establish `h1` using `congrArg (fun I => (Ideal.absNorm I : ℝ) ^ n) hxy'`. Simplify using `only [map_mul, Nat.cast_mul, mul_pow] at h1`. Rewrite `h1` using `[← hNabs x σ, ← hNabs y σ, ← hcabs σ]`.

Establish `h2 : ‖σ (N x)‖ ≠ 0`. Rewrite using `[norm_ne_zero_iff, map_ne_zero]`. Conclude with `hN0 x hx`. Rewrite using `[map_mul, map_mul, map_inv₀, norm_mul, norm_mul, norm_inv, mul_pow, mul_pow, ← h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_finset_typeNorm_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], (∀ z ∈ S, z ∈ K) → (∀ (τ : E →+* ℂ) x, τ x ∈ K) → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  intro E _ _ _ _ r n hr
  classical
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : 0 < h := Fintype.card_pos
  choose 𝔠 γ h𝔠 hγ0 hγ using exists_rep_pow_classNumber E
  have hex : ∀ c, ∃ z : ℂ, z ^ h = ∏ τ : E →+* ℂ, τ (γ c : E) ^ r τ := fun c =>
    IsAlgClosed.exists_pow_nat_eq _ hpos
  choose b hb using hex
  refine ⟨Finset.univ.image b, ?_, ?_⟩
  · intro z hz
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hz
    refine IsAlgebraic.of_pow hpos ?_
    rw [hb]
    refine IsIntegral.isAlgebraic (IsIntegral.prod _ fun τ _ => IsIntegral.pow ?_ _)
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) (γ c : E)).map τ.toRatAlgHom
  intro K _ hS hK 𝔞 h𝔞
  have : NumberField K := NumberField.mk
  let f : (E →+* ℂ) → (E →+* K) := fun τ => τ.codRestrict K (hK τ)
  let N : 𝓞 E → K := fun a => ∏ τ : E →+* ℂ, f τ (a : E) ^ r τ
  have hN0 : ∀ a, a ≠ 0 → N a ≠ 0 := fun a ha =>
    Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (by
      rw [map_ne_zero]; exact_mod_cast ha)
  have hNabs : ∀ (a : 𝓞 E) (σ : K →+* ℂ),
      ‖σ (N a)‖ ^ 2 = (Ideal.absNorm (Ideal.span {a}) : ℝ) ^ n := by
    intro a σ
    have := norm_typeNorm_sq_eq E r n hr K hK (a : E) σ
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]
    rw [← Algebra.coe_norm_int] at this
    rw [Rat.cast_intCast] at this
    exact this
  let Φ : Ideal (𝓞 E) → Submodule (𝓞 K) K := fun I => ∏ τ : E →+* ℂ, extendIdealHom (f τ) I ^ r τ
  have hΦmul : ∀ I J, Φ (I * J) = Φ I * Φ J := by
    intro I J
    simp only [Φ, map_mul, mul_pow, Finset.prod_mul_distrib]
  have hΦpow : ∀ I, Φ (I ^ h) = Φ I ^ h := by
    intro I
    simp only [Φ, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]
  have hΦspan : ∀ a, Φ (Ideal.span {a}) = Submodule.span (𝓞 K) {N a} := by
    intro a
    simp only [Φ, N, extendIdealHom_span, span_singleton_prod_pow]
  have hgoal : ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ
      = Φ 𝔞 := by
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (f τ) 𝔞)
    congr 1
    ext x
    simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
    rfl
  rw [hgoal]
  let 𝔞' : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
  set c := ClassGroup.mk0 𝔞' with hc
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 (hc.symm.trans (h𝔠 c).symm)
  have hxy' : Ideal.span {x} * 𝔞 = Ideal.span {y} * (𝔠 c : Ideal (𝓞 E)) := hxy
  let βc : K := ⟨b c, hS _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩
  have hβc : βc ^ h = N (γ c) := by
    apply Subtype.ext
    simp only [βc, N, SubmonoidClass.coe_pow, IntermediateField.coe_prod, hb]
    rfl
  have hβc0 : βc ≠ 0 := by
    intro h0
    rw [h0, zero_pow hpos.ne'] at hβc
    exact hN0 _ (hγ0 c) hβc.symm
  have hΦc : Φ (𝔠 c) = Submodule.span (𝓞 K) {βc} := by
    refine GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ βc h hpos hβc0
      (fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _) ?_
    rw [← hΦpow, hγ, hΦspan, hβc]
  have hcabs : ∀ σ : K →+* ℂ, ‖σ βc‖ ^ 2 = (Ideal.absNorm (𝔠 c : Ideal (𝓞 E)) : ℝ) ^ n := by
    intro σ
    have := hNabs (γ c) σ
    rw [← hγ, ← hβc, map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hpos.ne').1 this
  refine ⟨(N x)⁻¹ * (N y * βc), mul_ne_zero (inv_ne_zero (hN0 x hx)) (mul_ne_zero (hN0 y hy) hβc0),
    ?_, ?_⟩
  · have h1 := congrArg Φ hxy'
    rw [hΦmul, hΦmul, hΦspan, hΦspan, hΦc] at h1
    rw [← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span,
      ← Submodule.span_mul_span, ← h1, ← mul_assoc, Submodule.span_mul_span,
      Set.singleton_mul_singleton, inv_mul_cancel₀ (hN0 x hx), ← Submodule.one_eq_span, one_mul]
  · intro σ
    have h1 := congrArg (fun I => (Ideal.absNorm I : ℝ) ^ n) hxy'
    simp only [map_mul, Nat.cast_mul, mul_pow] at h1
    rw [← hNabs x σ, ← hNabs y σ, ← hcabs σ] at h1
    have h2 : ‖σ (N x)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hN0 x hx
    rw [map_mul, map_mul, map_inv₀, norm_mul, norm_mul, norm_inv, mul_pow, mul_pow, ← h1]
    field_simp

end GlobalTheory.Mem
