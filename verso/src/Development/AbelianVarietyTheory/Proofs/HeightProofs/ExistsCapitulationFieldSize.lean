import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeAdjoinKthRootStatement
open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.Mem
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

/- English proof (translation)
Introduce `m`. Proceed by induction on `m using Nat.strong_induction_on with`. Consider the case `_ m ih`. Introduce `i t hm hi`. Distinguish the cases in `htop : C i = ⊤`.

Conclude with `⟨i, le_rfl, hS i t _ (le_add_of_nonneg_right (Real.log_natCast_nonneg m)) hi, htop⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c, c ∉ C i := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `htop (eq_top_iff.2 fun x _ => h x)`.

Use `set D : Subgroup G := C i ⊔ Subgroup.zpowers c with hD`. Establish `hle : C i ≤ D` using `le_sup_left`. Establish `hcD : c ∈ D` using `(le_sup_right : Subgroup.zpowers c ≤ D) (Subgroup.mem_zpowers c)`. Establish `hmul` using `Subgroup.relIndex_mul_index hle`. Use `set k := (C i).relIndex D with hk`.

Establish `hm0 : m ≠ 0` using `hm ▸ Subgroup.index_ne_zero_of_finite`. Establish `hk0 : k ≠ 0`. Introduce `h`. Rewrite `hmul` using `[h, zero_mul, hm]`. Conclude with `hm0 hmul.symm`.

Establish `hk1 : k ≠ 1` using `fun h => hc (Subgroup.relIndex_eq_one.1 h hcD)`. Take `⟨j, hij, hj, hcj⟩` from `step i t c k hi (Nat.pos_of_ne_zero hk0) (Subgroup.pow_relIndex_mem _ hcD)`. Establish `hDj : D ≤ C j` using `sup_le (hC hij) ((Subgroup.zpowers_le_of_mem hcj))`. Establish `hD0 : D.index ≠ 0` using `Subgroup.index_ne_zero_of_finite`. Establish `hj0 : (C j).index ≠ 0` using `Subgroup.index_ne_zero_of_finite`.

Establish `hidx : (C j).index ≤ D.index` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) (Subgroup.index_dvd_of_le hDj)`. Establish `hlt : (C j).index < m`. Rewrite using `[← hm, ← hmul]`. Establish `: 2 ≤ k` using `by omega`. Use `Nat.pos_of_ne_zero hD0` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨l, hjl, hl, hl'⟩` from `ih _ hlt j _ rfl hj`. Use `⟨l, hij.trans hjl, hS l _ _ ?_ hl, hl'⟩` and prove the remaining obligations. Rewrite using `[add_assoc, ← Real.log_mul (by exact_mod_cast hk0) (by exact_mod_cast hj0)]`. Use `add_le_add le_rfl (Real.log_le_log (by positivity) ?_)` and prove the remaining obligations.

Rewrite using `[← hm, ← hmul]`. Conclude with `Nat.mul_le_mul_left k hidx` after adjusting the coercions.
-/
theorem exists_eq_top_of_root_step {G ι : Type} [CommGroup G] [Finite G] [Preorder ι] (C : ι → Subgroup G)
    (hC : Monotone C) (S : ι → ℝ → Prop) (hS : ∀ i s t, s ≤ t → S i s → S i t)
    (step : ∀ i t (c : G) (k : ℕ), S i t → 0 < k → c ^ k ∈ C i → ∃ j, i ≤ j ∧ S j (t + Real.log k) ∧ c ∈ C j) :
    ∀ (m : ℕ) (i : ι) (t : ℝ), (C i).index = m → S i t → ∃ j, i ≤ j ∧ S j (t + Real.log m) ∧ C j = ⊤ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro i t hm hi
    by_cases htop : C i = ⊤
    · exact ⟨i, le_rfl, hS i t _ (le_add_of_nonneg_right (Real.log_natCast_nonneg m)) hi, htop⟩
    obtain ⟨c, hc⟩ : ∃ c, c ∉ C i := by
      by_contra h
      push Not at h
      exact htop (eq_top_iff.2 fun x _ => h x)
    set D : Subgroup G := C i ⊔ Subgroup.zpowers c with hD
    have hle : C i ≤ D := le_sup_left
    have hcD : c ∈ D := (le_sup_right : Subgroup.zpowers c ≤ D) (Subgroup.mem_zpowers c)
    have hmul := Subgroup.relIndex_mul_index hle
    set k := (C i).relIndex D with hk
    have hm0 : m ≠ 0 := hm ▸ Subgroup.index_ne_zero_of_finite
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, zero_mul, hm] at hmul
      exact hm0 hmul.symm
    have hk1 : k ≠ 1 := fun h => hc (Subgroup.relIndex_eq_one.1 h hcD)
    obtain ⟨j, hij, hj, hcj⟩ := step i t c k hi (Nat.pos_of_ne_zero hk0) (Subgroup.pow_relIndex_mem _ hcD)
    have hDj : D ≤ C j := sup_le (hC hij) ((Subgroup.zpowers_le_of_mem hcj))
    have hD0 : D.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hj0 : (C j).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hidx : (C j).index ≤ D.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) (Subgroup.index_dvd_of_le hDj)
    have hlt : (C j).index < m := by
      rw [← hm, ← hmul]
      have : 2 ≤ k := by omega
      have := Nat.pos_of_ne_zero hD0
      nlinarith
    obtain ⟨l, hjl, hl, hl'⟩ := ih _ hlt j _ rfl hj
    refine ⟨l, hij.trans hjl, hS l _ _ ?_ hl, hl'⟩
    rw [add_assoc, ← Real.log_mul (by exact_mod_cast hk0) (by exact_mod_cast hj0)]
    refine add_le_add le_rfl (Real.log_le_log (by positivity) ?_)
    rw [← hm, ← hmul]
    exact_mod_cast Nat.mul_le_mul_left k hidx

/- English proof (translation)
Take `⟨h0, h1, h2⟩` from `h`. Conclude with `⟨h0, h1.trans ha, h2.trans hb⟩`.
-/
theorem Sz.weaken {F : IntermediateField ℚ ℂ} {a b a' b' : ℝ} (h : Sz F a b) (ha : a ≤ a') (hb : b ≤ b') :
    Sz F a' b' := by
  obtain ⟨h0, h1, h2⟩ := h
  exact ⟨h0, h1.trans ha, h2.trans hb⟩

section

variable {E : Type} [Field E] [NumberField E] (r : (E →+* ℂ) → ℕ) (n : ℕ)

noncomputable def typeNormMod (K : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) : Submodule (𝓞 K) K :=
  ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ

def GenTypeNorm (K : IntermediateField ℚ ℂ) (β : K) (𝔞 : Ideal (𝓞 E)) : Prop :=
  Submodule.span (𝓞 K) {β} = typeNormMod r K 𝔞 ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n

variable {r n}

/- English proof (translation)
Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K (hK τ)) 𝔞)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `x`.

Simplify using `only [Set.mem_ofPred_eq, Subtype.ext_iff]`. Both sides reduce to the same expression.
-/
theorem typeNormMod_eq (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (𝔞 : Ideal (𝓞 E)) :
    typeNormMod r K 𝔞 = ∏ τ : E →+* ℂ, extendIdealHom (τ.codRestrict K (hK τ)) 𝔞 ^ r τ := by
  refine Finset.prod_congr rfl fun τ _ => ?_
  congr 1
  refine Eq.trans ?_ (span_image_eq_coeSubmodule_map (τ.codRestrict K (hK τ)) 𝔞)
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Subtype.ext_iff]
  rfl

/- English proof (translation)
Simplify using `only [typeNormMod_eq K hK, map_mul, mul_pow, Finset.prod_mul_distrib]`.
-/
theorem typeNormMod_mul (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (I J : Ideal (𝓞 E)) : typeNormMod r K (I * J) = typeNormMod r K I * typeNormMod r K J := by
  simp only [typeNormMod_eq K hK, map_mul, mul_pow, Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `only [typeNormMod_eq K hK, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]`.
-/
theorem typeNormMod_pow (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    (I : Ideal (𝓞 E)) (k : ℕ) : typeNormMod r K (I ^ k) = typeNormMod r K I ^ k := by
  simp only [typeNormMod_eq K hK, map_pow, ← Finset.prod_pow, ← pow_mul, mul_comm]

/- English proof (translation)
Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[typeNormMod_mul K hK, ← h1.1, ← h2.1, Submodule.span_mul_span, Set.singleton_mul_singleton]`. Rewrite using `[map_mul, map_mul, norm_mul, mul_pow, h1.2, h2.2, Nat.cast_mul, mul_pow]`.
-/
theorem GenTypeNorm.mul {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I J : Ideal (𝓞 E)} {β γ : K} (h1 : GenTypeNorm r n K β I) (h2 : GenTypeNorm r n K γ J) :
    GenTypeNorm r n K (β * γ) (I * J) := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [typeNormMod_mul K hK, ← h1.1, ← h2.1, Submodule.span_mul_span, Set.singleton_mul_singleton]
  · rw [map_mul, map_mul, norm_mul, mul_pow, h1.2, h2.2, Nat.cast_mul, mul_pow]

/- English proof (translation)
Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[← Set.singleton_mul_singleton, ← Submodule.span_mul_span, h2.1, typeNormMod_mul K hK, ← h1.1, ← mul_assoc, Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hβ, ← Submodule.one_eq_span, one_mul]`. Establish `h3` using `h2.2 σ`. Rewrite `h3` using `[map_mul, Nat.cast_mul, mul_pow, ← h1.2 σ]`. Establish `h4 : ‖σ β‖ ≠ 0`.

Rewrite using `[norm_ne_zero_iff, map_ne_zero]`. Conclude with `hβ`. Rewrite using `[map_mul, map_inv₀, norm_mul, norm_inv, mul_pow, h3]`. Clear the denominators using the available nonvanishing facts.
-/
theorem GenTypeNorm.cancel {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I J : Ideal (𝓞 E)} {β γ : K} (hβ : β ≠ 0) (h1 : GenTypeNorm r n K β I) (h2 : GenTypeNorm r n K γ (I * J)) :
    GenTypeNorm r n K (β⁻¹ * γ) J := by
  refine ⟨?_, fun σ => ?_⟩
  · rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, h2.1, typeNormMod_mul K hK, ← h1.1, ← mul_assoc,
      Submodule.span_mul_span, Set.singleton_mul_singleton, inv_mul_cancel₀ hβ, ← Submodule.one_eq_span, one_mul]
  · have h3 := h2.2 σ
    rw [map_mul, Nat.cast_mul, mul_pow, ← h1.2 σ] at h3
    have h4 : ‖σ β‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hβ
    rw [map_mul, map_inv₀, norm_mul, norm_inv, mul_pow, h3]
    field_simp

/- English proof (translation)
Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β k hk hβ ?_ ?_).symm` and prove the remaining obligations. Rewrite using `[typeNormMod_eq K hK]`. Conclude with `fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _`. Rewrite using `[← typeNormMod_pow K hK, h.1]`.

Use `h.2 σ` as an intermediate fact. Rewrite `this` using `[map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul]`. Conclude with `(pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this`.
-/
theorem GenTypeNorm.root {K : IntermediateField ℚ ℂ} [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K)
    {I : Ideal (𝓞 E)} {β : K} {k : ℕ} (hk : 0 < k) (hβ : β ≠ 0) (h : GenTypeNorm r n K (β ^ k) (I ^ k)) :
    GenTypeNorm r n K β I := by
  refine ⟨?_, fun σ => ?_⟩
  · refine (GlobalTheory.submodule_eq_span_of_pow_eq_span_pow K _ β k hk hβ ?_ ?_).symm
    · rw [typeNormMod_eq K hK]
      exact fg_prod_pow _ _ _ fun τ => extendIdealHom_fg _ _
    · rw [← typeNormMod_pow K hK, h.1]
  · have := h.2 σ
    rw [map_pow, map_pow, norm_pow, Nat.cast_pow, ← pow_mul, ← pow_mul,
      mul_comm _ 2, mul_comm _ n, pow_mul, pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this

/- English proof (translation)
Use `⟨?_, fun σ => ?_⟩` and prove the remaining obligations. Simplify using `only [typeNormMod_eq K hK, extendIdealHom_span, span_singleton_prod_pow]`. Both sides reduce to the same expression. Use `norm_typeNorm_sq_eq E r n hr K hK (a : E) σ` as an intermediate fact. Rewrite using `[Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]`.

Rewrite `this` using `[← Algebra.coe_norm_int]`. Rewrite `this` using `[Rat.cast_intCast]`. Conclude with `this`.
-/
theorem genTypeNorm_span [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    (K : IntermediateField ℚ ℂ) [NumberField K] (hK : ∀ (τ : E →+* ℂ) x, τ x ∈ K) (a : 𝓞 E) :
    GenTypeNorm r n K (∏ τ : E →+* ℂ, (⟨τ (a : E), hK τ _⟩ : K) ^ r τ) (Ideal.span {a}) := by
  refine ⟨?_, fun σ => ?_⟩
  · simp only [typeNormMod_eq K hK, extendIdealHom_span, span_singleton_prod_pow]
    rfl
  · have := norm_typeNorm_sq_eq E r n hr K hK (a : E) σ
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, Int.cast_abs]
    rw [← Algebra.coe_norm_int] at this
    rw [Rat.cast_intCast] at this
    exact this

variable (r n)

def HasTypeNormGen (F : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) : Prop :=
  ∃ β : F, β ≠ 0 ∧ ∀ (K : IntermediateField ℚ ℂ) [NumberField K] (h : F ≤ K),
    GenTypeNorm r n K (IntermediateField.inclusion h β) 𝔞

variable {r n}

/- English proof (translation)
Take `⟨β, h0, hβ⟩` from `hI`. Conclude with `⟨IntermediateField.inclusion h β, (map_ne_zero _).2 h0, fun K _ hK => hβ K (h.trans hK)⟩`.
-/
theorem HasTypeNormGen.mono {F F' : IntermediateField ℚ ℂ} (h : F ≤ F') {I : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) : HasTypeNormGen r n F' I := by
  obtain ⟨β, h0, hβ⟩ := hI
  exact ⟨IntermediateField.inclusion h β, (map_ne_zero _).2 h0, fun K _ hK => hβ K (h.trans hK)⟩

/- English proof (translation)
Take `⟨β, h0, hβ⟩` from `hI`. Take `⟨γ, h1, hγ⟩` from `hJ`. Use `⟨β * γ, mul_ne_zero h0 h1, fun K _ hK => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `(hβ K hK).mul (fun τ x => hK (hF τ x)) (hγ K hK)`.
-/
theorem HasTypeNormGen.mul {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) (hJ : HasTypeNormGen r n F J) : HasTypeNormGen r n F (I * J) := by
  obtain ⟨β, h0, hβ⟩ := hI
  obtain ⟨γ, h1, hγ⟩ := hJ
  refine ⟨β * γ, mul_ne_zero h0 h1, fun K _ hK => ?_⟩
  rw [map_mul]
  exact (hβ K hK).mul (fun τ x => hK (hF τ x)) (hγ K hK)

/- English proof (translation)
Take `⟨β, h0, hβ⟩` from `hI`. Take `⟨γ, h1, hγ⟩` from `hJ`. Use `⟨β⁻¹ * γ, mul_ne_zero (inv_ne_zero h0) h1, fun K _ hK => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv₀]`. Conclude with `(hβ K hK).cancel (fun τ x => hK (hF τ x)) ((map_ne_zero _).2 h0) (hγ K hK)`.
-/
theorem HasTypeNormGen.cancel {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : Ideal (𝓞 E)}
    (hI : HasTypeNormGen r n F I) (hJ : HasTypeNormGen r n F (I * J)) : HasTypeNormGen r n F J := by
  obtain ⟨β, h0, hβ⟩ := hI
  obtain ⟨γ, h1, hγ⟩ := hJ
  refine ⟨β⁻¹ * γ, mul_ne_zero (inv_ne_zero h0) h1, fun K _ hK => ?_⟩
  rw [map_mul, map_inv₀]
  exact (hβ K hK).cancel (fun τ x => hK (hF τ x)) ((map_ne_zero _).2 h0) (hγ K hK)

/- English proof (translation)
Use `⟨∏ τ : E →+* ℂ, (⟨τ (a : E), hF τ _⟩ : F) ^ r τ, ?_, fun K _ hK => ?_⟩` and prove the remaining obligations. Use `Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_` and prove the remaining obligations. Introduce `h`. Establish `h' : τ (a : E) = 0` using `congrArg Subtype.val h`. Rewrite `h'` using `[map_eq_zero]`.

Conclude with `ha (by exact_mod_cast h')`. Rewrite using `[map_prod]`. Simplify using `only [map_pow]`. Conclude with `genTypeNorm_span hr K (fun τ x => hK (hF τ x)) a`.
-/
theorem hasTypeNormGen_span [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {a : 𝓞 E} (ha : a ≠ 0) :
    HasTypeNormGen r n F (Ideal.span {a}) := by
  refine ⟨∏ τ : E →+* ℂ, (⟨τ (a : E), hF τ _⟩ : F) ^ r τ, ?_, fun K _ hK => ?_⟩
  · refine Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ ?_
    intro h
    have h' : τ (a : E) = 0 := congrArg Subtype.val h
    rw [map_eq_zero] at h'
    exact ha (by exact_mod_cast h')
  · rw [map_prod]
    simp only [map_pow]
    exact genTypeNorm_span hr K (fun τ x => hK (hF τ x)) a

/- English proof (translation)
Take `⟨x, y, hx, hy, hxy⟩` from `ClassGroup.mk0_eq_mk0_iff.1 h`. Use `(hasTypeNormGen_span hr hF hx).cancel hF ?_` and prove the remaining obligations. Rewrite using `[hxy]`. Conclude with `(hasTypeNormGen_span hr hF hy).mul hF hJ`.
-/
theorem HasTypeNormGen.hasTypeNormGen_of_class_eq [IsCMField E] [IsGalois ℚ E]
    (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    {F : IntermediateField ℚ ℂ} (hF : ∀ (τ : E →+* ℂ) x, τ x ∈ F) {I J : (Ideal (𝓞 E))⁰}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) (hJ : HasTypeNormGen r n F (J : Ideal (𝓞 E))) :
    HasTypeNormGen r n F (I : Ideal (𝓞 E)) := by
  obtain ⟨x, y, hx, hy, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.1 h
  refine (hasTypeNormGen_span hr hF hx).cancel hF ?_
  rw [hxy]
  exact (hasTypeNormGen_span hr hF hy).mul hF hJ

def typeNormClasses [IsCMField E] [IsGalois ℚ E] (hr : ∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n)
    (F : {F : IntermediateField ℚ ℂ // ∀ (τ : E →+* ℂ) x, τ x ∈ F}) : Subgroup (ClassGroup (𝓞 E)) where
  carrier := {c | ∃ I : (Ideal (𝓞 E))⁰, ClassGroup.mk0 I = c ∧ HasTypeNormGen r n F.1 (I : Ideal (𝓞 E))}
  one_mem' := ⟨1, map_one _, by
    have := hasTypeNormGen_span hr F.2 (a := 1) one_ne_zero
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top] at this
    exact this⟩
  mul_mem' := by
    rintro _ _ ⟨I, rfl, hI⟩ ⟨J, rfl, hJ⟩
    exact ⟨I * J, map_mul _ _ _, hI.mul F.2 hJ⟩
  inv_mem' := by
    rintro _ ⟨I, rfl, hI⟩
    obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective (ClassGroup.mk0 I)⁻¹
    refine ⟨J, hJ, hI.cancel F.2 ?_⟩
    have h1 := hasTypeNormGen_span hr F.2 (a := 1) one_ne_zero
    rw [Ideal.span_singleton_one, ← Ideal.one_eq_top] at h1
    exact HasTypeNormGen.hasTypeNormGen_of_class_eq hr F.2 (I := I * J) (J := 1) (by rw [map_mul, hJ, mul_inv_cancel, map_one]) h1

end

/- English proof (translation)
Introduce `E _ _ _ _ r n hr F a b hF hE`. Establish `key` using `exists_eq_top_of_root_step (typeNormClasses hr) (fun i j hij c ⟨I, hI, h⟩ => ⟨I, hI, h.mono hij⟩) (fun i t => Sz i.1 (a + t) (b + t)) (fun i s t hst h => h.weaken (by linarith) (by linarith)) ?_ _ ⟨F, hE⟩ 0 rfl (by simpa using hF)`. Take `⟨j, hj, hS, htop⟩` from `key`. Establish `hle : Real.log ((typeNormClasses hr ⟨F, hE⟩).index) ≤ Real.log (classNumber E)`. Use `Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_` and prove the remaining obligations.

Use `Nat.le_of_dvd Nat.card_pos (typeNormClasses hr ⟨F, hE⟩).index_dvd_card` as an intermediate fact. Rewrite `this` using `[Nat.card_eq_fintype_card]`. Conclude with `this` after adjusting the coercions. Use `⟨j.1, hj, Sz.weaken hS (by linarith) (by linarith), fun K _ hK 𝔞 h𝔞 => ?_⟩` and prove the remaining obligations. Establish `: NumberField K` using `NumberField.mk`.

Set `I : (Ideal (𝓞 E))⁰` to `⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩`. Take `⟨J, hJ, hJ'⟩ : ClassGroup.mk0 I ∈ typeNormClasses hr j` from `htop ▸ Subgroup.mem_top _`. Take `⟨β, h0, hβ⟩` from `HasTypeNormGen.hasTypeNormGen_of_class_eq hr j.2 hJ.symm hJ'`. Conclude with `⟨IntermediateField.inclusion hK β, (map_ne_zero _).2 h0, hβ K hK⟩`. Introduce and unpack `⟨L, hL⟩ t c k hS hk ⟨J, hJ, hJ'⟩`.

Take `⟨I, rfl⟩` from `ClassGroup.mk0_surjective c`. Take `⟨y, hy0, hy⟩` from `HasTypeNormGen.hasTypeNormGen_of_class_eq hr hL (I := I ^ k) (by rw [map_pow, hJ]) hJ'`. Take `⟨z, hz⟩ : ∃ z : ℂ, z ^ k = (y : ℂ)` from `IsAlgClosed.exists_pow_nat_eq _ hk`. Establish `: FiniteDimensional ℚ L` using `hS.1`. Establish `: NumberField L` using `NumberField.mk`.

Establish `h1 : typeNormMod r L (I : Ideal (𝓞 E)) ^ k = Submodule.span (𝓞 L) {y}`. Rewrite using `[← typeNormMod_pow L hL]`. Conclude with `(hy L le_rfl).1.symm`. Establish `h2` using `GlobalTheory.T.field_size_adjoin_kth_root L _ _ k y _ z hS hk hy0 h1 hz`. Establish `hzm : z ∈ L ⊔ ℚ⟮z⟯` using `(le_sup_right : ℚ⟮z⟯ ≤ L ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)`.

Establish `hle : L ≤ L ⊔ ℚ⟮z⟯` using `le_sup_left`. Establish `hz0 : (⟨z, hzm⟩ : (L ⊔ ℚ⟮z⟯ : IntermediateField ℚ ℂ)) ≠ 0`. Introduce `h`. Establish `h' : z = 0` using `congrArg Subtype.val h`. Rewrite `hz` using `[h', zero_pow hk.ne']`.

Conclude with `hy0 (Subtype.ext hz.symm)`. Use `⟨⟨L ⊔ ℚ⟮z⟯, fun τ x => hle (hL τ x)⟩, hle, by simpa only [add_assoc] using h2, I, rfl, ⟨z, hzm⟩, hz0, fun K _ hK => ?_⟩` and prove the remaining obligations. Use `GenTypeNorm.root (fun τ x => hK (hle (hL τ x))) hk ((map_ne_zero _).2 hz0) ?_` and prove the remaining obligations. Establish `h3` using `hy K (hle.trans hK)`. Establish `h4 : IntermediateField.inclusion hK ⟨z, hzm⟩ ^ k = IntermediateField.inclusion (hle.trans hK) y` using `Subtype.ext hz`.

Rewrite using `[h4]`. Conclude with `h3`.
-/
theorem exists_sz_typeNorm_principal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (r : (E →+* ℂ) → ℕ) (n : ℕ), (∀ τ, r τ + r (ComplexEmbedding.conjugate τ) = n) → ∀ (F : IntermediateField ℚ ℂ) (a b : ℝ), Sz F a b → (∀ (τ : E →+* ℂ) x, τ x ∈ F) → ∃ F' : IntermediateField ℚ ℂ, F ≤ F' ∧ Sz F' (a + Real.log (classNumber E)) (b + Real.log (classNumber E)) ∧ ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K], F' ≤ K → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧ Submodule.span (𝓞 K) {β} = ∏ τ : E →+* ℂ, Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)} ^ r τ ∧ ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ n := by
  intro E _ _ _ _ r n hr F a b hF hE
  have key := exists_eq_top_of_root_step (typeNormClasses hr)
    (fun i j hij c ⟨I, hI, h⟩ => ⟨I, hI, h.mono hij⟩) (fun i t => Sz i.1 (a + t) (b + t))
    (fun i s t hst h => h.weaken (by linarith) (by linarith)) ?_ _ ⟨F, hE⟩ 0 rfl (by simpa using hF)
  · obtain ⟨j, hj, hS, htop⟩ := key
    have hle : Real.log ((typeNormClasses hr ⟨F, hE⟩).index) ≤ Real.log (classNumber E) := by
      refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) ?_
      have := Nat.le_of_dvd Nat.card_pos (typeNormClasses hr ⟨F, hE⟩).index_dvd_card
      rw [Nat.card_eq_fintype_card] at this
      exact_mod_cast this
    refine ⟨j.1, hj, Sz.weaken hS (by linarith) (by linarith), fun K _ hK 𝔞 h𝔞 => ?_⟩
    have : NumberField K := NumberField.mk
    let I : (Ideal (𝓞 E))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
    obtain ⟨J, hJ, hJ'⟩ : ClassGroup.mk0 I ∈ typeNormClasses hr j := htop ▸ Subgroup.mem_top _
    obtain ⟨β, h0, hβ⟩ := HasTypeNormGen.hasTypeNormGen_of_class_eq hr j.2 hJ.symm hJ'
    exact ⟨IntermediateField.inclusion hK β, (map_ne_zero _).2 h0, hβ K hK⟩
  · rintro ⟨L, hL⟩ t c k hS hk ⟨J, hJ, hJ'⟩
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    obtain ⟨y, hy0, hy⟩ := HasTypeNormGen.hasTypeNormGen_of_class_eq hr hL (I := I ^ k) (by rw [map_pow, hJ]) hJ'
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ k = (y : ℂ) := IsAlgClosed.exists_pow_nat_eq _ hk
    have : FiniteDimensional ℚ L := hS.1
    have : NumberField L := NumberField.mk
    have h1 : typeNormMod r L (I : Ideal (𝓞 E)) ^ k = Submodule.span (𝓞 L) {y} := by
      rw [← typeNormMod_pow L hL]
      exact (hy L le_rfl).1.symm
    have h2 := GlobalTheory.T.field_size_adjoin_kth_root L _ _ k y _ z hS hk hy0 h1 hz
    have hzm : z ∈ L ⊔ ℚ⟮z⟯ := (le_sup_right : ℚ⟮z⟯ ≤ L ⊔ ℚ⟮z⟯) (IntermediateField.mem_adjoin_simple_self ℚ z)
    have hle : L ≤ L ⊔ ℚ⟮z⟯ := le_sup_left
    have hz0 : (⟨z, hzm⟩ : (L ⊔ ℚ⟮z⟯ : IntermediateField ℚ ℂ)) ≠ 0 := by
      intro h
      have h' : z = 0 := congrArg Subtype.val h
      rw [h', zero_pow hk.ne'] at hz
      exact hy0 (Subtype.ext hz.symm)
    refine ⟨⟨L ⊔ ℚ⟮z⟯, fun τ x => hle (hL τ x)⟩, hle, by simpa only [add_assoc] using h2, I, rfl,
      ⟨z, hzm⟩, hz0, fun K _ hK => ?_⟩
    refine GenTypeNorm.root (fun τ x => hK (hle (hL τ x))) hk ((map_ne_zero _).2 hz0) ?_
    have h3 := hy K (hle.trans hK)
    have h4 : IntermediateField.inclusion hK ⟨z, hzm⟩ ^ k = IntermediateField.inclusion (hle.trans hK) y :=
      Subtype.ext hz
    rw [h4]
    exact h3

end GlobalTheory.FieldSize
