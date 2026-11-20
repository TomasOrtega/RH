import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop

open IsDiscreteValuationRing Pointwise

namespace GlobalTheory

section TorsionFree

variable {R V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup V]
  [Module R V] [Module.IsTorsionFree R V]

end TorsionFree

section Span

variable {R : Type*} (K : Type*) {V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

/- English proof (translation)
Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ x hx`. Rewrite `ht` using `[Submodule.span_eq]`. Conclude with `⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩`.
-/
theorem exists_ne_zero_smul_mem_of_mem_span_fractionField {M : Submodule R V} {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

/- English proof (translation)
Take `⟨s, rfl⟩` from `hN`. Establish `key : ∀ x : s, ∃ a : R, a ≠ 0 ∧ a • (x : V) ∈ M` using `fun x => exists_ne_zero_smul_mem_of_mem_span_fractionField K (h (Submodule.subset_span x.2))`. Use `choose c hc hc' using key`. Use `⟨∏ x, c x, Finset.prod_ne_zero_iff.mpr fun x _ => hc x, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.smul_span, Submodule.span_le]`.

Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨d, hd⟩ : c ⟨x, hx⟩ ∣ ∏ x, c x` from `Finset.dvd_prod_of_mem _ (Finset.mem_univ _)`. Express the relevant statement in the definitionally equal form `(∏ x, c x) • x ∈ M`. Rewrite using `[hd, mul_comm, mul_smul]`. Conclude with `M.smul_mem _ (hc' ⟨x, hx⟩)`.
-/
theorem exists_ne_zero_smul_le_of_le_span_fractionField {M N : Submodule R V} (hN : N.FG)
    (h : (N : Set V) ⊆ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • N ≤ M := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have key : ∀ x : s, ∃ a : R, a ≠ 0 ∧ a • (x : V) ∈ M := fun x =>
    exists_ne_zero_smul_mem_of_mem_span_fractionField K (h (Submodule.subset_span x.2))
  choose c hc hc' using key
  refine ⟨∏ x, c x, Finset.prod_ne_zero_iff.mpr fun x _ => hc x, ?_⟩
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, hd⟩ : c ⟨x, hx⟩ ∣ ∏ x, c x := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  change (∏ x, c x) • x ∈ M
  rw [hd, mul_comm, mul_smul]
  exact M.smul_mem _ (hc' ⟨x, hx⟩)

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_` and prove the remaining obligations. Take `⟨a, ha, hax⟩` from `exists_ne_zero_smul_mem_of_mem_span_fractionField K (h hx)`. Establish `ha' : algebraMap R K a ≠ 0` using `by simpa using ha`. Rewrite using `[← Submodule.smul_mem_iff _ ha', algebraMap_smul]`. Conclude with `Submodule.subset_span ⟨hax, W.smul_of_tower_mem a hx⟩`.
-/
theorem span_inf_restrictScalars_eq {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) = W := by
  refine le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_
  obtain ⟨a, ha, hax⟩ := exists_ne_zero_smul_mem_of_mem_span_fractionField K (h hx)
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha
  rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
  exact Submodule.subset_span ⟨hax, W.smul_of_tower_mem a hx⟩

variable {K}

omit [IsDomain R] [IsFractionRing R K] in

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists, Submodule.restrictScalars_mem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y, hy, rfl⟩, h⟩`. Conclude with `⟨y, ⟨hy, (W.smul_mem_iff hs).mp h⟩, rfl⟩`.

Introduce and unpack `⟨y, ⟨hy, h⟩, rfl⟩`. Conclude with `⟨⟨y, hy, rfl⟩, W.smul_mem s h⟩`.
-/
theorem fractionField_smul_inf_restrictScalars {s : K} (hs : s ≠ 0) (Θ : Submodule R V) (W : Submodule K V) :
    s • Θ ⊓ W.restrictScalars R = s • (Θ ⊓ W.restrictScalars R) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    exact ⟨y, ⟨hy, (W.smul_mem_iff hs).mp h⟩, rfl⟩
  · rintro ⟨y, ⟨hy, h⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, W.smul_mem s h⟩

variable [IsPrincipalIdealRing R]

/- English proof (translation)
Apply `Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars R) W.injective_subtype` to reduce the goal to its premises. Conclude with `hM.of_le (Submodule.map_comap_le _ _)`. Use `span_eq_top := by`. Use `eq_top_iff.mpr fun x _ => ?_` and prove the remaining obligations. Take `⟨a, ha, hax⟩` from `exists_ne_zero_smul_mem_of_mem_span_fractionField K (h x.2)`.

Establish `ha' : algebraMap R K a ≠ 0` using `by simpa using ha`. Rewrite using `[← Submodule.smul_mem_iff _ ha', algebraMap_smul]`. Conclude with `Submodule.subset_span hax`.
-/
theorem isLattice_comap_subtype {M : Submodule R V} (hM : M.FG) {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.IsLattice K (M.comap (W.subtype.restrictScalars R)) where
  fg := by
    apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars R) W.injective_subtype
    exact hM.of_le (Submodule.map_comap_le _ _)
  span_eq_top := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, ha, hax⟩ := exists_ne_zero_smul_mem_of_mem_span_fractionField K (h x.2)
    have ha' : algebraMap R K a ≠ 0 := by simpa using ha
    rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
    exact Submodule.subset_span hax

/- English proof (translation)
Use `isLattice_comap_subtype hM h` as an intermediate fact. Establish `e` using `Submodule.equivMapOfInjective (W.subtype.restrictScalars R) W.injective_subtype (M.comap (W.subtype.restrictScalars R))`. Establish `hr : LinearMap.range (W.subtype.restrictScalars R) = W.restrictScalars R`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Rewrite `e` using `[Submodule.map_comap_eq, hr, inf_comm]`. Rewrite using `[← e.finrank_eq, Module.finrank, Module.finrank, Submodule.IsLattice.rank' K]`.
-/
theorem finrank_inf_restrictScalars_of_le_span {M : Submodule R V} (hM : M.FG)
    {W : Submodule K V} (h : W ≤ Submodule.span K (M : Set V)) :
    Module.finrank R ↥(M ⊓ W.restrictScalars R) = Module.finrank K W := by
  have := isLattice_comap_subtype hM h
  have e := Submodule.equivMapOfInjective (W.subtype.restrictScalars R) W.injective_subtype
    (M.comap (W.subtype.restrictScalars R))
  have hr : LinearMap.range (W.subtype.restrictScalars R) = W.restrictScalars R := by
    ext x
    simp
  rw [Submodule.map_comap_eq, hr, inf_comm] at e
  rw [← e.finrank_eq, Module.finrank, Module.finrank, Submodule.IsLattice.rank' K]

end Span

section FractionField

variable {R K V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
  [IsScalarTower R K V]

/- English proof (translation)
Rewrite using `[Units.smul_def, Algebra.smul_def, map_mul, Ring.ordFrac_of_isUnit u.isUnit, one_mul, map_zpow₀, Ring.ordFrac_irreducible hϖ, WithZero.log_zpow, WithZero.log_exp]`. Simplify using the standard rewrite rules.
-/
theorem log_ordFrac_units_smul_zpow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ) :
    WithZero.log (Ring.ordFrac R (u • algebraMap R K ϖ ^ n)) = n := by
  rw [Units.smul_def, Algebra.smul_def, map_mul, Ring.ordFrac_of_isUnit u.isUnit, one_mul,
    map_zpow₀, Ring.ordFrac_irreducible hϖ, WithZero.log_zpow, WithZero.log_exp]
  simp

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Take `⟨n, u, rfl⟩` from `eq_unit_mul_pow_irreducible ha hϖ`. Use `log_ordFrac_units_smul_zpow (K := K) hϖ u n` as an intermediate fact. Rewrite `this` using `[Units.smul_def, Algebra.smul_def, zpow_natCast, ← map_pow, ← map_mul]`. Rewrite using `[this, addVal_def' u hϖ]`.

Simplify using the standard rewrite rules.
-/
theorem log_ordFrac_algebraMap {a : R} (ha : a ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R K a)) = (addVal R a).toNat := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have := log_ordFrac_units_smul_zpow (K := K) hϖ u n
  rw [Units.smul_def, Algebra.smul_def, zpow_natCast, ← map_pow, ← map_mul] at this
  rw [this, addVal_def' u hϖ]
  simp

variable (K) in

/- English proof (translation)
Use `Module.IsTorsionFree.trans_faithfulSMul R K V` as an intermediate fact. Take `⟨a, ha, hab⟩` from `exists_ne_zero_smul_le_of_le_span_fractionField K hA h`. Conclude with `ne_top_of_le_ne_top (relLength_smul_self_ne_top hA ha) (relLength_anti_right A hab)`.
-/
theorem relLength_ne_top_of_subset_span {A B : Submodule R V} (hA : A.FG)
    (h : (A : Set V) ⊆ Submodule.span K (B : Set V)) : relLength A B ≠ ⊤ := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  obtain ⟨a, ha, hab⟩ := exists_ne_zero_smul_le_of_le_span_fractionField K hA h
  exact ne_top_of_le_ne_top (relLength_smul_self_ne_top hA ha) (relLength_anti_right A hab)

variable (K) in

/- English proof (translation)
Introduce `x hx`. Take `⟨ϖ, hϖ⟩` from `exists_irreducible R`. Rewrite `h` using `[relLength_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]`. Take `⟨-, h⟩` from `h`. Take `⟨n, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd (M := Submodule.span R {(Submodule.Quotient.mk ⟨x, hx⟩ : A ⧸ B.submoduleOf A)}) ϖ ⟨_, Submodule.mem_span_singleton_self _⟩`.

Take `⟨y, hy'⟩` from `y`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.mp hy'`. Establish `h₁ : (ϖ ^ n * (ϖ * c - 1)) • (Submodule.Quotient.mk ⟨x, hx⟩ : A ⧸ B.submoduleOf A) = 0`. Use `congrArg Subtype.val hy` as an intermediate fact. Simplify using `only [Submodule.coe_smul, smul_smul] at this`.

Rewrite using `[mul_sub, mul_one, sub_smul, ← mul_assoc, ← pow_succ, sub_eq_zero]`. Conclude with `this`. Rewrite `h₁` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `h₂ : ϖ ^ n * (ϖ * c - 1) ≠ 0` using `mul_ne_zero (pow_ne_zero n hϖ.ne_zero) fun h₀ => hϖ.not_isUnit (IsUnit.of_mul_eq_one c (sub_eq_zero.mp h₀))`. Establish `h₃ : algebraMap R K (ϖ ^ n * (ϖ * c - 1)) ≠ 0`.

Rewrite using `[map_ne_zero_iff _ (IsFractionRing.injective R K)]` and apply the resulting hypothesis. Rewrite using `[SetLike.mem_coe, ← Submodule.smul_mem_iff _ h₃, algebraMap_smul]`. Conclude with `Submodule.subset_span h₁`.
-/
theorem subset_span_of_relLength_ne_top {A B : Submodule R V} (h : relLength A B ≠ ⊤) :
    (A : Set V) ⊆ Submodule.span K (B : Set V) := by
  intro x hx
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [relLength_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
    (M := Submodule.span R {(Submodule.Quotient.mk ⟨x, hx⟩ : A ⧸ B.submoduleOf A)}) ϖ
    ⟨_, Submodule.mem_span_singleton_self _⟩
  obtain ⟨y, hy'⟩ := y
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
  have h₁ : (ϖ ^ n * (ϖ * c - 1)) •
      (Submodule.Quotient.mk ⟨x, hx⟩ : A ⧸ B.submoduleOf A) = 0 := by
    have := congrArg Subtype.val hy
    simp only [Submodule.coe_smul, smul_smul] at this
    rw [mul_sub, mul_one, sub_smul, ← mul_assoc, ← pow_succ, sub_eq_zero]
    exact this
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h₁
  have h₂ : ϖ ^ n * (ϖ * c - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero n hϖ.ne_zero) fun h₀ =>
      hϖ.not_isUnit (IsUnit.of_mul_eq_one c (sub_eq_zero.mp h₀))
  have h₃ : algebraMap R K (ϖ ^ n * (ϖ * c - 1)) ≠ 0 := by
    rwa [map_ne_zero_iff _ (IsFractionRing.injective R K)]
  rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ h₃, algebraMap_smul]
  exact Submodule.subset_span h₁

variable (K) in

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => le_antisymm (Submodule.span_le.mpr (subset_span_of_relLength_ne_top K h.1)) (Submodule.span_le.mpr (subset_span_of_relLength_ne_top K h.2)), fun h => ⟨relLength_ne_top_of_subset_span K hA (h ▸ Submodule.subset_span), relLength_ne_top_of_subset_span K hB (h ▸ Submodule.s …`.
-/
theorem lengthCommensurable_iff_span_eq {A B : Submodule R V} (hA : A.FG) (hB : B.FG) :
    LengthCommensurable A B ↔
      Submodule.span K (A : Set V) = Submodule.span K (B : Set V) :=
  ⟨fun h => le_antisymm (Submodule.span_le.mpr (subset_span_of_relLength_ne_top K h.1))
      (Submodule.span_le.mpr (subset_span_of_relLength_ne_top K h.2)),
    fun h => ⟨relLength_ne_top_of_subset_span K hA (h ▸ Submodule.subset_span),
      relLength_ne_top_of_subset_span K hB (h ▸ Submodule.subset_span)⟩⟩

/- English proof (translation)
Rewrite using `[lengthCommensurable_iff_span_eq K (hM.of_le inf_le_left) (hΘ.of_le inf_le_left), span_inf_restrictScalars_eq K hW, span_inf_restrictScalars_eq K hW']`.
-/
theorem lengthCommensurable_inf_restrictScalars_of_le_span {M Θ : Submodule R V} (hM : M.FG)
    (hΘ : Θ.FG) {W : Submodule K V} (hW : W ≤ Submodule.span K (M : Set V))
    (hW' : W ≤ Submodule.span K (Θ : Set V)) :
    LengthCommensurable (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) := by
  rw [lengthCommensurable_iff_span_eq K (hM.of_le inf_le_left) (hΘ.of_le inf_le_left),
    span_inf_restrictScalars_eq K hW, span_inf_restrictScalars_eq K hW']

/- English proof (translation)
Use `Module.IsTorsionFree.trans_faithfulSMul R K V` as an intermediate fact. Establish `key : ∀ {a : R}, a ≠ 0 → LengthCommensurable B (algebraMap R K a • B) ∧ signedLength B (algebraMap R K a • B) = WithZero.log (Ring.ordFrac R (algebraMap R K a)) * Module.finrank R B`. Introduce `a ha`. Establish `e : algebraMap R K a • B = a • B`. Use extensionality with `x`.

Simplify using `only [Submodule.mem_smul_pointwise_iff_exists, algebraMap_smul]`. Rewrite using `[e, log_ordFrac_algebraMap ha]`. Conclude with `⟨lengthCommensurable_smul_self hB ha, signedLength_smul_self hB ha⟩`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := R) s`. Establish `hb₀ : b ≠ 0` using `nonZeroDivisors.ne_zero hb`.

Establish `hb₁ : algebraMap R K b ≠ 0` using `by simpa using hb₀`. Establish `ha₁ : algebraMap R K a ≠ 0` using `fun h => hs (by rw [h, zero_div])`. Establish `ha₀ : a ≠ 0` using `by simpa using ha₁`. Take `⟨ca, sa⟩` from `key ha₀`. Take `⟨cb, sb⟩` from `key hb₀`.

Establish `hreg : IsSMulRegular V (algebraMap R K a / algebraMap R K b)` using `IsSMulRegular.of_ne_zero hs`. Establish `e : (algebraMap R K a / algebraMap R K b) • algebraMap R K b • B = algebraMap R K a • B`. Rewrite using `[smul_smul, div_mul_cancel₀ _ hb₁]`. Establish `cb'` using `(lengthCommensurable_smul_smul_iff hreg).mpr cb`. Establish `sb'` using `cb.signedLength_smul_smul hreg`.

Rewrite `cb'`, `sb'` using `[e]`. Use `⟨ca.trans cb'.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[ca.signedLength_eq_add cb'.symm, cb'.signedLength_swap, sb', sa, sb, map_div₀, WithZero.log_div ((map_ne_zero _).mpr ha₁) ((map_ne_zero _).mpr hb₁)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem signedLength_smul_self_fractionField {B : Submodule R V} (hB : B.FG) {s : K} (hs : s ≠ 0) :
    LengthCommensurable B (s • B) ∧
      signedLength B (s • B) = WithZero.log (Ring.ordFrac R s) * Module.finrank R B := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  have key : ∀ {a : R}, a ≠ 0 → LengthCommensurable B (algebraMap R K a • B) ∧
      signedLength B (algebraMap R K a • B) =
        WithZero.log (Ring.ordFrac R (algebraMap R K a)) * Module.finrank R B := by
    intro a ha
    have e : algebraMap R K a • B = a • B := by
      ext x
      simp only [Submodule.mem_smul_pointwise_iff_exists, algebraMap_smul]
    rw [e, log_ordFrac_algebraMap ha]
    exact ⟨lengthCommensurable_smul_self hB ha, signedLength_smul_self hB ha⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
  have hb₀ : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb₁ : algebraMap R K b ≠ 0 := by simpa using hb₀
  have ha₁ : algebraMap R K a ≠ 0 := fun h => hs (by rw [h, zero_div])
  have ha₀ : a ≠ 0 := by simpa using ha₁
  obtain ⟨ca, sa⟩ := key ha₀
  obtain ⟨cb, sb⟩ := key hb₀
  have hreg : IsSMulRegular V (algebraMap R K a / algebraMap R K b) := IsSMulRegular.of_ne_zero hs
  have e : (algebraMap R K a / algebraMap R K b) • algebraMap R K b • B = algebraMap R K a • B := by
    rw [smul_smul, div_mul_cancel₀ _ hb₁]
  have cb' := (lengthCommensurable_smul_smul_iff hreg).mpr cb
  have sb' := cb.signedLength_smul_smul hreg
  rw [e] at cb' sb'
  refine ⟨ca.trans cb'.symm, ?_⟩
  rw [ca.signedLength_eq_add cb'.symm, cb'.signedLength_swap, sb', sa, sb, map_div₀,
    WithZero.log_div ((map_ne_zero _).mpr ha₁) ((map_ne_zero _).mpr hb₁)]
  ring

/- English proof (translation)
Take `⟨c, e⟩` from `signedLength_smul_self_fractionField hB hs`. Conclude with `⟨h.trans c, by rw [h.signedLength_eq_add c, e]⟩`.
-/
theorem LengthCommensurable.signedLength_smul_right {A B : Submodule R V}
    (h : LengthCommensurable A B) (hB : B.FG) {s : K} (hs : s ≠ 0) :
    LengthCommensurable A (s • B) ∧
      signedLength A (s • B) =
        signedLength A B + WithZero.log (Ring.ordFrac R s) * Module.finrank R B := by
  obtain ⟨c, e⟩ := signedLength_smul_self_fractionField hB hs
  exact ⟨h.trans c, by rw [h.signedLength_eq_add c, e]⟩

/- English proof (translation)
Establish `h` using `lengthCommensurable_inf_restrictScalars_of_le_span hM hΘ hW hW'`. Rewrite using `[fractionField_smul_inf_restrictScalars hs, ← finrank_inf_restrictScalars_of_le_span hΘ hW']`. Conclude with `⟨h, h.signedLength_smul_right (hΘ.of_le inf_le_left) hs⟩`.
-/
theorem signedLength_inf_smul_inf_of_le_span {M Θ : Submodule R V} (hM : M.FG) (hΘ : Θ.FG)
    {W : Submodule K V} (hW : W ≤ Submodule.span K (M : Set V))
    (hW' : W ≤ Submodule.span K (Θ : Set V)) {s : K} (hs : s ≠ 0) :
    LengthCommensurable (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) ∧
      LengthCommensurable (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) ∧
      signedLength (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) =
        signedLength (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) +
          WithZero.log (Ring.ordFrac R s) * Module.finrank K W := by
  have h := lengthCommensurable_inf_restrictScalars_of_le_span hM hΘ hW hW'
  rw [fractionField_smul_inf_restrictScalars hs, ← finrank_inf_restrictScalars_of_le_span hΘ hW']
  exact ⟨h, h.signedLength_smul_right (hΘ.of_le inf_le_left) hs⟩

/- English proof (translation)
The claim follows from `signedLength_inf_smul_inf_of_le_span Submodule.IsLattice.fg Submodule.IsLattice.fg (by rw [Submodule.IsLattice.span_eq_top]; exact le_top) (by rw [Submodule.IsLattice.span_eq_top]; exact le_top) hs`.
-/
theorem signedLength_inf_smul_inf (M Θ : Submodule R V) [Submodule.IsLattice K M]
    [Submodule.IsLattice K Θ] (W : Submodule K V) {s : K} (hs : s ≠ 0) :
    LengthCommensurable (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) ∧
      LengthCommensurable (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) ∧
      signedLength (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) =
        signedLength (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) +
          WithZero.log (Ring.ordFrac R s) * Module.finrank K W :=
  signedLength_inf_smul_inf_of_le_span Submodule.IsLattice.fg Submodule.IsLattice.fg
    (by rw [Submodule.IsLattice.span_eq_top]; exact le_top)
    (by rw [Submodule.IsLattice.span_eq_top]; exact le_top) hs

/- English proof (translation)
Establish `hs : u • algebraMap R K ϖ ^ n ≠ 0`. Rewrite using `[ne_eq, smul_eq_zero_iff_eq]`. Conclude with `zpow_ne_zero n (by simpa using hϖ.ne_zero)`. Rewrite using `[(signedLength_inf_smul_inf M Θ W hs).2.2, log_ordFrac_units_smul_zpow hϖ]`.
-/
theorem signedLength_inf_smul_inf_zpow {ϖ : R} (hϖ : Irreducible ϖ) (M Θ : Submodule R V)
    [Submodule.IsLattice K M] [Submodule.IsLattice K Θ] (W : Submodule K V) (u : Rˣ) (n : ℤ) :
    signedLength (M ⊓ W.restrictScalars R)
        ((u • algebraMap R K ϖ ^ n) • Θ ⊓ W.restrictScalars R) =
      signedLength (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) +
        n * Module.finrank K W := by
  have hs : u • algebraMap R K ϖ ^ n ≠ 0 := by
    rw [ne_eq, smul_eq_zero_iff_eq]
    exact zpow_ne_zero n (by simpa using hϖ.ne_zero)
  rw [(signedLength_inf_smul_inf M Θ W hs).2.2, log_ordFrac_units_smul_zpow hϖ]

end FractionField

/- English proof (translation)
Establish `: Submodule.IsLattice ℚ_[p] (Submodule.span ℤ_[p] {(1 : ℚ_[p])})` using `⟨Submodule.fg_span_singleton _, by rw [Submodule.span_span_of_tower]; simp⟩`. Establish `h` using `signedLength_inf_smul_inf_zpow (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)) (Submodule.span ℤ_[p] {(1 : ℚ_[p])}) (Submodule.span ℤ_[p] {(1 : ℚ_[p])}) ⊤ 1 (-1)`. Simplify using `using h`.
-/
example (p : ℕ) [Fact p.Prime] :
    signedLength (Submodule.span ℤ_[p] {(1 : ℚ_[p])})
      (((1 : ℤ_[p]ˣ) • algebraMap ℤ_[p] ℚ_[p] p ^ (-1 : ℤ)) • Submodule.span ℤ_[p] {(1 : ℚ_[p])}) =
      -1 := by
  have : Submodule.IsLattice ℚ_[p] (Submodule.span ℤ_[p] {(1 : ℚ_[p])}) :=
    ⟨Submodule.fg_span_singleton _, by rw [Submodule.span_span_of_tower]; simp⟩
  have h := signedLength_inf_smul_inf_zpow (K := ℚ_[p]) (PadicInt.irreducible_p (p := p))
    (Submodule.span ℤ_[p] {(1 : ℚ_[p])}) (Submodule.span ℤ_[p] {(1 : ℚ_[p])}) ⊤ 1 (-1)
  simpa using h

end GlobalTheory
