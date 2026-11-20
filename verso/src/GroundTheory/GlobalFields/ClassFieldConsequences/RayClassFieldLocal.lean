import Mathlib
import GroundTheory.GlobalFields.GlobalReciprocity.Frobenius
import GroundTheory.GlobalFields.GlobalReciprocity.LocalSurjective
import GroundTheory.GlobalFields.KummerTheory.Splitting

namespace GroundTheory.Global

open IsDedekindDomain NumberField ValuativeRel GroundTheory.LocalField SemiLocal WithZero
open scoped Pointwise

noncomputable section

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [CharZero k] {M : Type*} [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [Algebra k M] [ValuativeExtension k M] [FiniteDimensional k M]
  [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)]

omit [CharZero k] [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [ValuativeExtension k M] [FiniteDimensional k M] in
variable (k) in

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[k]`. Establish `h0 : (ϖ : k) ≠ 0` using `by exact_mod_cast hϖ.ne_zero`. Conclude with `⟨Units.mk0 _ h0, ord_uniformizer hϖ⟩`.
-/
theorem exists_ord_eq_one_units : ∃ π : kˣ, ord (π : k) = 1 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have h0 : (ϖ : k) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, ord_uniformizer hϖ⟩

omit [CharZero k] [IsGalois k M] [IsMulCommutative (M ≃ₐ[k] M)] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M] [ValuativeExtension k M] [FiniteDimensional k M] in

/- English proof (translation)
Rewrite using `[Units.val_zpow_eq_zpow_val, ord_zpow π.ne_zero, hπ, mul_one]`.
-/
theorem ord_zpow_units {π : kˣ} (hπ : ord (π : k) = 1) (n : ℤ) : ord ((π ^ n : kˣ) : k) = n := by
  rw [Units.val_zpow_eq_zpow_val, ord_zpow π.ne_zero, hπ, mul_one]

omit [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [ValuativeExtension k M] in

/- English proof (translation)
Establish `e : kˣ ⧸ (normUnits k M).range ≃* (M ≃ₐ[k] M)` using `(QuotientGroup.quotientMulEquivOfEq ker_normResidueSymbol.symm).trans (QuotientGroup.quotientKerEquivOfSurjective _ normResidueSymbol_surjective)`. Rewrite using `[Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]`.
-/
theorem natCard_quotient_range_normUnits :
    Nat.card (kˣ ⧸ (normUnits k M).range) = Module.finrank k M := by
  have e : kˣ ⧸ (normUnits k M).range ≃* (M ≃ₐ[k] M) :=
    (QuotientGroup.quotientMulEquivOfEq ker_normResidueSymbol.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ normResidueSymbol_surjective)
  rw [Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]

/- English proof (translation)
Use `set N := (normUnits k M).range`. Use `set f := residueDegree k M`. Take `⟨π, hπ⟩` from `exists_ord_eq_one_units k`. Take `⟨ϖ, hϖ⟩` from `exists_ord_eq_one_units M`. Establish `hπf : π ^ (f : ℤ) ∈ N`.

Establish `hu : (π ^ (f : ℤ))⁻¹ * normUnits k M ϖ ∈ unitFiltrationUnits k 0`. Rewrite using `[← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _), coe_normUnits, ord_norm, hϖ, ← zpow_neg, ord_zpow_units hπ]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `N.mul_mem (h hu) (N.inv_mem (⟨ϖ, rfl⟩ : normUnits k M ϖ ∈ N))`. Rewrite `h2` using `[mul_inv_cancel_right, inv_mem_iff]`. Then use the resulting hypothesis.

Establish `htop : Subgroup.zpowers (π : kˣ ⧸ N) = ⊤`. Use `eq_top_iff.2 fun c _ ↦ ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective c`. Use `⟨ord (x : k), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((π : kˣ ⧸ N)) ^ ord (x : k) = (x : kˣ ⧸ N)`.

Rewrite using `[← QuotientGroup.mk_zpow, QuotientGroup.eq]`. Apply `h` to reduce the goal to its premises. Rewrite using `[← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _), ← zpow_neg, ord_zpow_units hπ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hf0 : 0 < f`.

Establish `h1` using `ramificationIndex_mul_residueDegree k M`. Establish `h2 : 0 < Module.finrank k M` using `Module.finrank_pos`. Rewrite `h2` using `[← h1]`. Conclude with `Nat.pos_of_mul_pos_left h2`. Establish `hle : Module.finrank k M ≤ f`.

Rewrite using `[← natCard_quotient_range_normUnits, ← Subgroup.card_top (G := kˣ ⧸ N), ← htop, Nat.card_zpowers]`. Use `orderOf_le_of_pow_eq_one hf0 ?_` and prove the remaining obligations. Rewrite using `[← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]`. Conclude with `hπf` after adjusting the coercions. Establish `h1 : ramificationIndex k M * f = Module.finrank k M` using `ramificationIndex_mul_residueDegree k M`.

Establish `he : ramificationIndex k M ≤ 1`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `: 2 * f ≤ ramificationIndex k M * f` using `Nat.mul_le_mul_right f hc`. Use linear arithmetic over natural numbers and integers.

Establish `he0 : ramificationIndex k M ≠ 0`. Introduce `h0`. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `(Module.finrank_pos (R := k) (M := M)).ne' h1.symm`. Use linear arithmetic over natural numbers and integers.
-/
theorem ramificationIndex_eq_one_of_units_le
    (h : unitFiltrationUnits k 0 ≤ (normUnits k M).range) : ramificationIndex k M = 1 := by
  set N := (normUnits k M).range
  set f := residueDegree k M
  obtain ⟨π, hπ⟩ := exists_ord_eq_one_units k
  obtain ⟨ϖ, hϖ⟩ := exists_ord_eq_one_units M

  have hπf : π ^ (f : ℤ) ∈ N := by
    have hu : (π ^ (f : ℤ))⁻¹ * normUnits k M ϖ ∈ unitFiltrationUnits k 0 := by
      rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _),
        coe_normUnits, ord_norm, hϖ, ← zpow_neg, ord_zpow_units hπ]
      ring
    have h2 := N.mul_mem (h hu) (N.inv_mem (⟨ϖ, rfl⟩ : normUnits k M ϖ ∈ N))
    rwa [mul_inv_cancel_right, inv_mem_iff] at h2

  have htop : Subgroup.zpowers (π : kˣ ⧸ N) = ⊤ := by
    refine eq_top_iff.2 fun c _ ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨ord (x : k), ?_⟩
    change ((π : kˣ ⧸ N)) ^ ord (x : k) = (x : kˣ ⧸ N)
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
    apply h
    rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _),
      ← zpow_neg, ord_zpow_units hπ]
    ring
  have hf0 : 0 < f := by
    have h1 := ramificationIndex_mul_residueDegree k M
    have h2 : 0 < Module.finrank k M := Module.finrank_pos
    rw [← h1] at h2
    exact Nat.pos_of_mul_pos_left h2
  have hle : Module.finrank k M ≤ f := by
    rw [← natCard_quotient_range_normUnits, ← Subgroup.card_top (G := kˣ ⧸ N), ← htop,
      Nat.card_zpowers]
    refine orderOf_le_of_pow_eq_one hf0 ?_
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact_mod_cast hπf
  have h1 : ramificationIndex k M * f = Module.finrank k M := ramificationIndex_mul_residueDegree k M
  have he : ramificationIndex k M ≤ 1 := by
    by_contra hc
    push Not at hc
    have : 2 * f ≤ ramificationIndex k M * f := Nat.mul_le_mul_right f hc
    omega
  have he0 : ramificationIndex k M ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact (Module.finrank_pos (R := k) (M := M)).ne' h1.symm
  omega

end Local

section Completion

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
The claim follows from `ValuativeRel.isEquiv _ _`.
-/
theorem isEquiv_valuation_valued :
    (ValuativeRel.valuation (v.adicCompletion K)).IsEquiv
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) :=
  ValuativeRel.isEquiv _ _

variable {v} in

/- English proof (translation)
Rewrite using `[mem_unitFiltrationUnits_zero_iff]`. Conclude with `(isEquiv_valuation_valued v).eq_one_iff_eq_one`.
-/
theorem mem_unitFiltrationUnits_zero_iff_valued {x : (v.adicCompletion K)ˣ} :
    x ∈ unitFiltrationUnits (v.adicCompletion K) 0 ↔ Valued.v (x : v.adicCompletion K) = 1 := by
  rw [mem_unitFiltrationUnits_zero_iff]
  exact (isEquiv_valuation_valued v).eq_one_iff_eq_one

/- English proof (translation)
Establish `he` using `isEquiv_valuation_valued v`. Establish `hne : Valued.v (ϖ : v.adicCompletion K) ≠ 0`. Rewrite using `[Ne, Valuation.zero_iff]`. Conclude with `hϖ.ne_zero` after adjusting the coercions. Establish `hlt : Valued.v (ϖ : v.adicCompletion K) < 1` using `he.lt_one_iff_lt_one.1 (valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ))`.

Take `⟨y, hy⟩` from `valued_adicCompletion_surjective (K := K) v (exp (-1 : ℤ))`. Establish `hexp : exp (-1 : ℤ) < 1`. Rewrite using `[← exp_zero, exp_lt_exp]`. Evaluate the numerical expressions. Establish `hy1 : valuation (v.adicCompletion K) y < 1` using `he.lt_one_iff_lt_one.2 (hy ▸ hexp)`.

Establish `hymem : (⟨y, hy1.le⟩ : 𝒪[v.adicCompletion K]) ∈ 𝓂[v.adicCompletion K]`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, (Valuation.integer.integers (valuation (v.adicCompletion K))).isUnit_iff_valuation_eq_one]`. Conclude with `hy1.ne`. Establish `hyϖ : valuation (v.adicCompletion K) y ≤ valuation (v.adicCompletion K) ϖ`. Establish `hs` using `hϖ.maximalIdeal_eq_setOfPred_le_v_coe (v := valuation (v.adicCompletion K))`.

Establish `h2 : (⟨y, hy1.le⟩ : 𝒪[v.adicCompletion K]) ∈ (𝓂[v.adicCompletion K] : Set _)` using `hymem`. Rewrite `h2` using `[hs]`. Conclude with `h2`. Establish `hyϖ'` using `(he y ϖ).1 hyϖ`. Rewrite `hyϖ'` using `[hy]`.

Rewrite `hyϖ'`, `hlt`, the goal using `[← exp_log hne]`. Rewrite `hlt` using `[← exp_zero, exp_lt_exp]`. Rewrite `hyϖ'` using `[exp_le_exp]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem valued_irreducible_valuationInteger {ϖ : 𝒪[v.adicCompletion K]} (hϖ : Irreducible ϖ) :
    Valued.v (ϖ : v.adicCompletion K) = exp (-1 : ℤ) := by
  have he := isEquiv_valuation_valued v
  have hne : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast hϖ.ne_zero
  have hlt : Valued.v (ϖ : v.adicCompletion K) < 1 :=
    he.lt_one_iff_lt_one.1 (valuation_lt_one_of_mem_maximalIdeal (uniformizer_mem_maximalIdeal hϖ))
  obtain ⟨y, hy⟩ := valued_adicCompletion_surjective (K := K) v (exp (-1 : ℤ))
  have hexp : exp (-1 : ℤ) < 1 := by
    rw [← exp_zero, exp_lt_exp]
    norm_num
  have hy1 : valuation (v.adicCompletion K) y < 1 := he.lt_one_iff_lt_one.2 (hy ▸ hexp)
  have hymem : (⟨y, hy1.le⟩ : 𝒪[v.adicCompletion K]) ∈ 𝓂[v.adicCompletion K] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation (v.adicCompletion K))).isUnit_iff_valuation_eq_one]
    exact hy1.ne
  have hyϖ : valuation (v.adicCompletion K) y ≤ valuation (v.adicCompletion K) ϖ := by
    have hs := hϖ.maximalIdeal_eq_setOfPred_le_v_coe (v := valuation (v.adicCompletion K))
    have h2 : (⟨y, hy1.le⟩ : 𝒪[v.adicCompletion K]) ∈ (𝓂[v.adicCompletion K] : Set _) := hymem
    rw [hs] at h2
    exact h2
  have hyϖ' := (he y ϖ).1 hyϖ
  rw [hy] at hyϖ'
  rw [← exp_log hne] at hyϖ' hlt ⊢
  rw [← exp_zero, exp_lt_exp] at hlt
  rw [exp_le_exp] at hyϖ'
  congr 1
  omega

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]`. Establish `h0 : (ϖ : v.adicCompletion K) ≠ 0` using `by exact_mod_cast hϖ.ne_zero`. Conclude with `⟨Units.mk0 _ h0, ord_uniformizer hϖ, valued_irreducible_valuationInteger v hϖ⟩`.
-/
theorem exists_ord_eq_one_valued :
    ∃ π : (v.adicCompletion K)ˣ, ord (π : v.adicCompletion K) = 1 ∧
      Valued.v (π : v.adicCompletion K) = exp (-1 : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  have h0 : (ϖ : v.adicCompletion K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  exact ⟨Units.mk0 _ h0, ord_uniformizer hϖ, valued_irreducible_valuationInteger v hϖ⟩

end Completion

section Global

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] (v : HeightOneSpectrum (𝓞 K))

/- English proof (translation)
Set `w' : PlacesOver L v` to `⟨w, inferInstance⟩`. Use `isMulCommutative_gal_adicCompletion L v w'` as an intermediate fact. Establish `hM : ramificationIndex (v.adicCompletion K) (w.adicCompletion L) = 1` using `ramificationIndex_eq_one_of_units_le (by rw [← ker_localSymbol L v w']; exact h)`. Conclude with `(ramificationIdx_integer v w).symm.trans hM`.
-/
theorem ramificationIdx_eq_one_of_units_le_ker_localSymbol
    (h : unitFiltrationUnits (v.adicCompletion K) 0 ≤ (localSymbol L v).ker)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) = 1 := by
  let w' : PlacesOver L v := ⟨w, inferInstance⟩
  have := isMulCommutative_gal_adicCompletion L v w'
  have hM : ramificationIndex (v.adicCompletion K) (w.adicCompletion L) = 1 :=
    ramificationIndex_eq_one_of_units_le (by rw [← ker_localSymbol L v w']; exact h)
  exact (ramificationIdx_integer v w).symm.trans hM

/- English proof (translation)
Use `isMulCommutative_gal_adicCompletion L v w` as an intermediate fact. Rewrite using `[localSymbol_eq_symbolAt L v w]`. Express the relevant statement in the definitionally equal form `(((decompositionMulEquiv v w.1).symm (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x) : MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal) : L ≃ₐ[K] L) = 1 ↔ _`. Rewrite using `[OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]`.
-/
theorem localSymbol_eq_one_iff_normResidueSymbol (w : PlacesOver L v) (x : (v.adicCompletion K)ˣ) :
    localSymbol L v x = 1 ↔
      normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x = 1 := by
  have := isMulCommutative_gal_adicCompletion L v w
  rw [localSymbol_eq_symbolAt L v w]
  change (((decompositionMulEquiv v w.1).symm
    (normResidueSymbol (v.adicCompletion K) (w.1.adicCompletion L) x) :
      MulAction.stabilizer (L ≃ₐ[K] L) w.1.asIdeal) : L ≃ₐ[K] L) = 1 ↔ _
  rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]

/- English proof (translation)
Take `⟨w⟩` from `nonempty_placesOver L v`. Use `isMulCommutative_gal_adicCompletion L v w` as an intermediate fact. Rewrite using `[splitsCompletely_iff_forall_finrank]`. Prove the components needed by the constructor for the conclusion. Introduce `h x`.

Rewrite using `[localSymbol_eq_one_iff_normResidueSymbol v w]`. Establish `hc : Nat.card (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) = 1`. Rewrite using `[IsGalois.card_aut_eq_finrank, h w]`. Conclude with `(Nat.card_eq_one_iff_unique.1 hc).1.elim _ _`. Introduce `h w'`.

Rewrite using `[← finrank_eq_of_isGalois v w w', ← IsGalois.card_aut_eq_finrank, Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun σ τ ↦ ?_⟩, inferInstance⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `normResidueSymbol_surjective σ`. Take `⟨y, rfl⟩` from `normResidueSymbol_surjective τ`. Rewrite using `[(localSymbol_eq_one_iff_normResidueSymbol v w x).1 (h x), (localSymbol_eq_one_iff_normResidueSymbol v w y).1 (h y)]`.
-/
theorem splitsCompletely_iff_localSymbol_eq_one :
    SplitsCompletely L v ↔ ∀ x : (v.adicCompletion K)ˣ, localSymbol L v x = 1 := by
  obtain ⟨w⟩ := nonempty_placesOver L v
  have := isMulCommutative_gal_adicCompletion L v w
  rw [splitsCompletely_iff_forall_finrank]
  constructor
  · intro h x
    rw [localSymbol_eq_one_iff_normResidueSymbol v w]
    have hc : Nat.card (w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L) = 1 := by
      rw [IsGalois.card_aut_eq_finrank, h w]
    exact (Nat.card_eq_one_iff_unique.1 hc).1.elim _ _
  · intro h w'
    rw [← finrank_eq_of_isGalois v w w', ← IsGalois.card_aut_eq_finrank,
      Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun σ τ ↦ ?_⟩, inferInstance⟩
    obtain ⟨x, rfl⟩ := normResidueSymbol_surjective σ
    obtain ⟨y, rfl⟩ := normResidueSymbol_surjective τ
    rw [(localSymbol_eq_one_iff_normResidueSymbol v w x).1 (h x), (localSymbol_eq_one_iff_normResidueSymbol v w y).1 (h y)]

/- English proof (translation)
Establish `he` using `ramificationIdx_eq_one_of_units_le_ker_localSymbol v h w`. Take `⟨π, hπ⟩` from `exists_ord_eq_one_units (v.adicCompletion K)`. Establish `hF` using `localSymbol_eq_arithFrobAt v w he hπ`. Rewrite using `[splitsCompletely_iff_localSymbol_eq_one]`. Prove the components needed by the constructor for the conclusion.

Introduce `h1`. Rewrite using `[← hF]`. Conclude with `h1 π`. Introduce `h1 x`. Establish `hu : (π ^ ord (x : v.adicCompletion K))⁻¹ * x ∈ unitFiltrationUnits (v.adicCompletion K) 0`.

Rewrite using `[← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _), ← zpow_neg, ord_zpow_units hπ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hx : x = π ^ ord (x : v.adicCompletion K) * ((π ^ ord (x : v.adicCompletion K))⁻¹ * x)`. Rewrite using `[mul_inv_cancel_left]`. Rewrite using `[hx, map_mul, h hu, mul_one, map_zpow, hF, h1, one_zpow]`.
-/
theorem splitsCompletely_iff_arithFrobAt_eq_one
    (h : unitFiltrationUnits (v.adicCompletion K) 0 ≤ (localSymbol L v).ker)
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    SplitsCompletely L v ↔ arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal = 1 := by
  have he := ramificationIdx_eq_one_of_units_le_ker_localSymbol v h w
  obtain ⟨π, hπ⟩ := exists_ord_eq_one_units (v.adicCompletion K)
  have hF := localSymbol_eq_arithFrobAt v w he hπ
  rw [splitsCompletely_iff_localSymbol_eq_one]
  constructor
  · intro h1
    rw [← hF]
    exact h1 π
  · intro h1 x
    have hu : (π ^ ord (x : v.adicCompletion K))⁻¹ * x ∈ unitFiltrationUnits (v.adicCompletion K) 0 := by
      rw [← ord_eq_zero_iff_mem, Units.val_mul, ord_mul (Units.ne_zero _) (Units.ne_zero _),
        ← zpow_neg, ord_zpow_units hπ]
      ring
    have hx : x = π ^ ord (x : v.adicCompletion K) * ((π ^ ord (x : v.adicCompletion K))⁻¹ * x) := by
      rw [mul_inv_cancel_left]
    rw [hx, map_mul, h hu, mul_one, map_zpow, hF, h1, one_zpow]

end Global

end

end GroundTheory.Global
