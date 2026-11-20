import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassFieldStatement

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurveAny

/- English proof (translation)
Introduce `hRF E _ _ _ H ι K hK n hn F hF`. Establish `hdm` using `H.d_mod`. Establish `hd0 : 0 < H.d` using `H.d_prime.pos`. Take `⟨hfin, h2⟩` from `finrank_adjoin hd0 H.sqrt_neg_disc_sq`. Establish `hconj` using `conj_eq_neg hd0 H.sqrt_neg_disc_sq`.

Establish `hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯` using `IntermediateField.mem_adjoin_simple_self ℚ H.rt0`. Generalize the expression as in `ℚ⟮H.rt0⟯ = K₀ at hK hfin h2 hr0`. Establish `hNF : NumberField K₀` using `NumberField.mk`. Establish `hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀)` using `Subtype.ext (by simpa using H.sqrt_neg_disc_sq)`. Establish `hD : discr K₀ = -(H.d : ℤ)` using `discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr`.

Establish `hTC : IsTotallyComplex K₀`. Use `⟨fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← InfinitePlace.not_isReal_iff_isComplex]`. Introduce `hv`. Establish `h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ)`.

Rewrite using `[← map_pow, hr, map_neg, map_natCast]`. Establish `h3 : (0 : ℝ) < H.d` using `by exact_mod_cast hd0`. Use polynomial arithmetic with `[sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]`. Take `⟨w, hw, hgen⟩` from `exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr`. Set `φ : K₀ →+* ℂ` to `algebraMap K₀ ℂ`.

Establish `hw' : φ w = (1 + H.rt0) / 2`. Use `congrArg φ hw` as an intermediate fact. Rewrite `this` using `[map_mul, map_add, map_one, map_ofNat]`. Express the relevant statement in the definitionally equal form `_ = 1 + H.rt0 at this`. Take the linear combination `this / 2`.

Establish `hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2)` using `fun a b => by`. Rewrite using `[← hw']`. Simplify using the standard rewrite rules. Establish `hn0 : (n : 𝓞 K₀) ≠ 0` using `by exact_mod_cast (show n ≠ 0 by omega)`. Take `⟨L, _, _, _, hL⟩` from `GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)}) (by rwa [Ne, Ideal.span_singleton_eq_bot])`.

Set `ψ : L →ₐ[K₀] ℂ` to `IsAlgClosed.lift`. Set `e₀ : L ≃ₐ[K₀] ψ.fieldRange` to `AlgEquiv.ofInjectiveField ψ`. Establish `hfR : FiniteDimensional K₀ ψ.fieldRange` using `e₀.toLinearEquiv.finiteDimensional`. Establish `hLR` using `fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀`. Generalize the expression as in `ψ.fieldRange = R at hfR hLR`.

Establish `hNR : NumberField R` using `NumberField.of_module_finite K₀ R`. Take `⟨hab, hR⟩` from `hLR hNR`. Express the relevant statement in the definitionally equal form `IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR`. Set `M : IntermediateField ℚ (AlgebraicClosure ℚ)` to `(R.restrictScalars ℚ).comap ι`. Establish `hM : M.map ι = R.restrictScalars ℚ`.

Use `IntermediateField.map_comap_eq_self fun z hz => ?_` and prove the remaining obligations. Establish `hi : IsIntegral ℚ z` using `(IsIntegral.of_finite ℚ (⟨z, hz⟩ : R)).map (algebraMap R ℂ).toRatAlgHom`. Conclude with `hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι`. Set `e : M ≃ₐ[ℚ] R` to `(M.equivMap ι).trans (IntermediateField.equivOfEq hM)`. Establish `hfM : FiniteDimensional ℚ M` using `e.symm.toLinearEquiv.finiteDimensional`.

Establish `hNM : NumberField M` using `NumberField.mk`. Establish `hRle : R.restrictScalars ℚ ≤ F`. Rewrite using `[← hM]`. Use `hF M ⟨fun x hx => ?_, hfM, ?_⟩` and prove the remaining obligations. Establish `: ι x ∈ K₀` using `hK ▸ ⟨x, hx, rfl⟩`.

Conclude with `R.algebraMap_mem (⟨ι x, this⟩ : K₀)`. Introduce and unpack `p ⟨hp, π, hπ, -, hπ1, σ, hσ⟩`. Rewrite using `[ncard_congr e.toRingEquiv p, e.toLinearEquiv.finrank_eq]`. Take `⟨r, -, hrr⟩ : H.rt0 ∈ K.map ι` from `hK ▸ hr0`. Express the relevant statement in the definitionally equal form `ι r = H.rt0 at hrr`.

Establish `hn1 : (n : AlgebraicClosure ℚ) ≠ 0` using `by exact_mod_cast (show n ≠ 0 by omega)`. Establish `hcK : ι ((π - 1) / n) ∈ K₀` using `hK ▸ ⟨_, K.div_mem (K.sub_mem hπ K.one_mem) (natCast_mem K n), rfl⟩`. Establish `hci : IsIntegral ℤ (⟨_, hcK⟩ : K₀)` using `(isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 (hπ1.map (ι : AlgebraicClosure ℚ →+* ℂ).toIntAlgHom)`. Take `⟨x, y, hxy⟩` from `hgen ⟨_, hci⟩`. Establish `h3 : ι ((π - 1) / n) = x + y * ((1 + H.rt0) / 2)`.

Rewrite using `[← hc, ← hxy]`. Both sides reduce to the same expression. Establish `h4 : π = 1 + n * (x + y * ((1 + r) / 2))`. Establish `: (π - 1) / n = x + y * ((1 + r) / 2)` using `ι.injective (by`. Express the relevant statement in the definitionally equal form `ι _ = ι _`.

Rewrite using `[h3]`. Simplify using `[hrr, map_ofNat])`. Rewrite using `[← this]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hr2 : r ^ 2 = -(H.d : AlgebraicClosure ℚ)` using `ι.injective (by`. Express the relevant statement in the definitionally equal form `ι _ = ι _`. Rewrite using `[map_pow, hrr, H.sqrt_neg_disc_sq]`. Use the proof step `simp)`. Establish `h5 : σ π = 1 + n * (x + y * ((1 + σ r) / 2))`.

Rewrite using `[h4]`. Simplify using `[map_ofNat]`. Establish `h6 : ι π * ι (σ π) = p` using `by rw [← map_mul, hσ, map_natCast]`. Establish `h7 : ι π = φ (1 + n * (x + y * w) : 𝓞 K₀)`. Rewrite using `[h4]`.

Simplify using `[hrr, map_ofNat, hw']`. Establish `hinj : ∀ a b : 𝓞 K₀, φ a = φ b → a = b` using `fun a b h => RingOfIntegers.coe_injective (φ.injective h)`. Establish `hs : σ r = r ∨ σ r = -r` using `sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [← map_pow, hr2]; simp)`. Break down `hs with hs | hs` into its components or cases. Rewrite `h5` using `[hs, ← h4]`.

Rewrite `h6` using `[h5, h7]`. Conclude with `absurd (hinj _ _ (by simpa using h6)) (sq_ne_prime h2 hD φ hp (1 + n * (x + y * w)))`. Establish `h8 : ι (σ π) = φ (1 + n * (x + y * (1 - w)) : 𝓞 K₀)`. Rewrite using `[h5, hs]`. Simplify using `only [map_add, map_mul, map_sub, map_neg, map_div₀, map_one, map_ofNat, map_natCast, map_intCast, hrr, hw']`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h6` using `[h7, h8]`. Use `ncard_eq_finrank h2 hD φ hn R hR hp (c := x + y * w) (c' := x + y * (1 - w)) ?_ (hinj _ _ (by simpa using h6))` and prove the remaining obligations. Rewrite using `[← Complex.norm_conj (φ (1 + n * (x + y * w) : 𝓞 K₀))]`. Use `congr 1`.

Simplify using `only [map_add, map_mul, map_sub, map_div₀, map_one, map_ofNat, map_natCast, map_intCast, hconj, hw']`. Expand and normalize the polynomial expressions, which then agree. Use `(GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn E H F n (by omega)).1 (hRle (R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀))) fun P hP => ?_` and prove the remaining obligations. Establish `hW` using `GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField K₀ h2 (by omega) P (fun z => ?_) n hn R hR`. Conclude with `⟨hRle (hW (Set.mem_insert _ _)), fun s hs => hRle (hW (Set.mem_insert_of_mem _ ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩))⟩`.

Rewrite using `[hP]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, rfl⟩`. Conclude with `⟨_, hc s.1 s.2⟩`. Introduce and unpack `⟨a, rfl⟩`.

Take `⟨a, b, rfl⟩` from `hgen a`. Conclude with `⟨(a, b), hc a b⟩`.
-/
theorem curveOver_of_rayField_any : GlobalTheory.NT.RayField → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (ι : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) (K : IntermediateField ℚ (AlgebraicClosure ℚ)), K.map ι = ℚ⟮H.rt0⟯ → ∀ n : ℕ, 3 ≤ n → ∀ F : IntermediateField ℚ ℂ, (∀ M : IntermediateField ℚ (AlgebraicClosure ℚ), (K ≤ M ∧ FiniteDimensional ℚ M ∧ ∀ p : ℕ, (p.Prime ∧ ∃ π : AlgebraicClosure ℚ, π ∈ K ∧ IsIntegral ℤ π ∧ IsIntegral ℤ ((π - 1) / (n : AlgebraicClosure ℚ)) ∧ ∃ σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ, π * σ π = (p : AlgebraicClosure ℚ)) → {v : HeightOneSpectrum (𝓞 M) | ((p : ℕ) : 𝓞 M) ∈ v.asIdeal}.ncard = Module.finrank ℚ M) → M.map ι ≤ F) → GlobalTheory.CompRat.CurveOver H F n := by
  intro hRF E _ _ _ H ι K hK n hn F hF
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hconj := conj_eq_neg hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hK hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := IsAlgClosed.lift
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := (R.restrictScalars ℚ).comap ι
  have hM : M.map ι = R.restrictScalars ℚ := by
    refine IntermediateField.map_comap_eq_self fun z hz => ?_
    have hi : IsIntegral ℚ z :=
      (IsIntegral.of_finite ℚ (⟨z, hz⟩ : R)).map (algebraMap R ℂ).toRatAlgHom
    exact hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι
  let e : M ≃ₐ[ℚ] R := (M.equivMap ι).trans (IntermediateField.equivOfEq hM)
  have hfM : FiniteDimensional ℚ M := e.symm.toLinearEquiv.finiteDimensional
  have hNM : NumberField M := NumberField.mk
  have hRle : R.restrictScalars ℚ ≤ F := by
    rw [← hM]
    refine hF M ⟨fun x hx => ?_, hfM, ?_⟩
    · have : ι x ∈ K₀ := hK ▸ ⟨x, hx, rfl⟩
      exact R.algebraMap_mem (⟨ι x, this⟩ : K₀)
    rintro p ⟨hp, π, hπ, -, hπ1, σ, hσ⟩
    rw [ncard_congr e.toRingEquiv p, e.toLinearEquiv.finrank_eq]
    obtain ⟨r, -, hrr⟩ : H.rt0 ∈ K.map ι := hK ▸ hr0
    change ι r = H.rt0 at hrr
    have hn1 : (n : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hcK : ι ((π - 1) / n) ∈ K₀ := hK ▸ ⟨_, K.div_mem (K.sub_mem hπ K.one_mem) (natCast_mem K n), rfl⟩
    have hci : IsIntegral ℤ (⟨_, hcK⟩ : K₀) :=
      (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 (hπ1.map (ι : AlgebraicClosure ℚ →+* ℂ).toIntAlgHom)
    obtain ⟨x, y, hxy⟩ := hgen ⟨_, hci⟩
    have h3 : ι ((π - 1) / n) = x + y * ((1 + H.rt0) / 2) := by
      rw [← hc, ← hxy]; rfl
    have h4 : π = 1 + n * (x + y * ((1 + r) / 2)) := by
      have : (π - 1) / n = x + y * ((1 + r) / 2) := ι.injective (by
        change ι _ = ι _
        rw [h3]; simp [hrr, map_ofNat])
      rw [← this]; field_simp; ring
    have hr2 : r ^ 2 = -(H.d : AlgebraicClosure ℚ) := ι.injective (by
      change ι _ = ι _
      rw [map_pow, hrr, H.sqrt_neg_disc_sq]; simp)
    have h5 : σ π = 1 + n * (x + y * ((1 + σ r) / 2)) := by
      rw [h4]; simp [map_ofNat]
    have h6 : ι π * ι (σ π) = p := by rw [← map_mul, hσ, map_natCast]
    have h7 : ι π = φ (1 + n * (x + y * w) : 𝓞 K₀) := by
      rw [h4]; simp [hrr, map_ofNat, hw']
    have hinj : ∀ a b : 𝓞 K₀, φ a = φ b → a = b := fun a b h => RingOfIntegers.coe_injective (φ.injective h)
    have hs : σ r = r ∨ σ r = -r := sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [← map_pow, hr2]; simp)
    rcases hs with hs | hs
    · rw [hs, ← h4] at h5
      rw [h5, h7] at h6
      exact absurd (hinj _ _ (by simpa using h6)) (sq_ne_prime h2 hD φ hp (1 + n * (x + y * w)))
    · have h8 : ι (σ π) = φ (1 + n * (x + y * (1 - w)) : 𝓞 K₀) := by
        rw [h5, hs]
        simp only [map_add, map_mul, map_sub, map_neg, map_div₀, map_one, map_ofNat, map_natCast, map_intCast, hrr, hw']
        ring
      rw [h7, h8] at h6
      refine ncard_eq_finrank h2 hD φ hn R hR hp (c := x + y * w) (c' := x + y * (1 - w)) ?_
        (hinj _ _ (by simpa using h6))
      rw [← Complex.norm_conj (φ (1 + n * (x + y * w) : 𝓞 K₀))]
      congr 1
      simp only [map_add, map_mul, map_sub, map_div₀, map_one, map_ofNat, map_natCast, map_intCast, hconj, hw']
      ring
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn E H F n (by omega)).1
    (hRle (R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀))) fun P hP => ?_
  have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField K₀ h2 (by omega) P (fun z => ?_) n hn R hR
  · exact ⟨hRle (hW (Set.mem_insert _ _)), fun s hs => hRle (hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩))⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end GlobalTheory.FieldSize.RayExistCurveAny
