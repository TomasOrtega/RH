import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZetaMemRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerExtensionPrimeNotMapComapLeSqStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisorDescentModUnramifiedGaloisSubmoduleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationEqOneOfPowEqSpanStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupAffineCurveDivisibleCharZeroStatement
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

/- English proof (translation)
Use `haveI : IsDedekindDomain (integralClosure A E) := integralClosure.isDedekindDomain A K E`. Use `haveI : IsFractionRing (integralClosure A E) E := integralClosure.isFractionRing_of_finite_extension K E`. Take `⟨f, J, hf, hJ⟩` from `GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule A (integralClosure A E) K E N hN (GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq A K E N hNu s hs hsu) hcl w hw hσ`. Use `⟨f, hf, fun B hB => ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span E Ω (integralClosure A E).toSubring B J N hN ?_ _ ?_ hJ` and prove the remaining obligations.

Introduce `x show algebraMap E Ω (x : E) ∈ B`. Take `⟨p, hp, hpx⟩ : IsIntegral A (x : E)` from `x.2`. Set `φ : A →+* B` to `((algebraMap E Ω).comp (algebraMap A E)).codRestrict B.toSubring hB`. Establish `hint : IsIntegral B (algebraMap E Ω x)`. Use `⟨p.map φ, hp.map φ, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.eval₂_map]`. Establish `h` using `congrArg (algebraMap E Ω) hpx`. Rewrite `h` using `[Polynomial.hom_eval₂, map_zero]`. Conclude with `h`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`.

Rewrite using `[← hy]`. Conclude with `y.2`. Conclude with `div_ne_zero hw ((_root_.map_ne_zero _).mpr hf)`.
-/
theorem descent_abstract (A K E Ω : Type) [CommRing A] [IsDedekindDomain A] [Field K] [CharZero K] [Algebra A K]
    [IsFractionRing A K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E] [Algebra A E]
    [IsScalarTower A K E] [Field Ω] [Algebra E Ω] (N : ℕ) (hN : 0 < N) (hNu : IsUnit (N : A))
    (s : Finset E) (hs : IntermediateField.adjoin K (s : Set E) = ⊤)
    (hsu : ∀ x ∈ s, ∃ u : Aˣ, x ^ N = algebraMap A E u)
    (hcl : ∀ c : ClassGroup A, ∃ d, c = d ^ N) (w : E) (hw : w ≠ 0)
    (hσ : ∀ σ : E ≃ₐ[K] E, ∃ u : E, u ≠ 0 ∧ σ w = w * u ^ N) :
    ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, (∀ x : A, algebraMap E Ω (algebraMap A E x) ∈ B) →
      ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / algebraMap K E f / c ^ N)) = 1 := by
  haveI : IsDedekindDomain (integralClosure A E) := integralClosure.isDedekindDomain A K E
  haveI : IsFractionRing (integralClosure A E) E := integralClosure.isFractionRing_of_finite_extension K E
  obtain ⟨f, J, hf, hJ⟩ := GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule A (integralClosure A E) K E N hN
    (GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq A K E N hNu s hs hsu) hcl w hw hσ
  refine ⟨f, hf, fun B hB => ?_⟩
  refine GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span E Ω (integralClosure A E).toSubring B J N hN ?_ _ ?_ hJ
  · intro x
    show algebraMap E Ω (x : E) ∈ B
    obtain ⟨p, hp, hpx⟩ : IsIntegral A (x : E) := x.2
    let φ : A →+* B := ((algebraMap E Ω).comp (algebraMap A E)).codRestrict B.toSubring hB
    have hint : IsIntegral B (algebraMap E Ω x) := by
      refine ⟨p.map φ, hp.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have h := congrArg (algebraMap E Ω) hpx
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hy]
    exact y.2
  · exact div_ne_zero hw ((_root_.map_ne_zero _).mpr hf)

/- English proof (translation)
Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K`. Establish `key : ∀ (c : K) (γ x : Ω), c ≠ 0 → γ ^ N = algebraMap K Ω c → γ ∈ IntermediateField.adjoin K {α, β} → x ^ N = algebraMap K Ω c → x ∈ IntermediateField.adjoin K {α, β}`. Introduce `c γ x hc hγ hm hx`. Establish `hc' : algebraMap K Ω c ≠ 0` using `(_root_.map_ne_zero _).mpr hc`.

Establish `hγ0 : γ ≠ 0`. Introduce and unpack `rfl`. Rewrite `hγ` using `[zero_pow hN.ne']`. Conclude with `hc' hγ.symm`. Establish `h1 : (x / γ) ^ N = 1` using `by rw [div_pow, hx, hγ, div_self hc']`.

Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one h1`. Take `⟨z, rfl⟩` from `hζK`. Establish `: x = algebraMap K Ω z ^ i * γ` using `by rw [hi, div_mul_cancel₀ _ hγ0]`. Rewrite using `[this]`. Conclude with `mul_mem (pow_mem (IntermediateField.algebraMap_mem _ z) i) hm`.

Set `p : K[X]` to `(X ^ N - C a) * (X ^ N - C b)`. Establish `hp0 : p ≠ 0` using `mul_ne_zero (X_pow_sub_C_ne_zero hN a) (X_pow_sub_C_ne_zero hN b)`. Establish `hroot : ∀ x : Ω, x ∈ p.rootSet Ω ↔ x ^ N = algebraMap K Ω a ∨ x ^ N = algebraMap K Ω b`. Introduce `x`. Rewrite using `[mem_rootSet_of_ne hp0]`.

Simplify using `[p, sub_eq_zero]`. Establish `heq : IntermediateField.adjoin K {α, β} = IntermediateField.adjoin K (p.rootSet Ω)`. Apply `le_antisymm` to reduce the goal to its premises. Apply `IntermediateField.adjoin.mono` to reduce the goal to its premises. Introduce and unpack `x (rfl | rfl)`.

Conclude with `(hroot _).mpr (Or.inl hα)`. Conclude with `(hroot _).mpr (Or.inr hβ)`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `x hx`. Break down `(hroot x).mp hx with h | h` into its components or cases.

Conclude with `key a α x ha hα (IntermediateField.subset_adjoin _ _ (by simp)) h`. Conclude with `key b β x hb hβ (IntermediateField.subset_adjoin _ _ (by simp)) h`. Rewrite using `[heq]`. Use `haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := p) (IsAlgClosed.splits _)`. Use `haveI : Normal K (IntermediateField.adjoin K (p.rootSet Ω)) := Normal.of_isSplittingField p`.

Conclude with `⟨⟩`.
-/
theorem isGalois_adjoin_pair (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hζK : ζ ∈ Set.range (algebraMap K Ω))
    (a b : K) (α β : Ω) (ha : a ≠ 0) (hb : b ≠ 0) (hα : α ^ N = algebraMap K Ω a) (hβ : β ^ N = algebraMap K Ω b) :
    IsGalois K (IntermediateField.adjoin K {α, β}) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have key : ∀ (c : K) (γ x : Ω), c ≠ 0 → γ ^ N = algebraMap K Ω c → γ ∈ IntermediateField.adjoin K {α, β} →
      x ^ N = algebraMap K Ω c → x ∈ IntermediateField.adjoin K {α, β} := by
    intro c γ x hc hγ hm hx
    have hc' : algebraMap K Ω c ≠ 0 := (_root_.map_ne_zero _).mpr hc
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hγ
      exact hc' hγ.symm
    have h1 : (x / γ) ^ N = 1 := by rw [div_pow, hx, hγ, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    obtain ⟨z, rfl⟩ := hζK
    have : x = algebraMap K Ω z ^ i * γ := by rw [hi, div_mul_cancel₀ _ hγ0]
    rw [this]
    exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ z) i) hm
  let p : K[X] := (X ^ N - C a) * (X ^ N - C b)
  have hp0 : p ≠ 0 := mul_ne_zero (X_pow_sub_C_ne_zero hN a) (X_pow_sub_C_ne_zero hN b)
  have hroot : ∀ x : Ω, x ∈ p.rootSet Ω ↔ x ^ N = algebraMap K Ω a ∨ x ^ N = algebraMap K Ω b := by
    intro x
    rw [mem_rootSet_of_ne hp0]
    simp [p, sub_eq_zero]
  have heq : IntermediateField.adjoin K {α, β} = IntermediateField.adjoin K (p.rootSet Ω) := by
    apply le_antisymm
    · apply IntermediateField.adjoin.mono
      rintro x (rfl | rfl)
      · exact (hroot _).mpr (Or.inl hα)
      · exact (hroot _).mpr (Or.inr hβ)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases (hroot x).mp hx with h | h
      · exact key a α x ha hα (IntermediateField.subset_adjoin _ _ (by simp)) h
      · exact key b β x hb hβ (IntermediateField.subset_adjoin _ _ (by simp)) h
  rw [heq]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := p) (IsAlgClosed.splits _)
  haveI : Normal K (IntermediateField.adjoin K (p.rootSet Ω)) := Normal.of_isSplittingField p
  exact ⟨⟩

/- English proof (translation)
Apply `IntermediateField.map_injective (IntermediateField.adjoin K {α, β}).val` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val, Set.image_pair]`. Simplify using `[hα, hβ]`.
-/
theorem adjoin_pair_eq_top (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (α β : Ω)
    (α' β' : IntermediateField.adjoin K {α, β}) (hα : (α' : Ω) = α) (hβ : (β' : Ω) = β) :
    IntermediateField.adjoin K ({α', β'} : Set (IntermediateField.adjoin K {α, β})) = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin K {α, β}).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
    Set.image_pair]
  simp [hα, hβ]

/- English proof (translation)
Introduce `k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ hθ hw hs`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective`. Use `haveI := isGalois_adjoin_pair K Ω N ζ hN hζ (zeta_mem_range k K Ω N ζ hN hζ) a b α β ha0 hb0 hα hβ`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K {α, β}) := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Use `haveI : Normal K Ω := IsAlgClosure.normal K Ω`.

Establish `hNu : IsUnit (N : FunctionField.ringOfIntegers k K)`. Establish `h1 : IsUnit (N : k)` using `(Nat.cast_ne_zero.mpr hN.ne').isUnit`. Establish `h2` using `h1.map ((algebraMap k[X] (FunctionField.ringOfIntegers k K)).comp C)`. Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis. Set `α' : IntermediateField.adjoin K {α, β}` to `⟨α, IntermediateField.subset_adjoin _ _ (by simp)⟩`.

Set `β' : IntermediateField.adjoin K {α, β}` to `⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩`. Take `⟨f, hf, hB⟩` from `descent_abstract (FunctionField.ringOfIntegers k K) K (IntermediateField.adjoin K {α, β}) Ω N hN hNu {α', β'} (by rw [Finset.coe_pair]; exact adjoin_pair_eq_top K Ω α β α' β' rfl rfl) (by`. Introduce `x hx`. Break down `Finset.mem_insert.mp hx with rfl | hx` into its components or cases. Conclude with `⟨⟨⟨a, ha⟩, ⟨a⁻¹, ha'⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩, Subtype.ext hα⟩`.

Rewrite using `[Finset.mem_singleton.mp hx]`. Conclude with `⟨⟨⟨b, hb⟩, ⟨b⁻¹, hb'⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩, Subtype.ext hβ⟩)`. Use the proof step `(GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K N hN) ⟨θ ^ N, hw⟩ (fun h => pow_ne_zero N hθ (congrArg Subtype.val h))`. Use the proof step `(by`. Introduce `σ`.

Take `⟨u, hu, hu0, h⟩` from `hs (σ.liftNormal Ω)`. Use `⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h), Subtype.ext ?_⟩` and prove the remaining obligations. Conclude with `(σ.liftNormal_commutes Ω ⟨θ ^ N, hw⟩).symm.trans h)`. Use `⟨f, hf, fun B hO => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hv⟩` from `hB B fun x => hO x.1 x.2`.

Use `⟨c, c.2, fun h => hc (Subtype.ext h), ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[div_div, map_div₀, map_mul, map_pow]`. Conclude with `hv`.
-/
theorem divisor_descends : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ hθ hw hs
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI := isGalois_adjoin_pair K Ω N ζ hN hζ (zeta_mem_range k K Ω N ζ hN hζ) a b α β ha0 hb0 hα hβ
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α, β}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hNu : IsUnit (N : FunctionField.ringOfIntegers k K) := by
    have h1 : IsUnit (N : k) := (Nat.cast_ne_zero.mpr hN.ne').isUnit
    have h2 := h1.map ((algebraMap k[X] (FunctionField.ringOfIntegers k K)).comp C)
    rwa [map_natCast] at h2
  let α' : IntermediateField.adjoin K {α, β} := ⟨α, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let β' : IntermediateField.adjoin K {α, β} := ⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  obtain ⟨f, hf, hB⟩ := descent_abstract (FunctionField.ringOfIntegers k K) K (IntermediateField.adjoin K {α, β}) Ω
    N hN hNu {α', β'} (by rw [Finset.coe_pair]; exact adjoin_pair_eq_top K Ω α β α' β' rfl rfl)
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, ha'⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩,
          Subtype.ext hα⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨⟨⟨b, hb⟩, ⟨b⁻¹, hb'⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩,
          Subtype.ext hβ⟩)
    (GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K N hN) ⟨θ ^ N, hw⟩ (fun h => pow_ne_zero N hθ (congrArg Subtype.val h))
    (by
      intro σ
      obtain ⟨u, hu, hu0, h⟩ := hs (σ.liftNormal Ω)
      refine ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      exact (σ.liftNormal_commutes Ω ⟨θ ^ N, hw⟩).symm.trans h)
  refine ⟨f, hf, fun B hO => ?_⟩
  obtain ⟨c, hc, hv⟩ := hB B fun x => hO x.1 x.2
  refine ⟨c, c.2, fun h => hc (Subtype.ext h), ?_⟩
  rw [div_div, map_div₀, map_mul, map_pow] at hv
  exact hv

end GlobalTheory.KummerCob
