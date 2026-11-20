import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EmbeddingMemCoefficientField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubOneLtOfRed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsInertiaLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameKummerInertia

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A L _ _ _ K _ Q _ hQ hfix`. Rewrite using `[GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix E K L Q]`. Introduce `τ hτ y`. Establish `hint : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (a : L)) ≤ 1` using `fun a => GlobalTheory.CMRam.val_int_le (algebraMap L Ω) A a`. Establish `hsm : ∀ a : 𝓞 L, ((τ • a : 𝓞 L) : L) = τ (a : L)` using `fun a => rfl`.

Establish `hτ' : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (τ (a : L)) - algebraMap L Ω (a : L)) < 1`. Introduce `a`. Use `(hQ _).1 (hτ a)` as an intermediate fact. Simplify `this` using `[hsm]`. Establish `hlift : ∀ x : L, A.valuation (algebraMap L Ω x) ≤ 1 → A.valuation (algebraMap L Ω (τ x) - algebraMap L Ω x) < 1`.

Introduce `x hx`. Take `⟨s, t, hs, e⟩` from `GlobalTheory.CMRam.exists_den_field (algebraMap L Ω) A hx`. Establish `hτs : A.valuation (algebraMap L Ω (τ (s : L))) = 1`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Use `hint (τ • s)` as an intermediate fact.

Rewrite `this` using `[hsm]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hlt push Not at hlt`. Establish `h2 : A.valuation (algebraMap L Ω (s : L)) < 1`. Establish `e2 : algebraMap L Ω (s : L) = algebraMap L Ω (τ (s : L)) - (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L))` using `by ring`. Rewrite using `[e2]`.

Conclude with `Valuation.map_sub_lt _ hlt (hτ' s)`. Rewrite `h2` using `[hs]`. Conclude with `lt_irrefl _ h2`. Establish `he' : τ (s : L) * τ x = τ (t : L)` using `by rw [← map_mul, e]`. Establish `key : algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x) = (algebraMap L Ω (τ (t : L)) - algebraMap L Ω (t : L)) + algebraMap L Ω x * (algebraMap L Ω (s : L) - algebraMap L Ω (τ (s : L)))`.

Rewrite using `[← he', ← e]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : A.valuation (algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x)) < 1`. Rewrite using `[key]`.

Use `Valuation.map_add_lt _ (hτ' t) ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_mul, Valuation.map_sub_swap]`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hv` using `[Valuation.map_mul, hτs, one_mul]`. Then use the resulting hypothesis. Take `⟨σ, hσ, hσx⟩` from `GlobalTheory.InertiaLift.exists_mem_Ine_lift A L τ hlift`.

Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1` using `hσx (algebraMap K L y)`. Establish `h2` using `hfix σ hσ y`. Conclude with `(h1.symm.trans h2 : _)`.
-/
theorem unram_of_fixed : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (L : IntermediateField E Ω) [FiniteDimensional E L] [IsGalois E L] [NumberField L] (K : IntermediateField E L) [NumberField K] (Q : Ideal (𝓞 L)) [Q.IsPrime], (∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (((x : L) : Ω)) < 1) → (∀ σ ∈ Ine (F := E) A, ∀ y : K, σ (((y : L) : Ω)) = ((y : L) : Ω)) → (Q.under (𝓞 K)).ramificationIdx (𝓞 E) = 1 := by
  intro E Ω _ _ _ _ _ A L _ _ _ K _ Q _ hQ hfix
  rw [GlobalTheory.UnramCompositum.ramificationIdx_eq_one_iff_fix E K L Q]
  intro τ hτ y
  have hint : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (a : L)) ≤ 1 := fun a =>
    GlobalTheory.CMRam.val_int_le (algebraMap L Ω) A a
  have hsm : ∀ a : 𝓞 L, ((τ • a : 𝓞 L) : L) = τ (a : L) := fun a => rfl
  have hτ' : ∀ a : 𝓞 L, A.valuation (algebraMap L Ω (τ (a : L)) - algebraMap L Ω (a : L)) < 1 := by
    intro a
    have := (hQ _).1 (hτ a)
    simpa [hsm] using this
  have hlift : ∀ x : L, A.valuation (algebraMap L Ω x) ≤ 1 →
      A.valuation (algebraMap L Ω (τ x) - algebraMap L Ω x) < 1 := by
    intro x hx
    obtain ⟨s, t, hs, e⟩ := GlobalTheory.CMRam.exists_den_field (algebraMap L Ω) A hx
    have hτs : A.valuation (algebraMap L Ω (τ (s : L))) = 1 := by
      refine le_antisymm ?_ ?_
      · have := hint (τ • s); rwa [hsm] at this
      · by_contra hlt
        push Not at hlt
        have h2 : A.valuation (algebraMap L Ω (s : L)) < 1 := by
          have e2 : algebraMap L Ω (s : L) = algebraMap L Ω (τ (s : L)) - (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L)) := by ring
          rw [e2]; exact Valuation.map_sub_lt _ hlt (hτ' s)
        rw [hs] at h2; exact lt_irrefl _ h2
    have he' : τ (s : L) * τ x = τ (t : L) := by rw [← map_mul, e]
    have key : algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x) =
        (algebraMap L Ω (τ (t : L)) - algebraMap L Ω (t : L)) + algebraMap L Ω x * (algebraMap L Ω (s : L) - algebraMap L Ω (τ (s : L))) := by
      rw [← he', ← e]; simp only [map_mul]; ring
    have hv : A.valuation (algebraMap L Ω (τ (s : L)) * (algebraMap L Ω (τ x) - algebraMap L Ω x)) < 1 := by
      rw [key]
      refine Valuation.map_add_lt _ (hτ' t) ?_
      rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (algebraMap L Ω x) * A.valuation (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L))
          ≤ 1 * A.valuation (algebraMap L Ω (τ (s : L)) - algebraMap L Ω (s : L)) := mul_le_mul_left hx _
        _ < 1 := by rw [one_mul]; exact hτ' s
    rwa [Valuation.map_mul, hτs, one_mul] at hv
  obtain ⟨σ, hσ, hσx⟩ := GlobalTheory.InertiaLift.exists_mem_Ine_lift A L τ hlift
  apply Subtype.ext
  have h1 := hσx (algebraMap K L y)
  have h2 := hfix σ hσ y
  exact (h1.symm.trans h2 : _)

/- English proof (translation)
Introduce `E K _ _ _ _ _ v P _ hPv he g hgv hgv2 k Z hZ`. Assume the negation of the conclusion as `hk`. Use `push Not at hk`. Use `haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩`. Establish `he' : Ideal.ramificationIdx' v.asIdeal P = 1`.

Rewrite using `[Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P v.ne_bot]`. Conclude with `he`. Establish `hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P` using `Ideal.map_le_iff_le_comap.2 (le_of_eq hPv.symm)`. Establish `hnot : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P ^ 2` using `fun h => (Ideal.ramificationIdx'_ne_one_iff hmap).2 h he'`. Establish `hZi : IsIntegral ℤ Z`.

Use `IsIntegral.of_pow (n := k) (by omega) ?_` and prove the remaining obligations. Rewrite using `[hZ, ← map_natCast (algebraMap ℤ K) g]`. Conclude with `isIntegral_algebraMap`. Use `set z : 𝓞 K := ⟨Z, hZi⟩ with hzdef`. Establish `hz : z ^ k = ((g : ℕ) : 𝓞 K)`.

Apply `NumberField.RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]`. Conclude with `hZ`. Establish `hgP : ((g : ℕ) : 𝓞 K) ∈ P`. Establish `h0 : ((g : ℕ) : 𝓞 E) ∈ P.under (𝓞 E)` using `hPv ▸ hgv`.

Rewrite `h0` using `[Ideal.under, Ideal.mem_comap, map_natCast]`. Conclude with `h0`. Establish `hzP : z ∈ P` using `Ideal.IsPrime.mem_of_pow_mem ‹_› k (hz ▸ hgP)`. Establish `hgP2 : ((g : ℕ) : 𝓞 K) ∈ P ^ 2`. Rewrite using `[← hz, show k = 2 + (k - 2) by omega, pow_add]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hzP 2)`. Take `⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {((g : ℕ) : 𝓞 E)}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgv)`. Establish `hJv : ¬ J ≤ v.asIdeal`. Introduce `hle`. Apply `hgv2` to reduce the goal to its premises.

Establish `: Ideal.span {((g : ℕ) : 𝓞 E)} ≤ v.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `this (Ideal.mem_span_singleton_self _)`. Take `⟨j, hjJ, hjv⟩` from `Set.not_subset.1 hJv`.

Establish `hjP : algebraMap (𝓞 E) (𝓞 K) j ∉ P`. Introduce `h`. Apply `hjv` to reduce the goal to its premises. Rewrite using `[← hPv]`. Conclude with `h`.

Use `haveI hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (by rw [show Ideal.comap (algebraMap (𝓞 E) (𝓞 K)) P = v.asIdeal from hPv]; exact v.isMaximal)`. Establish `hrad : (P ^ 2).radical = P` using `by rw [Ideal.radical_pow _ two_ne_zero, hPmax.isPrime.radical]`. Establish `hprim : (P ^ 2).IsPrimary` using `Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hPmax)`. Apply `hnot` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `x hx`. Establish `hxj : x * j ∈ Ideal.span {((g : ℕ) : 𝓞 E)}` using `by rw [hJ]; exact Ideal.mul_mem_mul hx hjJ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hxj`. Establish `h1 : algebraMap (𝓞 E) (𝓞 K) j * algebraMap (𝓞 E) (𝓞 K) x ∈ P ^ 2`. Rewrite using `[← map_mul, mul_comm, ← hc, map_mul, map_natCast]`.

Conclude with `Ideal.mul_mem_left _ _ hgP2`. Break down `hprim.mem_or_mem h1 with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `h` using `[Submodule.colon_univ, hrad]`.

Conclude with `hjP h`.
-/
theorem index_one_root : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] (v : HeightOneSpectrum (𝓞 E)) (P : Ideal (𝓞 K)) [P.IsPrime], P.under (𝓞 E) = v.asIdeal → P.ramificationIdx (𝓞 E) = 1 → ∀ (g : ℕ), ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (k : ℕ) (Z : K), Z ^ k = ((g : ℕ) : K) → k ≤ 1 := by
  intro E K _ _ _ _ _ v P _ hPv he g hgv hgv2 k Z hZ
  by_contra hk
  push Not at hk
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  have he' : Ideal.ramificationIdx' v.asIdeal P = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal P v.ne_bot]; exact he
  have hmap : Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P :=
    Ideal.map_le_iff_le_comap.2 (le_of_eq hPv.symm)
  have hnot : ¬ Ideal.map (algebraMap (𝓞 E) (𝓞 K)) v.asIdeal ≤ P ^ 2 := fun h =>
    (Ideal.ramificationIdx'_ne_one_iff hmap).2 h he'
  have hZi : IsIntegral ℤ Z := by
    refine IsIntegral.of_pow (n := k) (by omega) ?_
    rw [hZ, ← map_natCast (algebraMap ℤ K) g]
    exact isIntegral_algebraMap
  set z : 𝓞 K := ⟨Z, hZi⟩ with hzdef
  have hz : z ^ k = ((g : ℕ) : 𝓞 K) := by
    apply NumberField.RingOfIntegers.ext
    simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_natCast]
    exact hZ
  have hgP : ((g : ℕ) : 𝓞 K) ∈ P := by
    have h0 : ((g : ℕ) : 𝓞 E) ∈ P.under (𝓞 E) := hPv ▸ hgv
    rw [Ideal.under, Ideal.mem_comap, map_natCast] at h0
    exact h0
  have hzP : z ∈ P := Ideal.IsPrime.mem_of_pow_mem ‹_› k (hz ▸ hgP)
  have hgP2 : ((g : ℕ) : 𝓞 K) ∈ P ^ 2 := by
    rw [← hz, show k = 2 + (k - 2) by omega, pow_add]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hzP 2)
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {((g : ℕ) : 𝓞 E)} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hgv)
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle; apply hgv2
    have : Ideal.span {((g : ℕ) : 𝓞 E)} ≤ v.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self _)
  obtain ⟨j, hjJ, hjv⟩ := Set.not_subset.1 hJv
  have hjP : algebraMap (𝓞 E) (𝓞 K) j ∉ P := by
    intro h; apply hjv; rw [← hPv]; exact h
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P
    (by rw [show Ideal.comap (algebraMap (𝓞 E) (𝓞 K)) P = v.asIdeal from hPv]; exact v.isMaximal)
  have hrad : (P ^ 2).radical = P := by rw [Ideal.radical_pow _ two_ne_zero, hPmax.isPrime.radical]
  have hprim : (P ^ 2).IsPrimary := Ideal.isPrimary_of_isMaximal_radical (by rw [hrad]; exact hPmax)
  apply hnot
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hxj : x * j ∈ Ideal.span {((g : ℕ) : 𝓞 E)} := by rw [hJ]; exact Ideal.mul_mem_mul hx hjJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hxj
  have h1 : algebraMap (𝓞 E) (𝓞 K) j * algebraMap (𝓞 E) (𝓞 K) x ∈ P ^ 2 := by
    rw [← map_mul, mul_comm, ← hc, map_mul, map_natCast]; exact Ideal.mul_mem_left _ _ hgP2
  rcases hprim.mem_or_mem h1 with h | h
  · exact h
  · exfalso; rw [Submodule.colon_univ, hrad] at h; exact hjP h

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A v hA g _ hgv hgv2 m hm hgm Y μ hY hμ`. Establish `hgp : g.Prime` using `Fact.out`. Establish `hg` using `GlobalTheory.TameCoupledEx.val_g_lt A v hA hgv`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`.

Use `haveI : NeZero m := ⟨hm.ne'⟩`. Establish `hg0 : ((g : ℕ) : Ω) ≠ 0` using `Nat.cast_ne_zero.2 hgp.ne_zero`. Establish `hY0 : Y ≠ 0` using `GlobalTheory.TameCoupledEx.ne_zero_of_pow_eq hgp hm hY`. Establish `hpow : ∀ σ : G E Ω, (σ Y / Y) ^ m = 1` using `fun σ => tameQuot_pow σ hg0 hY`. Establish `hne : ∀ σ : G E Ω, σ Y / Y ≠ 0` using `fun σ => div_ne_zero (by simpa using hY0) hY0`.

Set `χ : Ine (F` to `E) A →* rootsOfUnity m Ω := { toFun := fun σ => ⟨Units.mk0 (σ.1 Y / Y) (hne σ.1), by`. Rewrite using `[mem_rootsOfUnity]`. Use `ext`. Simplify using `[hpow]⟩`. Use the proof step `map_one' := by ext; simp [hY0]`.

Use the proof step `map_mul' := fun σ τ => by`. Use `ext`. Simplify using `only [Subgroup.coe_mul, Units.val_mk0, Subgroup.coe_mul, Units.val_mul]`. Conclude with `GlobalTheory.TameCoupledEx.ratio_mul hgp hg σ.2 τ.1 hm hgm hY }`. Establish `hχ : ∀ σ, (((χ σ : rootsOfUnity m Ω) : Ωˣ) : Ω) = σ.1 Y / Y` using `fun σ => rfl`.

Take `⟨⟨c, σ0, hσ0⟩, hc⟩` from `IsCyclic.exists_generator (α := χ.range)`. Use `set d := orderOf c with hd`. Establish `hcm : c ^ m = 1` using `by ext; simpa [← hσ0, hχ] using hpow σ0.1`. Establish `hdm : d ∣ m` using `orderOf_dvd_of_pow_eq_one hcm`. Establish `hd0 : 0 < d` using `Nat.pos_of_dvd_of_pos hdm hm`.

Establish `hall : ∀ σ : G E Ω, σ ∈ Ine (F` using `E) A → (σ Y / Y) ^ d = 1 := by`. Introduce `σ hσ`. Take `⟨j, hj⟩` from `Subgroup.mem_zpowers_iff.1 (hc ⟨χ ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩)`. Establish `h1 : (χ ⟨σ, hσ⟩) ^ d = 1`. Use `congrArg Subtype.val hj` as an intermediate fact.

Simplify using `only [Subgroup.coe_zpow] at this`. Rewrite using `[← this, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, pow_orderOf_eq_one, one_zpow]`. Establish `h2` using `congrArg (fun u : rootsOfUnity m Ω => ((u : Ωˣ) : Ω)) h1`. Simplify `h2` using `[hχ]`. Use `set Z := Y ^ d with hZ`.

Establish `hZfix : ∀ σ : G E Ω, σ ∈ Ine (F` using `E) A → σ Z = Z := by`. Introduce `σ hσ`. Establish `e : σ Y = (σ Y / Y) * Y` using `by field_simp`. Rewrite using `[hZ, map_pow, e, mul_pow, hall σ hσ, one_mul]`. Use `set n := m / d with hn`.

Establish `hnd : d * n = m` using `Nat.mul_div_cancel' hdm`. Establish `hZn : Z ^ n = ((g : ℕ) : Ω)` using `by rw [hZ, ← pow_mul, hnd, hY]`. Establish `hn1 : n ≤ 1`. Establish `hZi : IsIntegral E Z` using `Algebra.IsIntegral.isIntegral Z`. Use `haveI : FiniteDimensional E (IntermediateField.adjoin E {Z}) := IntermediateField.adjoin.finiteDimensional hZi`.

Use `set L := IntermediateField.normalClosure E (IntermediateField.adjoin E {Z}) Ω with hLdef`. Use `haveI : NumberField L := NumberField.of_module_finite E L`. Establish `hZL : Z ∈ L` using `IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self E Z)`. Use `set Z' : L := ⟨Z, hZL⟩ with hZ'`. Use `set K : IntermediateField E L := IntermediateField.adjoin E {Z'} with hK`.

Use `haveI : NumberField K := NumberField.of_module_finite E K`. Set `f : 𝓞 L →+* A` to `((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring (fun x => ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ L Ω))))`. Use `set Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f with hQ`. Use `haveI : Q.IsPrime := Ideal.comap_isPrime f _`. Establish `hQmem : ∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (((x : L) : Ω)) < 1` using `fun x => Ideal.mem_comap.trans (ValuationSubring.valuation_lt_one_iff A (f x))`.

Establish `hfixK : ∀ σ ∈ Ine (F` using `E) A, ∀ y : K, σ (((y : L) : Ω)) = ((y : L) : Ω) := by`. Introduce `σ hσ y`. Establish `hle : K.toSubalgebra ≤ AlgHom.equalizer ((σ : Ω →ₐ[E] Ω).comp L.val) L.val`. Rewrite using `[hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic Z')]`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ rfl`. Conclude with `hZfix σ hσ`. Conclude with `hle y.2`. Establish `e1` using `unram_of_fixed E Ω A L K Q hQmem hfixK`. Establish `hunder : (Q.under (𝓞 K)).under (𝓞 E) = v.asIdeal`.

Use extensionality with `x`. Rewrite using `[Ideal.under_under, Ideal.mem_comap, hQmem, ← hA x]`. Both sides reduce to the same expression. Use `set Z'' : K := ⟨Z', IntermediateField.mem_adjoin_simple_self E Z'⟩ with hZ''`. Establish `hZ''n : Z'' ^ n = ((g : ℕ) : K)`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hZn`. Conclude with `index_one_root E K v (Q.under (𝓞 K)) hunder e1 g hgv hgv2 n Z'' hZ''n`. Establish `hdm' : d = m`.

Establish `hn0 : 0 < n` using `Nat.pos_of_ne_zero (by rintro h; rw [h, mul_zero] at hnd; exact hm.ne' hnd.symm)`. Establish `: n = 1` using `le_antisymm hn1 hn0`. Rewrite `hnd` using `[this, mul_one]`. Conclude with `hnd`. Establish `hprim : IsPrimitiveRoot (σ0.1 Y / Y) m`.

Establish `h1 : orderOf (σ0.1 Y / Y) = m`. Rewrite using `[← hχ, orderOf_units, Subgroup.orderOf_coe, hσ0, ← hd, hdm']`. Rewrite using `[← h1]`. Conclude with `IsPrimitiveRoot.orderOf _`. Take `⟨i, -, hi⟩` from `hprim.eq_pow_of_pow_eq_one hμ`.

Use `⟨σ0.1 ^ i, pow_mem σ0.2 i, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.TameCoupledEx.ratio_pow hgp hg σ0.2 hm hgm hY i` as an intermediate fact. Rewrite `this` using `[hi]`. Clear denominators, using `at this` for the nonvanishing conditions. Rewrite using `[this, mul_comm]`.
-/
theorem tame_kummer_surj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime], ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2 → ∀ (m : ℕ), 0 < m → ¬ g ∣ m → ∀ Y μ : Ω, Y ^ m = ((g : ℕ) : Ω) → μ ^ m = 1 → ∃ σ ∈ Ine (F := E) A, σ Y = μ * Y := by
  intro E Ω _ _ _ _ _ A v hA g _ hgv hgv2 m hm hgm Y μ hY hμ
  have hgp : g.Prime := Fact.out
  have hg := GlobalTheory.TameCoupledEx.val_g_lt A v hA hgv
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  haveI : NeZero m := ⟨hm.ne'⟩
  have hg0 : ((g : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.2 hgp.ne_zero
  have hY0 : Y ≠ 0 := GlobalTheory.TameCoupledEx.ne_zero_of_pow_eq hgp hm hY
  have hpow : ∀ σ : G E Ω, (σ Y / Y) ^ m = 1 := fun σ => tameQuot_pow σ hg0 hY
  have hne : ∀ σ : G E Ω, σ Y / Y ≠ 0 := fun σ => div_ne_zero (by simpa using hY0) hY0
  let χ : Ine (F := E) A →* rootsOfUnity m Ω :=
    { toFun := fun σ => ⟨Units.mk0 (σ.1 Y / Y) (hne σ.1), by
        rw [mem_rootsOfUnity]; ext; simp [hpow]⟩
      map_one' := by ext; simp [hY0]
      map_mul' := fun σ τ => by
        ext
        simp only [Subgroup.coe_mul, Units.val_mk0, Subgroup.coe_mul, Units.val_mul]
        exact GlobalTheory.TameCoupledEx.ratio_mul hgp hg σ.2 τ.1 hm hgm hY }
  have hχ : ∀ σ, (((χ σ : rootsOfUnity m Ω) : Ωˣ) : Ω) = σ.1 Y / Y := fun σ => rfl
  obtain ⟨⟨c, σ0, hσ0⟩, hc⟩ := IsCyclic.exists_generator (α := χ.range)
  set d := orderOf c with hd
  have hcm : c ^ m = 1 := by
    ext; simpa [← hσ0, hχ] using hpow σ0.1
  have hdm : d ∣ m := orderOf_dvd_of_pow_eq_one hcm
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdm hm
  have hall : ∀ σ : G E Ω, σ ∈ Ine (F := E) A → (σ Y / Y) ^ d = 1 := by
    intro σ hσ
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hc ⟨χ ⟨σ, hσ⟩, ⟨σ, hσ⟩, rfl⟩)
    have h1 : (χ ⟨σ, hσ⟩) ^ d = 1 := by
      have := congrArg Subtype.val hj
      simp only [Subgroup.coe_zpow] at this
      rw [← this, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, pow_orderOf_eq_one, one_zpow]
    have h2 := congrArg (fun u : rootsOfUnity m Ω => ((u : Ωˣ) : Ω)) h1
    simpa [hχ] using h2
  set Z := Y ^ d with hZ
  have hZfix : ∀ σ : G E Ω, σ ∈ Ine (F := E) A → σ Z = Z := by
    intro σ hσ
    have e : σ Y = (σ Y / Y) * Y := by field_simp
    rw [hZ, map_pow, e, mul_pow, hall σ hσ, one_mul]
  set n := m / d with hn
  have hnd : d * n = m := Nat.mul_div_cancel' hdm
  have hZn : Z ^ n = ((g : ℕ) : Ω) := by rw [hZ, ← pow_mul, hnd, hY]
  have hn1 : n ≤ 1 := by
    have hZi : IsIntegral E Z := Algebra.IsIntegral.isIntegral Z
    haveI : FiniteDimensional E (IntermediateField.adjoin E {Z}) := IntermediateField.adjoin.finiteDimensional hZi
    set L := IntermediateField.normalClosure E (IntermediateField.adjoin E {Z}) Ω with hLdef
    haveI : NumberField L := NumberField.of_module_finite E L
    have hZL : Z ∈ L := IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self E Z)
    set Z' : L := ⟨Z, hZL⟩ with hZ'
    set K : IntermediateField E L := IntermediateField.adjoin E {Z'} with hK
    haveI : NumberField K := NumberField.of_module_finite E K
    let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring
      (fun x => ReciprocityTheory.Gal.mem_of_isIntegral_int A ((x.isIntegral_coe.map (IsScalarTower.toAlgHom ℤ L Ω))))
    set Q : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f with hQ
    haveI : Q.IsPrime := Ideal.comap_isPrime f _
    have hQmem : ∀ x : 𝓞 L, x ∈ Q ↔ A.valuation (((x : L) : Ω)) < 1 := fun x =>
      Ideal.mem_comap.trans (ValuationSubring.valuation_lt_one_iff A (f x))
    have hfixK : ∀ σ ∈ Ine (F := E) A, ∀ y : K, σ (((y : L) : Ω)) = ((y : L) : Ω) := by
      intro σ hσ y
      have hle : K.toSubalgebra ≤ AlgHom.equalizer ((σ : Ω →ₐ[E] Ω).comp L.val) L.val := by
        rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic Z')]
        refine Algebra.adjoin_le ?_
        rintro _ rfl
        exact hZfix σ hσ
      exact hle y.2
    have e1 := unram_of_fixed E Ω A L K Q hQmem hfixK
    have hunder : (Q.under (𝓞 K)).under (𝓞 E) = v.asIdeal := by
      ext x
      rw [Ideal.under_under, Ideal.mem_comap, hQmem, ← hA x]
      rfl
    set Z'' : K := ⟨Z', IntermediateField.mem_adjoin_simple_self E Z'⟩ with hZ''
    have hZ''n : Z'' ^ n = ((g : ℕ) : K) := by
      apply Subtype.ext; apply Subtype.ext
      simpa using hZn
    exact index_one_root E K v (Q.under (𝓞 K)) hunder e1 g hgv hgv2 n Z'' hZ''n
  have hdm' : d = m := by
    have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro h; rw [h, mul_zero] at hnd; exact hm.ne' hnd.symm)
    have : n = 1 := le_antisymm hn1 hn0
    rw [this, mul_one] at hnd; exact hnd
  have hprim : IsPrimitiveRoot (σ0.1 Y / Y) m := by
    have h1 : orderOf (σ0.1 Y / Y) = m := by
      rw [← hχ, orderOf_units, Subgroup.orderOf_coe, hσ0, ← hd, hdm']
    rw [← h1]; exact IsPrimitiveRoot.orderOf _
  obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one hμ
  refine ⟨σ0.1 ^ i, pow_mem σ0.2 i, ?_⟩
  have := GlobalTheory.TameCoupledEx.ratio_pow hgp hg σ0.2 hm hgm hY i
  rw [hi] at this
  field_simp at this
  rw [this, mul_comm]

end GlobalTheory.TameKummerInertia
