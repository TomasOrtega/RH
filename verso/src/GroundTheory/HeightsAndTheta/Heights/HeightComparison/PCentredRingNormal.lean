import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightCentredRingNormal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PSubringPrimeMaximal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField IsDedekindDomain

namespace CentredRingNormal

variable {L : Type} [Field L] [NumberField L]

omit [NumberField L] in

/- English proof (translation)
Take `⟨p, hp, hpx⟩` from `hx`. Conclude with `⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map, hf]; exact hpx⟩`.
-/
theorem isIntegral_of_comp {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R L] [Algebra R' L]
    (f : R →+* R') (hf : (algebraMap R' L).comp f = algebraMap R L) {x : L}
    (hx : IsIntegral R x) : IsIntegral R' x := by
  obtain ⟨p, hp, hpx⟩ := hx
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map, hf]; exact hpx⟩

/- English proof (translation)
Rewrite using `[Valuation.mem_valuationSubring_iff, FinitePlace.mk_apply, FinitePlace.norm_embedding', NNReal.coe_le_one, ← map_one (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)), (WithZeroMulInt.toNNReal_strictMono (NumberField.HeightOneSpectrum.one_lt_absNorm_nnre …`.
-/
theorem mem_valuationSubring_iff_place (v : HeightOneSpectrum (𝓞 L)) (x : L) :
    x ∈ (v.valuation L).valuationSubring ↔ FinitePlace.mk v x ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, FinitePlace.mk_apply, FinitePlace.norm_embedding',
    NNReal.coe_le_one,
    ← map_one (WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)),
    (WithZeroMulInt.toNNReal_strictMono
      (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le]

/- English proof (translation)
Establish `hint : ∀ a : 𝓞 L, algebraMap (𝓞 L) L a ∈ V` using `fun a ↦ by`. Establish `h : IsIntegral V (algebraMap (𝓞 L) L a)` using `isIntegral_of_comp (Int.castRingHom V) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe a)`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Rewrite using `[← hy]`. Conclude with `y.2`.

Set `φ : 𝓞 L →+* V` to `(algebraMap (𝓞 L) L).codRestrict V hint`. Set `P : Ideal (𝓞 L)` to `(IsLocalRing.maximalIdeal V).comap φ`. Establish `hinv : ∀ s : 𝓞 L, s ∉ P → (algebraMap (𝓞 L) L s)⁻¹ ∈ V` using `fun s hs ↦ by`. Establish `h1 : V.valuation (φ s : L) = 1`. Break down `V.valuation_lt_one_or_eq_one (φ s) with h | h` into its components or cases.

Conclude with `absurd ((V.valuation_lt_one_iff (φ s)).mpr h) hs`. Conclude with `h`. Rewrite using `[← V.valuation_le_one_iff, map_inv₀]`. Express the relevant statement in the definitionally equal form `(V.valuation (φ s : L))⁻¹ ≤ 1`. Rewrite using `[h1, inv_one]`.

Establish `hPne : P ≠ ⊥`. Introduce `hP`. Apply `hV` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [ValuationSubring.mem_top, iff_true]`.

Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 L) x`. Establish `hbP : b ∉ P`. Rewrite using `[hP, Ideal.mem_bot]`. Conclude with `nonZeroDivisors.ne_zero hb`. Rewrite using `[div_eq_mul_inv]`.

Conclude with `mul_mem (hint a) (hinv b hbP)`. Set `v : HeightOneSpectrum (𝓞 L)` to `⟨P, Ideal.comap_isPrime _ _, hPne⟩`. Establish `hle : HeightOneSpectrum.valuationSubringAtPrime L v ≤ V`. Introduce and unpack `x ⟨a, s, hs, rfl⟩`. Conclude with `mul_mem (hint a) (hinv s hs)`.

Use `⟨FinitePlace.mk v, fun x ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← mem_valuationSubring_iff_place, ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := L) v, ValuationSubring.eq_of_le_of_ne_top _ hle hV]`.
-/
theorem exists_place_of_valuationSubring (V : ValuationSubring L) (hV : V ≠ ⊤) :
    ∃ w : FinitePlace L, ∀ x : L, x ∈ V ↔ w x ≤ 1 := by
  have hint : ∀ a : 𝓞 L, algebraMap (𝓞 L) L a ∈ V := fun a ↦ by
    have h : IsIntegral V (algebraMap (𝓞 L) L a) :=
      isIntegral_of_comp (Int.castRingHom V) (RingHom.ext_int _ _) (RingOfIntegers.isIntegral_coe a)
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    rw [← hy]
    exact y.2
  let φ : 𝓞 L →+* V := (algebraMap (𝓞 L) L).codRestrict V hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal V).comap φ
  have hinv : ∀ s : 𝓞 L, s ∉ P → (algebraMap (𝓞 L) L s)⁻¹ ∈ V := fun s hs ↦ by
    have h1 : V.valuation (φ s : L) = 1 := by
      rcases V.valuation_lt_one_or_eq_one (φ s) with h | h
      · exact absurd ((V.valuation_lt_one_iff (φ s)).mpr h) hs
      · exact h
    rw [← V.valuation_le_one_iff, map_inv₀]
    change (V.valuation (φ s : L))⁻¹ ≤ 1
    rw [h1, inv_one]
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hV
    ext x
    simp only [ValuationSubring.mem_top, iff_true]
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 L) x
    have hbP : b ∉ P := by
      rw [hP, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hb
    rw [div_eq_mul_inv]
    exact mul_mem (hint a) (hinv b hbP)
  let v : HeightOneSpectrum (𝓞 L) := ⟨P, Ideal.comap_isPrime _ _, hPne⟩
  have hle : HeightOneSpectrum.valuationSubringAtPrime L v ≤ V := by
    rintro x ⟨a, s, hs, rfl⟩
    exact mul_mem (hint a) (hinv s hs)
  refine ⟨FinitePlace.mk v, fun x ↦ ?_⟩
  rw [← mem_valuationSubring_iff_place,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring (K := L) v,
    ValuationSubring.eq_of_le_of_ne_top _ hle hV]

/- English proof (translation)
Establish `hO : ∀ u : O, w u ≤ 1` using `fun u ↦ hA _ (Subalgebra.algebraMap_mem _ u)`. Set `q : Ideal O` to `{ carrier := {u | w u < 1} zero_mem' := by simp add_mem' := fun {a b} ha hb ↦ by`. Express the relevant statement in the definitionally equal form `w ((a : L) + b) < 1`. Conclude with `(FinitePlace.add_le w _ _).trans_lt (max_lt ha hb)`. Use the proof step `smul_mem' := fun c a ha ↦ by`.

Express the relevant statement in the definitionally equal form `w ((c : L) * a) < 1`. Rewrite using `[map_mul]`. Conclude with `(mul_le_of_le_one_left (apply_nonneg w _) (hO c)).trans_lt ha }`. Establish `hmem : ∀ u : O, u ∈ q ↔ w u < 1` using `fun _ ↦ Iff.rfl`. Establish `hq_prime : q.IsPrime`.

Use `⟨fun h ↦ ?_, fun {a b} hab ↦ ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : O) ∈ q` using `h ▸ Submodule.mem_top`. Rewrite `h1` using `[hmem]`. Simplify using `at h1`. Assume the negation of the conclusion as `hne`.

Rewrite `hne` using `[not_or, hmem, hmem, not_lt, not_lt]`. Rewrite `hab` using `[hmem]`. Express the relevant statement in the definitionally equal form `w ((a : L) * b) < 1 at hab`. Rewrite `hab` using `[map_mul, le_antisymm (hO a) hne.1, le_antisymm (hO b) hne.2, one_mul]`. Conclude with `lt_irrefl _ hab`.

Establish `hq_ne : q ≠ ⊥`. Introduce `hq`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) x`. Establish `hb1 : w (algebraMap O L b) = 1`. Use `le_antisymm (hO b) (not_lt.mp fun h ↦ nonZeroDivisors.ne_zero hb ?_)` and prove the remaining obligations.

Rewrite using `[← Ideal.mem_bot, ← hq]`. Conclude with `h`. Rewrite `hx` using `[map_div₀, hb1, div_one]`. Conclude with `absurd (hO a) (not_le.mpr hx)`. Establish `hq_max : q.IsMaximal` using `SubringPrimeMaximal.proof L O q hq_prime hq_ne`.

Establish `hqm : q ≤ m` using `fun u hu ↦ by`. Assume the negation of the conclusion as `hum`. Establish `hu0 : (u : L) ≠ 0` using `fun h ↦ hum (by rw [show u = 0 from Subtype.ext h]; exact m.zero_mem)`. Establish `hinv : w (u : L)⁻¹ ≤ 1` using `hA _ ⟨1, u, hum, by rw [map_one, one_mul]; rfl⟩`. Establish `hprod : w (u : L) * w (u : L)⁻¹ = 1` using `by rw [← map_mul, mul_inv_cancel₀ hu0, map_one]`.

Establish `hu' : w u < 1` using `hu`. Use polynomial arithmetic with `[apply_nonneg w (u : L), apply_nonneg w (u : L)⁻¹]`. Establish `hqe : q = m` using `hq_max.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hqm`. Use `⟨hO, fun u ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[← hqe]`.

Conclude with `(hmem u).symm`.
-/
theorem absCentredAt_of_le_one (O : Subalgebra ℤ L) [IsFractionRing O L] (m : Ideal O) [m.IsMaximal]
    (w : FinitePlace L)
    (hA : ∀ y ∈ Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors,
      w y ≤ 1)
    (x : L) (hx : 1 < w x) : AbsCentredAt O m fun t ↦ w t := by
  have hO : ∀ u : O, w u ≤ 1 := fun u ↦ hA _ (Subalgebra.algebraMap_mem _ u)
  let q : Ideal O :=
    { carrier := {u | w u < 1}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb ↦ by
        change w ((a : L) + b) < 1
        exact (FinitePlace.add_le w _ _).trans_lt (max_lt ha hb)
      smul_mem' := fun c a ha ↦ by
        change w ((c : L) * a) < 1
        rw [map_mul]
        exact (mul_le_of_le_one_left (apply_nonneg w _) (hO c)).trans_lt ha }
  have hmem : ∀ u : O, u ∈ q ↔ w u < 1 := fun _ ↦ Iff.rfl
  have hq_prime : q.IsPrime := by
    refine ⟨fun h ↦ ?_, fun {a b} hab ↦ ?_⟩
    · have h1 : (1 : O) ∈ q := h ▸ Submodule.mem_top
      rw [hmem] at h1
      simp at h1
    · by_contra hne
      rw [not_or, hmem, hmem, not_lt, not_lt] at hne
      rw [hmem] at hab
      change w ((a : L) * b) < 1 at hab
      rw [map_mul, le_antisymm (hO a) hne.1, le_antisymm (hO b) hne.2, one_mul] at hab
      exact lt_irrefl _ hab
  have hq_ne : q ≠ ⊥ := by
    intro hq
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb1 : w (algebraMap O L b) = 1 := by
      refine le_antisymm (hO b) (not_lt.mp fun h ↦ nonZeroDivisors.ne_zero hb ?_)
      rw [← Ideal.mem_bot, ← hq]
      exact h
    rw [map_div₀, hb1, div_one] at hx
    exact absurd (hO a) (not_le.mpr hx)
  have hq_max : q.IsMaximal := SubringPrimeMaximal.proof L O q hq_prime hq_ne
  have hqm : q ≤ m := fun u hu ↦ by
    by_contra hum
    have hu0 : (u : L) ≠ 0 := fun h ↦ hum (by rw [show u = 0 from Subtype.ext h]; exact m.zero_mem)
    have hinv : w (u : L)⁻¹ ≤ 1 := hA _ ⟨1, u, hum, by rw [map_one, one_mul]; rfl⟩
    have hprod : w (u : L) * w (u : L)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hu0, map_one]
    have hu' : w u < 1 := hu
    nlinarith [apply_nonneg w (u : L), apply_nonneg w (u : L)⁻¹]
  have hqe : q = m := hq_max.eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hqm
  refine ⟨hO, fun u ↦ ?_⟩
  rw [← hqe]
  exact (hmem u).symm

/- English proof (translation)
Introduce `L _ _ O _ _ m _`. Use `set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef`. Establish `hcent : ∀ w : FinitePlace L, AbsCentredAt O m (fun t ↦ w t) → ∀ y ∈ A, w y ≤ 1`. Introduce and unpack `w ⟨hO, hm⟩ y ⟨a, s, hs, rfl⟩`. Establish `hs1 : w (algebraMap O L s) = 1` using `le_antisymm (hO s) (not_lt.mp fun h ↦ hs ((hm s).mp h))`.

Rewrite using `[map_mul, map_inv₀, hs1, inv_one, mul_one]`. Conclude with `hO a`. Use extensionality with `x`. Rewrite using `[mem_placesRing, Subalgebra.mem_toSubring, mem_integralClosure_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx`. Establish `hall : x ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring}, V.1.toSubring`. Use `Subring.mem_iInf.mpr fun ⟨V, hAV⟩ ↦ ?_` and prove the remaining obligations. Distinguish the cases in `hV : V = ⊤`. Establish `h : x ∈ V` using `hV ▸ ValuationSubring.mem_top x`.

Conclude with `h`. Take `⟨w, hw⟩` from `exists_place_of_valuationSubring V hV`. Assume the negation of the conclusion as `hxV`. Establish `hwx : 1 < w x` using `not_le.mp fun h ↦ hxV ((hw x).mpr h)`. Establish `hc` using `absCentredAt_of_le_one O m w (fun y hy ↦ (hw y).mp (hAV hy)) x hwx`.

Conclude with `hxV ((hw x).mpr (hx w hc))`. Rewrite `hall` using `[iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff]`. Use `isIntegral_of_comp ((algebraMap (Subring.closure (A : Set L)) L).codRestrict A fun y ↦ ?_) (RingHom.ext fun _ ↦ rfl) hall` and prove the remaining obligations. Conclude with `(Subring.closure_le (t := A.toSubring)).mpr (fun z hz ↦ hz) y.2`. Introduce `hx w hw`.

Set `v` to `FinitePlace.maximalIdeal w`. Establish `hAV : ∀ y ∈ A, y ∈ (v.valuation L).valuationSubring` using `fun y hy ↦ by`. Rewrite using `[mem_valuationSubring_iff_place, FinitePlace.mk_maximalIdeal]`. Conclude with `hcent w hw y hy`. Establish `hxV : IsIntegral (v.valuation L).valuationSubring x` using `isIntegral_of_comp ((algebraMap A L).codRestrict _ fun y ↦ hAV y y.2) (RingHom.ext fun _ ↦ rfl) hx`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hxV`. Establish `h` using `(mem_valuationSubring_iff_place v x).mp (hy ▸ y.2)`. Rewrite `h` using `[FinitePlace.mk_maximalIdeal]`. Then use the resulting hypothesis.
-/
theorem proof : CentredRingNormal.Statement := by
  intro L _ _ O _ _ m _
  set A := Localization.subalgebra.ofField L m.primeCompl m.primeCompl_le_nonZeroDivisors with hAdef
  have hcent : ∀ w : FinitePlace L, AbsCentredAt O m (fun t ↦ w t) → ∀ y ∈ A, w y ≤ 1 := by
    rintro w ⟨hO, hm⟩ y ⟨a, s, hs, rfl⟩
    have hs1 : w (algebraMap O L s) = 1 := le_antisymm (hO s) (not_lt.mp fun h ↦ hs ((hm s).mp h))
    rw [map_mul, map_inv₀, hs1, inv_one, mul_one]
    exact hO a
  ext x
  rw [mem_placesRing, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · intro hx
    have hall : x ∈ ⨅ V : {V : ValuationSubring L // (A : Set L) ⊆ V.toSubring}, V.1.toSubring := by
      refine Subring.mem_iInf.mpr fun ⟨V, hAV⟩ ↦ ?_
      by_cases hV : V = ⊤
      · have h : x ∈ V := hV ▸ ValuationSubring.mem_top x
        exact h
      obtain ⟨w, hw⟩ := exists_place_of_valuationSubring V hV
      by_contra hxV
      have hwx : 1 < w x := not_le.mp fun h ↦ hxV ((hw x).mpr h)
      have hc := absCentredAt_of_le_one O m w (fun y hy ↦ (hw y).mp (hAV hy)) x hwx
      exact hxV ((hw x).mpr (hx w hc))
    rw [iInf_valuationSubring_superset, Subalgebra.mem_toSubring, mem_integralClosure_iff] at hall
    refine isIntegral_of_comp ((algebraMap (Subring.closure (A : Set L)) L).codRestrict A fun y ↦ ?_) (RingHom.ext fun _ ↦ rfl) hall
    exact (Subring.closure_le (t := A.toSubring)).mpr (fun z hz ↦ hz) y.2
  · intro hx w hw
    let v := FinitePlace.maximalIdeal w
    have hAV : ∀ y ∈ A, y ∈ (v.valuation L).valuationSubring := fun y hy ↦ by
      rw [mem_valuationSubring_iff_place, FinitePlace.mk_maximalIdeal]
      exact hcent w hw y hy
    have hxV : IsIntegral (v.valuation L).valuationSubring x :=
      isIntegral_of_comp ((algebraMap A L).codRestrict _ fun y ↦ hAV y y.2)
        (RingHom.ext fun _ ↦ rfl) hx
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxV
    have h := (mem_valuationSubring_iff_place v x).mp (hy ▸ y.2)
    rwa [FinitePlace.mk_maximalIdeal] at h

end CentredRingNormal

end GroundTheory.Heights₂.Heights
