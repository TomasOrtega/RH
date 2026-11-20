import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalFieldIso

/- English proof (translation)
Introduce `k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' χ χ' e hψ hχ he`. Take `⟨_, hv1, hord, hres, _⟩` from `continuous_iso_keeps_valuation k k' i hi`. Use `set u : kˣ →* k'ˣ := Units.map i.toRingHom.toMonoidHom with hu`. Establish `hcoe : ∀ x : kˣ, ((u x : k'ˣ) : k') = i x` using `fun x => rfl`. Establish `hle : ∀ x y : k, valuation k' (i x) ≤ valuation k' (i y) ↔ valuation k x ≤ valuation k y`.

Introduce `x y`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Simplify using the standard rewrite rules. Establish `hy' : i y ≠ 0` using `by simpa using hy`.

Establish `h1` using `hv1 (x / y)`. Rewrite `h1` using `[map_div₀, map_div₀, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hy'), div_le_one₀ ((Valuation.pos_iff _).2 hy)]`. Conclude with `h1`. Establish `hsurj : ∀ x' : k'ˣ, ∃ x : kˣ, u x = x'` using `fun x' => ⟨Units.map i.symm.toRingHom.toMonoidHom x', by ext; simp [hu]⟩`. Establish `huinj : Function.Injective u` using `fun x y h => by ext; exact i.injective (by simpa [hcoe] using congrArg (fun z : k'ˣ => (z : k')) h)`.

Establish `hunif : ∀ a : ℕ, ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ valuation k' (i p) = uniformizer k' ^ a`. Introduce `a`. Take `⟨p, hp, hp'⟩` from `exists_unit_pow k a`. Take `⟨q, hq, hq'⟩` from `exists_unit_pow k' a`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hq, ← hcoe, valuation_eq_iff_ord, hord, hp', hq']`. Establish `hfilt : ∀ (x : kˣ) (b : ℕ), u x ∈ unitFilt k' b ↔ x ∈ unitFilt k b`. Introduce `x b`. Take `⟨p, hp, hp'⟩` from `hunif b`. Simplify using `only [unitFilt, Set.mem_setOf_eq]`.

Establish `e1 : valuation k' ((u x : k'ˣ) : k') = 1 ↔ valuation k (x : k) = 1`. Rewrite using `[← ord_eq_zero_iff, ← ord_eq_zero_iff, hord]`. Establish `e2 : valuation k' (((u x : k'ˣ) : k') - 1) ≤ uniformizer k' ^ b ↔ valuation k ((x : k) - 1) ≤ uniformizer k ^ b`. Establish `hs : i ((x : k) - 1) = i x - 1` using `by rw [map_sub, map_one]`. Rewrite using `[← hp, ← hp', hcoe, ← hle, hs]`.

Rewrite using `[e1, e2]`. Take `⟨c, a, R, hc, ha, hR, rfl⟩` from `he`. Use `⟨u c, a, R.image u, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x'`. Take `⟨x, rfl⟩` from `i.surjective x'`.

Rewrite using `[hcoe, hle, ← hc x]`. Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Rewrite using `[← hψ]`. Conclude with `h (i y) ((hle y x).2 hy)`.

Introduce `h y' hy'`. Take `⟨y, rfl⟩` from `i.surjective y'`. Rewrite using `[hψ]`. Conclude with `h y ((hle y x).1 hy')`. Use `⟨fun x' hx' => ?_, fun b hb => ?_⟩` and prove the remaining obligations.

Take `⟨x, rfl⟩` from `hsurj x'`. Rewrite using `[hχ]`. Conclude with `ha.1 x ((hfilt x a).1 hx')`. Take `⟨x, hx, hx'⟩` from `ha.2 b hb`. Conclude with `⟨u x, (hfilt x b).2 hx, by rw [hχ]; exact hx'⟩`.

Use `⟨fun r' hr' => ?_, fun y' hy' => ?_⟩` and prove the remaining obligations. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hr'`. Rewrite using `[hord, hord]`. Conclude with `hR.1 r hr`. Take `⟨y, rfl⟩` from `hsurj y'`.

Rewrite `hy'` using `[hord, hord]`. Take `⟨r, ⟨hr, hrv⟩, hru⟩` from `hR.2 y hy'`. Use `⟨u r, ⟨Finset.mem_image_of_mem u hr, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hcoe, hcoe, hcoe, ← map_sub i, hle]`. Conclude with `hrv`.

Introduce and unpack `r' ⟨hr', hr'v⟩`. Take `⟨r0, hr0, rfl⟩` from `Finset.mem_image.1 hr'`. Rewrite `hr'v` using `[hcoe, hcoe, hcoe, ← map_sub i, hle]`. Rewrite using `[hru r0 ⟨hr0, hr'v⟩]`. Rewrite using `[hres, Finset.sum_image (fun x _ y _ h => huinj h)]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hχ, hcoe, hψ]`.
-/
theorem isTateEps_transport : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → ∀ (ψ : AddChar k Circle) (ψ' : AddChar k' Circle) (χ : kˣ →* ℂˣ) (χ' : k'ˣ →* ℂˣ) (e : ℂ), (∀ x, ψ' (i x) = ψ x) → (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → IsTateEps ψ χ e → IsTateEps ψ' χ' e := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi ψ ψ' χ χ' e hψ hχ he
  classical
  obtain ⟨_, hv1, hord, hres, _⟩ := continuous_iso_keeps_valuation k k' i hi
  set u : kˣ →* k'ˣ := Units.map i.toRingHom.toMonoidHom with hu
  have hcoe : ∀ x : kˣ, ((u x : k'ˣ) : k') = i x := fun x => rfl
  have hle : ∀ x y : k, valuation k' (i x) ≤ valuation k' (i y) ↔ valuation k x ≤ valuation k y := by
    intro x y
    by_cases hy : y = 0
    · subst hy
      simp
    · have hy' : i y ≠ 0 := by simpa using hy
      have h1 := hv1 (x / y)
      rw [map_div₀, map_div₀, map_div₀, div_le_one₀ ((Valuation.pos_iff _).2 hy'),
        div_le_one₀ ((Valuation.pos_iff _).2 hy)] at h1
      exact h1
  have hsurj : ∀ x' : k'ˣ, ∃ x : kˣ, u x = x' := fun x' =>
    ⟨Units.map i.symm.toRingHom.toMonoidHom x', by ext; simp [hu]⟩
  have huinj : Function.Injective u := fun x y h => by
    ext; exact i.injective (by simpa [hcoe] using congrArg (fun z : k'ˣ => (z : k')) h)
  have hunif : ∀ a : ℕ, ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧
      valuation k' (i p) = uniformizer k' ^ a := by
    intro a
    obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
    obtain ⟨q, hq, hq'⟩ := exists_unit_pow k' a
    refine ⟨p, hp, ?_⟩
    rw [← hq, ← hcoe, valuation_eq_iff_ord, hord, hp', hq']
  have hfilt : ∀ (x : kˣ) (b : ℕ), u x ∈ unitFilt k' b ↔ x ∈ unitFilt k b := by
    intro x b
    obtain ⟨p, hp, hp'⟩ := hunif b
    simp only [unitFilt, Set.mem_setOf_eq]
    have e1 : valuation k' ((u x : k'ˣ) : k') = 1 ↔ valuation k (x : k) = 1 := by
      rw [← ord_eq_zero_iff, ← ord_eq_zero_iff, hord]
    have e2 : valuation k' (((u x : k'ˣ) : k') - 1) ≤ uniformizer k' ^ b ↔
        valuation k ((x : k) - 1) ≤ uniformizer k ^ b := by
      have hs : i ((x : k) - 1) = i x - 1 := by rw [map_sub, map_one]
      rw [← hp, ← hp', hcoe, ← hle, hs]
    rw [e1, e2]
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := he
  refine ⟨u c, a, R.image u, ?_, ?_, ?_, ?_⟩
  · intro x'
    obtain ⟨x, rfl⟩ := i.surjective x'
    rw [hcoe, hle, ← hc x]
    constructor
    · intro h y hy
      rw [← hψ]
      exact h (i y) ((hle y x).2 hy)
    · intro h y' hy'
      obtain ⟨y, rfl⟩ := i.surjective y'
      rw [hψ]
      exact h y ((hle y x).1 hy')
  · refine ⟨fun x' hx' => ?_, fun b hb => ?_⟩
    · obtain ⟨x, rfl⟩ := hsurj x'
      rw [hχ]
      exact ha.1 x ((hfilt x a).1 hx')
    · obtain ⟨x, hx, hx'⟩ := ha.2 b hb
      exact ⟨u x, (hfilt x b).2 hx, by rw [hχ]; exact hx'⟩
  · refine ⟨fun r' hr' => ?_, fun y' hy' => ?_⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hr'
      rw [hord, hord]
      exact hR.1 r hr
    · obtain ⟨y, rfl⟩ := hsurj y'
      rw [hord, hord] at hy'
      obtain ⟨r, ⟨hr, hrv⟩, hru⟩ := hR.2 y hy'
      refine ⟨u r, ⟨Finset.mem_image_of_mem u hr, ?_⟩, ?_⟩
      · rw [hcoe, hcoe, hcoe, ← map_sub i, hle]
        exact hrv
      · rintro r' ⟨hr', hr'v⟩
        obtain ⟨r0, hr0, rfl⟩ := Finset.mem_image.1 hr'
        rw [hcoe, hcoe, hcoe, ← map_sub i, hle] at hr'v
        rw [hru r0 ⟨hr0, hr'v⟩]
  · rw [hres, Finset.sum_image (fun x _ y _ h => huinj h)]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hχ, hcoe, hψ]

end GlobalTheory.LocalFieldIso
