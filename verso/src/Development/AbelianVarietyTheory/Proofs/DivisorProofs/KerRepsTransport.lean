import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTrSelf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

/- English proof (translation)
Introduce `K _ ι Λ₀ Λ₁ T a S hT ha hmul hS`. Establish `hιa : ι a ≠ 0` using `(map_ne_zero ι).mpr ha`. Take `⟨hS1, hS2, hS3⟩` from `hS`. Establish `hex : ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ T k k'`. Introduce `P hP`.

Take `⟨b, hb⟩` from `hT.rat₀ _ (hS1 P hP).1`. Take `⟨k', hk'⟩` from `hT.left (b / a)`. Use `⟨b / a, k', ?_, hk'⟩` and prove the remaining obligations. Rewrite using `[map_div₀, hb]`. Clear the denominators using the available nonvanishing facts.

Use `choose! k k' hk hT' using hex`. Use `set φ : ℂ → ℂ := fun P => ι (k' P) with hφ`. Establish `himg : ∀ P ∈ S, ι a * φ P ∈ Λ₁.lattice ∧ φ P ∉ Λ₁.lattice`. Introduce `P hP`. Establish `h1` using `hT.mem_iff _ _ (hmul _ _ (hT' P hP))`.

Establish `h2` using `hT.mem_iff _ _ (hT' P hP)`. Rewrite `h1` using `[map_mul, map_mul, hk P hP]`. Rewrite `h2` using `[hk P hP]`. Conclude with `⟨h1.mp (hS1 P hP).1, fun h => (hS1 P hP).2 (h2.mpr h)⟩`. Establish `hdiff : ∀ P ∈ S, ∀ Q ∈ S, φ P - φ Q ∈ Λ₁.lattice → P = Q`.

Introduce `P hP Q hQ h`. Establish `h1` using `hT.mem_iff _ _ (hT.sub _ _ _ _ (hT' P hP) (hT' Q hQ))`. Rewrite `h1` using `[map_sub, map_sub, hk P hP, hk Q hQ]`. Conclude with `hS2 P hP Q hQ (h1.mpr h)`. Use `⟨φ, S.image φ, ⟨?_, ?_, ?_⟩, ⟨fun P hP => Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hP), fun P hP Q hQ h => hdiff P hP Q hQ (by rw [h, sub_self]; exact zero_mem _), ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `P' hP'`. Take `⟨P, hP, rfl⟩` from `Finset.mem_image.mp hP'`. Conclude with `himg P hP`. Introduce `P' hP' Q' hQ' h`. Take `⟨P, hP, rfl⟩` from `Finset.mem_image.mp hP'`.

Take `⟨Q, hQ, rfl⟩` from `Finset.mem_image.mp hQ'`. Rewrite using `[hdiff P hP Q hQ h]`. Introduce `z hz hz'`. Take `⟨c, hc⟩` from `hT.rat₁ _ hz`. Establish `hzc : ι (c / a) = z` using `by rw [map_div₀, hc]; field_simp`.

Take `⟨m, hm⟩` from `hT.right (c / a)`. Establish `h1` using `hT.mem_iff _ _ (hmul _ _ hm)`. Establish `h2` using `hT.mem_iff _ _ hm`. Rewrite `h1` using `[map_mul, map_mul, hzc]`. Rewrite `h2` using `[hzc]`.

Take `⟨P, hP, hmP⟩` from `hS3 (ι m) (h1.mpr hz) (fun h => hz' (h2.mp h))`. Use `⟨φ P, Finset.mem_image_of_mem φ hP, ?_⟩` and prove the remaining obligations. Establish `h3` using `hT.mem_iff _ _ (hT.sub _ _ _ _ hm (hT' P hP))`. Rewrite `h3` using `[map_sub, map_sub, hk P hP, hzc]`. Conclude with `h3.mp hmP`.

Introduce `P' hP'`. Take `⟨P, hP, rfl⟩` from `Finset.mem_image.mp (Finset.mem_coe.mp hP')`. Conclude with `⟨P, hP, rfl⟩`. Introduce `P hP`. Conclude with `⟨k P, k' P, hk P hP, rfl, hT' P hP⟩`.
-/
theorem kerReps_transport : ∀ (K : Type) [Field K] (ι : K →+* ℂ) (Λ₀ Λ₁ : PeriodPair) (T : K → K → Prop) (a : K) (S : Finset ℂ), IsTr ι Λ₀ Λ₁ T → a ≠ 0 → (∀ x x', T x x' → T (a * x) (a * x')) → IsKerReps Λ₀ (ι a) S → ∃ (φ : ℂ → ℂ) (S' : Finset ℂ), IsKerReps Λ₁ (ι a) S' ∧ Set.BijOn φ S S' ∧ ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ ι k' = φ P ∧ T k k' := by
  intro K _ ι Λ₀ Λ₁ T a S hT ha hmul hS
  classical
  have hιa : ι a ≠ 0 := (map_ne_zero ι).mpr ha
  obtain ⟨hS1, hS2, hS3⟩ := hS

  have hex : ∀ P ∈ S, ∃ k k' : K, ι k = P ∧ T k k' := by
    intro P hP
    obtain ⟨b, hb⟩ := hT.rat₀ _ (hS1 P hP).1
    obtain ⟨k', hk'⟩ := hT.left (b / a)
    refine ⟨b / a, k', ?_, hk'⟩
    rw [map_div₀, hb]; field_simp
  choose! k k' hk hT' using hex
  set φ : ℂ → ℂ := fun P => ι (k' P) with hφ

  have himg : ∀ P ∈ S, ι a * φ P ∈ Λ₁.lattice ∧ φ P ∉ Λ₁.lattice := by
    intro P hP
    have h1 := hT.mem_iff _ _ (hmul _ _ (hT' P hP))
    have h2 := hT.mem_iff _ _ (hT' P hP)
    rw [map_mul, map_mul, hk P hP] at h1
    rw [hk P hP] at h2
    exact ⟨h1.mp (hS1 P hP).1, fun h => (hS1 P hP).2 (h2.mpr h)⟩
  have hdiff : ∀ P ∈ S, ∀ Q ∈ S, φ P - φ Q ∈ Λ₁.lattice → P = Q := by
    intro P hP Q hQ h
    have h1 := hT.mem_iff _ _ (hT.sub _ _ _ _ (hT' P hP) (hT' Q hQ))
    rw [map_sub, map_sub, hk P hP, hk Q hQ] at h1
    exact hS2 P hP Q hQ (h1.mpr h)
  refine ⟨φ, S.image φ, ⟨?_, ?_, ?_⟩, ⟨fun P hP => Finset.mem_coe.mpr (Finset.mem_image_of_mem φ hP),
    fun P hP Q hQ h => hdiff P hP Q hQ (by rw [h, sub_self]; exact zero_mem _), ?_⟩, ?_⟩
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    exact himg P hP
  · intro P' hP' Q' hQ' h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hQ'
    rw [hdiff P hP Q hQ h]
  · intro z hz hz'
    obtain ⟨c, hc⟩ := hT.rat₁ _ hz
    have hzc : ι (c / a) = z := by rw [map_div₀, hc]; field_simp
    obtain ⟨m, hm⟩ := hT.right (c / a)
    have h1 := hT.mem_iff _ _ (hmul _ _ hm)
    have h2 := hT.mem_iff _ _ hm
    rw [map_mul, map_mul, hzc] at h1
    rw [hzc] at h2
    obtain ⟨P, hP, hmP⟩ := hS3 (ι m) (h1.mpr hz) (fun h => hz' (h2.mp h))
    refine ⟨φ P, Finset.mem_image_of_mem φ hP, ?_⟩
    have h3 := hT.mem_iff _ _ (hT.sub _ _ _ _ hm (hT' P hP))
    rw [map_sub, map_sub, hk P hP, hzc] at h3
    exact h3.mp hmP
  · intro P' hP'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hP')
    exact ⟨P, hP, rfl⟩
  · intro P hP
    exact ⟨k P, k' P, hk P hP, rfl, hT' P hP⟩

end GlobalTheory.WpFam
