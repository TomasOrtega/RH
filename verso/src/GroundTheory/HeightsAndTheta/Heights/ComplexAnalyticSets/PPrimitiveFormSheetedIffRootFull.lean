import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedIffRootFull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

/- English proof (translation)
Use `set D : (Fin d → ℂ) × ℂ × ℂ → ℂ := fun v => ∑ m ∈ Finset.range N, v.2.1 ^ m * v.2.2 ^ (N - 1 - m) + ∑ j : Fin N, a j v.1 * ∑ m ∈ Finset.range (j : ℕ), v.2.1 ^ m * v.2.2 ^ ((j : ℕ) - 1 - m) with hDdef`. Establish `hkey : ∀ s T₁ T₂, (T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ)) - (T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ)) = D (s, T₁, T₂) * (T₁ - T₂)`. Introduce `s T₁ T₂`. Rewrite using `[hDdef, add_mul, geom_sum₂_mul, Finset.sum_mul]`. Repeatedly rewrite using `[mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc : ∀ j, ContinuousAt (fun v : (Fin d → ℂ) × ℂ × ℂ => a j v.1) (t, τ, τ)` using `fun j => (hcont j).comp continuousAt_fst`. Establish `hcD : ContinuousAt D (t, τ, τ)`. Rewrite using `[hDdef]`. Use `fun_prop (disch := assumption)`.

Establish `hD0 : D (t, τ, τ) ≠ 0`. Establish `h1` using `hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ) (by`. Simplify `hroot)` using `[Polynomial.eval₂_finsetSum]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [hDdef, geom_sum₂_self, Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, RingHom.id_apply]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff.1 (hcD.eventually_ne hD0)`. Use `⟨ε, hε, fun s hs T₁ T₂ h₁ h₂ hr₁ hr₂ => ?_⟩` and prove the remaining obligations.

Establish `hne : D (s, T₁, T₂) ≠ 0` using `hball (by simp [Prod.dist_eq, hs, h₁, h₂])`. Establish `h` using `hkey s T₁ T₂`. Rewrite `h` using `[hr₁, hr₂, sub_zero, eq_comm]`. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hne)`.
-/
theorem monic_simpleRoot_isolated {d N : ℕ} (a : Fin N → (Fin d → ℂ) → ℂ) (t : Fin d → ℂ) (τ : ℂ)
    (hcont : ∀ j, ContinuousAt (a j) t)
    (hsep : (Polynomial.X ^ N + ∑ j, Polynomial.C (a j t) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable)
    (hroot : τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0) :
    ∃ ε > 0, ∀ s, dist s t < ε → ∀ T₁ T₂ : ℂ, dist T₁ τ < ε → dist T₂ τ < ε →
      T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ) = 0 → T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ) = 0 → T₁ = T₂ := by

  set D : (Fin d → ℂ) × ℂ × ℂ → ℂ := fun v =>
    ∑ m ∈ Finset.range N, v.2.1 ^ m * v.2.2 ^ (N - 1 - m) +
      ∑ j : Fin N, a j v.1 * ∑ m ∈ Finset.range (j : ℕ), v.2.1 ^ m * v.2.2 ^ ((j : ℕ) - 1 - m) with hDdef
  have hkey : ∀ s T₁ T₂, (T₁ ^ N + ∑ j, a j s * T₁ ^ (j : ℕ)) - (T₂ ^ N + ∑ j, a j s * T₂ ^ (j : ℕ)) =
      D (s, T₁, T₂) * (T₁ - T₂) := by
    intro s T₁ T₂
    rw [hDdef, add_mul, geom_sum₂_mul, Finset.sum_mul]
    simp_rw [mul_assoc, geom_sum₂_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  have hc : ∀ j, ContinuousAt (fun v : (Fin d → ℂ) × ℂ × ℂ => a j v.1) (t, τ, τ) :=
    fun j => (hcont j).comp continuousAt_fst
  have hcD : ContinuousAt D (t, τ, τ) := by
    rw [hDdef]
    fun_prop (disch := assumption)
  have hD0 : D (t, τ, τ) ≠ 0 := by
    have h1 := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ) (by
      simpa [Polynomial.eval₂_finsetSum] using hroot)
    convert h1 using 1
    simp only [hDdef, geom_sum₂_self, Polynomial.derivative_add, Polynomial.derivative_X_pow,
      Polynomial.derivative_sum, Polynomial.derivative_C_mul_X_pow, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum, RingHom.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcD.eventually_ne hD0)
  refine ⟨ε, hε, fun s hs T₁ T₂ h₁ h₂ hr₁ hr₂ => ?_⟩
  have hne : D (s, T₁, T₂) ≠ 0 := hball (by simp [Prod.dist_eq, hs, h₁, h₂])
  have h := hkey s T₁ T₂
  rw [hr₁, hr₂, sub_zero, eq_comm] at h
  exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hne)

/- English proof (translation)
Introduce `σ _ X w d A ℓ N a δ q ha hδ hq hP hsep hQ`. Take `⟨UA, hUA, hUAo, hwUA⟩` from `eventually_nhds_iff.1 ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and (hδ.eventually_analyticAt.and ((eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt).and hsep)))`. Take `⟨UX, hUX, hUXo, hwUX⟩` from `eventually_nhds_iff.1 (hP.and (eventually_all.2 hQ))`. Use `set S : Set (σ → ℂ) := UX ∩ A ⁻¹' UA with hSdef`. Establish `hSo : IsOpen S` using `hUXo.inter (hUAo.preimage A.continuous)`.

Use `set D : Set (Fin d → ℂ) := UA ∩ δ ⁻¹' {0}ᶜ with hDdef`. Establish `hDo : IsOpen D` using `ContinuousOn.isOpen_inter_preimage (fun y hy => (hUA y hy).2.1.continuousAt.continuousWithinAt) hUAo isOpen_compl_singleton`. Establish `hrep : ∀ x ∈ X, x ∈ S → δ (A x) ≠ 0 → (fun i => (∑ j, q i j (A x) * ℓ x ^ (j : ℕ)) / δ (A x)) = x`. Introduce `x hxX hxS hδx`. Use function extensionality and compare the values at `i`.

Rewrite using `[← (hUX x hxS.1).2 i hxX, mul_div_cancel_left₀ _ hδx]`. Use `filter_upwards [hSo.mem_nhds ⟨hwUX, hwUA⟩] with z hzS hzX hδz W hWo hzW`. Establish `hzD : A z ∈ D` using `⟨hzS.2, hδz⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨O, V, g, hOo, hVo, hzV, hg, hAg, hXV⟩`.

Establish `hzg : z ∈ g '' O` using `by rw [← hXV]; exact ⟨hzX, hzV⟩`. Take `⟨t₀, ht₀, hgt₀⟩` from `hzg`. Establish `hAz : A z = t₀` using `by rw [← hgt₀, hAg t₀ ht₀]`. Substitute `hAz` using the available equality. Establish `hO'o : IsOpen ((O ∩ g ⁻¹' (S ∩ W)) ∩ D)` using `(hg.continuousOn.isOpen_inter_preimage hOo (hSo.inter hWo)).inter hDo`.

Use `⟨(O ∩ g ⁻¹' (S ∩ W)) ∩ D, fun s => ℓ (g s), hO'o, ⟨⟨ht₀, by rw [Set.mem_preimage, hgt₀]; exact ⟨hzS, hzW⟩⟩, hzD⟩, fun s hs => (ℓ.analyticAt (g s)).comp (hg s hs.1.1), by simp only [hgt₀], fun s hs => ?_⟩` and prove the remaining obligations. Establish `hgXV : g s ∈ X ∩ V` using `by rw [hXV]; exact Set.mem_image_of_mem g hs.1.1`. Establish `hgs : (fun i => (∑ j, q i j s * ℓ (g s) ^ (j : ℕ)) / δ s) = g s`. Establish `e` using `hrep (g s) hgXV.1 hs.1.2.1 (by rw [hAg s hs.1.1]; exact hs.2.2)`. Rewrite `e` using `[hAg s hs.1.1]`. Then use the resulting hypothesis.

Use `beta_reduce`. Rewrite using `[hgs]`. Conclude with `⟨⟨hgXV.1, hs.1.2.2⟩, hAg s hs.1.1, rfl⟩`. Introduce and unpack `⟨O, r, hOo, hzO, hr, hrz, hfull⟩ set H : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hHdef`. Establish `hfull' : ∀ s ∈ O, H s ∈ X ∩ W ∧ A (H s) = s ∧ ℓ (H s) = r s` using `hfull`.

Establish `hH : AnalyticOnNhd ℂ H (O ∩ D)`. Introduce `s hs`. Use `AnalyticAt.pi fun i => ?_` and prove the remaining obligations. Conclude with `(Finset.analyticAt_fun_sum _ fun j _ => ((hUA s hs.2.1).2.2.1 i j).mul ((hr s hs.1).pow _)).div (hUA s hs.2.1).2.1 hs.2.2`. Establish `hHz : H (A z) = z`.

Establish `e` using `hrep z hzX hzS hδz`. Rewrite `e` using `[← hrz]`. Conclude with `e`. Take `⟨ε, hε, hiso⟩` from `monic_simpleRoot_isolated a (A z) (ℓ z) (fun j => ((hUA (A z) hzS.2).1 j).continuousAt) ((hUA (A z) hzS.2).2.2.2 hδz) ((hUX z hzS.1).1 hzX)`. Use `set B : Set (σ → ℂ) := S ∩ ℓ ⁻¹' Metric.ball (ℓ z) ε ∩ A ⁻¹' Metric.ball (A z) ε with hBdef`.

Establish `hBo : IsOpen B` using `(hSo.inter (Metric.isOpen_ball.preimage ℓ.continuous)).inter (Metric.isOpen_ball.preimage A.continuous)`. Establish `hzB : z ∈ B` using `⟨⟨hzS, Metric.mem_ball_self hε⟩, Metric.mem_ball_self hε⟩`. Establish `hO₁o : IsOpen ((O ∩ D) ∩ H ⁻¹' B)` using `hH.continuousOn.isOpen_inter_preimage (hOo.inter hDo) hBo`. Establish `hzO₁ : A z ∈ (O ∩ D) ∩ H ⁻¹' B` using `⟨⟨hzO, hzD⟩, by rw [Set.mem_preimage, hHz]; exact hzB⟩`. Use `⟨(O ∩ D) ∩ H ⁻¹' B, B ∩ A ⁻¹' ((O ∩ D) ∩ H ⁻¹' B), H, hO₁o, hBo.inter (hO₁o.preimage A.continuous), ⟨hzB, hzO₁⟩, fun s hs => hH s hs.1, fun s hs => (hfull' s hs.1.1).2.1, ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxX, hxB, hxO⟩`. Use `⟨A x, hxO, ?_⟩` and prove the remaining obligations. Establish `hs` using `hfull' (A x) hxO.1.1`.

Establish `hHB : H (A x) ∈ B` using `hxO.2`. Establish `hroot : r (A x) ^ N + ∑ j, a j (A x) * r (A x) ^ (j : ℕ) = 0`. Establish `e` using `(hUX _ hHB.1.1.1).1 hs.1.1`. Rewrite `e` using `[hs.2.1, hs.2.2]`. Then use the resulting hypothesis. Establish `hℓx : ℓ x = r (A x)` using `hiso (A x) hxB.2 (ℓ x) (r (A x)) hxB.1.2 (by rw [← hs.2.2]; exact hHB.1.2) ((hUX x hxB.1.1.1).1 hxX) hroot`.

Establish `e` using `hrep x hxX hxB.1.1 hxO.1.2.2`. Rewrite `e` using `[hℓx]`. Conclude with `e`. Introduce and unpack `⟨s, hs, rfl⟩`. Conclude with `⟨(hfull' s hs.1.1).1.1, hs.2, by rw [Set.mem_preimage, (hfull' s hs.1.1).2.1]; exact hs⟩`.
-/
theorem PrimitiveFormSheetedIffRootFull.proof : PrimitiveFormSheetedIffRootFull.Statement := by
  intro σ _ X w d A ℓ N a δ q ha hδ hq hP hsep hQ

  obtain ⟨UA, hUA, hUAo, hwUA⟩ := eventually_nhds_iff.1
    ((eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((eventually_all.2 fun i => eventually_all.2 fun j => (hq i j).eventually_analyticAt).and hsep)))

  obtain ⟨UX, hUX, hUXo, hwUX⟩ := eventually_nhds_iff.1 (hP.and (eventually_all.2 hQ))
  set S : Set (σ → ℂ) := UX ∩ A ⁻¹' UA with hSdef
  have hSo : IsOpen S := hUXo.inter (hUAo.preimage A.continuous)
  set D : Set (Fin d → ℂ) := UA ∩ δ ⁻¹' {0}ᶜ with hDdef
  have hDo : IsOpen D := ContinuousOn.isOpen_inter_preimage
    (fun y hy => (hUA y hy).2.1.continuousAt.continuousWithinAt) hUAo isOpen_compl_singleton

  have hrep : ∀ x ∈ X, x ∈ S → δ (A x) ≠ 0 →
      (fun i => (∑ j, q i j (A x) * ℓ x ^ (j : ℕ)) / δ (A x)) = x := by
    intro x hxX hxS hδx
    funext i
    rw [← (hUX x hxS.1).2 i hxX, mul_div_cancel_left₀ _ hδx]
  filter_upwards [hSo.mem_nhds ⟨hwUX, hwUA⟩] with z hzS hzX hδz W hWo hzW
  have hzD : A z ∈ D := ⟨hzS.2, hδz⟩
  constructor
  · rintro ⟨O, V, g, hOo, hVo, hzV, hg, hAg, hXV⟩
    have hzg : z ∈ g '' O := by rw [← hXV]; exact ⟨hzX, hzV⟩
    obtain ⟨t₀, ht₀, hgt₀⟩ := hzg
    have hAz : A z = t₀ := by rw [← hgt₀, hAg t₀ ht₀]
    subst hAz
    have hO'o : IsOpen ((O ∩ g ⁻¹' (S ∩ W)) ∩ D) :=
      (hg.continuousOn.isOpen_inter_preimage hOo (hSo.inter hWo)).inter hDo
    refine ⟨(O ∩ g ⁻¹' (S ∩ W)) ∩ D, fun s => ℓ (g s), hO'o,
      ⟨⟨ht₀, by rw [Set.mem_preimage, hgt₀]; exact ⟨hzS, hzW⟩⟩, hzD⟩,
      fun s hs => (ℓ.analyticAt (g s)).comp (hg s hs.1.1), by simp only [hgt₀], fun s hs => ?_⟩
    have hgXV : g s ∈ X ∩ V := by rw [hXV]; exact Set.mem_image_of_mem g hs.1.1
    have hgs : (fun i => (∑ j, q i j s * ℓ (g s) ^ (j : ℕ)) / δ s) = g s := by
      have e := hrep (g s) hgXV.1 hs.1.2.1 (by rw [hAg s hs.1.1]; exact hs.2.2)
      rwa [hAg s hs.1.1] at e
    beta_reduce
    rw [hgs]
    exact ⟨⟨hgXV.1, hs.1.2.2⟩, hAg s hs.1.1, rfl⟩
  · rintro ⟨O, r, hOo, hzO, hr, hrz, hfull⟩
    set H : (Fin d → ℂ) → σ → ℂ := fun s i => (∑ j, q i j s * r s ^ (j : ℕ)) / δ s with hHdef
    have hfull' : ∀ s ∈ O, H s ∈ X ∩ W ∧ A (H s) = s ∧ ℓ (H s) = r s := hfull
    have hH : AnalyticOnNhd ℂ H (O ∩ D) := by
      intro s hs
      refine AnalyticAt.pi fun i => ?_
      exact (Finset.analyticAt_fun_sum _ fun j _ =>
        ((hUA s hs.2.1).2.2.1 i j).mul ((hr s hs.1).pow _)).div (hUA s hs.2.1).2.1 hs.2.2
    have hHz : H (A z) = z := by
      have e := hrep z hzX hzS hδz
      rw [← hrz] at e
      exact e
    obtain ⟨ε, hε, hiso⟩ := monic_simpleRoot_isolated a (A z) (ℓ z)
      (fun j => ((hUA (A z) hzS.2).1 j).continuousAt) ((hUA (A z) hzS.2).2.2.2 hδz) ((hUX z hzS.1).1 hzX)
    set B : Set (σ → ℂ) := S ∩ ℓ ⁻¹' Metric.ball (ℓ z) ε ∩ A ⁻¹' Metric.ball (A z) ε with hBdef
    have hBo : IsOpen B :=
      (hSo.inter (Metric.isOpen_ball.preimage ℓ.continuous)).inter (Metric.isOpen_ball.preimage A.continuous)
    have hzB : z ∈ B := ⟨⟨hzS, Metric.mem_ball_self hε⟩, Metric.mem_ball_self hε⟩
    have hO₁o : IsOpen ((O ∩ D) ∩ H ⁻¹' B) := hH.continuousOn.isOpen_inter_preimage (hOo.inter hDo) hBo
    have hzO₁ : A z ∈ (O ∩ D) ∩ H ⁻¹' B := ⟨⟨hzO, hzD⟩, by rw [Set.mem_preimage, hHz]; exact hzB⟩
    refine ⟨(O ∩ D) ∩ H ⁻¹' B, B ∩ A ⁻¹' ((O ∩ D) ∩ H ⁻¹' B), H, hO₁o,
      hBo.inter (hO₁o.preimage A.continuous), ⟨hzB, hzO₁⟩, fun s hs => hH s hs.1,
      fun s hs => (hfull' s hs.1.1).2.1, ?_⟩
    ext x
    constructor
    · rintro ⟨hxX, hxB, hxO⟩
      refine ⟨A x, hxO, ?_⟩
      have hs := hfull' (A x) hxO.1.1
      have hHB : H (A x) ∈ B := hxO.2

      have hroot : r (A x) ^ N + ∑ j, a j (A x) * r (A x) ^ (j : ℕ) = 0 := by
        have e := (hUX _ hHB.1.1.1).1 hs.1.1
        rwa [hs.2.1, hs.2.2] at e
      have hℓx : ℓ x = r (A x) := hiso (A x) hxB.2 (ℓ x) (r (A x)) hxB.1.2
        (by rw [← hs.2.2]; exact hHB.1.2) ((hUX x hxB.1.1.1).1 hxX) hroot
      have e := hrep x hxX hxB.1.1 hxO.1.2.2
      rw [hℓx] at e
      exact e
    · rintro ⟨s, hs, rfl⟩
      exact ⟨(hfull' s hs.1.1).1.1, hs.2, by rw [Set.mem_preimage, (hfull' s hs.1.1).2.1]; exact hs⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
