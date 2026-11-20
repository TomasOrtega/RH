import Mathlib
import Formalism.UnipotentAdelicQuotients.SmComplete
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtExpMulExpOfFiniteDimensional
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothLog
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace GlobalTheory.CompanionTheory.ClosedSubgroup

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using h1`. Consider the case `succ m ih => rw [pow_succ]`. Conclude with `hmul _ ih _ hg`.
-/
theorem pow_mem_of_mul_closed {G : Set A} (h1 : (1 : A) ∈ G) (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    {g : A} (hg : g ∈ G) (m : ℕ) : g ^ m ∈ G := by
  induction m with
  | zero => simpa using h1
  | succ m ih => rw [pow_succ]; exact hmul _ ih _ hg

/- English proof (translation)
Use `haveI : CompleteSpace A := FiniteDimensional.complete ℝ A`. Use `letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A`. Take `⟨h, hh, hhg, -⟩` from `hinv _ hx`. Establish `hone : NormedSpace.exp x * NormedSpace.exp (-x) = 1`. Rewrite using `[← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl x)), add_neg_cancel, NormedSpace.exp_zero]`.

Establish `heq : h = NormedSpace.exp (-x)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `heq ▸ hh`.
-/
theorem exp_neg_mem {G : Set A} (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1) {x : A}
    (hx : NormedSpace.exp x ∈ G) : NormedSpace.exp (-x) ∈ G := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨h, hh, hhg, -⟩ := hinv _ hx
  have hone : NormedSpace.exp x * NormedSpace.exp (-x) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl x)), add_neg_cancel,
      NormedSpace.exp_zero]
  have heq : h = NormedSpace.exp (-x) := by
    calc h = h * (NormedSpace.exp x * NormedSpace.exp (-x)) := by rw [hone, mul_one]
      _ = NormedSpace.exp (-x) := by rw [← mul_assoc, hhg, one_mul]
  exact heq ▸ hh

/- English proof (translation)
Use `haveI : CompleteSpace A := FiniteDimensional.complete ℝ A`. Use `letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A`. Establish `hm : Tendsto (fun k => (⌊t / ε k⌋₊ : ℝ) * ε k) atTop (𝓝 t)`. Establish `hlo : ∀ k, t - ε k ≤ (⌊t / ε k⌋₊ : ℝ) * ε k`. Introduce `k`.

Establish `h3` using `Nat.lt_floor_add_one (t / ε k)`. Establish `h2 : t / ε k * ε k = t` using `div_mul_cancel₀ _ (hε0 k).ne'`. Use polynomial arithmetic with `[hε0 k]`. Establish `hhi : ∀ k, (⌊t / ε k⌋₊ : ℝ) * ε k ≤ t`. Introduce `k`.

Establish `h3` using `Nat.floor_le (div_nonneg ht (hε0 k).le)`. Establish `h2 : t / ε k * ε k = t` using `div_mul_cancel₀ _ (hε0 k).ne'`. Use polynomial arithmetic with `[hε0 k]`. Establish `hl : Tendsto (fun k => t - ε k) atTop (𝓝 t)`. Simplify using `using (tendsto_const_nhds (x := t)).sub hε`.

Conclude with `tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hhi`. Establish `hlim : Tendsto (fun k => NormedSpace.exp (((⌊t / ε k⌋₊ : ℝ) * ε k) • a k)) atTop (𝓝 (NormedSpace.exp (t • Y)))` using `(NormedSpace.exp_continuous.tendsto _).comp (hm.smul ha)`. Use `hc.mem_of_tendsto hlim (Eventually.of_forall fun k => ?_)` and prove the remaining obligations. Establish `hk : ((⌊t / ε k⌋₊ : ℝ) * ε k) • a k = ⌊t / ε k⌋₊ • (ε k • a k)`. Rewrite using `[mul_smul, Nat.cast_smul_eq_nsmul]`.

Rewrite using `[hk, NormedSpace.exp_nsmul]`. Conclude with `pow_mem_of_mul_closed h1 hmul (hG k) _`.
-/
theorem exp_smul_limit_mem {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) {ε : ℕ → ℝ} {a : ℕ → A} {Y : A}
    (hε0 : ∀ k, 0 < ε k) (hε : Tendsto ε atTop (𝓝 0)) (ha : Tendsto a atTop (𝓝 Y))
    (hG : ∀ k, NormedSpace.exp (ε k • a k) ∈ G) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp (t • Y) ∈ G := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hm : Tendsto (fun k => (⌊t / ε k⌋₊ : ℝ) * ε k) atTop (𝓝 t) := by
    have hlo : ∀ k, t - ε k ≤ (⌊t / ε k⌋₊ : ℝ) * ε k := by
      intro k
      have h3 := Nat.lt_floor_add_one (t / ε k)
      have h2 : t / ε k * ε k = t := div_mul_cancel₀ _ (hε0 k).ne'
      nlinarith [hε0 k]
    have hhi : ∀ k, (⌊t / ε k⌋₊ : ℝ) * ε k ≤ t := by
      intro k
      have h3 := Nat.floor_le (div_nonneg ht (hε0 k).le)
      have h2 : t / ε k * ε k = t := div_mul_cancel₀ _ (hε0 k).ne'
      nlinarith [hε0 k]
    have hl : Tendsto (fun k => t - ε k) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).sub hε
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlo hhi
  have hlim : Tendsto (fun k => NormedSpace.exp (((⌊t / ε k⌋₊ : ℝ) * ε k) • a k)) atTop
      (𝓝 (NormedSpace.exp (t • Y))) :=
    (NormedSpace.exp_continuous.tendsto _).comp (hm.smul ha)
  refine hc.mem_of_tendsto hlim (Eventually.of_forall fun k => ?_)
  have hk : ((⌊t / ε k⌋₊ : ℝ) * ε k) • a k = ⌊t / ε k⌋₊ • (ε k • a k) := by
    rw [mul_smul, Nat.cast_smul_eq_nsmul]
  rw [hk, NormedSpace.exp_nsmul]
  exact pow_mem_of_mul_closed h1 hmul (hG k) _

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hseq : ∀ k : ℕ, ∃ Y : A, ‖Y‖ < 1 / ((k : ℝ) + 1) ∧ NormedSpace.exp Y ∈ G ∧ p Y = 0 ∧ Y ≠ 0`. Introduce `k`. Take `⟨Y, hY, hYG, hYp, hY0⟩` from `hcon (Metric.ball 0 (1 / ((k : ℝ) + 1))) (Metric.ball_mem_nhds _ (by positivity))`.

Conclude with `⟨Y, by simpa using hY, hYG, hYp, hY0⟩`. Use `choose Y hYn hYG hYp hY0 using hseq`. Establish `hpos : ∀ k, 0 < ‖Y k‖` using `fun k => norm_pos_iff.2 (hY0 k)`. Establish `hsph : ∀ k, (‖Y k‖)⁻¹ • Y k ∈ Metric.sphere (0 : A) 1`. Introduce `k`.

Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos k).ne']`. Use `haveI : ProperSpace A := FiniteDimensional.proper ℝ A`. Take `⟨b, hb, φ, hφ, hlim⟩` from `(isCompact_sphere (0 : A) 1).tendsto_subseq hsph`. Establish `hε : Tendsto (fun k => ‖Y k‖) atTop (𝓝 0)` using `squeeze_zero (fun _ => norm_nonneg _) (fun k => (hYn k).le) tendsto_one_div_add_atTop_nhds_zero_nat`. Establish `hεφ : Tendsto (fun k => ‖Y (φ k)‖) atTop (𝓝 0)` using `hε.comp hφ.tendsto_atTop`.

Establish `hmem : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • b) ∈ G`. Introduce `t ht`. Use `exp_smul_limit_mem hc h1 hmul (ε := fun k => ‖Y (φ k)‖) (a := fun k => (‖Y (φ k)‖)⁻¹ • Y (φ k)) (fun k => hpos _) hεφ hlim (fun k => ?_) ht` and prove the remaining obligations. Establish `: ‖Y (φ k)‖ • (‖Y (φ k)‖)⁻¹ • Y (φ k) = Y (φ k)`. Rewrite using `[smul_smul, mul_inv_cancel₀ (hpos _).ne', one_smul]`.

Simplify `hYG (φ k)` using `only [this]`. Establish `hbS : b ∈ S`. Use `(hS b).2 fun t => ?_` and prove the remaining obligations. Break down `le_total 0 t with ht | ht` into its components or cases. Conclude with `hmem t ht`.

Use `exp_neg_mem hinv (hmem (-t) (by linarith))` as an intermediate fact. Simplify using `using this`. Establish `hpb : p b = 0`. Establish `h2 : Tendsto (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) atTop (𝓝 (p b))` using `(p.continuous.tendsto b).comp hlim`. Establish `h3 : (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) = fun _ => 0`.

Use function extensionality and compare the values at `k`. Rewrite using `[map_smul, hYp, smul_zero]`. Rewrite `h2` using `[h3]`. Conclude with `tendsto_nhds_unique h2 tendsto_const_nhds`. Establish `hb0 : b = 0` using `by rw [← hp b hbS, hpb]`.

Establish `hb1 : ‖b‖ = 1` using `mem_sphere_zero_iff_norm.1 hb`. Rewrite `hb1` using `[hb0, norm_zero]`. Conclude with `zero_ne_one hb1`.
-/
theorem exists_nhds_kernel_eq_zero {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1)
    {S : Submodule ℝ A} (hS : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    (p : A →L[ℝ] A) (hp : ∀ Z ∈ S, p Z = Z) :
    ∃ W₀ ∈ 𝓝 (0 : A), ∀ Y ∈ W₀, NormedSpace.exp Y ∈ G → p Y = 0 → Y = 0 := by
  by_contra hcon
  push_neg at hcon
  have hseq : ∀ k : ℕ, ∃ Y : A, ‖Y‖ < 1 / ((k : ℝ) + 1) ∧ NormedSpace.exp Y ∈ G ∧ p Y = 0 ∧ Y ≠ 0 := by
    intro k
    obtain ⟨Y, hY, hYG, hYp, hY0⟩ :=
      hcon (Metric.ball 0 (1 / ((k : ℝ) + 1))) (Metric.ball_mem_nhds _ (by positivity))
    exact ⟨Y, by simpa using hY, hYG, hYp, hY0⟩
  choose Y hYn hYG hYp hY0 using hseq
  have hpos : ∀ k, 0 < ‖Y k‖ := fun k => norm_pos_iff.2 (hY0 k)
  have hsph : ∀ k, (‖Y k‖)⁻¹ • Y k ∈ Metric.sphere (0 : A) 1 := by
    intro k
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hpos k).ne']
  haveI : ProperSpace A := FiniteDimensional.proper ℝ A
  obtain ⟨b, hb, φ, hφ, hlim⟩ := (isCompact_sphere (0 : A) 1).tendsto_subseq hsph
  have hε : Tendsto (fun k => ‖Y k‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _) (fun k => (hYn k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hεφ : Tendsto (fun k => ‖Y (φ k)‖) atTop (𝓝 0) := hε.comp hφ.tendsto_atTop
  have hmem : ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • b) ∈ G := by
    intro t ht
    refine exp_smul_limit_mem hc h1 hmul (ε := fun k => ‖Y (φ k)‖)
      (a := fun k => (‖Y (φ k)‖)⁻¹ • Y (φ k)) (fun k => hpos _) hεφ hlim (fun k => ?_) ht
    have : ‖Y (φ k)‖ • (‖Y (φ k)‖)⁻¹ • Y (φ k) = Y (φ k) := by
      rw [smul_smul, mul_inv_cancel₀ (hpos _).ne', one_smul]
    simpa only [this] using hYG (φ k)
  have hbS : b ∈ S := by
    refine (hS b).2 fun t => ?_
    rcases le_total 0 t with ht | ht
    · exact hmem t ht
    · have := exp_neg_mem hinv (hmem (-t) (by linarith))
      simpa using this
  have hpb : p b = 0 := by
    have h2 : Tendsto (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) atTop (𝓝 (p b)) :=
      (p.continuous.tendsto b).comp hlim
    have h3 : (fun k => p ((‖Y (φ k)‖)⁻¹ • Y (φ k))) = fun _ => 0 := by
      funext k
      rw [map_smul, hYp, smul_zero]
    rw [h3] at h2
    exact tendsto_nhds_unique h2 tendsto_const_nhds
  have hb0 : b = 0 := by rw [← hp b hbS, hpb]
  have hb1 : ‖b‖ = 1 := mem_sphere_zero_iff_norm.1 hb
  rw [hb0, norm_zero] at hb1
  exact zero_ne_one hb1

/- English proof (translation)
Use `haveI : CompleteSpace A := FiniteDimensional.complete ℝ A`. Use `letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A`. Take `⟨f, hf⟩` from `S.subtype.exists_leftInverse_of_injective (by simp)`. Set `p : A →L[ℝ] A` to `LinearMap.toContinuousLinearMap (S.subtype ∘ₗ f)`. Establish `hpS : ∀ Z, p Z ∈ S` using `fun Z => (f Z).2`.

Establish `hp : ∀ Z ∈ S, p Z = Z`. Introduce `Z hZ`. Establish `h2` using `LinearMap.congr_fun hf ⟨Z, hZ⟩`. Establish `h3 : f Z = ⟨Z, hZ⟩` using `h2`. Express the relevant statement in the definitionally equal form `((f Z : S) : A) = Z`.

Rewrite using `[h3]`. Take `⟨W₀, hW₀, hker⟩` from `exists_nhds_kernel_eq_zero hc h1 hmul hinv hS p hp`. Set `q : A →L[ℝ] A` to `ContinuousLinearMap.id ℝ A - p`. Establish `hq : ∀ Z, q Z = Z - p Z` using `fun Z => rfl`. Set `Φ : A → A` to `fun Z => NormedSpace.exp (p Z) * NormedSpace.exp (q Z)`.

Establish `hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0` using `hasStrictFDerivAt_exp_zero`. Establish `hEp : HasStrictFDerivAt (fun Z => NormedSpace.exp (p Z)) p (0 : A)`. Establish `h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (p 0)`. Simplify using `using hE`. Conclude with `(h2.comp (0 : A) p.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)`.

Establish `hEq : HasStrictFDerivAt (fun Z => NormedSpace.exp (q Z)) q (0 : A)`. Establish `h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (q 0)`. Simplify using `using hE`. Conclude with `(h2.comp (0 : A) q.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)`. Establish `hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0`.

Establish `h2 : HasStrictFDerivAt Φ _ 0` using `hEp.mul' hEq`. Use `h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)` and prove the remaining obligations. Simplify using `[hq]`. Establish `hΦ0 : Φ 0 = 1` using `by simp [Φ]`. Establish `hmap` using `hΦ.map_nhds_eq_of_equiv`.

Establish `hW' : p ⁻¹' W ∩ q ⁻¹' W₀ ∈ 𝓝 (0 : A)`. Use `inter_mem (p.continuous.continuousAt.preimage_mem_nhds ?_) (q.continuous.continuousAt.preimage_mem_nhds ?_)` and prove the remaining obligations. Simplify using `using hW`. Simplify using `using hW₀`. Establish `himg : Φ '' (p ⁻¹' W ∩ q ⁻¹' W₀) ∈ 𝓝 (1 : A)`.

Rewrite using `[← hΦ0, ← hmap]`. Conclude with `image_mem_map hW'`. Use `filter_upwards [himg]`. Introduce and unpack `g ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩ hg`. Establish `hpG : NormedSpace.exp (p Z) ∈ G`.

Simplify using `using (hS _).1 (hpS Z) 1`. Establish `hnG : NormedSpace.exp (-(p Z)) ∈ G` using `exp_neg_mem hinv hpG`. Establish `hone : NormedSpace.exp (-(p Z)) * NormedSpace.exp (p Z) = 1`. Rewrite using `[← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl (p Z))), neg_add_cancel, NormedSpace.exp_zero]`. Establish `hqG : NormedSpace.exp (q Z) ∈ G`.

Establish `h2` using `hmul _ hnG _ hg`. Simplify `h2` using `only [Φ, ← mul_assoc, hone, one_mul]`. Establish `hpq : p (q Z) = 0`. Rewrite using `[hq, map_sub, hp _ (hpS Z), sub_self]`. Establish `hq0 : q Z = 0` using `hker _ hZ2 hqG hpq`.

Use `⟨p Z, hpS Z, hZ1, ?_⟩` and prove the remaining obligations. Simplify using `[Φ, hq0]`.
-/
theorem eventually_exp_of_mem {G : Set A} (hc : IsClosed G) (h1 : (1 : A) ∈ G)
    (hmul : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G) (hinv : ∀ g ∈ G, ∃ h ∈ G, h * g = 1 ∧ g * h = 1)
    {S : Submodule ℝ A} (hS : ∀ X, X ∈ S ↔ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G)
    {W : Set A} (hW : W ∈ 𝓝 (0 : A)) :
    ∀ᶠ g in 𝓝 (1 : A), g ∈ G → ∃ X ∈ S, X ∈ W ∧ NormedSpace.exp X = g := by
  haveI : CompleteSpace A := FiniteDimensional.complete ℝ A
  letI : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨f, hf⟩ := S.subtype.exists_leftInverse_of_injective (by simp)
  let p : A →L[ℝ] A := LinearMap.toContinuousLinearMap (S.subtype ∘ₗ f)
  have hpS : ∀ Z, p Z ∈ S := fun Z => (f Z).2
  have hp : ∀ Z ∈ S, p Z = Z := by
    intro Z hZ
    have h2 := LinearMap.congr_fun hf ⟨Z, hZ⟩
    have h3 : f Z = ⟨Z, hZ⟩ := h2
    change ((f Z : S) : A) = Z
    rw [h3]
  obtain ⟨W₀, hW₀, hker⟩ := exists_nhds_kernel_eq_zero hc h1 hmul hinv hS p hp
  let q : A →L[ℝ] A := ContinuousLinearMap.id ℝ A - p
  have hq : ∀ Z, q Z = Z - p Z := fun Z => rfl
  let Φ : A → A := fun Z => NormedSpace.exp (p Z) * NormedSpace.exp (q Z)
  have hE : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) 0 :=
    hasStrictFDerivAt_exp_zero
  have hEp : HasStrictFDerivAt (fun Z => NormedSpace.exp (p Z)) p (0 : A) := by
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (p 0) := by
      simpa using hE
    exact (h2.comp (0 : A) p.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hEq : HasStrictFDerivAt (fun Z => NormedSpace.exp (q Z)) q (0 : A) := by
    have h2 : HasStrictFDerivAt (NormedSpace.exp : A → A) (1 : A →L[ℝ] A) (q 0) := by
      simpa using hE
    exact (h2.comp (0 : A) q.hasStrictFDerivAt).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hΦ : HasStrictFDerivAt Φ ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    have h2 : HasStrictFDerivAt Φ _ 0 := hEp.mul' hEq
    refine h2.congr_fderiv (ContinuousLinearMap.ext fun Z => ?_)
    simp [hq]
  have hΦ0 : Φ 0 = 1 := by simp [Φ]
  have hmap := hΦ.map_nhds_eq_of_equiv
  have hW' : p ⁻¹' W ∩ q ⁻¹' W₀ ∈ 𝓝 (0 : A) := by
    refine inter_mem (p.continuous.continuousAt.preimage_mem_nhds ?_)
      (q.continuous.continuousAt.preimage_mem_nhds ?_)
    · simpa using hW
    · simpa using hW₀
  have himg : Φ '' (p ⁻¹' W ∩ q ⁻¹' W₀) ∈ 𝓝 (1 : A) := by
    rw [← hΦ0, ← hmap]
    exact image_mem_map hW'
  filter_upwards [himg]
  rintro g ⟨Z, ⟨hZ1, hZ2⟩, rfl⟩ hg
  have hpG : NormedSpace.exp (p Z) ∈ G := by
    simpa using (hS _).1 (hpS Z) 1
  have hnG : NormedSpace.exp (-(p Z)) ∈ G := exp_neg_mem hinv hpG
  have hone : NormedSpace.exp (-(p Z)) * NormedSpace.exp (p Z) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl (p Z))), neg_add_cancel,
      NormedSpace.exp_zero]
  have hqG : NormedSpace.exp (q Z) ∈ G := by
    have h2 := hmul _ hnG _ hg
    simpa only [Φ, ← mul_assoc, hone, one_mul] using h2
  have hpq : p (q Z) = 0 := by
    rw [hq, map_sub, hp _ (hpS Z), sub_self]
  have hq0 : q Z = 0 := hker _ hZ2 hqG hpq
  refine ⟨p Z, hpS Z, hZ1, ?_⟩
  simp [Φ, hq0]

end Banach

end GlobalTheory.CompanionTheory.ClosedSubgroup
