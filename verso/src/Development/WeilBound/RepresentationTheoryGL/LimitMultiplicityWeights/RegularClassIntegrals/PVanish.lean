import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PVanish

def mul3 {n : ℕ} (A B C : MainStatements.WeightKernel.Mx n) : MainStatements.WeightKernel.Mx n := fun a b => (of A * of B * of C) a b

/- English proof (translation)
Establish `e : ∀ (u : E → Mx n), ContDiff ℝ ∞ u → ∀ a b : Fin n, ContDiff ℝ ∞ fun x => u x a b` using `fun u hu a b => contDiff_pi.1 (contDiff_pi.1 hu a) b`. Use `contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_` and prove the remaining obligations. Simplify using `only [mul3, Matrix.mul_apply, Matrix.of_apply]`. Conclude with `ContDiff.sum fun j _ => (ContDiff.sum fun k _ => (e f hf a k).mul (e g hg k j)).mul (e h hh j b)`.
-/
theorem contDiff_triple_matrix_product {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g h : E → MainStatements.WeightKernel.Mx n}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ fun x => mul3 (f x) (g x) (h x) := by
  have e : ∀ (u : E → Mx n), ContDiff ℝ ∞ u → ∀ a b : Fin n, ContDiff ℝ ∞ fun x => u x a b :=
    fun u hu a b => contDiff_pi.1 (contDiff_pi.1 hu a) b
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [mul3, Matrix.mul_apply, Matrix.of_apply]
  exact ContDiff.sum fun j _ =>
    (ContDiff.sum fun k _ => (e f hf a k).mul (e g hg k j)).mul (e h hh j b)

/- English proof (translation)
Use function extensionality and compare the values at `a b`. Use `show (ι g * ι h * ι l) a b = ι (g * h * l) a b`. Rewrite using `[map_mul, map_mul]`.
-/
theorem triple_product_matrix_coordinates {H : Type} [Group H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (g h l : H) :
    mul3 (matCoord ι g) (matCoord ι h) (matCoord ι l) = matCoord ι (g * h * l) := by
  funext a b
  show (ι g * ι h * ι l) a b = ι (g * h * l) a b
  rw [map_mul, map_mul]

end MainStatements.WeightKernel.PVanish

open MainStatements.WeightKernel.PVanish in
/- English proof (translation)
Introduce `hSwap hOne hTwo H _ _ _ _ _ _ _ _ n ι hemb s B hB μ _ _ dt _ _ Ω I _ _ m _ c q hK hq hInv φ hφ hOrb`. Take `⟨hφc, Φφ, hΦφ, hφeq⟩` from `hφ`. Establish `hmc : Continuous (matCoord ι)` using `hemb.continuous`. Establish `hφcont : Continuous φ`. Rewrite using `[show φ = fun g => Φφ (matCoord ι g) from funext hφeq]`.

Conclude with `hΦφ.continuous.comp hmc`. Set `bp : ContDiffBump (matCoord ι s)` to `⟨1, 2, one_pos, one_lt_two⟩`. Set `ψ : H → ℝ` to `fun y => bp (matCoord ι y)`. Establish `hψc : Continuous ψ` using `bp.continuous.comp hmc`. Establish `hψcs : HasCompactSupport ψ` using `bp.hasCompactSupport.comp_isClosedEmbedding hemb`.

Establish `hψs : 0 < ψ s`. Establish `: ψ s = 1` using `bp.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)`. Rewrite using `[this]`. Conclude with `one_pos`. Take `⟨a, ha0, ha⟩` from `hOne H n ι hmc s B hB μ dt ψ hψc hψcs (fun y => bp.nonneg) hψs`.

Take `⟨Kset, hKc, hKprop⟩` from `hB.proper (tsupport φ) (tsupport ψ) hφc.isCompact hψcs.isCompact`. Set `p : H → Mx n × Mx n` to `fun k => (matCoord ι k, matCoord ι k⁻¹)`. Establish `hp : Continuous p` using `hmc.prodMk (hmc.comp continuous_inv)`. Set `W₁ : Mx n × (Mx n × Mx n) → ℂ` to `fun z => Φφ z.1 * ((B (z.1, z.2.1) : ℝ) : ℂ) * ((bp (mul3 z.2.2 z.1 z.2.1) : ℝ) : ℂ)`. Set `W₂ : Mx n × (Mx n × Mx n) → ℂ` to `fun z => Φφ (mul3 z.2.1 z.1 z.2.2) * ((B (mul3 z.2.1 z.1 z.2.2, z.2.1) : ℝ) : ℂ) * ((bp z.1 : ℝ) : ℂ)`.

Establish `hfst : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.1` using `contDiff_fst`. Establish `hA : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.1` using `contDiff_fst.comp contDiff_snd`. Establish `hC : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.2` using `contDiff_snd.comp contDiff_snd`. Establish `hM1` using `contDiff_triple_matrix_product hC hfst hA`. Establish `hM2` using `contDiff_triple_matrix_product hA hfst hC`.

Establish `hW₁ : ContDiff ℝ ∞ W₁` using `((hΦφ.comp hfst).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hfst.prodMk hA)))).mul (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hM1))`. Establish `hW₂ : ContDiff ℝ ∞ W₂` using `((hΦφ.comp hM2).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hM2.prodMk hA)))).mul (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hfst))`. Establish `hW₁pt : ∀ y k : H, W₁ (matCoord ι y, p k) = φ y * ((B (matCoord ι y, matCoord ι k) : ℂ) * (ψ (k⁻¹ * y * k) : ℂ))`. Introduce `y k`. Simplify using `only [W₁, p, ψ]`.

Rewrite using `[triple_product_matrix_coordinates, hφeq, mul_assoc]`. Establish `hW₂pt : ∀ y k : H, W₂ (matCoord ι y, p k) = φ (k * y * k⁻¹) * (B (matCoord ι (k * y * k⁻¹), matCoord ι k) : ℂ) * (ψ y : ℂ)`. Introduce `y k`. Simplify using `only [W₂, p, ψ]`. Rewrite using `[triple_product_matrix_coordinates, hφeq]`.

Establish `hvan1 : ∀ z k : H, k ∉ Kset → W₁ (matCoord ι (z⁻¹ * s * z), p k) = 0`. Introduce `z k hk`. Rewrite using `[hW₁pt]`. Assume the negation of the conclusion as `hne`. Apply `hk` to reduce the goal to its premises.

Establish `h1 : φ (z⁻¹ * s * z) ≠ 0` using `left_ne_zero_of_mul hne`. Establish `h23` using `right_ne_zero_of_mul hne`. Establish `h2 : (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) ≠ 0` using `left_ne_zero_of_mul h23`. Establish `h3 : (ψ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ≠ 0` using `right_ne_zero_of_mul h23`. Establish `e : (z * k)⁻¹ * s * (z * k) = k⁻¹ * (z⁻¹ * s * z) * k` using `by group`.

Use `hKprop z k (subset_tsupport _ h1) ?_ (fun h0 => h2 (by simp [h0]))` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))`. Establish `hvan2 : ∀ w k : H, k ∉ Kset → W₂ (matCoord ι (w⁻¹ * s * w), p k) = 0`. Introduce `w k hk`.

Rewrite using `[hW₂pt]`. Assume the negation of the conclusion as `hne`. Apply `hk` to reduce the goal to its premises. Establish `h12` using `left_ne_zero_of_mul hne`. Establish `h3 : (ψ (w⁻¹ * s * w) : ℂ) ≠ 0` using `right_ne_zero_of_mul hne`.

Establish `h1 : φ (k * (w⁻¹ * s * w) * k⁻¹) ≠ 0` using `left_ne_zero_of_mul h12`. Establish `h2 : (B (matCoord ι (k * (w⁻¹ * s * w) * k⁻¹), matCoord ι k) : ℂ) ≠ 0` using `right_ne_zero_of_mul h12`. Establish `e1 : (w * k⁻¹)⁻¹ * s * (w * k⁻¹) = k * (w⁻¹ * s * w) * k⁻¹` using `by group`. Establish `e2 : (w * k⁻¹ * k)⁻¹ * s * (w * k⁻¹ * k) = w⁻¹ * s * w` using `by group`. Use `hKprop (w * k⁻¹) k ?_ ?_ ?_` and prove the remaining obligations.

Rewrite using `[e1]`. Conclude with `subset_tsupport _ h1`. Rewrite using `[e2]`. Conclude with `subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))`. Rewrite using `[e1]`.

Conclude with `fun h0 => h2 (by simp [h0])`. Establish `h1` using `hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₁ p Kset (tsupport φ) hW₁ hp hKc hφc.isCompact (by`. Introduce `k _ y hy`. Establish `: φ y = 0`. Assume the negation of the conclusion as `h0`.

Conclude with `hy (subset_tsupport _ h0)`. Rewrite using `[hW₁pt, this, zero_mul])`. Establish `h2` using `hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₂ p Kset (tsupport ψ) hW₂ hp hKc hψcs.isCompact (by`. Introduce `k _ y hy`. Establish `: ψ y = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hy (subset_tsupport _ h0)`. Rewrite using `[hW₂pt, this]`. Use the proof step `simp)`. Establish `hR1 : ∫ x, ker c q (fun y => ∫ k in Kset, W₁ (matCoord ι y, p k) ∂μ) x ∂m = a * ∫ x, ker c q φ x ∂m`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [MainStatements.WeightKernel.ker]`. Rewrite using `[← tsum_mul_left]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Take `⟨z, hz⟩` from `hq i x`. Rewrite using `[hz, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan1 z)]`. Simplify using `only [hW₁pt]`.

Rewrite using `[integral_const_mul, ha z]`. Expand and normalize the polynomial expressions, which then agree. Establish `hstep : ∀ k : H, ∫ x, ker c q (fun y => W₁ (matCoord ι y, p k)) x ∂m = ∫ x, ker c q (fun y => W₂ (matCoord ι y, p k)) x ∂m`. Introduce `k`. Establish `hmem : (fun y => W₂ (matCoord ι y, p k)) ∈ CcMat ι`.

Use `⟨?_, fun Y => W₂ (Y, p k), hW₂.comp (contDiff_id.prodMk contDiff_const), fun g => rfl⟩` and prove the remaining obligations. Use `hψcs.mono ?_` and prove the remaining obligations. Introduce `y hy`. Rewrite `hy`, the goal using `[Function.mem_support]`. Introduce `h0`.

Apply `hy` to reduce the goal to its premises. Rewrite using `[hW₂pt, h0]`. Simplify using the standard rewrite rules. Establish `hfun : (fun y => W₁ (matCoord ι y, p k)) = fun y => W₂ (matCoord ι (k⁻¹ * y * k⁻¹⁻¹), p k)`. Use function extensionality and compare the values at `y`.

Rewrite using `[hW₂pt, hW₁pt]`. Establish `e : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y` using `by group`. Rewrite using `[e, inv_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`.

Conclude with `hInv _ hmem k⁻¹`. Establish `hR2 : ∫ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x ∂m = 0`. Establish `hz : ∀ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x = 0`. Introduce `x`. Simplify using `only [MainStatements.WeightKernel.ker]`.

Use `(tsum_congr fun i => ?_).trans tsum_zero` and prove the remaining obligations. Take `⟨w, hw⟩` from `hq i x`. Rewrite using `[hw, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan2 w)]`. Simplify using `only [hW₂pt]`. Rewrite using `[integral_mul_const, hTwo H n ι hmc s B hB μ dt φ hφcont hφc hOrb w]`.

Simplify using the standard rewrite rules. Simplify using `[hz]`. Establish `key : a * ∫ x, ker c q φ x ∂m = 0`. Rewrite using `[← hR1, ← h1]`. Simplify using `only [hstep]`.

Rewrite using `[h2]`. Conclude with `hR2`. Conclude with `(mul_eq_zero.1 key).resolve_left ha0`.
-/
theorem MainStatements.WeightKernel.vanish : KerSwap → IdentOne → IdentTwo → Vanish := by
  intro hSwap hOne hTwo H _ _ _ _ _ _ _ _ n ι hemb s B hB μ _ _ dt _ _ Ω I _ _ m _ c q hK hq hInv φ hφ hOrb
  obtain ⟨hφc, Φφ, hΦφ, hφeq⟩ := hφ
  have hmc : Continuous (matCoord ι) := hemb.continuous
  have hφcont : Continuous φ := by
    rw [show φ = fun g => Φφ (matCoord ι g) from funext hφeq]
    exact hΦφ.continuous.comp hmc
  let bp : ContDiffBump (matCoord ι s) := ⟨1, 2, one_pos, one_lt_two⟩
  let ψ : H → ℝ := fun y => bp (matCoord ι y)
  have hψc : Continuous ψ := bp.continuous.comp hmc
  have hψcs : HasCompactSupport ψ := bp.hasCompactSupport.comp_isClosedEmbedding hemb
  have hψs : 0 < ψ s := by
    have : ψ s = 1 := bp.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
    rw [this]
    exact one_pos
  obtain ⟨a, ha0, ha⟩ := hOne H n ι hmc s B hB μ dt ψ hψc hψcs (fun y => bp.nonneg) hψs
  obtain ⟨Kset, hKc, hKprop⟩ := hB.proper (tsupport φ) (tsupport ψ) hφc.isCompact hψcs.isCompact
  let p : H → Mx n × Mx n := fun k => (matCoord ι k, matCoord ι k⁻¹)
  have hp : Continuous p := hmc.prodMk (hmc.comp continuous_inv)
  let W₁ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ z.1 * ((B (z.1, z.2.1) : ℝ) : ℂ) * ((bp (mul3 z.2.2 z.1 z.2.1) : ℝ) : ℂ)
  let W₂ : Mx n × (Mx n × Mx n) → ℂ := fun z =>
    Φφ (mul3 z.2.1 z.1 z.2.2) * ((B (mul3 z.2.1 z.1 z.2.2, z.2.1) : ℝ) : ℂ) * ((bp z.1 : ℝ) : ℂ)
  have hfst : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.1 := contDiff_fst
  have hA : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.1 := contDiff_fst.comp contDiff_snd
  have hC : ContDiff ℝ ∞ fun z : Mx n × (Mx n × Mx n) => z.2.2 := contDiff_snd.comp contDiff_snd
  have hM1 := contDiff_triple_matrix_product hC hfst hA
  have hM2 := contDiff_triple_matrix_product hA hfst hC
  have hW₁ : ContDiff ℝ ∞ W₁ :=
    ((hΦφ.comp hfst).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hfst.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hM1))
  have hW₂ : ContDiff ℝ ∞ W₂ :=
    ((hΦφ.comp hM2).mul (Complex.ofRealCLM.contDiff.comp (hB.smooth.comp (hM2.prodMk hA)))).mul
      (Complex.ofRealCLM.contDiff.comp (bp.contDiff.comp hfst))
  have hW₁pt : ∀ y k : H, W₁ (matCoord ι y, p k) =
      φ y * ((B (matCoord ι y, matCoord ι k) : ℂ) * (ψ (k⁻¹ * y * k) : ℂ)) := by
    intro y k
    simp only [W₁, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq, mul_assoc]
  have hW₂pt : ∀ y k : H, W₂ (matCoord ι y, p k) =
      φ (k * y * k⁻¹) * (B (matCoord ι (k * y * k⁻¹), matCoord ι k) : ℂ) * (ψ y : ℂ) := by
    intro y k
    simp only [W₂, p, ψ]
    rw [triple_product_matrix_coordinates, hφeq]
  have hvan1 : ∀ z k : H, k ∉ Kset → W₁ (matCoord ι (z⁻¹ * s * z), p k) = 0 := by
    intro z k hk
    rw [hW₁pt]
    by_contra hne
    apply hk
    have h1 : φ (z⁻¹ * s * z) ≠ 0 := left_ne_zero_of_mul hne
    have h23 := right_ne_zero_of_mul hne
    have h2 : (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) ≠ 0 := left_ne_zero_of_mul h23
    have h3 : (ψ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ≠ 0 := right_ne_zero_of_mul h23
    have e : (z * k)⁻¹ * s * (z * k) = k⁻¹ * (z⁻¹ * s * z) * k := by group
    refine hKprop z k (subset_tsupport _ h1) ?_ (fun h0 => h2 (by simp [h0]))
    rw [e]
    exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
  have hvan2 : ∀ w k : H, k ∉ Kset → W₂ (matCoord ι (w⁻¹ * s * w), p k) = 0 := by
    intro w k hk
    rw [hW₂pt]
    by_contra hne
    apply hk
    have h12 := left_ne_zero_of_mul hne
    have h3 : (ψ (w⁻¹ * s * w) : ℂ) ≠ 0 := right_ne_zero_of_mul hne
    have h1 : φ (k * (w⁻¹ * s * w) * k⁻¹) ≠ 0 := left_ne_zero_of_mul h12
    have h2 : (B (matCoord ι (k * (w⁻¹ * s * w) * k⁻¹), matCoord ι k) : ℂ) ≠ 0 :=
      right_ne_zero_of_mul h12
    have e1 : (w * k⁻¹)⁻¹ * s * (w * k⁻¹) = k * (w⁻¹ * s * w) * k⁻¹ := by group
    have e2 : (w * k⁻¹ * k)⁻¹ * s * (w * k⁻¹ * k) = w⁻¹ * s * w := by group
    refine hKprop (w * k⁻¹) k ?_ ?_ ?_
    · rw [e1]
      exact subset_tsupport _ h1
    · rw [e2]
      exact subset_tsupport _ (Function.mem_support.2 (fun h0 => h3 (by simp [h0])))
    · rw [e1]
      exact fun h0 => h2 (by simp [h0])
  have h1 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₁ p Kset (tsupport φ) hW₁ hp hKc
    hφc.isCompact (by
      intro k _ y hy
      have : φ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₁pt, this, zero_mul])
  have h2 := hSwap H n ι hemb μ Ω I m c q hK (Mx n × Mx n) W₂ p Kset (tsupport ψ) hW₂ hp hKc
    hψcs.isCompact (by
      intro k _ y hy
      have : ψ y = 0 := by
        by_contra h0
        exact hy (subset_tsupport _ h0)
      rw [hW₂pt, this]
      simp)
  have hR1 : ∫ x, ker c q (fun y => ∫ k in Kset, W₁ (matCoord ι y, p k) ∂μ) x ∂m =
      a * ∫ x, ker c q φ x ∂m := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [MainStatements.WeightKernel.ker]
    rw [← tsum_mul_left]
    congr 1
    funext i
    obtain ⟨z, hz⟩ := hq i x
    rw [hz, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan1 z)]
    simp only [hW₁pt]
    rw [integral_const_mul, ha z]
    ring
  have hstep : ∀ k : H, ∫ x, ker c q (fun y => W₁ (matCoord ι y, p k)) x ∂m =
      ∫ x, ker c q (fun y => W₂ (matCoord ι y, p k)) x ∂m := by
    intro k
    have hmem : (fun y => W₂ (matCoord ι y, p k)) ∈ CcMat ι := by
      refine ⟨?_, fun Y => W₂ (Y, p k), hW₂.comp (contDiff_id.prodMk contDiff_const), fun g => rfl⟩
      refine hψcs.mono ?_
      intro y hy
      rw [Function.mem_support] at hy ⊢
      intro h0
      apply hy
      rw [hW₂pt, h0]
      simp
    have hfun : (fun y => W₁ (matCoord ι y, p k)) =
        fun y => W₂ (matCoord ι (k⁻¹ * y * k⁻¹⁻¹), p k) := by
      funext y
      rw [hW₂pt, hW₁pt]
      have e : k * (k⁻¹ * y * k⁻¹⁻¹) * k⁻¹ = y := by group
      rw [e, inv_inv]
      ring
    rw [hfun]
    exact hInv _ hmem k⁻¹
  have hR2 : ∫ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x ∂m = 0 := by
    have hz : ∀ x, ker c q (fun y => ∫ k in Kset, W₂ (matCoord ι y, p k) ∂μ) x = 0 := by
      intro x
      simp only [MainStatements.WeightKernel.ker]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      obtain ⟨w, hw⟩ := hq i x
      rw [hw, setIntegral_eq_integral_of_forall_compl_eq_zero (hvan2 w)]
      simp only [hW₂pt]
      rw [integral_mul_const, hTwo H n ι hmc s B hB μ dt φ hφcont hφc hOrb w]
      simp
    simp [hz]
  have key : a * ∫ x, ker c q φ x ∂m = 0 := by
    rw [← hR1, ← h1]
    simp only [hstep]
    rw [h2]
    exact hR2
  exact (mul_eq_zero.1 key).resolve_left ha0

end
