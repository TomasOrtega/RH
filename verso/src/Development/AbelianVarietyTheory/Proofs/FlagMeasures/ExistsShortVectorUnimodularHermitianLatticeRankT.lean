import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountSt
import ReciprocityTheory.SemistableReduction.SemiDegC

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.ShortVec

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, (σ x).im ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `h` to reduce the goal to its premises. Use `show ComplexEmbedding.conjugate σ = σ`.

Use extensionality with `a`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]`. Conclude with `hcon a`. Set `T : Subring ℂ` to `σ.range.topologicalClosure`. Establish `mem : ∀ y, y ∈ closure (Set.range σ) → y ∈ T` using `fun y hy => by show y ∈ closure (σ.range : Set ℂ)`.

Rewrite using `[RingHom.coe_range]`. Conclude with `hy`. Establish `hR : ∀ r : ℝ, (r : ℂ) ∈ T` using `fun r => mem _ <| map_mem_closure Complex.continuous_ofReal (Rat.denseRange_cast r) (fun y hy => by`. Take `⟨q, rfl⟩` from `hy`. Conclude with `⟨(q : K), by simp⟩)`.

Establish `hz : σ x ∈ T` using `mem _ (subset_closure ⟨x, rfl⟩)`. Use `show ∀ w, w ∈ closure (Set.range σ)`. Introduce `w`. Establish `hw : w = (w.re : ℂ) + ((w.im / (σ x).im : ℝ) : ℂ) * (σ x - ((σ x).re : ℂ))`. Apply the tactic sequence `apply Complex.ext <;> simp [hx]`.

Establish `: w ∈ T`. Rewrite using `[hw]`. Conclude with `T.add_mem (hR _) (T.mul_mem (hR _) (T.sub_mem hz (hR _)))`. Establish `h2 : w ∈ closure (σ.range : Set ℂ)` using `this`. Rewrite `h2` using `[RingHom.coe_range]`. Then use the resulting hypothesis.
-/
theorem denseRange_emb {K : Type} [Field K] (σ : K →+* ℂ) (h : ¬ ComplexEmbedding.IsReal σ) :
    DenseRange σ := by
  obtain ⟨x, hx⟩ : ∃ x, (σ x).im ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply h
    show ComplexEmbedding.conjugate σ = σ
    ext a
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
    exact hcon a
  let T : Subring ℂ := σ.range.topologicalClosure
  have mem : ∀ y, y ∈ closure (Set.range σ) → y ∈ T := fun y hy => by
    show y ∈ closure (σ.range : Set ℂ)
    rw [RingHom.coe_range]
    exact hy
  have hR : ∀ r : ℝ, (r : ℂ) ∈ T := fun r => mem _ <|
    map_mem_closure Complex.continuous_ofReal (Rat.denseRange_cast r)
      (fun y hy => by
        obtain ⟨q, rfl⟩ := hy
        exact ⟨(q : K), by simp⟩)
  have hz : σ x ∈ T := mem _ (subset_closure ⟨x, rfl⟩)
  show ∀ w, w ∈ closure (Set.range σ)
  intro w
  have hw : w = (w.re : ℂ) + ((w.im / (σ x).im : ℝ) : ℂ) * (σ x - ((σ x).re : ℂ)) := by
    apply Complex.ext <;> simp [hx]
  have : w ∈ T := by
    rw [hw]
    exact T.add_mem (hR _) (T.mul_mem (hR _) (T.sub_mem hz (hR _)))
  have h2 : w ∈ closure (σ.range : Set ℂ) := this
  rwa [RingHom.coe_range] at h2

/- English proof (translation)
Establish `hH : (G.map σ).IsHermitian`. Use extensionality with `i j`. Simplify using `only [conjTranspose_apply, map_apply]`. Rewrite using `[Complex.star_def, ← hs, ← conjTranspose_apply, hG]`. Use `set f : (Fin n → K) → (Fin n → ℂ) := fun y i => σ (y i) with hf`.

Establish `hqv : ∀ y, star (f y) ⬝ᵥ (G.map σ *ᵥ f y) = σ (star y ⬝ᵥ (G *ᵥ y))`. Introduce `y`. Simplify using `[hf, dotProduct, mulVec, map_sum, map_mul, hs]`. Establish `hnn : ∀ y : Fin n → K, 0 ≤ star (f y) ⬝ᵥ (G.map σ *ᵥ f y)`. Introduce `y`.

Rewrite using `[Complex.le_def]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hqv]`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`.

Simplify using `using (h y hy).le`. Establish `h1` using `hH.im_star_dotProduct_mulVec_self (f y)`. Simplify using `only [RCLike.im_to_complex] at h1`. Simplify using `[h1]`. Establish `hd : DenseRange f` using `DenseRange.piMap (fun _ : Fin n => denseRange_emb σ hσ)`.

Establish `hpsd : ∀ w : Fin n → ℂ, 0 ≤ star w ⬝ᵥ (G.map σ *ᵥ w)`. Introduce `w`. Use `hd.induction_on (p := fun w => 0 ≤ star w ⬝ᵥ (G.map σ *ᵥ w)) w ?_ hnn` and prove the remaining obligations. Use `isClosed_le continuous_const ?_` and prove the remaining obligations. Simplify using `only [dotProduct, mulVec]`.

Use `fun_prop`. Establish `hpsdM : (G.map σ).PosSemidef` using `PosSemidef.of_dotProduct_mulVec_nonneg hH hpsd`. Use `PosDef.of_dotProduct_mulVec_pos hH fun w hw => lt_of_le_of_ne (hpsd w) fun h0 => ?_` and prove the remaining obligations. Establish `hk : G.map σ *ᵥ w = 0` using `(hpsdM.dotProduct_mulVec_zero_iff w).1 h0.symm`. Establish `hdet : (G.map σ).det = 0` using `Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw, hk⟩`.

Establish `hdσ : σ G.det = 0`. Rewrite using `[RingHom.map_det]`. Conclude with `hdet`. Take `⟨y, hy, hGy⟩` from `Matrix.exists_mulVec_eq_zero_iff.2 ((map_eq_zero σ).1 hdσ)`. Use `h y hy` as an intermediate fact.

Simplify using `[hGy] at this`.
-/
theorem posDef_map {K : Type} [Field K] [StarRing K] {n : ℕ} (σ : K →+* ℂ)
    (hσ : ¬ ComplexEmbedding.IsReal σ) (hs : ∀ a, σ (star a) = starRingEnd ℂ (σ a))
    (G : Matrix (Fin n) (Fin n) K) (hG : Gᴴ = G)
    (h : ∀ y : Fin n → K, y ≠ 0 → 0 < (σ (star y ⬝ᵥ (G *ᵥ y))).re) : (G.map σ).PosDef := by
  have hH : (G.map σ).IsHermitian := by
    ext i j
    simp only [conjTranspose_apply, map_apply]
    rw [Complex.star_def, ← hs, ← conjTranspose_apply, hG]
  set f : (Fin n → K) → (Fin n → ℂ) := fun y i => σ (y i) with hf
  have hqv : ∀ y, star (f y) ⬝ᵥ (G.map σ *ᵥ f y) = σ (star y ⬝ᵥ (G *ᵥ y)) := by
    intro y
    simp [hf, dotProduct, mulVec, map_sum, map_mul, hs]
  have hnn : ∀ y : Fin n → K, 0 ≤ star (f y) ⬝ᵥ (G.map σ *ᵥ f y) := by
    intro y
    rw [Complex.le_def]
    refine ⟨?_, ?_⟩
    · rw [hqv]
      by_cases hy : y = 0
      · simp [hy]
      · simpa using (h y hy).le
    · have h1 := hH.im_star_dotProduct_mulVec_self (f y)
      simp only [RCLike.im_to_complex] at h1
      simp [h1]
  have hd : DenseRange f := DenseRange.piMap (fun _ : Fin n => denseRange_emb σ hσ)
  have hpsd : ∀ w : Fin n → ℂ, 0 ≤ star w ⬝ᵥ (G.map σ *ᵥ w) := by
    intro w
    refine hd.induction_on (p := fun w => 0 ≤ star w ⬝ᵥ (G.map σ *ᵥ w)) w ?_ hnn
    refine isClosed_le continuous_const ?_
    simp only [dotProduct, mulVec]
    fun_prop
  have hpsdM : (G.map σ).PosSemidef := PosSemidef.of_dotProduct_mulVec_nonneg hH hpsd
  refine PosDef.of_dotProduct_mulVec_pos hH fun w hw => lt_of_le_of_ne (hpsd w) fun h0 => ?_
  have hk : G.map σ *ᵥ w = 0 := (hpsdM.dotProduct_mulVec_zero_iff w).1 h0.symm
  have hdet : (G.map σ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw, hk⟩
  have hdσ : σ G.det = 0 := by
    rw [RingHom.map_det]
    exact hdet
  obtain ⟨y, hy, hGy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 ((map_eq_zero σ).1 hdσ)
  have := h y hy
  simp [hGy] at this

/- English proof (translation)
Establish `hH` using `hG.isHermitian`. Establish `h00 : 0 < G 0 0` using `hG.diag_pos`. Establish `h11 : 0 < G 1 1` using `hG.diag_pos`. Establish `hdet : 0 < G.det` using `hG.det_pos`. Use `set a := (G 0 0).re with ha`.

Use `set d := (G 1 1).re with hd`. Use `set Δ := G.det.re with hΔ`. Use `set b := G 0 1 with hb`. Establish `ha0 : 0 < a` using `(Complex.lt_def.1 h00).1`. Establish `hΔ0 : 0 < Δ` using `(Complex.lt_def.1 hdet).1`.

Establish `hG00 : G 0 0 = (a : ℂ)`. Use `(Complex.lt_def.1 h00).2` as an intermediate fact. Apply the tactic sequence `apply Complex.ext <;> simp at this ⊢ <;> linarith`. Establish `hG11 : G 1 1 = (d : ℂ)`. Use `(Complex.lt_def.1 h11).2` as an intermediate fact.

Apply the tactic sequence `apply Complex.ext <;> simp at this ⊢ <;> linarith`. Establish `hdC : G.det = (Δ : ℂ)`. Use `(Complex.lt_def.1 hdet).2` as an intermediate fact. Apply the tactic sequence `apply Complex.ext <;> simp at this ⊢ <;> linarith`. Establish `hG10 : G 1 0 = starRingEnd ℂ b` using `(hH.apply 1 0).symm`.

Establish `hΔe : (Δ : ℂ) = a * d - b * starRingEnd ℂ b`. Rewrite using `[← hdC, Matrix.det_fin_two, hG00, hG11, hG10]`. Use `set s := Real.sqrt a with hsdef`. Use `set t := Real.sqrt (Δ / a) with htdef`. Establish `hs0 : 0 < s` using `Real.sqrt_pos.2 ha0`.

Establish `ht0 : 0 < t` using `Real.sqrt_pos.2 (div_pos hΔ0 ha0)`. Establish `hs2 : (s : ℂ) ^ 2 = a`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt ha0.le]`. Establish `ht2 : (t : ℂ) ^ 2 = Δ / a`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (div_pos hΔ0 ha0).le, Complex.ofReal_div]`.

Establish `hsC : (s : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hs0.ne'`. Establish `haC : (a : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 ha0.ne'`. Establish `hsinv : (s : ℂ) * (s : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ hsC`. Establish `haa : (a : ℂ) * (a : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ haC`. Establish `hsa : ((s : ℂ)⁻¹) ^ 2 = (a : ℂ)⁻¹` using `by rw [inv_pow, hs2]`.

Set `M : Matrix (Fin 2) (Fin 2) ℂ` to `!![(s : ℂ), b / s; 0, (t : ℂ)]`. Establish `e1 : ∀ z : ℂ, ‖z‖ ^ 2 = (starRingEnd ℂ z * z).re` using `fun z => by`. Rewrite using `[Complex.sq_norm, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]`. Establish `key : ∀ y : Fin 2 → ℂ, ReciprocityTheory.GeometryOfNumbersTheory.qC G y = ‖(M *ᵥ y) 0‖ ^ 2 + ‖(M *ᵥ y) 1‖ ^ 2`. Introduce `y`.

Rewrite using `[e1, e1, ← Complex.add_re]`. Simplify using `only [ReciprocityTheory.GeometryOfNumbersTheory.qC, Fin.sum_univ_two]`. Use `congr 1`. Simplify using `[M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hG00, hG11, hG10]`. Take the linear combination `(-(starRingEnd ℂ (y 0) * y 0)) * hs2 - (starRingEnd ℂ (y 0) * b * y 1 + starRingEnd ℂ (y 1) * starRingEnd ℂ b * y 0) * hsinv - (starRingEnd ℂ (y 1) * y 1) * ht2 - (starRingEnd ℂ (y 1) * y 1) * b * starRingEnd ℂ b * hsa - (starRingEnd ℂ (y 1) * y 1) * (a : ℂ)⁻¹ * hΔe - (starRingEn …`.

Set `L : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ)` to `(Matrix.toLin' M).restrictScalars ℝ`. Establish `hLdet : LinearMap.det L = Δ`. Simplify using `only [L]`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]`. Simplify using `only [M]`.

Rewrite using `[Matrix.det_fin_two_of, mul_zero, sub_zero, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal, Real.mul_self_sqrt ha0.le, Real.mul_self_sqrt (div_pos hΔ0 ha0).le]`. Clear the denominators using the available nonvanishing facts. Establish `hLne : LinearMap.det L ≠ 0` using `by rw [hLdet]; exact hΔ0.ne'`. Establish `hset : {y : Fin 2 → ℂ | ReciprocityTheory.GeometryOfNumbersTheory.qC G y ≤ R ^ 2} = L ⁻¹' {u : Fin 2 → ℂ | (∑ i, ‖u i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ R}`. Use extensionality with `y`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_preimage, L, LinearMap.coe_restrictScalars, Matrix.toLin'_apply, Real.rpow_two, Fin.sum_univ_two]`. Rewrite using `[key y, ← Real.sqrt_eq_rpow, Real.sqrt_le_left hR.le]`. Establish `hΓ2 : Real.Gamma (2 / 2 + 1) = 1` using `by norm_num [Real.Gamma_two]`. Establish `hΓ3 : Real.Gamma (2 * 2 / 2 + 1) = 2`. Rewrite using `[show (2 * 2 / 2 + 1 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]`.

Evaluate the numerical expressions. Establish `hvol : volume {u : Fin 2 → ℂ | (∑ i, ‖u i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ R} = ENNReal.ofReal (R ^ 4 * (Real.pi ^ 2 / 2))`. Rewrite using `[Complex.volume_sum_rpow_le (Fin 2) (by norm_num : (1 : ℝ) ≤ 2) R]`. Simplify using `only [Fintype.card_fin, Nat.cast_ofNat, hΓ2, hΓ3]`. Rewrite using `[← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (by positivity)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hset, MeasureTheory.Measure.addHaar_preimage_linearMap volume hLne, hLdet, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by positivity), abs_of_pos (inv_pos.2 hΔ0)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volume_ellipsoid {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {R : ℝ} (hR : 0 < R) :
    (volume {y : Fin 2 → ℂ | ReciprocityTheory.GeometryOfNumbersTheory.qC G y ≤ R ^ 2}).toReal =
      Real.pi ^ 2 / 2 * (R ^ 2) ^ 2 / G.det.re := by
  have hH := hG.isHermitian
  have h00 : 0 < G 0 0 := hG.diag_pos
  have h11 : 0 < G 1 1 := hG.diag_pos
  have hdet : 0 < G.det := hG.det_pos
  set a := (G 0 0).re with ha
  set d := (G 1 1).re with hd
  set Δ := G.det.re with hΔ
  set b := G 0 1 with hb
  have ha0 : 0 < a := (Complex.lt_def.1 h00).1
  have hΔ0 : 0 < Δ := (Complex.lt_def.1 hdet).1
  have hG00 : G 0 0 = (a : ℂ) := by
    have := (Complex.lt_def.1 h00).2
    apply Complex.ext <;> simp at this ⊢ <;> linarith
  have hG11 : G 1 1 = (d : ℂ) := by
    have := (Complex.lt_def.1 h11).2
    apply Complex.ext <;> simp at this ⊢ <;> linarith
  have hdC : G.det = (Δ : ℂ) := by
    have := (Complex.lt_def.1 hdet).2
    apply Complex.ext <;> simp at this ⊢ <;> linarith
  have hG10 : G 1 0 = starRingEnd ℂ b := (hH.apply 1 0).symm
  have hΔe : (Δ : ℂ) = a * d - b * starRingEnd ℂ b := by
    rw [← hdC, Matrix.det_fin_two, hG00, hG11, hG10]
  set s := Real.sqrt a with hsdef
  set t := Real.sqrt (Δ / a) with htdef
  have hs0 : 0 < s := Real.sqrt_pos.2 ha0
  have ht0 : 0 < t := Real.sqrt_pos.2 (div_pos hΔ0 ha0)
  have hs2 : (s : ℂ) ^ 2 = a := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ha0.le]
  have ht2 : (t : ℂ) ^ 2 = Δ / a := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (div_pos hΔ0 ha0).le, Complex.ofReal_div]
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha0.ne'
  have hsinv : (s : ℂ) * (s : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hsC
  have haa : (a : ℂ) * (a : ℂ)⁻¹ = 1 := mul_inv_cancel₀ haC
  have hsa : ((s : ℂ)⁻¹) ^ 2 = (a : ℂ)⁻¹ := by rw [inv_pow, hs2]
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![(s : ℂ), b / s; 0, (t : ℂ)]
  have e1 : ∀ z : ℂ, ‖z‖ ^ 2 = (starRingEnd ℂ z * z).re := fun z => by
    rw [Complex.sq_norm, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have key : ∀ y : Fin 2 → ℂ, ReciprocityTheory.GeometryOfNumbersTheory.qC G y = ‖(M *ᵥ y) 0‖ ^ 2 + ‖(M *ᵥ y) 1‖ ^ 2 := by
    intro y
    rw [e1, e1, ← Complex.add_re]
    simp only [ReciprocityTheory.GeometryOfNumbersTheory.qC, Fin.sum_univ_two]
    congr 1
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hG00, hG11, hG10]
    linear_combination (-(starRingEnd ℂ (y 0) * y 0)) * hs2
      - (starRingEnd ℂ (y 0) * b * y 1 + starRingEnd ℂ (y 1) * starRingEnd ℂ b * y 0) * hsinv
      - (starRingEnd ℂ (y 1) * y 1) * ht2
      - (starRingEnd ℂ (y 1) * y 1) * b * starRingEnd ℂ b * hsa
      - (starRingEnd ℂ (y 1) * y 1) * (a : ℂ)⁻¹ * hΔe
      - (starRingEnd ℂ (y 1) * y 1) * d * haa
  let L : (Fin 2 → ℂ) →ₗ[ℝ] (Fin 2 → ℂ) := (Matrix.toLin' M).restrictScalars ℝ
  have hLdet : LinearMap.det L = Δ := by
    simp only [L]
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
    simp only [M]
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, Complex.normSq_mul, Complex.normSq_ofReal,
      Complex.normSq_ofReal, Real.mul_self_sqrt ha0.le, Real.mul_self_sqrt (div_pos hΔ0 ha0).le]
    field_simp
  have hLne : LinearMap.det L ≠ 0 := by rw [hLdet]; exact hΔ0.ne'
  have hset : {y : Fin 2 → ℂ | ReciprocityTheory.GeometryOfNumbersTheory.qC G y ≤ R ^ 2} =
      L ⁻¹' {u : Fin 2 → ℂ | (∑ i, ‖u i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ R} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, L, LinearMap.coe_restrictScalars,
      Matrix.toLin'_apply, Real.rpow_two, Fin.sum_univ_two]
    rw [key y, ← Real.sqrt_eq_rpow, Real.sqrt_le_left hR.le]
  have hΓ2 : Real.Gamma (2 / 2 + 1) = 1 := by norm_num [Real.Gamma_two]
  have hΓ3 : Real.Gamma (2 * 2 / 2 + 1) = 2 := by
    rw [show (2 * 2 / 2 + 1 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num
  have hvol : volume {u : Fin 2 → ℂ | (∑ i, ‖u i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ R} =
      ENNReal.ofReal (R ^ 4 * (Real.pi ^ 2 / 2)) := by
    rw [Complex.volume_sum_rpow_le (Fin 2) (by norm_num : (1 : ℝ) ≤ 2) R]
    simp only [Fintype.card_fin, Nat.cast_ofNat, hΓ2, hΓ3]
    rw [← ENNReal.ofReal_pow hR.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [hset, MeasureTheory.Measure.addHaar_preimage_linearMap volume hLne, hLdet, hvol,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (by positivity),
    abs_of_pos (inv_pos.2 hΔ0)]
  ring

section

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Establish `key : star (∑ i, c i • v i) ⬝ᵥ (J *ᵥ ∑ i, c i • v i) = ∑ i, ∑ j, star (c i) * c j * (star (v i) ⬝ᵥ (J *ᵥ v j))`. Simplify using `only [star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[key]`. Use `set g := fun i j => star (v i) ⬝ᵥ (J *ᵥ v j) with hg`. Establish `e : ∀ i j, star (v i) ⬝ᵥ (J *ᵥ v j) = g i j` using `fun i j => rfl`. Simplify using `only [e]`. Simplify using `only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_comb {m n : ℕ} (J : Matrix (Fin m) (Fin m) E) (v : Fin n → Fin m → E)
    (c : Fin n → E) :
    star c ⬝ᵥ ((Matrix.of fun i j => star (v i) ⬝ᵥ (J *ᵥ v j)) *ᵥ c) =
      star (∑ i, c i • v i) ⬝ᵥ (J *ᵥ ∑ i, c i • v i) := by
  have key : star (∑ i, c i • v i) ⬝ᵥ (J *ᵥ ∑ i, c i • v i) =
      ∑ i, ∑ j, star (c i) * c j * (star (v i) ⬝ᵥ (J *ᵥ v j)) := by
    simp only [star_sum, star_smul, mulVec_sum, mulVec_smul, sum_dotProduct, dotProduct_sum,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key]
  set g := fun i j => star (v i) ⬝ᵥ (J *ᵥ v j) with hg
  have e : ∀ i j, star (v i) ⬝ᵥ (J *ᵥ v j) = g i j := fun i j => rfl
  simp only [e]
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[star_dotProduct, star_mulVec, star_star, hJ, ← dotProduct_mulVec]`.
-/
theorem star_form {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (hJ : Jᴴ = J) (x y : Fin m → E) :
    star (star x ⬝ᵥ (J *ᵥ y)) = star y ⬝ᵥ (J *ᵥ x) := by
  rw [star_dotProduct, star_mulVec, star_star, hJ, ← dotProduct_mulVec]

noncomputable def fam [IsTotallyComplex E] (hs : ∀ (φ : E →+* ℂ) (a : E), φ (star a) = starRingEnd ℂ (φ a))
    {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (hJ : Jᴴ = J)
    (hp : ∀ (φ : E →+* ℂ) (y : Fin m → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) :
    ReciprocityTheory.GeometryOfNumbersTheory.HermFam E (Fin m → E) where
  form σ x y := σ (star x ⬝ᵥ (J *ᵥ y))
  add_right σ x y z := by rw [mulVec_add, dotProduct_add, map_add]
  smul_right σ a x y := by rw [mulVec_smul, dotProduct_smul, smul_eq_mul, map_mul]
  conj_symm σ x y := by rw [← hs, star_form hJ]
  posDef σ n v hv := by
    refine posDef_map σ (IsTotallyComplex.complexEmbedding_not_isReal σ) (hs σ)
      (Matrix.of fun i j => star (v i) ⬝ᵥ (J *ᵥ v j)) ?_ ?_
    · ext i j
      rw [conjTranspose_apply, Matrix.of_apply, Matrix.of_apply, star_form hJ]
    · intro y hy
      rw [gram_comb]
      refine hp σ _ fun h0 => hy ?_
      funext i
      exact Fintype.linearIndependent_iff.1 hv y h0 i

end

/- English proof (translation)
Establish `hn : 0 < n` using `hP.trans_le hPn`. Establish `h4 : (0 : ℝ) < 4 ^ f` using `by positivity`. Establish `hs : ((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 = D / 4 ^ f`. Rewrite using `[mul_pow, Real.sq_sqrt hD.le, ← pow_mul, mul_comm f 2, pow_mul, show ((2 : ℝ)⁻¹ ^ 2) = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv, mul_comm]`. Establish `h8 : (1 : ℝ) < (Real.pi ^ 2 / 8) ^ f` using `one_lt_pow₀ (by nlinarith [Real.pi_gt_three]) hf.ne'`.

Establish `e1 : (2 : ℝ) ^ (4 * f) = 4 ^ f * 4 ^ f`. Rewrite using `[← mul_pow, pow_mul]`. Evaluate the numerical expressions. Establish `e2 : (Real.pi ^ 2 / 2) ^ f = (Real.pi ^ 2 / 8) ^ f * 4 ^ f`. Rewrite using `[← mul_pow]`.

Put the polynomial expressions in normal form. Rewrite using `[hs, lt_div_iff₀ (by positivity), one_mul, e1, e2]`. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ 4 ^ f * D / P := div_le_div_of_nonneg_left (by positivity) hP hPn`.

Use `_ < (Real.pi ^ 2 / 8) ^ f * 4 ^ f * D / P := by`. Rewrite using `[div_lt_div_iff_of_pos_right hP]`. Use polynomial arithmetic with `[mul_pos h4 hD]`.
-/
theorem one_lt_ratio {f : ℕ} (hf : 0 < f) {D P n : ℝ} (hD : 0 < D) (hP : 0 < P) (hPn : P ≤ n) :
    1 < (Real.pi ^ 2 / 2) ^ f * D / P /
      (2 ^ (4 * f) * (((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 / n)) := by
  have hn : 0 < n := hP.trans_le hPn
  have h4 : (0 : ℝ) < 4 ^ f := by positivity
  have hs : ((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 = D / 4 ^ f := by
    rw [mul_pow, Real.sq_sqrt hD.le, ← pow_mul, mul_comm f 2, pow_mul,
      show ((2 : ℝ)⁻¹ ^ 2) = (4 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv, mul_comm]
  have h8 : (1 : ℝ) < (Real.pi ^ 2 / 8) ^ f :=
    one_lt_pow₀ (by nlinarith [Real.pi_gt_three]) hf.ne'
  have e1 : (2 : ℝ) ^ (4 * f) = 4 ^ f * 4 ^ f := by
    rw [← mul_pow, pow_mul]; norm_num
  have e2 : (Real.pi ^ 2 / 2) ^ f = (Real.pi ^ 2 / 8) ^ f * 4 ^ f := by
    rw [← mul_pow]; ring_nf
  rw [hs, lt_div_iff₀ (by positivity), one_mul, e1, e2]
  calc 4 ^ f * 4 ^ f * (D / 4 ^ f / n) = 4 ^ f * D / n := by
        field_simp
    _ ≤ 4 ^ f * D / P := div_le_div_of_nonneg_left (by positivity) hP hPn
    _ < (Real.pi ^ 2 / 8) ^ f * 4 ^ f * D / P := by
        rw [div_lt_div_iff_of_pos_right hP]
        nlinarith [mul_pos h4 hD]

open ReciprocityTheory.GeometryOfNumbersTheory in

/- English proof (translation)
Introduce `E _ _ _ hCM J hJ hp Λ hΛ hdual`. Establish `: IsTotallyComplex E` using `hCM.1`. Establish `hs` using `hCM.2.1`. Set `h` to `fam hs J hJ hp`. Establish `hform : ∀ σ x y, h.form σ x y = σ (star x ⬝ᵥ (J *ᵥ y))` using `fun _ _ _ => rfl`.

Establish `hinv : h.IsConjInv`. Introduce `σ x y`. Rewrite using `[hform, hform, ComplexEmbedding.conjugate_coe_eq]`. Establish `hfg : Λ.FG` using `hΛ.fg`. Establish `hrank : latRank E Λ = 2`.

Unfold `latRank`. Rewrite using `[hΛ.span_eq_top, finrank_top, Module.finrank_fin_fun]`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v : Fin 2 → (Fin 2 → E), IsFrame E Λ v := by`. Use `exists_isFrame (K := E) Λ hfg` as an intermediate fact. Rewrite `this` using `[hrank]`.

Conclude with `this`. Use `set f := InfinitePlace.nrComplexPlaces E with hfdef`. Establish `hfin : Module.finrank ℚ E = 2 * f` using `IsTotallyComplex.finrank E`. Establish `hf : 0 < f`. Use `Module.finrank_pos (R := ℚ) (M := E)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hdetpos : ∀ σ : E →+* ℂ, 0 < (h.gram σ v).det.re` using `fun σ => by`. Use `(Complex.lt_def.1 (gram_posDef h σ hv.2.1).det_pos).1` as an intermediate fact. Simplify using `using this`. Use `set P := ∏ w : {w : InfinitePlace E // w.IsComplex}, (h.gram w.1.embedding v).det.re with hPdef`.

Establish `hP : 0 < P` using `Finset.prod_pos fun w _ => hdetpos _`. Use `set n := (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex Λ.toAddSubgroup with hndef`. Establish `hn0 : n ≠ 0` using `IsFrame.relIndex_ne_zero hfg hv`. Establish `hn : (0 : ℝ) < n` using `by exact_mod_cast Nat.pos_of_ne_zero hn0`. Set `S : ReciprocityTheory.MultiplicativeHeights.HermForm E 2` to `{ c := starRingEnd E, c_invol := fun x => star_star x, c_emb := fun σ x => hs σ x, G := J, G_herm := fun a b => by`.

Use `congrFun (congrFun hJ b) a` as an intermediate fact. Simplify `this }` using `[conjTranspose_apply, starRingEnd_apply]`. Establish `hSh : ∀ x y, S.h x y = star x ⬝ᵥ (J *ᵥ y)`. Introduce `x y`. Simplify using `[ReciprocityTheory.MultiplicativeHeights.HermForm.h, S, dotProduct, mulVec, mul_add, mul_assoc, starRingEnd_apply]`.

Establish `hstar : ∀ z : E, z ∈ (algebraMap (𝓞 E) E).range → star z ∈ (algebraMap (𝓞 E) E).range`. Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hw : IsIntegral ℤ (w : E)` using `w.2`. Conclude with `⟨⟨star (w : E), hw.map (starRingEnd E).toIntAlgHom⟩, rfl⟩`. Establish `hsd : ReciprocityTheory.MultiplicativeHeights.IsSelfDual S Λ`.

Use `⟨fun x hx y hy => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `(hdual y).1 hy x hx`. Conclude with `⟨w, by rw [hSh]; exact hw⟩`. Use `(hdual x).2 fun y hy => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `hx y hy`.

Establish `e : star y ⬝ᵥ (J *ᵥ x) = star (S.h x y)`. Rewrite using `[hSh, star_form hJ]`. Rewrite using `[e]`. Conclude with `hstar _ (RingHom.mem_range.2 ⟨w, hw⟩)`. Establish `hb : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn Λ v` using `⟨hv.1, hv.2.1, hv.2.2⟩`.

Establish `hbound` using `ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.vec_selfDual_bound (ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordForm S v) _ (ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_fg hfg hb) (ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.intVec_le_coordLa …`. Rewrite `hbound` using `[← ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.spanIdx_eq_vecIdx hb]`. Use `set a := (ReciprocityTheory.MultiplicativeHeights.hGram S v).det with hadef`. Establish `hbound' : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ (n : ℝ) ^ 2`. Establish `h0 : |Algebra.norm ℚ a| ≤ (n : ℚ) ^ 2` using `hbound`.

Conclude with `h0` after adjusting the coercions. Establish `hgram : ∀ σ : E →+* ℂ, h.gram σ v = (ReciprocityTheory.MultiplicativeHeights.hGram S v).map σ`. Introduce `σ`. Use extensionality with `i j`. Simplify using `only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply, Matrix.map_apply, ReciprocityTheory.MultiplicativeHeights.hGram, hSh, hform]`.

Establish `hdetσ : ∀ σ : E →+* ℂ, (h.gram σ v).det = σ a`. Introduce `σ`. Rewrite using `[hgram, RingHom.map_det]`. Both sides reduce to the same expression. Establish `hnorm : ∀ σ : E →+* ℂ, ‖σ a‖ = (h.gram σ v).det.re`.

Introduce `σ`. Rewrite using `[← hdetσ]`. Take `⟨h1, h2⟩` from `Complex.lt_def.1 (gram_posDef h σ hv.2.1).det_pos`. Establish `e : (h.gram σ v).det = ((h.gram σ v).det.re : ℂ)` using `Complex.ext (by simp) (by simp at h2 ⊢; linarith)`. Use `conv_lhs => rw [e]`.

Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hdetpos σ)]`. Establish `hPn : P ≤ (n : ℝ)`. Establish `hPa : P = ∏ w : {w : InfinitePlace E // w.IsComplex}, w.1 a`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← hnorm, InfinitePlace.norm_embedding_eq]`.

Establish `hP2 : P ^ 2 = ((|Algebra.norm ℚ a| : ℚ) : ℝ)`. Rewrite using `[← InfinitePlace.prod_eq_abs_norm, hPa, ← Finset.prod_pow]`. Use `Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w)) _ _ (fun w => ?_)` and prove the remaining obligations. Use `show (w.1 a) ^ 2 = w.1 a ^ InfinitePlace.mult w.1`. Rewrite using `[InfinitePlace.mult_isComplex w]`.

Use polynomial arithmetic with `[hP, hn, hbound', hP2]`. Use `set D := |(discr E : ℝ)| with hDdef`. Establish `hD : 0 < D` using `abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero E))`. Establish `hcardpl : Fintype.card (InfinitePlace E) = f`. Rewrite using `[InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`.

Establish `hf' : (f : ℝ) ≠ 0` using `by exact_mod_cast hf.ne'`. Establish `h2v : 2 * Formalism.HermitianLatticesTheory.vInv E = D ^ ((1 : ℝ) / (2 * f))`. Unfold `Formalism.HermitianLatticesTheory.vInv Formalism.HermitianLatticesTheory.fDeg`. Rewrite using `[hcardpl]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hvpos : 0 < 2 * Formalism.HermitianLatticesTheory.vInv E` using `by rw [h2v]; positivity`. Use `set R := Real.sqrt (2 * Formalism.HermitianLatticesTheory.vInv E) with hRdef`. Establish `hR0 : 0 < R` using `Real.sqrt_pos.2 hvpos`. Establish `hR2 : R ^ 2 = 2 * Formalism.HermitianLatticesTheory.vInv E` using `Real.sq_sqrt hvpos.le`. Establish `hpow : ((R ^ 2) ^ 2) ^ f = D`.

Rewrite using `[hR2, h2v, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hD.le, ← Real.rpow_mul hD.le]`. Use `Real.rpow_one D using 2` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions. Establish `: DiscreteTopology (latE hv.2.1 Λ)` using `discrete_latE hfg hv`.

Establish `: IsZLattice ℝ (latE hv.2.1 Λ)` using `isZLattice_latE hfg hv`. Take `⟨hconv, hsymm, hbdd, hmeas⟩` from `ellS_props h hv.2.1 R`. Establish `hcount` using `measure_div_le_ncard_inter_lattice volume (latE hv.2.1 Λ) (ellS h v R) hconv hsymm hbdd hmeas`. Establish `: IsEmpty {w : InfinitePlace E // w.IsReal}` using `⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩`. Establish `hvol : (volume (ellS h v R)).toReal = (Real.pi ^ 2 / 2) ^ f * D / P`.

Rewrite using `[volume_ellS h hv.2.1 R, Finset.univ_eq_empty, Finset.prod_empty, one_mul, Finset.prod_congr rfl (fun w _ => volume_ellipsoid (gram_posDef h w.1.embedding hv.2.1) hR0), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, show Fintype.card {w : InfinitePlace E // w.IsCom …`. Establish `hfinrk : Module.finrank ℝ (Fin 2 → mixedEmbedding.mixedSpace E) = 4 * f`. Rewrite using `[Module.finrank_pi_fintype]`. Simplify using `only [mixedEmbedding.finrank, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hfin]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcov : ZLattice.covolume (latE hv.2.1 Λ) volume = ((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 / n`. Rewrite using `[covolume_latE hfg hv, covolume_standardLattice, mixedEmbedding.covolume_integerLattice]`. Rewrite `hcount` using `[hvol, hfinrk, hcov]`. Establish `h1 : 1 < (ellS h v R ∩ (latE hv.2.1 Λ : Set _)).ncard`. Conclude with `(one_lt_ratio hf hD hP hPn).trans_le hcount` after adjusting the coercions.

Take `⟨y, hyS, hy0⟩` from `Set.exists_ne_of_one_lt_ncard h1 0`. Take `⟨x, hxS, rfl⟩` from `mem_image_of_mem_ellS h hinv hv hR0.le hyS`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hy0 (map_zero _)`.

Use `⟨x, hxS.1, hx0, fun φ => ?_⟩` and prove the remaining obligations. Establish `h3 : Real.sqrt (h.form φ x x).re ≤ R` using `hxS.2 φ`. Rewrite `h3` using `[Real.sqrt_le_left hR0.le, hR2]`. Conclude with `h3`.
-/
theorem exists_short_vector : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∃ u ∈ Λ, u ≠ 0 ∧ ∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ 2 * Formalism.HermitianLatticesTheory.vInv E := by
  intro E _ _ _ hCM J hJ hp Λ hΛ hdual
  classical
  have : IsTotallyComplex E := hCM.1
  have hs := hCM.2.1
  let h := fam hs J hJ hp
  have hform : ∀ σ x y, h.form σ x y = σ (star x ⬝ᵥ (J *ᵥ y)) := fun _ _ _ => rfl
  have hinv : h.IsConjInv := by
    intro σ x y
    rw [hform, hform, ComplexEmbedding.conjugate_coe_eq]
  have hfg : Λ.FG := hΛ.fg
  have hrank : latRank E Λ = 2 := by
    unfold latRank
    rw [hΛ.span_eq_top, finrank_top, Module.finrank_fin_fun]
  obtain ⟨v, hv⟩ : ∃ v : Fin 2 → (Fin 2 → E), IsFrame E Λ v := by
    have := exists_isFrame (K := E) Λ hfg
    rw [hrank] at this
    exact this
  set f := InfinitePlace.nrComplexPlaces E with hfdef
  have hfin : Module.finrank ℚ E = 2 * f := IsTotallyComplex.finrank E
  have hf : 0 < f := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    omega
  have hdetpos : ∀ σ : E →+* ℂ, 0 < (h.gram σ v).det.re := fun σ => by
    have := (Complex.lt_def.1 (gram_posDef h σ hv.2.1).det_pos).1
    simpa using this
  set P := ∏ w : {w : InfinitePlace E // w.IsComplex}, (h.gram w.1.embedding v).det.re with hPdef
  have hP : 0 < P := Finset.prod_pos fun w _ => hdetpos _
  set n := (Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex Λ.toAddSubgroup with hndef
  have hn0 : n ≠ 0 := IsFrame.relIndex_ne_zero hfg hv
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  let S : ReciprocityTheory.MultiplicativeHeights.HermForm E 2 :=
    { c := starRingEnd E, c_invol := fun x => star_star x, c_emb := fun σ x => hs σ x,
      G := J, G_herm := fun a b => by
        have := congrFun (congrFun hJ b) a
        simpa [conjTranspose_apply, starRingEnd_apply] using this }
  have hSh : ∀ x y, S.h x y = star x ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp [ReciprocityTheory.MultiplicativeHeights.HermForm.h, S, dotProduct, mulVec, mul_add, mul_assoc, starRingEnd_apply]
  have hstar : ∀ z : E, z ∈ (algebraMap (𝓞 E) E).range → star z ∈ (algebraMap (𝓞 E) E).range := by
    rintro _ ⟨w, rfl⟩
    have hw : IsIntegral ℤ (w : E) := w.2
    exact ⟨⟨star (w : E), hw.map (starRingEnd E).toIntAlgHom⟩, rfl⟩
  have hsd : ReciprocityTheory.MultiplicativeHeights.IsSelfDual S Λ := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨w, hw⟩ := (hdual y).1 hy x hx
      exact ⟨w, by rw [hSh]; exact hw⟩
    · refine (hdual x).2 fun y hy => ?_
      obtain ⟨w, hw⟩ := hx y hy
      have e : star y ⬝ᵥ (J *ᵥ x) = star (S.h x y) := by
        rw [hSh, star_form hJ]
      rw [e]
      exact hstar _ (RingHom.mem_range.2 ⟨w, hw⟩)
  have hb : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn Λ v := ⟨hv.1, hv.2.1, hv.2.2⟩
  have hbound := ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.vec_selfDual_bound
    (ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordForm S v) _
    (ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_fg hfg hb) (ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.intVec_le_coordLat hb)
    (ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.coordLat_selfDual hb hsd)
  rw [← ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.spanIdx_eq_vecIdx hb] at hbound
  set a := (ReciprocityTheory.MultiplicativeHeights.hGram S v).det with hadef
  have hbound' : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    have h0 : |Algebra.norm ℚ a| ≤ (n : ℚ) ^ 2 := hbound
    exact_mod_cast h0
  have hgram : ∀ σ : E →+* ℂ, h.gram σ v = (ReciprocityTheory.MultiplicativeHeights.hGram S v).map σ := by
    intro σ
    ext i j
    simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply, Matrix.map_apply, ReciprocityTheory.MultiplicativeHeights.hGram,
      hSh, hform]
  have hdetσ : ∀ σ : E →+* ℂ, (h.gram σ v).det = σ a := by
    intro σ
    rw [hgram, RingHom.map_det]
    rfl
  have hnorm : ∀ σ : E →+* ℂ, ‖σ a‖ = (h.gram σ v).det.re := by
    intro σ
    rw [← hdetσ]
    obtain ⟨h1, h2⟩ := Complex.lt_def.1 (gram_posDef h σ hv.2.1).det_pos
    have e : (h.gram σ v).det = ((h.gram σ v).det.re : ℂ) :=
      Complex.ext (by simp) (by simp at h2 ⊢; linarith)
    conv_lhs => rw [e]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hdetpos σ)]
  have hPn : P ≤ (n : ℝ) := by
    have hPa : P = ∏ w : {w : InfinitePlace E // w.IsComplex}, w.1 a := by
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← hnorm, InfinitePlace.norm_embedding_eq]
    have hP2 : P ^ 2 = ((|Algebra.norm ℚ a| : ℚ) : ℝ) := by
      rw [← InfinitePlace.prod_eq_abs_norm, hPa, ← Finset.prod_pow]
      refine Fintype.prod_equiv (Equiv.subtypeUnivEquiv (fun w => IsTotallyComplex.isComplex w))
        _ _ (fun w => ?_)
      show (w.1 a) ^ 2 = w.1 a ^ InfinitePlace.mult w.1
      rw [InfinitePlace.mult_isComplex w]
    nlinarith [hP, hn, hbound', hP2]

  set D := |(discr E : ℝ)| with hDdef
  have hD : 0 < D := abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero E))
  have hcardpl : Fintype.card (InfinitePlace E) = f := by
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero,
      zero_add]
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have h2v : 2 * Formalism.HermitianLatticesTheory.vInv E = D ^ ((1 : ℝ) / (2 * f)) := by
    unfold Formalism.HermitianLatticesTheory.vInv Formalism.HermitianLatticesTheory.fDeg
    rw [hcardpl]
    ring
  have hvpos : 0 < 2 * Formalism.HermitianLatticesTheory.vInv E := by rw [h2v]; positivity
  set R := Real.sqrt (2 * Formalism.HermitianLatticesTheory.vInv E) with hRdef
  have hR0 : 0 < R := Real.sqrt_pos.2 hvpos
  have hR2 : R ^ 2 = 2 * Formalism.HermitianLatticesTheory.vInv E := Real.sq_sqrt hvpos.le
  have hpow : ((R ^ 2) ^ 2) ^ f = D := by
    rw [hR2, h2v, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hD.le,
      ← Real.rpow_mul hD.le]
    convert Real.rpow_one D using 2
    field_simp
    norm_num
  have : DiscreteTopology (latE hv.2.1 Λ) := discrete_latE hfg hv
  have : IsZLattice ℝ (latE hv.2.1 Λ) := isZLattice_latE hfg hv
  obtain ⟨hconv, hsymm, hbdd, hmeas⟩ := ellS_props h hv.2.1 R
  have hcount := measure_div_le_ncard_inter_lattice volume (latE hv.2.1 Λ) (ellS h v R)
    hconv hsymm hbdd hmeas
  have : IsEmpty {w : InfinitePlace E // w.IsReal} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2⟩
  have hvol : (volume (ellS h v R)).toReal = (Real.pi ^ 2 / 2) ^ f * D / P := by
    rw [volume_ellS h hv.2.1 R, Finset.univ_eq_empty, Finset.prod_empty, one_mul,
      Finset.prod_congr rfl (fun w _ => volume_ellipsoid (gram_posDef h w.1.embedding hv.2.1) hR0),
      Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
      show Fintype.card {w : InfinitePlace E // w.IsComplex} = f from rfl, mul_pow, hpow]
  have hfinrk : Module.finrank ℝ (Fin 2 → mixedEmbedding.mixedSpace E) = 4 * f := by
    rw [Module.finrank_pi_fintype]
    simp only [mixedEmbedding.finrank, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, hfin]
    ring
  have hcov : ZLattice.covolume (latE hv.2.1 Λ) volume = ((2 : ℝ)⁻¹ ^ f * Real.sqrt D) ^ 2 / n := by
    rw [covolume_latE hfg hv, covolume_standardLattice, mixedEmbedding.covolume_integerLattice]
  rw [hvol, hfinrk, hcov] at hcount
  have h1 : 1 < (ellS h v R ∩ (latE hv.2.1 Λ : Set _)).ncard := by
    exact_mod_cast (one_lt_ratio hf hD hP hPn).trans_le hcount
  obtain ⟨y, hyS, hy0⟩ := Set.exists_ne_of_one_lt_ncard h1 0
  obtain ⟨x, hxS, rfl⟩ := mem_image_of_mem_ellS h hinv hv hR0.le hyS
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hy0 (map_zero _)
  refine ⟨x, hxS.1, hx0, fun φ => ?_⟩
  have h3 : Real.sqrt (h.form φ x x).re ≤ R := hxS.2 φ
  rw [Real.sqrt_le_left hR0.le, hR2] at h3
  exact h3

end GlobalTheory.ShortVec
