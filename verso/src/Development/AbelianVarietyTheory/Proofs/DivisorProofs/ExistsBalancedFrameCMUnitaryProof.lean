import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajorantEqSumNormSqOrthonormalFrame

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BalancedPointPf

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Rewrite using `[X.cmType (ComplexEmbedding.conjugate σ)]`. Simplify using `[ComplexEmbedding.conjugate, star_star]`.
-/
theorem conj_mem_iff (X : Data E r) (σ : E →+* ℂ) :
    ComplexEmbedding.conjugate σ ∈ X.Ψ ↔ σ ∉ X.Ψ := by
  rw [X.cmType (ComplexEmbedding.conjugate σ)]
  simp [ComplexEmbedding.conjugate, star_star]

/- English proof (translation)
Rewrite using `[← Finset.sum_add_sum_compl X.Ψ, Finset.sum_coe_sort X.Ψ f]`. Establish `h : ∑ σ ∈ X.Ψᶜ, f σ = ∑ σ ∈ X.Ψ, f σ`. Use `Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ hσ`. Rewrite `hσ` using `[Finset.mem_compl]`.

Conclude with `(conj_mem_iff X σ).2 hσ`. Introduce `σ hσ`. Rewrite using `[Finset.mem_compl]`. Conclude with `(X.cmType σ).1 hσ`. Introduce `σ _`.

Simplify using `[ComplexEmbedding.conjugate, star_star]`. Introduce `σ _`. Simplify using `[ComplexEmbedding.conjugate, star_star]`. Introduce `σ _`. Conclude with `(hf σ).symm`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_eq_two_mul (X : Data E r) (f : (E →+* ℂ) → ℝ)
    (hf : ∀ σ, f (ComplexEmbedding.conjugate σ) = f σ) :
    ∑ σ, f σ = 2 * ∑ τ : X.Ψ, f τ.1 := by
  classical
  rw [← Finset.sum_add_sum_compl X.Ψ, Finset.sum_coe_sort X.Ψ f]
  have h : ∑ σ ∈ X.Ψᶜ, f σ = ∑ σ ∈ X.Ψ, f σ := by
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      rw [Finset.mem_compl] at hσ
      exact (conj_mem_iff X σ).2 hσ
    · intro σ hσ
      rw [Finset.mem_compl]
      exact (X.cmType σ).1 hσ
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; simp [ComplexEmbedding.conjugate, star_star]
    · intro σ _; exact (hf σ).symm
  rw [h]; ring

/- English proof (translation)
Establish `h` using `sum_eq_two_mul X (fun _ => (1 : ℝ)) (fun _ => rfl)`. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h`. Rewrite `h` using `[Embeddings.card E ℂ]`. Establish `h2 : Module.finrank ℚ E = 2 * Fintype.card X.Ψ` using `by exact_mod_cast h`. Rewrite using `[fdeg, h2, Nat.mul_div_cancel_left _ two_pos]`.
-/
theorem card_Ψ (X : Data E r) : (Fintype.card X.Ψ : ℝ) = fdeg E := by
  have h := sum_eq_two_mul X (fun _ => (1 : ℝ)) (fun _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  rw [Embeddings.card E ℂ] at h
  have h2 : Module.finrank ℚ E = 2 * Fintype.card X.Ψ := by exact_mod_cast h
  rw [fdeg, h2, Nat.mul_div_cancel_left _ two_pos]

end

end GlobalTheory.BalancedPointPf

namespace GlobalTheory.BalancedPointPf

open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[ReciprocityTheory.MultiplicativeHeights.embVec, ComplexEmbedding.conjugate_coe_eq]`.
-/
theorem embVec_conj (σ : E →+* ℂ) (v : Fin r → E) :
    ReciprocityTheory.MultiplicativeHeights.embVec (ComplexEmbedding.conjugate σ) v = star (ReciprocityTheory.MultiplicativeHeights.embVec σ v) := by
  funext k
  simp [ReciprocityTheory.MultiplicativeHeights.embVec, ComplexEmbedding.conjugate_coe_eq]

/- English proof (translation)
Establish `hmo` using `GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth r X x ho`. Establish `hu : IsUnit (mat x τ).det` using `isUnit_iff_ne_zero.mpr (hmo.1 τ)`. Establish `e : H τ.1 = ((mat x τ)⁻¹)ᴴ * (mat x τ)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hu]`.

Simplify using the standard rewrite rules. Use `_ = ((mat x τ)⁻¹)ᴴ * ((mat x τ)ᴴ * H τ.1 * mat x τ) * (mat x τ)⁻¹ := by`. Rewrite using `[Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hH τ, Matrix.mul_one]`.

Rewrite using `[hmo.2 τ u, e, GlobalTheory.Up.BallExPf.hq_ct_mul]`. Both sides reduce to the same expression.
-/
theorem maj_eq_hq (X : Data E r) (H : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r)
    (ho : IsOrth X x) (hH : ∀ τ : X.Ψ, (mat x τ)ᴴ * H τ.1 * mat x τ = 1) (τ : X.Ψ) (u : Fin r → ℂ) :
    X.maj x τ u = ReciprocityTheory.MultiplicativeHeights.hq (H τ.1) u := by
  have hmo := GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth r X x ho
  have hu : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (hmo.1 τ)
  have e : H τ.1 = ((mat x τ)⁻¹)ᴴ * (mat x τ)⁻¹ := by
    calc H τ.1 = (mat x τ * (mat x τ)⁻¹)ᴴ * H τ.1 * (mat x τ * (mat x τ)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hu]; simp
      _ = ((mat x τ)⁻¹)ᴴ * ((mat x τ)ᴴ * H τ.1 * mat x τ) * (mat x τ)⁻¹ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hH τ, Matrix.mul_one]
  rw [hmo.2 τ u, e, GlobalTheory.Up.BallExPf.hq_ct_mul]
  rfl

/- English proof (translation)
Introduce `E _ _ _ r X`. Take `⟨M, hss, hNC⟩` from `ReciprocityTheory.MultiplicativeHeights.Closed.semistable E r (MajorantOrthogonality.pform X.toData) X.L' (MajorantOrthogonality.isLattice X) (MajorantOrthogonality.selfDual X)`. Establish `hex : ∀ τ : X.Ψ, ∃ x : Matrix (Fin r) (Fin r) ℂ, xᴴ * (MajorantOrthogonality.pform X.toData).G.map τ.1 * x = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r ∧ xᴴ * M.H τ.1 * x = 1` using `fun τ => by`. Take `⟨P, hP, hPg⟩` from `X.signature τ`. Conclude with `GlobalTheory.Up.BallExPf.exists_frame (M.posDef τ.1) (M.major τ.1) hP ((GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 P).1 hPg)`.

Use `choose y hy1 hy2 using hex`. Set `x0 : Frame X.Ψ r` to `fun τ => y τ`. Establish `h0 : IsOrth X.toData x0` using `fun τ => (GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 _).2 (hy1 τ)`. Establish `hmaj : ∀ (τ : X.Ψ) (u : Fin r → ℂ), X.maj x0 τ u = ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) u` using `maj_eq_hq X.toData M.H x0 h0 hy2`. Use `⟨x0, IW.orth_mem_dom X.toData x0 h0, ?_, ?_⟩` and prove the remaining obligations.

Introduce `N hN hlt`. Establish `key : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ≠ 0 → ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) (N.map τ.1 *ᵥ w) < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w`. Introduce `τ w hw`. Take `⟨c, hc0, hc1, hc⟩` from `hlt τ`. Establish `h1` using `hc w`.

Rewrite `h1` using `[hmaj, hmaj]`. Establish `hpos : 0 < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w` using `(M.posDef τ.1).re_dotProduct_pos hw`. Establish `hc2 : c ^ 2 < 1` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Use `hNC N hN fun σ u hu => ?_` and prove the remaining obligations.

Distinguish the cases in `hσ : σ ∈ X.Ψ`. Conclude with `key ⟨σ, hσ⟩ u hu`. Establish `hσ' : ComplexEmbedding.conjugate σ ∈ X.Ψ` using `(conj_mem_iff X.toData σ).2 hσ`. Establish `hsu : star u ≠ 0` using `fun h => hu (by simpa using congrArg star h)`. Establish `h` using `key ⟨_, hσ'⟩ (star u) hsu`.

Establish `e1 : M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ)` using `M.conj_compat σ`. Establish `e2 : N.map (ComplexEmbedding.conjugate σ) *ᵥ star u = star (N.map σ *ᵥ u)`. Use function extensionality and compare the values at `k`. Simplify using `[Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]`. Simplify using `only at h`.

Rewrite `h` using `[e1, e2, GlobalTheory.Up.BallExPf.hq_conj, GlobalTheory.Up.BallExPf.hq_conj]`. Then use the resulting hypothesis. Introduce `v hv hv0 classical set h : (E →+* ℂ) → ℝ := fun σ => ReciprocityTheory.MultiplicativeHeights.hq (M.H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ v) with hhdef`. Establish `hpos : ∀ σ, 0 < h σ`. Introduce `σ`. Use `(M.posDef σ).re_dotProduct_pos fun h0 => hv0 ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Use `congrFun h0 k` as an intermediate fact. Simplify using `only [ReciprocityTheory.MultiplicativeHeights.embVec, Pi.zero_apply, map_eq_zero] at this`. Conclude with `this`. Establish `hconj : ∀ σ, h (ComplexEmbedding.conjugate σ) = h σ`.

Introduce `σ`. Simplify using `only [hhdef]`. Rewrite using `[embVec_conj, show M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) from M.conj_compat σ, GlobalTheory.Up.BallExPf.hq_conj]`. Use `set B : Submodule (𝓞 E) (Fin r → E) := Submodule.span (𝓞 E) {v} with hB`. Establish `hrange : Set.range ![v] = {v}` using `by simp`.

Establish `hBL : B ≤ X.L'` using `by rw [hB, Submodule.span_le]; simpa using hv`. Establish `hbasis : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn B ![v]`. Use `⟨fun i => ?_, ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.eq_zero i]`. Conclude with `Submodule.subset_span rfl`.

Conclude with `linearIndependent_unique_iff.2 (by simpa using hv0)`. Rewrite `hy` using `[hB, Submodule.mem_span_singleton]`. Take `⟨a, rfl⟩` from `hy`. Rewrite using `[hrange]`. Establish `: (algebraMap (𝓞 E) E a) • v ∈ Submodule.span E ({v} : Set (Fin r → E))` using `Submodule.smul_mem _ _ (Submodule.subset_span rfl)`.

Rewrite `this` using `[algebraMap_smul]`. Then use the resulting hypothesis. Establish `hdeg` using `hss.2 B hBL 1 ![v] hbasis`. Establish `hidx : (Submodule.span (𝓞 E) (Set.range ![v])).toAddSubgroup.relIndex B.toAddSubgroup = 1`. Rewrite using `[hrange, ← hB]`. Conclude with `AddSubgroup.relIndex_self _`.

Establish `hdet : ∀ σ, (ReciprocityTheory.MultiplicativeHeights.gramC (M.H σ) σ ![v]).det.re = h σ`. Introduce `σ`. Rewrite using `[Matrix.det_unique]`. Both sides reduce to the same expression. Simplify using `only [ReciprocityTheory.MultiplicativeHeights.latDeg, hidx, Nat.cast_one, Real.log_one, zero_sub, hdet] at hdeg`.

Establish `hsum : 0 ≤ ∑ σ, Real.log (h σ)` using `by linarith`. Rewrite `hsum` using `[sum_eq_two_mul X.toData (fun σ => Real.log (h σ)) (fun σ => by simp only [hconj])]`. Establish `hlog : ∀ τ : X.Ψ, Real.log (h τ.1) ≤ h τ.1 - 1` using `fun τ => Real.log_le_sub_one_of_pos (hpos τ.1)`. Establish `hsum2 : 0 ≤ ∑ τ : X.Ψ, (h τ.1 - 1)` using `(by linarith : 0 ≤ ∑ τ : X.Ψ, Real.log (h τ.1)).trans (Finset.sum_le_sum fun τ _ => hlog τ)`. Rewrite `hsum2` using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_Ψ X.toData]`.

Establish `e : ∀ τ : X.Ψ, X.maj x0 τ (Data.emb τ.1 v) = h τ.1` using `fun τ => hmaj τ _`. Simplify using `only [e]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem balancedPoint :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.BalancedPointStatement E := by
  intro E _ _ _ r X
  obtain ⟨M, hss, hNC⟩ := ReciprocityTheory.MultiplicativeHeights.Closed.semistable E r (MajorantOrthogonality.pform X.toData) X.L'
    (MajorantOrthogonality.isLattice X) (MajorantOrthogonality.selfDual X)
  have hex : ∀ τ : X.Ψ, ∃ x : Matrix (Fin r) (Fin r) ℂ,
      xᴴ * (MajorantOrthogonality.pform X.toData).G.map τ.1 * x = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r ∧
        xᴴ * M.H τ.1 * x = 1 := fun τ => by
    obtain ⟨P, hP, hPg⟩ := X.signature τ
    exact GlobalTheory.Up.BallExPf.exists_frame (M.posDef τ.1) (M.major τ.1) hP
      ((GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 P).1 hPg)
  choose y hy1 hy2 using hex
  let x0 : Frame X.Ψ r := fun τ => y τ
  have h0 : IsOrth X.toData x0 := fun τ => (GlobalTheory.Up.BallExPf.gram_iff X.toData τ.1 _).2 (hy1 τ)
  have hmaj : ∀ (τ : X.Ψ) (u : Fin r → ℂ), X.maj x0 τ u = ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) u :=
    maj_eq_hq X.toData M.H x0 h0 hy2
  refine ⟨x0, IW.orth_mem_dom X.toData x0 h0, ?_, ?_⟩
  · intro N hN hlt
    have key : ∀ (τ : X.Ψ) (w : Fin r → ℂ), w ≠ 0 →
        ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) (N.map τ.1 *ᵥ w) < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := by
      intro τ w hw
      obtain ⟨c, hc0, hc1, hc⟩ := hlt τ
      have h1 := hc w
      rw [hmaj, hmaj] at h1
      have hpos : 0 < ReciprocityTheory.MultiplicativeHeights.hq (M.H τ.1) w := (M.posDef τ.1).re_dotProduct_pos hw
      have hc2 : c ^ 2 < 1 := by nlinarith
      nlinarith
    refine hNC N hN fun σ u hu => ?_
    by_cases hσ : σ ∈ X.Ψ
    · exact key ⟨σ, hσ⟩ u hu
    · have hσ' : ComplexEmbedding.conjugate σ ∈ X.Ψ := (conj_mem_iff X.toData σ).2 hσ
      have hsu : star u ≠ 0 := fun h => hu (by simpa using congrArg star h)
      have h := key ⟨_, hσ'⟩ (star u) hsu
      have e1 : M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) := M.conj_compat σ
      have e2 : N.map (ComplexEmbedding.conjugate σ) *ᵥ star u = star (N.map σ *ᵥ u) := by
        funext k
        simp [Matrix.mulVec, dotProduct, ComplexEmbedding.conjugate_coe_eq]
      simp only at h
      rwa [e1, e2, GlobalTheory.Up.BallExPf.hq_conj, GlobalTheory.Up.BallExPf.hq_conj] at h
  · intro v hv hv0
    classical
    set h : (E →+* ℂ) → ℝ := fun σ => ReciprocityTheory.MultiplicativeHeights.hq (M.H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ v) with hhdef
    have hpos : ∀ σ, 0 < h σ := by
      intro σ
      refine (M.posDef σ).re_dotProduct_pos fun h0 => hv0 ?_
      funext k
      have := congrFun h0 k
      simp only [ReciprocityTheory.MultiplicativeHeights.embVec, Pi.zero_apply, map_eq_zero] at this
      exact this
    have hconj : ∀ σ, h (ComplexEmbedding.conjugate σ) = h σ := by
      intro σ
      simp only [hhdef]
      rw [embVec_conj, show M.H (ComplexEmbedding.conjugate σ) = (M.H σ).map (starRingEnd ℂ) from
        M.conj_compat σ, GlobalTheory.Up.BallExPf.hq_conj]

    set B : Submodule (𝓞 E) (Fin r → E) := Submodule.span (𝓞 E) {v} with hB
    have hrange : Set.range ![v] = {v} := by simp
    have hBL : B ≤ X.L' := by rw [hB, Submodule.span_le]; simpa using hv
    have hbasis : ReciprocityTheory.MultiplicativeHeights.IsKBasisIn B ![v] := by
      refine ⟨fun i => ?_, ?_, fun y hy => ?_⟩
      · rw [Fin.eq_zero i]; exact Submodule.subset_span rfl
      · exact linearIndependent_unique_iff.2 (by simpa using hv0)
      · rw [hB, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hy
        rw [hrange]
        have : (algebraMap (𝓞 E) E a) • v ∈ Submodule.span E ({v} : Set (Fin r → E)) :=
          Submodule.smul_mem _ _ (Submodule.subset_span rfl)
        rwa [algebraMap_smul] at this
    have hdeg := hss.2 B hBL 1 ![v] hbasis
    have hidx : (Submodule.span (𝓞 E) (Set.range ![v])).toAddSubgroup.relIndex B.toAddSubgroup = 1 := by
      rw [hrange, ← hB]; exact AddSubgroup.relIndex_self _
    have hdet : ∀ σ, (ReciprocityTheory.MultiplicativeHeights.gramC (M.H σ) σ ![v]).det.re = h σ := by
      intro σ
      rw [Matrix.det_unique]
      rfl
    simp only [ReciprocityTheory.MultiplicativeHeights.latDeg, hidx, Nat.cast_one, Real.log_one, zero_sub, hdet] at hdeg
    have hsum : 0 ≤ ∑ σ, Real.log (h σ) := by linarith
    rw [sum_eq_two_mul X.toData (fun σ => Real.log (h σ)) (fun σ => by simp only [hconj])] at hsum
    have hlog : ∀ τ : X.Ψ, Real.log (h τ.1) ≤ h τ.1 - 1 := fun τ => Real.log_le_sub_one_of_pos (hpos τ.1)
    have hsum2 : 0 ≤ ∑ τ : X.Ψ, (h τ.1 - 1) :=
      (by linarith : 0 ≤ ∑ τ : X.Ψ, Real.log (h τ.1)).trans (Finset.sum_le_sum fun τ _ => hlog τ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      card_Ψ X.toData] at hsum2
    have e : ∀ τ : X.Ψ, X.maj x0 τ (Data.emb τ.1 v) = h τ.1 := fun τ => hmaj τ _
    simp only [e]
    linarith

end GlobalTheory.BalancedPointPf
