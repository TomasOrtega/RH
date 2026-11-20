import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace CoefficientIntegrals

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/- English proof (translation)
Establish `h1 : coefOn σ v v g = ⟪v, v⟫_ℂ + ⟪v, σ (umat g) v - v⟫_ℂ`. Simplify using `[coefOn, inner_sub_right]`. Establish `h2 : ‖⟪v, σ (umat g) v - v⟫_ℂ‖ ≤ 1 / 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `(abs_le.1 ((Complex.abs_re_le_norm _).trans h2)).1`.

Establish `h5 : (⟪v, v⟫_ℂ).re = 1`. Use `inner_self_eq_norm_sq (𝕜 := ℂ) v` as an intermediate fact. Rewrite `this` using `[hv]`. Simplify using `using this`. Rewrite using `[h1, Complex.add_re, h5]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem re_coef_ge {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {g : UJ ε} {v : H} (hv : ‖v‖ = 1)
    (h : ‖σ (umat g) v - v‖ ≤ ‖v‖ / 2) : (1 / 2 : ℝ) ≤ (coefOn σ v v g).re := by
  have h1 : coefOn σ v v g = ⟪v, v⟫_ℂ + ⟪v, σ (umat g) v - v⟫_ℂ := by
    simp [coefOn, inner_sub_right]
  have h2 : ‖⟪v, σ (umat g) v - v⟫_ℂ‖ ≤ 1 / 2 := by
    calc _ ≤ ‖v‖ * ‖σ (umat g) v - v‖ := norm_inner_le_norm _ _
      _ ≤ 1 / 2 := by rw [hv] at h ⊢; linarith
  have h4 := (abs_le.1 ((Complex.abs_re_le_norm _).trans h2)).1
  have h5 : (⟪v, v⟫_ℂ).re = 1 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) v
    rw [hv] at this
    simpa using this
  rw [h1, Complex.add_re, h5]
  linarith

def sumCoef {ι : Type} [Fintype ι] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : ι → H) (g : UJ ε) : ℂ :=
  ∑ i, coefOn σ (v i) (v i) g

/- English proof (translation)
Unfold `sumCoef`. Rewrite using `[Complex.re_sum]`. Establish `hi : ∀ i, (1 / 2 : ℝ) ≤ (coefOn σ (v i) (v i) g).re` using `fun i => re_coef_ge (hv.1 i) (hg _ (hW i))`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := Finset.sum_le_sum fun i _ => hi i`.
-/
theorem re_sumCoef_ge {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H}
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) {g : UJ ε}
    (hg : ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2) :
    (Fintype.card ι : ℝ) / 2 ≤ (sumCoef σ v g).re := by
  unfold sumCoef
  rw [Complex.re_sum]
  have hi : ∀ i, (1 / 2 : ℝ) ≤ (coefOn σ (v i) (v i) g).re := fun i =>
    re_coef_ge (hv.1 i) (hg _ (hW i))
  calc (Fintype.card ι : ℝ) / 2 = ∑ _i : ι, (1 / 2 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => hi i

/- English proof (translation)
Establish `hexp : (fun g : UJ ε => sumCoef σ v g * star (sumCoef σ v g)) = fun g => ∑ i, ∑ j, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g)`. Use function extensionality and compare the values at `g`. Unfold `sumCoef`. Rewrite using `[star_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Establish `hint : ∀ i j, Integrable (fun g => coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g)) (muG ε)` using `fun i j => (hd.2 _ _ _ _).1`. Establish `hij : ∀ i j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) = if i = j then 1 / (d : ℂ) else 0`. Introduce `i j`. Rewrite using `[(hd.2 _ _ _ _).2, orthonormal_iff_ite.mp hv j i, orthonormal_iff_ite.mp hv i j]`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, Ne.symm h]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hexp]`. Conclude with `integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j`. Rewrite using `[hexp, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Conclude with `integral_finset_sum _ fun j _ => hint i j`. Use `_ = _ := by`. Simplify using `only [hij, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_sumCoef {ι : Type} [Fintype ι] [DecidableEq ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {d : ℝ} (hd : IsFdeg (muG ε) σ d) {v : ι → H} (hv : Orthonormal ℂ v) :
    Integrable (fun g => sumCoef σ v g * star (sumCoef σ v g)) (muG ε) ∧
      ∫ g, sumCoef σ v g * star (sumCoef σ v g) ∂(muG ε) = (Fintype.card ι : ℂ) / (d : ℂ) := by
  have hexp : (fun g : UJ ε => sumCoef σ v g * star (sumCoef σ v g)) = fun g =>
      ∑ i, ∑ j, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) := by
    funext g
    unfold sumCoef
    rw [star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hint : ∀ i j, Integrable
      (fun g => coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g)) (muG ε) :=
    fun i j => (hd.2 _ _ _ _).1
  have hij : ∀ i j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) =
      if i = j then 1 / (d : ℂ) else 0 := by
    intro i j
    rw [(hd.2 _ _ _ _).2, orthonormal_iff_ite.mp hv j i, orthonormal_iff_ite.mp hv i j]
    by_cases h : i = j
    · subst h
      simp
    · simp [h, Ne.symm h]
  refine ⟨?_, ?_⟩
  · rw [hexp]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j
  · rw [hexp, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
    calc _ = ∑ i, ∑ j, ∫ g, coefOn σ (v i) (v i) g * star (coefOn σ (v j) (v j) g) ∂(muG ε) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          exact integral_finset_sum _ fun j _ => hint i j
      _ = _ := by
          simp only [hij, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul]
          ring

/- English proof (translation)
Use `set m := (Fintype.card ι : ℝ) with hmdef`. Take `⟨hint, hval⟩` from `integral_sumCoef hd hv`. Set `f : UJ ε → ℝ` to `fun g => (sumCoef σ v g * star (sumCoef σ v g)).re`. Establish `hfint : Integrable f (muG ε)` using `hint.re`. Establish `hfn : ∀ g, f g = Complex.normSq (sumCoef σ v g)` using `fun g => by`.

Simplify using `[f, Complex.star_def, Complex.mul_conj]`. Establish `hf0 : ∀ g, 0 ≤ f g` using `fun g => by rw [hfn]; exact Complex.normSq_nonneg _`. Establish `hm0 : 0 ≤ m` using `by positivity`. Establish `hK' : ∀ g ∈ K, (m / 2) ^ 2 ≤ f g`. Introduce `g hg`.

Establish `h1` using `re_sumCoef_ge hv hW (hK g hg)`. Rewrite using `[hfn, Complex.normSq_apply]`. Use polynomial arithmetic with `[sq_nonneg (sumCoef σ v g).im]`. Establish `hset : (m / 2) ^ 2 * (muG ε).real K ≤ ∫ g in K, f g ∂(muG ε)`. Use `setIntegral_ge_of_const_le hKm hKf hK' hfint.integrableOn` as an intermediate fact.

Rewrite `this` using `[smul_eq_mul, mul_comm]`. Then use the resulting hypothesis. Establish `hle : ∫ g in K, f g ∂(muG ε) ≤ ∫ g, f g ∂(muG ε)` using `setIntegral_le_integral hfint (Filter.Eventually.of_forall hf0)`. Establish `htot : ∫ g, f g ∂(muG ε) = m / d` using `by show ∫ g, (sumCoef σ v g * star (sumCoef σ v g)).re ∂(muG ε) = m / d`. Establish `hc : ((Fintype.card ι : ℂ) / (d : ℂ)) = ((m / d : ℝ) : ℂ)`. Rewrite using `[hmdef]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hr` using `integral_re hint`. Simplify using `only [RCLike.re_to_complex] at hr`. Rewrite using `[hr, hval, hc, Complex.ofReal_re]`.

Establish `hd0` using `hd.1`. Break down `eq_or_lt_of_le hm0 with h0 | hpos` into its components or cases. Rewrite using `[← h0]`. Conclude with `div_nonneg (by norm_num) (mul_pos hd0 hKpos).le`. Rewrite using `[le_div_iff₀ (mul_pos hd0 hKpos)]`.

Establish `hA : (m / 2) ^ 2 * (muG ε).real K ≤ m / d` using `(hset.trans hle).trans_eq htot`. Establish `hB : (m / 2) ^ 2 * (muG ε).real K * d ≤ m`. Use `mul_le_mul_of_nonneg_right hA hd0.le` as an intermediate fact. Rewrite `this` using `[div_mul_cancel₀ _ hd0.ne']`. Then use the resulting hypothesis. Use polynomial arithmetic with `[hB, hpos, mul_pos hd0 hKpos]`.
-/
theorem card_le {ι : Type} [Fintype ι] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (hd : IsFdeg (muG ε) σ d) {W : Submodule ℂ H} {K : Set (UJ ε)} (hKm : MeasurableSet K)
    (hKf : muG ε K ≠ ⊤) (hKpos : 0 < (muG ε).real K)
    (hK : ∀ g ∈ K, ∀ w ∈ W, ‖σ (umat g) w - w‖ ≤ ‖w‖ / 2)
    {v : ι → H} (hv : Orthonormal ℂ v) (hW : ∀ i, v i ∈ W) :
    (Fintype.card ι : ℝ) ≤ 4 / (d * (muG ε).real K) := by
  classical
  set m := (Fintype.card ι : ℝ) with hmdef
  obtain ⟨hint, hval⟩ := integral_sumCoef hd hv
  let f : UJ ε → ℝ := fun g => (sumCoef σ v g * star (sumCoef σ v g)).re
  have hfint : Integrable f (muG ε) := hint.re
  have hfn : ∀ g, f g = Complex.normSq (sumCoef σ v g) := fun g => by
    simp [f, Complex.star_def, Complex.mul_conj]
  have hf0 : ∀ g, 0 ≤ f g := fun g => by rw [hfn]; exact Complex.normSq_nonneg _
  have hm0 : 0 ≤ m := by positivity
  have hK' : ∀ g ∈ K, (m / 2) ^ 2 ≤ f g := by
    intro g hg
    have h1 := re_sumCoef_ge hv hW (hK g hg)
    rw [hfn, Complex.normSq_apply]
    nlinarith [sq_nonneg (sumCoef σ v g).im]
  have hset : (m / 2) ^ 2 * (muG ε).real K ≤ ∫ g in K, f g ∂(muG ε) :=
    by
      have := setIntegral_ge_of_const_le hKm hKf hK' hfint.integrableOn
      rwa [smul_eq_mul, mul_comm] at this
  have hle : ∫ g in K, f g ∂(muG ε) ≤ ∫ g, f g ∂(muG ε) :=
    setIntegral_le_integral hfint (Filter.Eventually.of_forall hf0)
  have htot : ∫ g, f g ∂(muG ε) = m / d := by
    show ∫ g, (sumCoef σ v g * star (sumCoef σ v g)).re ∂(muG ε) = m / d
    have hc : ((Fintype.card ι : ℂ) / (d : ℂ)) = ((m / d : ℝ) : ℂ) := by
      rw [hmdef]
      push_cast
      ring
    have hr := integral_re hint
    simp only [RCLike.re_to_complex] at hr
    rw [hr, hval, hc, Complex.ofReal_re]
  have hd0 := hd.1
  rcases eq_or_lt_of_le hm0 with h0 | hpos
  · rw [← h0]
    exact div_nonneg (by norm_num) (mul_pos hd0 hKpos).le
  · rw [le_div_iff₀ (mul_pos hd0 hKpos)]
    have hA : (m / 2) ^ 2 * (muG ε).real K ≤ m / d := (hset.trans hle).trans_eq htot
    have hB : (m / 2) ^ 2 * (muG ε).real K * d ≤ m := by
      have := mul_le_mul_of_nonneg_right hA hd0.le
      rwa [div_mul_cancel₀ _ hd0.ne'] at this
    nlinarith [hB, hpos, mul_pos hd0 hKpos]

end CoefficientIntegrals

open CoefficientIntegrals in
/- English proof (translation)
Introduce `n ε H _ _ _ σ _ d hd W U hU hUW`. Use `haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance`. Take `⟨K, hKn, hKU, hKc⟩` from `local_compact_nhds hU`. Establish `hKm : MeasurableSet K` using `hKc.isClosed.measurableSet`. Establish `hKf : muG ε K ≠ ⊤` using `hKc.measure_lt_top.ne`.

Establish `hKpos : 0 < (muG ε).real K` using `ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne' hKf`. Establish `hbound : ∀ (m : ℕ) (v : Fin m → H), Orthonormal ℂ v → (∀ i, v i ∈ W) → (m : ℝ) ≤ 4 / (d * (muG ε).real K)`. Introduce `m v hv hvW`. Simplify using `using card_le hd hKm hKf hKpos (fun g hg => hUW g (hKU hg)) hv hvW`. Assume the negation of the conclusion as `hfin`.

Take `⟨m, hm⟩` from `exists_nat_gt (4 / (d * (muG ε).real K))`. Set `bW` to `Module.Basis.ofVectorSpace ℂ W`. Establish `hI : (Module.Basis.ofVectorSpaceIndex ℂ W).Infinite`. Introduce `hfinI`. Use `haveI : Finite (Module.Basis.ofVectorSpaceIndex ℂ W) := hfinI.to_subtype`.

Conclude with `hfin (Module.Finite.of_basis bW)`. Take `⟨t, htsub, htcard⟩` from `hI.exists_subset_card_eq m`. Set `u : t → W` to `fun x => bW ⟨x.1, htsub x.2⟩`. Establish `hu : LinearIndependent ℂ u` using `bW.linearIndependent.comp _ (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))`. Set `F : Submodule ℂ W` to `Submodule.span ℂ (Set.range u)`.

Use `haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)`. Establish `hF : Module.finrank ℂ F = m`. Rewrite using `[finrank_span_eq_card hu]`. Simplify using `[htcard]`. Set `ob` to `stdOrthonormalBasis ℂ F`.

Set `v : Fin (Module.finrank ℂ F) → H` to `fun i => ((ob i : F) : W)`. Apply the tactic sequence `have hv : Orthonormal ℂ v := (ob.orthonormal.comp_linearIsometry F.subtypeₗᵢ).comp_linearIsometry W.subtypeₗᵢ`. Establish `h` using `hbound _ v hv (fun i => ((ob i : F) : W).2)`. Rewrite `h` using `[hF]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem c7 : FormalDegreeFiniteDim := by
  intro n ε H _ _ _ σ _ d hd W U hU hUW
  classical
  haveI : (muG ε).IsHaarMeasure := by unfold muG; infer_instance
  obtain ⟨K, hKn, hKU, hKc⟩ := local_compact_nhds hU
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKf : muG ε K ≠ ⊤ := hKc.measure_lt_top.ne
  have hKpos : 0 < (muG ε).real K :=
    ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne' hKf
  have hbound : ∀ (m : ℕ) (v : Fin m → H), Orthonormal ℂ v → (∀ i, v i ∈ W) →
      (m : ℝ) ≤ 4 / (d * (muG ε).real K) := by
    intro m v hv hvW
    simpa using card_le hd hKm hKf hKpos (fun g hg => hUW g (hKU hg)) hv hvW
  by_contra hfin
  obtain ⟨m, hm⟩ := exists_nat_gt (4 / (d * (muG ε).real K))
  let bW := Module.Basis.ofVectorSpace ℂ W
  have hI : (Module.Basis.ofVectorSpaceIndex ℂ W).Infinite := by
    intro hfinI
    haveI : Finite (Module.Basis.ofVectorSpaceIndex ℂ W) := hfinI.to_subtype
    exact hfin (Module.Finite.of_basis bW)
  obtain ⟨t, htsub, htcard⟩ := hI.exists_subset_card_eq m
  let u : t → W := fun x => bW ⟨x.1, htsub x.2⟩
  have hu : LinearIndependent ℂ u :=
    bW.linearIndependent.comp _ (fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h))
  let F : Submodule ℂ W := Submodule.span ℂ (Set.range u)
  haveI : FiniteDimensional ℂ F := FiniteDimensional.span_of_finite ℂ (Set.finite_range u)
  have hF : Module.finrank ℂ F = m := by
    rw [finrank_span_eq_card hu]
    simp [htcard]
  let ob := stdOrthonormalBasis ℂ F
  let v : Fin (Module.finrank ℂ F) → H := fun i => ((ob i : F) : W)
  have hv : Orthonormal ℂ v :=
    (ob.orthonormal.comp_linearIsometry F.subtypeₗᵢ).comp_linearIsometry W.subtypeₗᵢ
  have h := hbound _ v hv (fun i => ((ob i : F) : W).2)
  rw [hF] at h
  linarith

end Formalism.L2.SG.Pf.admitted
