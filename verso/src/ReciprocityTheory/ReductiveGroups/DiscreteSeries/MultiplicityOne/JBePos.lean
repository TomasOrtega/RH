import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSInt
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBePosB

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

/- English proof (translation)
Establish `hS` using `stSInt h`. Take `⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, -⟩` from `h`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, a13, -, a15, a16, -, a18, -, a20, a21, a22, -, -, -, -, -⟩` from `h1`. Conclude with `⟨a22, a21, a20, a16, a15, a13 k r Wp Wp D, a18, h17, h16, fun b hb => hS k r Wp D hD b hb⟩`.
-/
theorem bePos_hyp (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) : BesselPositivity.Hyp D := by
  have hS := stSInt h
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, a13, -, a15, a16, -, a18, -, a20, a21, a22, -, -, -, -, -⟩ := h1
  exact ⟨a22, a21, a20, a16, a15, a13 k r Wp Wp D, a18, h17, h16, fun b hb => hS k r Wp D hD b hb⟩

/- English proof (translation)
Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Simplify using `only [AB, aM, nR]`. Use `push_cast`. Use polynomial arithmetic with `[mul_nonneg hk hr, mul_nonneg (mul_nonneg hk hr) hr, mul_nonneg (mul_nonneg hk hk) hr, mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg hr hr, mul_nonneg hk hk]`.
-/
private theorem two_mul_AB_le_aM (k r : ℕ) : 2 * AB k r ≤ aM k r := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  simp only [AB, aM, nR]
  push_cast
  nlinarith [mul_nonneg hk hr, mul_nonneg (mul_nonneg hk hr) hr, mul_nonneg (mul_nonneg hk hk) hr,
    mul_nonneg (mul_nonneg hr hr) hr, mul_nonneg (mul_nonneg hk hk) hk, mul_nonneg hr hr, mul_nonneg hk hk]

/- English proof (translation)
Conclude with `two_mul_AB_le_aM k r`.
-/
theorem two_AB_le_aM {k r : ℕ} (hk : 1 ≤ k) : 2 * AB k r ≤ aM k r := by
  exact two_mul_AB_le_aM k r

/- English proof (translation)
Take `⟨C, hC⟩` from `hu`. Use `⟨max C 0, ⟨?_, le_max_right _ _, (two_mul_AB_le_aM k r).trans haM, ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `X.rep.2.2 u`. Conclude with `(continuous_const.inner continuous_id).comp_continuousOn h1`. Introduce `y hy`.

Establish `ht : 0 ≤ gN y ^ (-X.a)` using `Real.rpow_nonneg (Real.sqrt_nonneg _) _`. Conclude with `(hC y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)`.
-/
private theorem exists_bessel_coef_of_mem_Vfl {k r : ℕ} (X : SigData k r) (haM : aM k r ≤ X.a) {u : X.Hs}
    (hu : u ∈ Vfl X) : ∃ C : ℝ, BesselPositivity.Coef (mc X u X.w) C X.a := by
  obtain ⟨C, hC⟩ := hu
  refine ⟨max C 0, ⟨?_, le_max_right _ _, (two_mul_AB_le_aM k r).trans haM, ?_⟩⟩
  ·
    have h1 := X.rep.2.2 u
    exact (continuous_const.inner continuous_id).comp_continuousOn h1
  · intro y hy
    have ht : 0 ≤ gN y ^ (-X.a) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    exact (hC y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht)

/- English proof (translation)
Conclude with `exists_bessel_coef_of_mem_Vfl X haM hu`.
-/
theorem bePos_coef {k r : ℕ} (X : SigData k r) (hk : 1 ≤ k) (haM : aM k r ≤ X.a) {u : X.Hs} (hu : u ∈ Vfl X) :
    ∃ C : ℝ, BesselPositivity.Coef (mc X u X.w) C X.a := by
  exact exists_bessel_coef_of_mem_Vfl X haM hu

/- English proof (translation)
Set `L : E →ₗᵢ[ℂ] E` to `⟨T.toLinearMap, hT⟩`. Establish `h1 : ⟪T x, T (S x)⟫_ℂ = ⟪x, S x⟫_ℂ` using `L.inner_map_map x (S x)`. Establish `h2 : T (S x) = x`. Use `congrArg (fun F : E →L[ℂ] E => F x) hTS` as an intermediate fact. Simplify using `using this`.

Rewrite `h1` using `[h2]`. Conclude with `h1.symm`.
-/
private lemma inner_apply_right_inverse_eq_inner_of_isometry {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (T S : E →L[ℂ] E)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (hTS : T.comp S = 1) (x : E) : ⟪x, S x⟫_ℂ = ⟪T x, x⟫_ℂ := by
  let L : E →ₗᵢ[ℂ] E := ⟨T.toLinearMap, hT⟩
  have h1 : ⟪T x, T (S x)⟫_ℂ = ⟪x, S x⟫_ℂ := L.inner_map_map x (S x)
  have h2 : T (S x) = x := by
    have := congrArg (fun F : E →L[ℂ] E => F x) hTS
    simpa using this
  rw [h2] at h1
  exact h1.symm

/- English proof (translation)
Take `⟨hd0, hdS⟩` from `hd`. Establish `hdC : (d : ℂ) ≠ 0` using `by exact_mod_cast hd0.ne'`. Establish `hA : ⟪ξ, beOp D X u u ξ⟫_ℂ = ∫ p, ⟪ξ, beInt D X u u p ξ⟫_ℂ ∂(D.μW.prod D.μN)`. Unfold `beOp`. Rewrite using `[ContinuousLinearMap.integral_apply hI, integral_inner (hI.apply_continuousLinearMap ξ)]`.

Establish `hGae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r` using `by first`. Consider the case `exact ae_iff.2 D.haarG.conc`. Consider the case `exact measure_mono_null (fun a ha => ha) D.haarG.conc`. Rewrite using `[hA, ← BesselPositivity.fubini1 D H hc ξ, ← integral_const_mul]`. Apply `integral_congr_ae` to reduce the goal to its premises.

Use `filter_upwards [BesselPositivity.ae_SS (D := D)] with p hp`. Establish `hs : BesselPositivity.sP p ∈ GV k r` using `BesselPositivity.sP_mem H.cg hp`. Establish `hSch : ∫ g, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) ∂D.μG = mc X u u (BesselPositivity.sP p) / d`. Establish `hc1 : ∀ᵐ g ∂D.μG, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) = mc X (X.σ (BesselPositivity.sP p) u) X.w (Matrix.of g) * star (mc X u X.w (Matrix.of g))` using `by filter_upwards [hGae] with g hg`. Simplify using `only [mc, X.rep.1.2 _ hg _ hs, ContinuousLinearMap.comp_apply]`.

Rewrite using `[integral_congr_ae hc1, ((hdS (X.σ (BesselPositivity.sP p) u) X.w u X.w).2)]`. Simplify using `only [mc, inner_self_eq_norm_sq_to_K, X.w_norm]`. Simplify using the standard rewrite rules. Rewrite using `[hSch]`. Establish `ha` using `hp.1`.

Apply the tactic sequence `have hinv := inner_apply_right_inverse_eq_inner_of_isometry (D.π (Matrix.of p.1)) (D.π (Matrix.of p.1)⁻¹) (D.π_unitary _ ha) (by`. Rewrite using `[← D.π_rep.2 _ ha _ ((H.cw k r D.z).inv_mem _ ha), Matrix.mul_nonsing_inv _ ((H.cw k r D.z).unit _ ha), D.π_rep.1]) ξ`. Establish `hc2 : star ⟪ξ, D.π (Matrix.of p.1) ξ⟫_ℂ = ⟪D.π (Matrix.of p.1) ξ, ξ⟫_ℂ` using `inner_conj_symm _ _`. Simplify using `only [beInt, BesselPositivity.Kf, BesselPositivity.PiO, BesselPositivity.sP, inner_smul_right, ContinuousLinearMap.smul_apply, inner_smul_right, star_mul', hinv, hc2]`. Clear the denominators using the available nonvanishing facts.
-/
theorem bePos_inner_eq {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (H : BesselPositivity.Hyp D)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} {C a : ℝ} (hc : BesselPositivity.Coef (mc X u X.w) C a) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ = (d : ℂ) * ∫ g, BesselPositivity.phi D (mc X u X.w) ξ (Matrix.of g) ∂D.μG := by
  obtain ⟨hd0, hdS⟩ := hd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have hA : ⟪ξ, beOp D X u u ξ⟫_ℂ = ∫ p, ⟪ξ, beInt D X u u p ξ⟫_ℂ ∂(D.μW.prod D.μN) := by
    unfold beOp
    rw [ContinuousLinearMap.integral_apply hI, integral_inner (hI.apply_continuousLinearMap ξ)]
  have hGae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by
    first
    | exact ae_iff.2 D.haarG.conc
    | exact measure_mono_null (fun a ha => ha) D.haarG.conc
  rw [hA, ← BesselPositivity.fubini1 D H hc ξ, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [BesselPositivity.ae_SS (D := D)] with p hp
  have hs : BesselPositivity.sP p ∈ GV k r := BesselPositivity.sP_mem H.cg hp

  have hSch : ∫ g, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) ∂D.μG =
      mc X u u (BesselPositivity.sP p) / d := by
    have hc1 : ∀ᵐ g ∂D.μG, mc X u X.w (Matrix.of g * BesselPositivity.sP p) * star (mc X u X.w (Matrix.of g)) =
        mc X (X.σ (BesselPositivity.sP p) u) X.w (Matrix.of g) * star (mc X u X.w (Matrix.of g)) := by
      filter_upwards [hGae] with g hg
      simp only [mc, X.rep.1.2 _ hg _ hs, ContinuousLinearMap.comp_apply]
    rw [integral_congr_ae hc1, ((hdS (X.σ (BesselPositivity.sP p) u) X.w u X.w).2)]
    simp only [mc, inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hSch]
  have ha := hp.1
  have hinv := inner_apply_right_inverse_eq_inner_of_isometry (D.π (Matrix.of p.1)) (D.π (Matrix.of p.1)⁻¹) (D.π_unitary _ ha) (by
    rw [← D.π_rep.2 _ ha _ ((H.cw k r D.z).inv_mem _ ha), Matrix.mul_nonsing_inv _ ((H.cw k r D.z).unit _ ha),
      D.π_rep.1]) ξ
  have hc2 : star ⟪ξ, D.π (Matrix.of p.1) ξ⟫_ℂ = ⟪D.π (Matrix.of p.1) ξ, ξ⟫_ℂ := inner_conj_symm _ _
  simp only [beInt, BesselPositivity.Kf, BesselPositivity.PiO, BesselPositivity.sP, inner_smul_right, ContinuousLinearMap.smul_apply,
    inner_smul_right, star_mul', hinv, hc2]
  field_simp

/- English proof (translation)
Take `⟨C, hc⟩` from `exists_bessel_coef_of_mem_Vfl X haM hu`. Establish `H` using `bePos_hyp h D hD`. Rewrite using `[bePos_inner_eq D X H hd hc ξ hI, BesselPositivity.phi_eq D H hc ξ]`.
-/
theorem bePos_identity (h : UnitaryGroupStructuralFacts) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [FiniteDimensional ℂ Wp] (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (haM : aM k r ≤ X.a)
    {d : ℝ} (hd : IsFdegG D X d) {u : X.Hs} (hu : u ∈ Vfl X) (ξ : Wp)
    (hI : Integrable (beInt D X u u) (D.μW.prod D.μN)) :
    ⟪ξ, beOp D X u u ξ⟫_ℂ =
      (d : ℂ) * ((∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG : ℝ) : ℂ) := by
  obtain ⟨C, hc⟩ := exists_bessel_coef_of_mem_Vfl X haM hu
  have H := bePos_hyp h D hD
  rw [bePos_inner_eq D X H hd hc ξ hI, BesselPositivity.phi_eq D H hc ξ]

/- English proof (translation)
Introduce `k r Wp _ _ _ D X hD hX ha u hu ξ`. Take `⟨d, hd⟩` from `stSchurG k r Wp D X hD hX`. Distinguish the cases in `hI : Integrable (beInt D X u u) (D.μW.prod D.μN)`. Use `swap`. Establish `h0 : beOp D X u u = 0` using `integral_undef hI`.

Rewrite using `[h0]`. Simplify using the standard rewrite rules. Rewrite using `[bePos_identity h D X hD ha hd hu ξ hI]`. Establish `h0 : 0 ≤ ∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG` using `integral_nonneg fun g => mul_nonneg (BesselPositivity.bet_nonneg (D := D) _) (sq_nonneg _)`. Rewrite using `[← Complex.ofReal_mul, Complex.ofReal_re]`.

Conclude with `mul_nonneg hd.1.le h0`.
-/
theorem stBePos (h : UnitaryGroupStructuralFacts) : StBePos := by
  intro k r Wp _ _ _ D X hD hX ha u hu ξ
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hX
  by_cases hI : Integrable (beInt D X u u) (D.μW.prod D.μN)
  swap
  · have h0 : beOp D X u u = 0 := integral_undef hI
    rw [h0]
    simp
  rw [bePos_identity h D X hD ha hd hu ξ hI]
  have h0 : 0 ≤ ∫ g, BesselPositivity.bet D (Matrix.of g) * ‖BesselPositivity.Bv D (mc X u X.w) ξ (Matrix.of g)‖ ^ 2 ∂D.μG :=
    integral_nonneg fun g => mul_nonneg (BesselPositivity.bet_nonneg (D := D) _) (sq_nonneg _)
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg hd.1.le h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
