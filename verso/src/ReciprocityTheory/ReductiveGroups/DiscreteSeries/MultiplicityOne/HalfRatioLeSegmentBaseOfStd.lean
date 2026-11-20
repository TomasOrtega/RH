import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MinorsOnOfDD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

/- English proof (translation)
Simplify using `[h.conc] left a ha := by rw [Measure.map_smul, h.left a ha] right a ha := by rw [Measure.map_smul, h.right a ha] finite_compact K hK := ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK) ne_zero := by`. Introduce `h0`. Establish `h1 : (c : ℝ≥0∞) * μ Set.univ = 0`. Rewrite using `[← smul_eq_mul, ← Measure.smul_apply, h0]`. Both sides reduce to the same expression.

Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 (by exact_mod_cast hc.ne')`. Conclude with `h.ne_zero (Measure.measure_univ_eq_zero.1 h2)`.
-/
theorem isHaarOn_smul {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) {c : ℝ≥0} (hc : 0 < c) :
    IsHaarOn U ((c : ℝ≥0∞) • μ) where
  conc := by simp [h.conc]
  left a ha := by rw [Measure.map_smul, h.left a ha]
  right a ha := by rw [Measure.map_smul, h.right a ha]
  finite_compact K hK := ENNReal.mul_lt_top ENNReal.coe_lt_top (h.finite_compact K hK)
  ne_zero := by
    intro h0
    have h1 : (c : ℝ≥0∞) * μ Set.univ = 0 := by
      rw [← smul_eq_mul, ← Measure.smul_apply, h0]; rfl
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (by exact_mod_cast hc.ne')
    · exact h.ne_zero (Measure.measure_univ_eq_zero.1 h2)

def rescale (D : RealPlaceData k r Wp Wp) {c : ℝ≥0} (hc : 0 < c) : RealPlaceData k r Wp Wp :=
  { D with μG := (c : ℝ≥0∞) • D.μG, haarG := isHaarOn_smul D.haarG hc }

/- English proof (translation)
Introduce `F c' _ hF`. Use `show (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂((c : ℝ≥0∞) • D.μG)) < ∞`. Rewrite using `[lintegral_smul_measure]`. Use `ENNReal.mul_lt_top ENNReal.coe_lt_top ?_` and prove the remaining obligations. Establish `hfin` using `hGN k r D.μG A D.haarG hA`.

Establish `hb : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤ ENNReal.ofReal (max c' 0) * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))` using `by filter_upwards [ae_G D] with g hg`. Establish `hp : 0 < gN (Matrix.of g) ^ A` using `Real.rpow_pos_of_pos (gN_pos hg) A`. Establish `h1 : ‖F (Matrix.of g)‖ ≤ max c' 0 * gN (Matrix.of g) ^ (-A)`. Rewrite using `[Real.rpow_neg (gN_nonneg _), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]`. Conclude with `(hF _ hg).trans (le_max_left _ _)`.

Rewrite using `[← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]`. Conclude with `ENNReal.ofReal_le_ofReal h1`. Use `lt_of_le_of_lt (lintegral_mono_ae hb) ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin`.
-/
theorem ccInt_of (D : RealPlaceData k r Wp Wp) (hGN : GNIntSharp) {A : ℝ} (hA : AB k r ≤ A) {c : ℝ≥0} (hc : 0 < c) :
    CCIntegrable (rescale D hc) A := by
  intro F c' _ hF
  show (∫⁻ g : Mt k r, ‖F (Matrix.of g)‖ₑ ∂((c : ℝ≥0∞) • D.μG)) < ∞
  rw [lintegral_smul_measure]
  refine ENNReal.mul_lt_top ENNReal.coe_lt_top ?_
  have hfin := hGN k r D.μG A D.haarG hA
  have hb : ∀ᵐ g ∂D.μG, ‖F (Matrix.of g)‖ₑ ≤
      ENNReal.ofReal (max c' 0) * ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) := by
    filter_upwards [ae_G D] with g hg
    have hp : 0 < gN (Matrix.of g) ^ A := Real.rpow_pos_of_pos (gN_pos hg) A
    have h1 : ‖F (Matrix.of g)‖ ≤ max c' 0 * gN (Matrix.of g) ^ (-A) := by
      rw [Real.rpow_neg (gN_nonneg _), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact (hF _ hg).trans (le_max_left _ _)
    rw [← ENNReal.ofReal_mul (le_max_right _ _), ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h1
  refine lt_of_le_of_lt (lintegral_mono_ae hb) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/- English proof (translation)
Take `⟨hB2, -, -, -, -, -, -, hJC, -, -, -, -, -, -, hINB, -⟩` from `hIn`. Take `⟨c, ⟨hc, hIF⟩, -⟩` from `hINB k r Wp Wp D`. Establish `hGN : GNIntSharp` using `hB2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Conclude with `hJC k r Wp Wp (rescale D hc) A hIF (ccInt_of D hGN hA hc)`.
-/
theorem jcont_of (hIn : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) {A : ℝ} (hA : AB k r ≤ A) : JCont D A := by
  obtain ⟨hB2, -, -, -, -, -, -, hJC, -, -, -, -, -, -, hINB, -⟩ := hIn
  obtain ⟨c, ⟨hc, hIF⟩, -⟩ := hINB k r Wp Wp D
  have hGN : GNIntSharp := hB2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  exact hJC k r Wp Wp (rescale D hc) A hIF (ccInt_of D hGN hA hc)

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hLBX, -⟩` from `hIn`. Take `⟨c, hc, -, -, hB, -⟩` from `(hLBX hXi).2 k r Wp Wp D A hA`. Conclude with `⟨c, by exact_mod_cast hc, hB⟩`.
-/
theorem lemB_of (hIn : UnitaryGroupStructuralFacts) (hXi : XiExists) (D : RealPlaceData k r Wp Wp) {A : ℝ} (hA : AB k r ≤ A) :
    ∃ c : ℝ, 0 < c ∧ ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' →
      beta D F F' = (c : ℂ) * betaInf D F F' := by
  obtain ⟨-, -, -, -, -, -, hLBX, -⟩ := hIn
  obtain ⟨c, hc, -, -, hB, -⟩ := (hLBX hXi).2 k r Wp Wp D A hA
  exact ⟨c, by exact_mod_cast hc, hB⟩

/- English proof (translation)
Establish `hlin : hsVec (A - B) = hsVec A - hsVec B`. Use extensionality with `i`. Simplify using `[hsVec]`. Establish `h1 : inner ℂ (hsVec (A - B)) (hsVec (A - B)) = 0`. Use `h (A - B)` as an intermediate fact.

Unfold `hsInner at this`. Rewrite `this`, the goal using `[hlin]`. Rewrite using `[inner_sub_right, this, sub_self]`. Rewrite `h1` using `[inner_self_eq_zero]`. Rewrite using `[← sub_eq_zero]`.

Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Use `(stdOrthonormalBasis ℂ Wp).toBasis.ext fun i => ?_` and prove the remaining obligations. Use `congrArg (fun v => v i) h1` as an intermediate fact. Simplify `this` using `[hsVec]`.
-/
theorem hs_ext {A B : Wp →L[ℂ] Wp} (h : ∀ X₀ : Wp →L[ℂ] Wp, hsInner A X₀ = hsInner B X₀) : A = B := by
  have hlin : hsVec (A - B) = hsVec A - hsVec B := by
    ext i; simp [hsVec]
  have h1 : inner ℂ (hsVec (A - B)) (hsVec (A - B)) = 0 := by
    have := h (A - B)
    unfold hsInner at this
    rw [hlin] at this ⊢
    rw [inner_sub_right, this, sub_self]
  rw [inner_self_eq_zero] at h1
  rw [← sub_eq_zero]
  apply ContinuousLinearMap.coe_injective
  refine (stdOrthonormalBasis ℂ Wp).toBasis.ext fun i => ?_
  have := congrArg (fun v => v i) h1
  simpa [hsVec] using this

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.TopH

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

/- English proof (translation)
Unfold `nR`. Establish `: 2 ≤ 2 * r + k + 1` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem nR_ge (hk : 1 ≤ k) : (2 : ℝ) ≤ nR k r := by
  unfold nR
  have : 2 ≤ 2 * r + k + 1 := by omega
  exact_mod_cast this

/- English proof (translation)
Establish `hn` using `nR_ge (r := r) hk`. Establish `e : nR k r = 2 * (r : ℝ) + k + 1` using `by unfold nR; push_cast; ring`. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `h1 : 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 ≤ nR k r ^ 2` using `by rw [e]; nlinarith`.

Establish `h2 : 2 * nR k r ^ 2 + 1 ≤ 4 * nR k r ^ 3` using `by nlinarith`. Unfold `AB AG`. Unfold `aM at ha`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_ratio_le_segment_base_of_std (hk : 1 ≤ k) {a : ℝ} (ha : aM k r ≤ a) : AB k r ≤ a - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  have e : nR k r = 2 * (r : ℝ) + k + 1 := by unfold nR; push_cast; ring
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 ≤ nR k r ^ 2 := by rw [e]; nlinarith
  have h2 : 2 * nR k r ^ 2 + 1 ≤ 4 * nR k r ^ 3 := by nlinarith
  unfold AB AG; unfold aM at ha
  linarith

/- English proof (translation)
Establish `hn` using `nR_ge (r := r) hk`. Establish `h2 : nR k r ^ 3 + 2 * nR k r ^ 2 + 3 ≤ 4 * nR k r ^ 3` using `by nlinarith`. Unfold `AS AG`. Unfold `aM at ha`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem decay_exponent_ge_double_shift (hk : 1 ≤ k) {a : ℝ} (ha : aM k r ≤ a) : AS k r + 1 ≤ a - AG k r - 1 - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  have h2 : nR k r ^ 3 + 2 * nR k r ^ 2 + 3 ≤ 4 * nR k r ^ 3 := by nlinarith
  unfold AS AG; unfold aM at ha
  linarith

/- English proof (translation)
Take `⟨d, hd⟩` from `h0 k r Wp D X hD hX`. Take `⟨C, hC⟩` from `h1 k r Wp D X hD hX d hd (X.a - AG k r - 1) X.a u hu v hv`. Establish `hAG : 0 ≤ AG k r` using `by unfold AG; positivity`. Establish `hmin : min (X.a - AG k r - 1) X.a = X.a - AG k r - 1` using `min_eq_left (by linarith)`. Rewrite `hC` using `[hmin]`.

Conclude with `h1' k r Wp D X hD hX _ (decay_exponent_ge_double_shift D.k_pos ha) u v ⟨C, hC⟩`.
-/
theorem beInt_int_mixed (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) (h0 : StSchurG) (h1 : StPairs) (h1' : StBeConv) {u v : X.Hs}
    (hu : u ∈ VflA X (X.a - AG k r - 1)) (hv : v ∈ Vfl X) : Integrable (beInt D X u v) (D.μW.prod D.μN) := by
  obtain ⟨d, hd⟩ := h0 k r Wp D X hD hX
  obtain ⟨C, hC⟩ := h1 k r Wp D X hD hX d hd (X.a - AG k r - 1) X.a u hu v hv
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have hmin : min (X.a - AG k r - 1) X.a = X.a - AG k r - 1 := min_eq_left (by linarith)
  rw [hmin] at hC
  exact h1' k r Wp D X hD hX _ (decay_exponent_ge_double_shift D.k_pos ha) u v ⟨C, hC⟩

/- English proof (translation)
Establish `h : ∀ a : Fin r, (if h : a.val + 1 < r then (1 : Mat k r) (eI k r a) (eI k r ⟨a.val + 1, h⟩) else ((1 : Mat k r) *ᵥ D.z) (eI k r a)) = 0`. Introduce `a`. Use `split_ifs with h`. Rewrite using `[Matrix.one_apply_ne]`. Introduce `he`.

Use `congrArg Fin.val he` as an intermediate fact. Simplify using `[eI] at this`. Rewrite using `[Matrix.one_mulVec]`. Conclude with `D.z_mem _ (Or.inl a.isLt)`. Unfold `psiD psi ell`.

Rewrite using `[Finset.sum_eq_zero (fun a _ => h a)]`. Simplify using the standard rewrite rules.
-/
theorem psiD_one (D : RealPlaceData k r Wp Wp) : psiD D 1 = 1 := by
  have h : ∀ a : Fin r, (if h : a.val + 1 < r then (1 : Mat k r) (eI k r a) (eI k r ⟨a.val + 1, h⟩)
      else ((1 : Mat k r) *ᵥ D.z) (eI k r a)) = 0 := by
    intro a
    split_ifs with h
    · rw [Matrix.one_apply_ne]
      intro he
      have := congrArg Fin.val he
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact D.z_mem _ (Or.inl a.isLt)
  unfold psiD psi ell
  rw [Finset.sum_eq_zero (fun a _ => h a)]
  simp

/- English proof (translation)
Establish `hgi` using `uw_inv_mem hg`. Use `symm`. Rewrite using `[ContinuousLinearMap.eq_adjoint_iff]`. Introduce `x y`. Set `L : Wp →ₗᵢ[ℂ] Wp` to `{ toLinearMap := (D.π g : Wp →ₗ[ℂ] Wp), norm_map' := D.π_unitary g hg }`.

Establish `h1 : D.π g (D.π g⁻¹ x) = x`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← D.π_rep.2 g hg g⁻¹ hgi, gv_mul_inv (uw_gv hg), D.π_rep.1]`. Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1]`.
-/
theorem pi_adj (D : RealPlaceData k r Wp Wp) {g : Mat k r} (hg : g ∈ UWset k r D.z) :
    ContinuousLinearMap.adjoint (D.π g) = D.π g⁻¹ := by
  have hgi := uw_inv_mem hg
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  let L : Wp →ₗᵢ[ℂ] Wp := { toLinearMap := (D.π g : Wp →ₗ[ℂ] Wp), norm_map' := D.π_unitary g hg }
  have h1 : D.π g (D.π g⁻¹ x) = x := by
    rw [← ContinuousLinearMap.comp_apply, ← D.π_rep.2 g hg g⁻¹ hgi, gv_mul_inv (uw_gv hg), D.π_rep.1]
    rfl
  calc ⟪D.π g⁻¹ x, y⟫_ℂ = ⟪L (D.π g⁻¹ x), L y⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪x, D.π g y⟫_ℂ := by
        show ⟪D.π g (D.π g⁻¹ x), D.π g y⟫_ℂ = _
        rw [h1]

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts D.μW'` using `⟨fun K hK => D.haarW'.finite_compact K hK⟩`. Establish `: IsFiniteMeasureOnCompacts D.μN` using `⟨fun K hK => D.haarN.finite_compact K hK⟩`. Establish `h1 : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z'` using `ae_iff.2 D.haarW'.conc`. Establish `h2 : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r` using `ae_iff.2 D.haarN.conc`. Use `filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2] with p hp1 hp2`.

Conclude with `⟨hp1, hp2⟩`.
-/
theorem ae_UN' (D : RealPlaceData k r Wp Wp) :
    ∀ᵐ p ∂(D.μW'.prod D.μN), Matrix.of p.1 ∈ UWset k r D.z' ∧ Matrix.of p.2 ∈ Nset k r := by
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  have h1 : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := ae_iff.2 D.haarW'.conc
  have h2 : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := ae_iff.2 D.haarN.conc
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨hp1, hp2⟩

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts D.μW'` using `⟨fun K hK => D.haarW'.finite_compact K hK⟩`. Establish `: IsFiniteMeasureOnCompacts D.μW` using `⟨fun K hK => D.haarW.finite_compact K hK⟩`. Establish `: IsFiniteMeasureOnCompacts D.μN` using `⟨fun K hK => D.haarN.finite_compact K hK⟩`. Use `filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_UN D), Measure.quasiMeasurePreserving_snd.ae (ae_UN' D)] with p h1 h2`. Conclude with `⟨h1.1, h1.2, h2.1, h2.2⟩`.
-/
theorem ae_SS (D : RealPlaceData k r Wp Wp) : ∀ᵐ p ∂D.μSS, D.inSS p := by
  have : IsFiniteMeasureOnCompacts D.μW' := ⟨fun K hK => D.haarW'.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μW := ⟨fun K hK => D.haarW.finite_compact K hK⟩
  have : IsFiniteMeasureOnCompacts D.μN := ⟨fun K hK => D.haarN.finite_compact K hK⟩
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_UN D),
    Measure.quasiMeasurePreserving_snd.ae (ae_UN' D)] with p h1 h2
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/- English proof (translation)
Take `⟨φ, hφ, rfl⟩` from `ha'`. Take `⟨φ', hφ', rfl⟩` from `hb`. Conclude with `hSm k r Wp D X hD hX ha φ φ' hφ hφ' 5`.
-/
theorem incc_dd (hSm : StSmooth) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    (ha : aM k r ≤ X.a) {a b : X.Hs} (ha' : a ∈ DDinf D X) (hb : b ∈ DDinf D X) :
    InCC (X.a - AG k r - 1) 5 (mc X a b) := by
  obtain ⟨φ, hφ, rfl⟩ := ha'
  obtain ⟨φ', hφ', rfl⟩ := hb
  exact hSm k r Wp D X hD hX ha φ φ' hφ hφ' 5

/- English proof (translation)
Take `⟨hI, hval⟩` from `h2 k r Wp D X hD d hd f x y a₂ b₂ X₀ hf hxa hyb`. Establish `i1 : InCC A 5 (scalF Wp f)` using `h1p k r Wp A 5 f (ContinuousLinearMap.id ℂ Wp) hfc`. Establish `i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀)` using `h1p k r Wp A 5 _ X₀ hc2`. Rewrite using `[hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI, hval]`.
-/
theorem beta_val (h1p : StCut1p) (h2 : StCut2) (hBI : StBetaInf) (hXi : XiExists)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) {d : ℝ} (hd : IsFdegG D X d)
    {A : ℝ} (hA : AB k r ≤ A) {c : ℝ}
    (hcB : ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = (c : ℂ) * betaInf D F F')
    (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (hf : ∀ g ∈ GV k r, f g = mc X x y g)
    (hfc : InCC A 5 f) (hc2 : InCC A 5 (mc X a₂ b₂))
    (hxa : Integrable (beInt D X x a₂) (D.μW.prod D.μN)) (hyb : Integrable (beInt D X y b₂) (D.μW.prod D.μN)) :
    beta D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) =
      (c : ℂ) * (hsInner ((ContinuousLinearMap.adjoint (beOp D X y b₂)).comp (beOp D X x a₂)) X₀ / (d : ℂ)) := by
  obtain ⟨hI, hval⟩ := h2 k r Wp D X hD d hd f x y a₂ b₂ X₀ hf hxa hyb
  have i1 : InCC A 5 (scalF Wp f) := h1p k r Wp A 5 f (ContinuousLinearMap.id ℂ Wp) hfc
  have i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀) := h1p k r Wp A 5 _ X₀ hc2
  rw [hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI, hval]

/- English proof (translation)
Establish `hPh : ∀ᵐ p ∂D.μSS, Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0` using `by filter_upwards [ae_SS D] with p hp`. Conclude with `h3 hInv k r Wp D X hD hX γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp`. Establish `hI : Integrable (Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀)) D.μSS` using `(integrable_zero _ _ _).congr (hPh.mono fun p hp => hp.symm)`. Establish `i1 : InCC A 5 (scalF Wp (mc X a₁ b₁ ∘ th k r γ))` using `h1p k r Wp A 5 _ (ContinuousLinearMap.id ℂ Wp) hf`. Establish `i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀)` using `h1p k r Wp A 5 _ X₀ hc2`.

Rewrite using `[hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI, integral_eq_zero_of_ae (hPh.mono fun p hp => by simp [hp]), mul_zero]`.
-/
theorem beta_zero (h3 : StCut3) (hInv : StInvGroup) (h1p : StCut1p) (hBI : StBetaInf) (hXi : XiExists)
    (D : RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D) (hX : SqIntG D X)
    {A : ℝ} (hA : AB k r ≤ A) {c : ℝ}
    (hcB : ∀ F F' : Mat k r → (Wp →L[ℂ] Wp), InCC A 5 F → InCC A 5 F' → beta D F F' = (c : ℂ) * betaInf D F F')
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hγ : IsZFrame k r D.z γ)
    (hZ : ∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0)
    (a₁ b₁ a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (hf : InCC A 5 (mc X a₁ b₁ ∘ th k r γ))
    (hc2 : InCC A 5 (mc X a₂ b₂)) :
    beta D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) = 0 := by
  have hPh : ∀ᵐ p ∂D.μSS, Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0 := by
    filter_upwards [ae_SS D] with p hp
    exact h3 hInv k r Wp D X hD hX γ hγ hZ a₁ b₁ a₂ b₂ X₀ p hp
  have hI : Integrable (Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀)) D.μSS :=
    (integrable_zero _ _ _).congr (hPh.mono fun p hp => hp.symm)
  have i1 : InCC A 5 (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) := h1p k r Wp A 5 _ (ContinuousLinearMap.id ℂ Wp) hf
  have i2 : InCC A 5 (fun g => mc X a₂ b₂ g • X₀) := h1p k r Wp A 5 _ X₀ hc2
  rw [hcB _ _ i1 i2, hBI k r Wp Wp D A hXi hA _ _ i1 i2 hI,
    integral_eq_zero_of_ae (hPh.mono fun p hp => by simp [hp]), mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Mult1.TopH
