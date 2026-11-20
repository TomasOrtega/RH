import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.ContinuousOnOrbit
import CompanionTheory.AutomorphicTheory.RankOneEstimates.DecSender
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.ThmMOfXi
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.FrameBlockWMem
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDiagExists
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.DiscreteSeriesUnitarySmoothBasicImports
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.PhiIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.WeightedL1OfL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.SigIntIntegrable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix MeasureTheory Formalism.FourierDecayAlt Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 CompanionTheory.D.Upq.Sm
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

/- English proof (translation)
Take `⟨d, hd⟩` from `stSchurG k r Wp D X hD hS`. Take `⟨K, hK⟩` from `hbd`. Establish `hae` using `BeEquiv.ae_mem_of_haarOn D.haarG`. Establish `hAB : B.AB k r ≤ X.a`. Use `(le_trans ?_ ha)` and prove the remaining obligations.

Establish `h1 : (1 : ℝ) ≤ r + 1` using `by have := Nat.cast_nonneg (α := ℝ) r; linarith`. Establish `h2 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `h3 : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Establish `hn : (1 : ℝ) ≤ nR k r` using `by unfold nR; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)`. Establish `h4 : B.AB k r ≤ nR k r ^ 2 + 1`.

Unfold `B.AB nR`. Use `push_cast`. Use polynomial arithmetic with `[sq_nonneg ((k : ℝ) + r - (r + 1))]`. Establish `h5 : nR k r ^ 2 ≤ nR k r ^ 3` using `pow_le_pow_right₀ hn (by norm_num)`. Establish `h6` using `one_le_pow₀ (n := 3) hn`.

Unfold `aM`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGN` using `TopH.gN_integrable D (SquareIntegrabilityOnOrbit.gnInt_of multiplicity_one_hypotheses_hold) hAB`. Establish `hcont` using `hB.continuousOn_orbit hF hU hw`. Establish `hWm` using `SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => Bm (X.σ g X.w)) hcont`.

Take `⟨c, hc⟩` from `stMFix multiplicity_one_hypotheses_hold k r Wp D X hD hS ha l hl d hd (fun g => Bm (X.σ g X.w)) hWm (fun h hh m hm x hx => by`. Establish `hi` using `WeylGroupFacts.uw_inv hh`. Take `⟨hn, he⟩` from `unitary_weyl_normal_holds k r D.z D.z_mem h⁻¹ hi m hm`. Establish `hu` using `WeylGroupFacts.isUnit_of_uh hh.1`. Rewrite `hn`, `he` using `[Matrix.nonsing_inv_nonsing_inv _ hu]`.

Establish `e : m * h * x = h * (h⁻¹ * m * h) * x`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]`. Use `show Bm (X.σ (m * h * x) X.w) = psi k r D.z cStd m • D.π h (Bm (X.σ x X.w))`. Rewrite using `[e, hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hx, heq h hh _ hn _ (hw.apply hU.rep hx)]`. Unfold `psi`.

Rewrite using `[he])`. Use the proof step `(fun x hx => by`. Establish `hxi : x⁻¹ ∈ B.GV k r` using `(hU.grp.2.2.2 x hx).1`. Establish `hmp : MeasurePreserving (lmulM x⁻¹) D.μG D.μG` using `⟨BeEquiv.measurable_lmul_mt x⁻¹, D.haarG.left x⁻¹ hxi⟩`. Establish `h1 : Integrable (fun y : Mt k r => B.gN (x⁻¹ * Matrix.of y) ^ (-X.a)) D.μG` using `hmp.integrable_comp_of_integrable hGN`.

Use `(h1.mul_const K).mono' (h1.aestronglyMeasurable.mul hWm.norm) ?_` and prove the remaining obligations. Use `filter_upwards [hae] with y hy`. Establish `h0 : 0 ≤ B.gN (x⁻¹ * Matrix.of y) ^ (-X.a)` using `Real.rpow_nonneg (Real.sqrt_nonneg _) _`. Rewrite using `[Real.norm_of_nonneg (mul_nonneg h0 (norm_nonneg _))]`. Conclude with `mul_le_mul_of_nonneg_left (hK _ hy) h0)`.

Establish `hμ : PI.IsHaarOnM (UH (Hpk k r)) D.μG` using `⟨BeEquiv.sigmaFinite_of_haarOn D.haarG, D.haarG.ne_zero, D.haarG.conc, D.haarG.left⟩`. Establish `hσc : ContinuousOn (fun g => X.σ g X.w) (B.GV k r)` using `X.rep.2.2 X.w`. Establish `hint : ∀ v, IsSm (UH (Hpk k r)) X.σ v → Integrable (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ) D.μG`. Introduce `v hv`. Take `⟨C, hC⟩` from `hdec v hv`.

Use `(hGN.const_mul C).mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => ⟪v, X.σ g X.w⟫_ℂ) ((innerSL ℂ v).continuous.comp_continuousOn hσc)) ?_` and prove the remaining obligations. Use `filter_upwards [hae] with y hy`. Conclude with `hC _ hy`. Establish `hd0 : (d : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hd.1.ne'`. Establish `hrep : ∀ v, IsSm (UH (Hpk k r)) X.σ v → ∫ y : Mt k r, conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w ∂D.μG = (d : ℂ)⁻¹ • v`.

Introduce `v hv`. Establish `hi : Integrable (fun y : Mt k r => conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w) D.μG`. Use `(hint v hv).norm.mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => conj ⟪v, X.σ g X.w⟫_ℂ • X.σ g X.w) ((Complex.continuous_conj.comp_continuousOn ((innerSL ℂ v).continuous.comp_continuousOn hσc)).smul hσc)) ?_` and prove the remaining obligations. Use `filter_upwards [hae] with y hy`. Rewrite using `[norm_smul, hU.iso _ hy, X.w_norm, mul_one, Complex.norm_conj]`.

Use `ext_inner_left ℂ fun ξ => ?_` and prove the remaining obligations. Rewrite using `[← integral_inner hi, inner_smul_right]`. Establish `h` using `(hd.2 X.w ξ X.w v).2`. Rewrite `h` using `[inner_self_eq_norm_sq_to_K, X.w_norm]`. Simplify using `only [inner_smul_right]`.

Use `Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)) (h.trans ?_)` and prove the remaining obligations. Simplify using `only [mc, Complex.star_def]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[div_eq_inv_mul]`. Use `⟨c, fun x hx => ?_⟩` and prove the remaining obligations.

Establish `hBx` using `hB.comp_sigma hAd hU hx`. Establish `hlim` using `hCL _ _ X.Hs X.σ hU Wp _ hBx D.μG hμ X.w hw hint _ hrep ⟨K, fun g hg => by rw [← hU.rep.apply_mul hx hg]; exact hK _ (hU.rep.mul_mem _ hx _ hg)⟩ X.w hw`. Rewrite using `[← hc x hx]`. Establish `e1 : Bm (X.σ x X.w) = (d : ℂ) • ((d : ℂ)⁻¹ • Bm (X.σ x X.w))`. Rewrite using `[smul_smul, mul_inv_cancel₀ hd0, one_smul]`.

Rewrite using `[e1, hlim, ← integral_smul]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with y hy`. Rewrite using `[hU.rep.apply_mul hx hy, smul_smul]`. Both sides reduce to the same expression.
-/
theorem orbit_mult (hCL : CutLim) (hAd : DsAd) (hF : Factor) {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (D : B.RealPlaceData k r Wp Wp) (X : SigData k r) (hD : IsDiag D)
    (hS : SqIntG D X) (ha : aM k r ≤ X.a) (hU : URep (Hpk k r) X.σ) (hw : IsSm (UH (Hpk k r)) X.σ X.w)
    (hdec : ∀ v, IsSm (UH (Hpk k r)) X.σ v → ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, X.σ x X.w⟫_ℂ‖ ≤ C * B.gN x ^ (-X.a))
    {l : X.Hs → Wp} (hl : IsMultOneMap D X l) {Bm : X.Hs → Wp} (hB : CWLin (Hpk k r) X.σ Bm)
    (heq : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      Bm (X.σ (h * m) v) = psi k r D.z cStd m • D.π h (Bm v))
    (hbd : ∃ K : ℝ, ∀ g ∈ UH (Hpk k r), ‖Bm (X.σ g X.w)‖ ≤ K) :
    ∃ c : ℂ, ∀ x ∈ UH (Hpk k r), Bm (X.σ x X.w) = c • l (X.σ x X.w) := by
  obtain ⟨d, hd⟩ := stSchurG k r Wp D X hD hS
  obtain ⟨K, hK⟩ := hbd
  have hae := BeEquiv.ae_mem_of_haarOn D.haarG
  have hAB : B.AB k r ≤ X.a := by
    refine (le_trans ?_ ha)
    have h1 : (1 : ℝ) ≤ r + 1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h3 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hn : (1 : ℝ) ≤ nR k r := by unfold nR; exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have h4 : B.AB k r ≤ nR k r ^ 2 + 1 := by
      unfold B.AB nR
      push_cast
      nlinarith [sq_nonneg ((k : ℝ) + r - (r + 1))]
    have h5 : nR k r ^ 2 ≤ nR k r ^ 3 := pow_le_pow_right₀ hn (by norm_num)
    have h6 := one_le_pow₀ (n := 3) hn
    unfold aM
    linarith
  have hGN := TopH.gN_integrable D (SquareIntegrabilityOnOrbit.gnInt_of multiplicity_one_hypotheses_hold) hAB
  have hcont := hB.continuousOn_orbit hF hU hw
  have hWm := SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => Bm (X.σ g X.w)) hcont
  obtain ⟨c, hc⟩ := stMFix multiplicity_one_hypotheses_hold k r Wp D X hD hS ha l hl d hd (fun g => Bm (X.σ g X.w)) hWm
    (fun h hh m hm x hx => by
      have hi := WeylGroupFacts.uw_inv hh
      obtain ⟨hn, he⟩ := unitary_weyl_normal_holds k r D.z D.z_mem h⁻¹ hi m hm
      have hu := WeylGroupFacts.isUnit_of_uh hh.1
      rw [Matrix.nonsing_inv_nonsing_inv _ hu] at hn he
      have e : m * h * x = h * (h⁻¹ * m * h) * x := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      show Bm (X.σ (m * h * x) X.w) = psi k r D.z cStd m • D.π h (Bm (X.σ x X.w))
      rw [e, hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hx, heq h hh _ hn _ (hw.apply hU.rep hx)]
      unfold psi
      rw [he])
    (fun x hx => by
      have hxi : x⁻¹ ∈ B.GV k r := (hU.grp.2.2.2 x hx).1
      have hmp : MeasurePreserving (lmulM x⁻¹) D.μG D.μG :=
        ⟨BeEquiv.measurable_lmul_mt x⁻¹, D.haarG.left x⁻¹ hxi⟩
      have h1 : Integrable (fun y : Mt k r => B.gN (x⁻¹ * Matrix.of y) ^ (-X.a)) D.μG :=
        hmp.integrable_comp_of_integrable hGN
      refine (h1.mul_const K).mono' (h1.aestronglyMeasurable.mul hWm.norm) ?_
      filter_upwards [hae] with y hy
      have h0 : 0 ≤ B.gN (x⁻¹ * Matrix.of y) ^ (-X.a) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [Real.norm_of_nonneg (mul_nonneg h0 (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hK _ hy) h0)
  have hμ : PI.IsHaarOnM (UH (Hpk k r)) D.μG :=
    ⟨BeEquiv.sigmaFinite_of_haarOn D.haarG, D.haarG.ne_zero, D.haarG.conc, D.haarG.left⟩
  have hσc : ContinuousOn (fun g => X.σ g X.w) (B.GV k r) := X.rep.2.2 X.w
  have hint : ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      Integrable (fun y : Mt k r => ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ) D.μG := by
    intro v hv
    obtain ⟨C, hC⟩ := hdec v hv
    refine (hGN.const_mul C).mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D (f := fun g => ⟪v, X.σ g X.w⟫_ℂ)
      ((innerSL ℂ v).continuous.comp_continuousOn hσc)) ?_
    filter_upwards [hae] with y hy
    exact hC _ hy
  have hd0 : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  have hrep : ∀ v, IsSm (UH (Hpk k r)) X.σ v →
      ∫ y : Mt k r, conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w ∂D.μG = (d : ℂ)⁻¹ • v := by
    intro v hv
    have hi : Integrable (fun y : Mt k r => conj ⟪v, X.σ (Matrix.of y) X.w⟫_ℂ • X.σ (Matrix.of y) X.w) D.μG := by
      refine (hint v hv).norm.mono' (SquareIntegrabilityOnOrbit.aesm_of_contOn multiplicity_one_hypotheses_hold D
        (f := fun g => conj ⟪v, X.σ g X.w⟫_ℂ • X.σ g X.w)
        ((Complex.continuous_conj.comp_continuousOn ((innerSL ℂ v).continuous.comp_continuousOn hσc)).smul hσc)) ?_
      filter_upwards [hae] with y hy
      rw [norm_smul, hU.iso _ hy, X.w_norm, mul_one, Complex.norm_conj]
    refine ext_inner_left ℂ fun ξ => ?_
    rw [← integral_inner hi, inner_smul_right]
    have h := (hd.2 X.w ξ X.w v).2
    rw [inner_self_eq_norm_sq_to_K, X.w_norm] at h
    simp only [inner_smul_right]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)) (h.trans ?_)
    · simp only [mc, Complex.star_def]
      ring
    · simp [div_eq_inv_mul]
  refine ⟨c, fun x hx => ?_⟩
  have hBx := hB.comp_sigma hAd hU hx
  have hlim := hCL _ _ X.Hs X.σ hU Wp _ hBx D.μG hμ X.w hw hint _ hrep
    ⟨K, fun g hg => by rw [← hU.rep.apply_mul hx hg]; exact hK _ (hU.rep.mul_mem _ hx _ hg)⟩ X.w hw
  rw [← hc x hx]
  have e1 : Bm (X.σ x X.w) = (d : ℂ) • ((d : ℂ)⁻¹ • Bm (X.σ x X.w)) := by
    rw [smul_smul, mul_inv_cancel₀ hd0, one_smul]
  rw [e1, hlim, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with y hy
  rw [hU.rep.apply_mul hx hy, smul_smul]
  rfl

/- English proof (translation)
Take `⟨h1, h2, -, C, Ws, hW, hb⟩` from `h`. Use `⟨fun x hx y hy => h1 x hx y hy, fun a x hx => h2 a x hx, C, Ws, hW, fun v hv => ?_⟩` and prove the remaining obligations. Use `hb v hv` as an intermediate fact. Simplify `this` using `only [dsigW_eq']`.
-/
theorem cwLin_of {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat (2 * r + k + 1) → (H →L[ℂ] H)} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat (2 * r + k + 1) → ℂ} {π : Mat (2 * r + k + 1) → (Wp →L[ℂ] Wp)}
    {Bm : H → Wp} (h : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π Bm) : CWLin (Hpk k r) σ Bm := by
  obtain ⟨h1, h2, -, C, Ws, hW, hb⟩ := h
  refine ⟨fun x hx y hy => h1 x hx y hy, fun a x hx => h2 a x hx, C, Ws, hW, fun v hv => ?_⟩
  have := hb v hv
  simpa only [dsigW_eq'] using this

/- English proof (translation)
Introduce `k r ε lam h H _ _ σ z c u Wp _ _ π hk hg hh hl hσ hz hT hc hπ B₁ B₂ hB₁ hB₂`. Use `haveI : CompleteSpace H := by obtain ⟨P, -, h1, -⟩ := hσ; exact h1`. Use `haveI : FiniteDimensional ℂ Wp := by obtain ⟨g, -, -, h1, -⟩ := hπ; exact h1`. Take `⟨hrep, hiso, hcont, hirr⟩` from `TopTA.pi_facts (u := u) (π := π) hz hT hπ`. Take `⟨D, hDz, hDπ, hD⟩` from `stDiagExists multiplicity_one_hypotheses_hold k r Wp z π hk hz hT hrep hiso hcont hirr`.

Substitute `hDz hDπ` using the available equality. Take `⟨hUR, hsq⟩` from `TopTA.sqInt_of_DSHpk (σ := σ) hσ D.haarG`. Establish `hG : PI.IsMatGroup (UH (Hpk k r))` using `PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r`. Establish `hU : URep (Hpk k r) σ` using `⟨(hermitian_pos_facts_hold k r).2.1, hG, ⟨hG.2.1, hG.2.2.1, hUR.1.1, hUR.1.2⟩, hUR.2.1⟩`. Establish `hm : thrStar ε + ((4 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ) < h`.

Use `CompanionTheory.FamilyDerivativeExpansion.DecS.thr_le (n := 2 * r + k + 1) (by omega) ε` as an intermediate fact. Establish `h1 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) ^ 3` using `by positivity`. Rewrite using `[Nat.cast_mul, Nat.cast_pow]`. Move the coercions through the operations in `at *`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `dec : ∀ w ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, σ x w⟫_ℂ‖ ≤ C * B.gN x ^ (-aM k r) := by`. Introduce `w hw v hv`. Take `⟨C, Ws, -, h2⟩` from `CompanionTheory.FamilyDerivativeExpansion.DecS.decayM hl hσ hg _ hm v hv`. Conclude with `⟨_, fun x hx => h2 (aM k r) (by unfold aM nR; push_cast; rfl) w hw x hx⟩`. Take `⟨-, -, -, -, hsm, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩` from `GlobalTheory.T.discreteSeries_unitary_smooth_basic CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam ⟨H, σ⟩ ⟨hl, hσ⟩`.

Establish `hw0s` using `hsm w0 (hKT w0 hw0K)`. Take `⟨C0, hC0⟩` from `dec w0 hw0s w0 hw0s`. Set `X : SigData k r` to `⟨H, σ, hUR, TopTA.irr_of_DSHpk (σ := σ) hσ, w0, hw0, aM k r, C0, hC0⟩`. Establish `hS : SqIntG D X` using `hsq`. Take `⟨l, hl1⟩` from `thmM k r Wp D X hD hS le_rfl`.

Take `⟨τ, hτ, hτW, hτN⟩` from `hTC k r D.z c hz hc`. Establish `hw : IsSm (UH (Hpk k r)) σ w0` using `hw0s`. Establish `hτi : τ⁻¹ * τ = 1` using `mul_eq_one_comm.1 (hG.2.2.2 τ hτ).2`. Establish `key : ∀ Bm : H → Wp, PI.BesselMapUniq.IsBesselMapSm (k` using `k) (r := r) D.z (PI.BesselMapUniq.psiGen k r D.z c) σ D.π Bm → ∃ c₀ : ℂ, ∀ x ∈ UH (Hpk k r), Bm (σ τ (σ x w0)) = c₀ • l (σ x w0) := by`. Introduce `Bm hBm`.

Establish `hCW` using `cwLin_of hBm`. Take `⟨K, hK⟩` from `hBd k r H σ hU hk D.z c hz hT hc Wp D.π hrep.1 hiso hcont Bm hCW (fun h hh m hm v hv => hBm.2.2.1 h hh m hm v hv) w0 hw`. Use `orbit_mult hCL hAd hF D X hD hS le_rfl hU hw (fun v hv => dec w0 hw0s v hv) hl1 (Bm := fun v => Bm (σ τ v)) (hCW.comp_sigma hAd hU hτ) (fun h hh m hm v hv => ?_) ⟨K, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨hn, hψ⟩` from `hτN m hm`. Establish `e : τ * (h * m) = h * (τ * m * τ⁻¹) * τ`.

Rewrite using `[← Matrix.mul_assoc, hτW h hh]`. Simplify using `only [Matrix.mul_assoc, hτi, Matrix.mul_one]`. Use `show Bm (σ τ (σ (h * m) v)) = psi k r D.z cStd m • D.π h (Bm (σ τ v))`. Rewrite using `[← hU.rep.apply_mul hτ (hU.rep.mul_mem _ hh.1 _ hm.1), e, hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hτ, hBm.2.2.1 h hh _ hn _ (hv.apply hU.rep hτ), hψ]`. Use `show ‖Bm (σ τ (σ g w0))‖ ≤ K`.

Rewrite using `[← hU.rep.apply_mul hτ hg]`. Conclude with `hK _ (hU.rep.mul_mem _ hτ _ hg)`. Take `⟨c₁, e₁⟩` from `key B₁ hB₁`. Take `⟨c₂, e₂⟩` from `key B₂ hB₂`. Establish `fin : ∀ a b : ℂ, a * c₁ + b * c₂ = 0 → ∀ v ∈ PI.UpqRep.smoothVecs (k` using `k) (r := r) σ, a • B₁ v + b • B₂ v = 0 := by`.

Introduce `a b hab v hv`. Establish `hE` using `(((cwLin_of hB₁).comb (cwLin_of hB₂) a b).comp_sigma hAd hU hτ)`. Establish `hτ'` using `(hG.2.2.2 τ hτ).1`. Establish `hv' : IsSm (UH (Hpk k r)) σ (σ τ⁻¹ v)` using `IsSm.apply hU.rep hv hτ'`. Establish `h0` using `hE.eq_zero hU hw (fun g hg => by show a • B₁ (σ τ (σ g w0)) + b • B₂ (σ τ (σ g w0)) = 0`.

Rewrite using `[e₁ g hg, e₂ g hg, smul_smul, smul_smul, ← add_smul, hab, zero_smul]) hv'`. Use the proof step `(fun Ws hWs δ hδ => by`. Use `cyc_of_smooth k r ε lam H σ w0 hσ (by intro e; rw [e, norm_zero] at hw0; exact zero_ne_one hw0) hw0s _ hv' Ws hWs δ hδ` as an intermediate fact. Simplify using `only [dsigW_eq'] at this`. Conclude with `this)`.

Establish `e : σ τ (σ τ⁻¹ v) = v`. Rewrite using `[← hU.rep.apply_mul hτ hτ', (hG.2.2.2 τ hτ).2, hU.rep.map_one]`. Both sides reduce to the same expression. Simplify `h0` using `only [e]`. Distinguish the cases in `h1 : c₁ = 0`.

Conclude with `⟨1, 0, Or.inl one_ne_zero, fin 1 0 (by rw [h1]; simp)⟩`. Conclude with `⟨c₂, -c₁, Or.inr (neg_ne_zero.2 h1), fin c₂ (-c₁) (by ring)⟩`.
-/
theorem uniq_of (hBd : Bounded) (hCL : CutLim) (hTC : TorConj) (hAd : DsAd) (hF : Factor) : BesselMapUniqGap := by
  intro k r ε lam h H _ _ σ z c u Wp _ _ π hk hg hh hl hσ hz hT hc hπ B₁ B₂ hB₁ hB₂
  haveI : CompleteSpace H := by obtain ⟨P, -, h1, -⟩ := hσ; exact h1
  haveI : FiniteDimensional ℂ Wp := by obtain ⟨g, -, -, h1, -⟩ := hπ; exact h1
  obtain ⟨hrep, hiso, hcont, hirr⟩ := TopTA.pi_facts (u := u) (π := π) hz hT hπ
  obtain ⟨D, hDz, hDπ, hD⟩ := stDiagExists multiplicity_one_hypotheses_hold k r Wp z π hk hz hT hrep hiso hcont hirr
  subst hDz hDπ
  obtain ⟨hUR, hsq⟩ := TopTA.sqInt_of_DSHpk (σ := σ) hσ D.haarG
  have hG : PI.IsMatGroup (UH (Hpk k r)) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  have hU : URep (Hpk k r) σ :=
    ⟨(hermitian_pos_facts_hold k r).2.1, hG, ⟨hG.2.1, hG.2.2.1, hUR.1.1, hUR.1.2⟩, hUR.2.1⟩
  have hm : thrStar ε + ((4 * (2 * r + k + 1) ^ 3 : ℕ) : ℝ) < h := by
    have := CompanionTheory.FamilyDerivativeExpansion.DecS.thr_le (n := 2 * r + k + 1) (by omega) ε
    have h1 : (0 : ℝ) < ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    rw [Nat.cast_mul, Nat.cast_pow]
    push_cast at *
    linarith
  have dec : ∀ w ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
      ∃ C : ℝ, ∀ x ∈ B.GV k r, ‖⟪v, σ x w⟫_ℂ‖ ≤ C * B.gN x ^ (-aM k r) := by
    intro w hw v hv
    obtain ⟨C, Ws, -, h2⟩ := CompanionTheory.FamilyDerivativeExpansion.DecS.decayM hl hσ hg _ hm v hv
    exact ⟨_, fun x hx => h2 (aM k r) (by unfold aM nR; push_cast; rfl) w hw x hx⟩
  obtain ⟨-, -, -, -, hsm, -, hKT, ⟨w0, hw0, hw0K, -⟩, -⟩ :=
    GlobalTheory.T.discreteSeries_unitary_smooth_basic CompanionTheory.D.gk.admitted.k_finite_smooth k r ε lam ⟨H, σ⟩ ⟨hl, hσ⟩
  have hw0s := hsm w0 (hKT w0 hw0K)
  obtain ⟨C0, hC0⟩ := dec w0 hw0s w0 hw0s
  let X : SigData k r := ⟨H, σ, hUR, TopTA.irr_of_DSHpk (σ := σ) hσ, w0, hw0, aM k r, C0, hC0⟩
  have hS : SqIntG D X := hsq
  obtain ⟨l, hl1⟩ := thmM k r Wp D X hD hS le_rfl
  obtain ⟨τ, hτ, hτW, hτN⟩ := hTC k r D.z c hz hc
  have hw : IsSm (UH (Hpk k r)) σ w0 := hw0s
  have hτi : τ⁻¹ * τ = 1 := mul_eq_one_comm.1 (hG.2.2.2 τ hτ).2
  have key : ∀ Bm : H → Wp,
      PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) D.z (PI.BesselMapUniq.psiGen k r D.z c) σ D.π Bm →
      ∃ c₀ : ℂ, ∀ x ∈ UH (Hpk k r), Bm (σ τ (σ x w0)) = c₀ • l (σ x w0) := by
    intro Bm hBm
    have hCW := cwLin_of hBm
    obtain ⟨K, hK⟩ := hBd k r H σ hU hk D.z c hz hT hc Wp D.π hrep.1 hiso hcont Bm hCW
      (fun h hh m hm v hv => hBm.2.2.1 h hh m hm v hv) w0 hw
    refine orbit_mult hCL hAd hF D X hD hS le_rfl hU hw (fun v hv => dec w0 hw0s v hv) hl1
      (Bm := fun v => Bm (σ τ v)) (hCW.comp_sigma hAd hU hτ) (fun h hh m hm v hv => ?_) ⟨K, fun g hg => ?_⟩
    · obtain ⟨hn, hψ⟩ := hτN m hm
      have e : τ * (h * m) = h * (τ * m * τ⁻¹) * τ := by
        rw [← Matrix.mul_assoc, hτW h hh]
        simp only [Matrix.mul_assoc, hτi, Matrix.mul_one]
      show Bm (σ τ (σ (h * m) v)) = psi k r D.z cStd m • D.π h (Bm (σ τ v))
      rw [← hU.rep.apply_mul hτ (hU.rep.mul_mem _ hh.1 _ hm.1), e,
        hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hn.1) hτ, hBm.2.2.1 h hh _ hn _ (hv.apply hU.rep hτ), hψ]
    · show ‖Bm (σ τ (σ g w0))‖ ≤ K
      rw [← hU.rep.apply_mul hτ hg]
      exact hK _ (hU.rep.mul_mem _ hτ _ hg)
  obtain ⟨c₁, e₁⟩ := key B₁ hB₁
  obtain ⟨c₂, e₂⟩ := key B₂ hB₂
  have fin : ∀ a b : ℂ, a * c₁ + b * c₂ = 0 →
      ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, a • B₁ v + b • B₂ v = 0 := by
    intro a b hab v hv
    have hE := (((cwLin_of hB₁).comb (cwLin_of hB₂) a b).comp_sigma hAd hU hτ)
    have hτ' := (hG.2.2.2 τ hτ).1
    have hv' : IsSm (UH (Hpk k r)) σ (σ τ⁻¹ v) := IsSm.apply hU.rep hv hτ'
    have h0 := hE.eq_zero hU hw (fun g hg => by
        show a • B₁ (σ τ (σ g w0)) + b • B₂ (σ τ (σ g w0)) = 0
        rw [e₁ g hg, e₂ g hg, smul_smul, smul_smul, ← add_smul, hab, zero_smul]) hv'
      (fun Ws hWs δ hδ => by
        have := cyc_of_smooth k r ε lam H σ w0 hσ (by intro e; rw [e, norm_zero] at hw0; exact zero_ne_one hw0)
          hw0s _ hv' Ws hWs δ hδ
        simp only [dsigW_eq'] at this
        exact this)
    have e : σ τ (σ τ⁻¹ v) = v := by
      rw [← hU.rep.apply_mul hτ hτ', (hG.2.2.2 τ hτ).2, hU.rep.map_one]; rfl
    simpa only [e] using h0
  by_cases h1 : c₁ = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, fin 1 0 (by rw [h1]; simp)⟩
  · exact ⟨c₂, -c₁, Or.inr (neg_ne_zero.2 h1), fin c₂ (-c₁) (by ring)⟩

end CompanionTheory.Bmu
