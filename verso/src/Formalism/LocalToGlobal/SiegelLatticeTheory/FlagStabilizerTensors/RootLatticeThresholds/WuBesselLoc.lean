import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.AmpTensorDSdNonemptyOfSubsingleton

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.WuBL

/- English proof (translation)
Substitute `hn` using the available equality. Conclude with `Formalism.L2.SG.Pf.WFL.cM_closedEmb (ε := ε) (A := Qi) (B := Q) (A' := Q) (B' := Qi) h2 h2`.
-/
theorem trG_closedEmb' {k r n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) :
    Topology.IsClosedEmbedding (fun γ : Formalism.REAL.UJ ε => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Formalism.QuantumDeterminants.Mt k r)) := by
  subst hn
  exact Formalism.L2.SG.Pf.WFL.cM_closedEmb (ε := ε) (A := Qi) (B := Q) (A' := Q) (B' := Qi) h2 h2

/- English proof (translation)
Establish `hSK` using `Formalism.L2.SG.Pf.Choice.haar_tr hn ε Q Qi h2 hg`. Establish `hce` using `trG_closedEmb' hn ε h2`. Take `⟨hz, hT1⟩` from `Formalism.FourierDecayAlt.P.base_vector_exists k r`. Establish `hT0 : 0 < Formalism.QuantumDeterminants.Tz k r (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k)))` using `by rw [hT1]; exact one_pos`. Establish `hright` using `(quotient_measure_unitary_group k r _ hz hT0).2.2.2.1 _ hSK`.

Take `⟨hsf, hne, hcon, hleft⟩` from `hSK`. Use `⟨hcon, hleft, hright, fun K hK => ?_, hne⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hce.measurable hK.isClosed.measurableSet]`. Conclude with `(hce.isCompact_preimage hK).measure_lt_top`.
-/
theorem haarG_B' {k r n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r)
      ((Formalism.REAL.muG ε).map (fun γ => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ) : Formalism.QuantumDeterminants.Mt k r))) := by
  have hSK := Formalism.L2.SG.Pf.Choice.haar_tr hn ε Q Qi h2 hg
  have hce := trG_closedEmb' hn ε h2
  obtain ⟨hz, hT1⟩ := Formalism.FourierDecayAlt.P.base_vector_exists k r
  have hT0 : 0 < Formalism.QuantumDeterminants.Tz k r (Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))) := by rw [hT1]; exact one_pos
  have hright := (quotient_measure_unitary_group k r _ hz hT0).2.2.2.1 _ hSK
  obtain ⟨hsf, hne, hcon, hleft⟩ := hSK
  refine ⟨hcon, hleft, hright, fun K hK => ?_, hne⟩
  rw [Measure.map_apply hce.measurable hK.isClosed.measurableSet]
  exact (hce.isCompact_preimage hK).measure_lt_top

def ReproTr : Prop :=
  ∀ (k r : ℕ) (μG : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.B.GV k r) μG →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Formalism.FourierDecayAlt.B.Mat k r → (H →L[ℂ] H)),
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) σ →
    (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ∀ x, ‖σ g x‖ = ‖x‖) →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [NormedSpace ℂ Vp] (W : Formalism.FourierDecayAlt.B.Mat k r → Vp) (w : H)
    (y : Formalism.FourierDecayAlt.B.Mat k r), y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) →
    ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ (σ y w) (Matrix.of g) • (fun x => W (x * y)) (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ (σ y w)) (fun x => W (x * y)) x = W (x * y)

def L2RightTranslation : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
  ∀ (μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG →
    Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS → Formalism.MainNotions.S.IsQuotMeas μG μS ν →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] (W : Formalism.FourierDecayAlt.B.Mat k r → Vp),
    ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) → (∀ x, x ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → W x = 0) →
    (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖W (s * x)‖ = ‖W x‖) →
  ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), l2SG ν (fun x => W (x * y)) = l2SG ν W

def GapOfHyp : Prop :=
  ∀ (D : D7), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ τ : D.what₂.Tau,
    ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h

section Facts

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

/- English proof (translation)
Establish `hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)|` using `abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))`. Establish `hr : 0 < D.host.rdE`. Unfold `Formalism.BasicNotions.Host.rdE`. Conclude with `Real.rpow_pos_of_pos hd _`. Unfold `Formalism.BasicNotions.Host.v`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem host_v_pos' (D : D7) : 0 < D.host.v := by
  have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
  have hr : 0 < D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    exact Real.rpow_pos_of_pos hd _
  unfold Formalism.BasicNotions.Host.v
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hθ`. Use `push_neg at hθ`. Establish `hv` using `host_v_pos' D`. Establish `hq` using `C.nuS_q u τ`. Unfold `muNB kapN haarLie muS at hq`.

Apply the tactic sequence `simp (disch := exact mul_nonpos_of_nonneg_of_nonpos (by first | positivity | exact Real.rpow_nonneg (by linarith) _ | exact zpow_nonneg (by linarith) _) hθ) only [ENNReal.ofReal_of_nonpos, zero_smul, Measure.prod_zero, Measure.map_zero] at hq`. Establish `hmeas : Measurable (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ))`. Apply `Continuous.measurable` to reduce the goal to its premises. Unfold `Formalism.L2.SG.RealObj.trG`. Conclude with `(continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const`.

Establish `hpos : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))) Set.univ ≠ 0`. Unfold `Formalism.REAL.muG`. Conclude with `(isOpen_univ.measure_pos _ Set.univ_nonempty).ne'`. Establish `h1` using `hq (fun _ => 1) measurable_const`. Simplify using `only [lintegral_const, Measure.coe_zero, Pi.zero_apply, zero_mul, lintegral_zero, mul_one] at h1`.

Unfold `muGB at h1`. Rewrite `h1` using `[Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ]`. Simplify using `only [one_mul, mul_zero, zero_mul] at h1`. Conclude with `hpos h1`.
-/
theorem theta_pos (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) : 0 < θ := by
  by_contra hθ
  push_neg at hθ
  have hv := host_v_pos' D
  have hq := C.nuS_q u τ
  unfold muNB kapN haarLie muS at hq
  simp (disch := exact mul_nonpos_of_nonneg_of_nonpos (by first | positivity | exact Real.rpow_nonneg (by linarith) _ | exact zpow_nonneg (by linarith) _) hθ) only [ENNReal.ofReal_of_nonpos, zero_smul, Measure.prod_zero, Measure.map_zero] at hq
  have hmeas : Measurable (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ)) := by
    apply Continuous.measurable
    unfold Formalism.L2.SG.RealObj.trG
    exact (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const
  have hpos : (Formalism.REAL.muG (X.B.I.ε (vOf X τ))) Set.univ ≠ 0 := by
    unfold Formalism.REAL.muG
    exact (isOpen_univ.measure_pos _ Set.univ_nonempty).ne'
  have h1 := hq (fun _ => 1) measurable_const
  simp only [lintegral_const, Measure.coe_zero, Pi.zero_apply, zero_mul, lintegral_zero, mul_one] at h1
  unfold muGB at h1
  rw [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ] at h1
  simp only [one_mul, mul_zero, zero_mul] at h1
  exact hpos h1

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `C.isT τ`. Take `⟨-, -, ⟨⟨hone, hmul⟩, hiso, -⟩, -⟩` from `X.ds (vOf X τ)`. Establish `hA : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]`. Establish `hB : ∀ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ, C.Qi τ * (C.Q τ * M) = M` using `fun M => by`.

Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `hmem : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), C.Q τ * m * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ))`. Introduce `m hm`. Establish `hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `hm`. Use `show (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (C.Qi τ)ᴴ * (mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m) * C.Qi τ := by rw [h3]`. Use `_ = (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ := by rw [hm']`. Use `_ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by rw [h3]`.

Use `_ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hA]`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show X.B.σ (vOf X τ) (C.Q τ * 1 * C.Qi τ) = 1`. Rewrite using `[Matrix.mul_one, h2, hone]`. Introduce `a ha b hb show X.B.σ (vOf X τ) (C.Q τ * (a * b) * C.Qi τ) = (X.B.σ (vOf X τ) (C.Q τ * a * C.Qi τ)).comp (X.B.σ (vOf X τ) (C.Q τ * b * C.Qi τ))`.

Rewrite using `[← hmul _ (hmem a ha) _ (hmem b hb)]`. Rewrite using `[show C.Q τ * a * C.Qi τ * (C.Q τ * b * C.Qi τ) = C.Q τ * (a * b) * C.Qi τ by`. Simplify using `only [Matrix.mul_assoc, hB]]`. Introduce `g hg x`. Conclude with `hiso _ (hmem g hg) x`.
-/
theorem sigB_rep (C : Choice X θ) (τ : D.what₂.Tau) :
    Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (sigB X (C.Q τ) (C.Qi τ) τ) ∧
      (∀ g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), ∀ x, ‖sigB X (C.Q τ) (C.Qi τ) τ g x‖ = ‖x‖) := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  obtain ⟨-, -, ⟨⟨hone, hmul⟩, hiso, -⟩, -⟩ := X.ds (vOf X τ)
  have hA : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]
  have hB : ∀ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ, C.Qi τ * (C.Q τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hmem : ∀ m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
      C.Q τ * m * C.Qi τ ∈ UJset (X.B.I.ε (vOf X τ)) := by
    intro m hm
    have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := hm
    show (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ) =
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ))
    calc (C.Q τ * m * C.Qi τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * m * C.Qi τ)
        = (C.Qi τ)ᴴ * (mᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * m) * C.Qi τ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (C.Qi τ)ᴴ * (mᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * m) * C.Qi τ := by rw [h3]
      _ = (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.Qi τ := by rw [hm']
      _ = (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ) * C.Qi τ := by rw [h3]
      _ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := by simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hA]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show X.B.σ (vOf X τ) (C.Q τ * 1 * C.Qi τ) = 1
    rw [Matrix.mul_one, h2, hone]
  · intro a ha b hb
    show X.B.σ (vOf X τ) (C.Q τ * (a * b) * C.Qi τ) =
      (X.B.σ (vOf X τ) (C.Q τ * a * C.Qi τ)).comp (X.B.σ (vOf X τ) (C.Q τ * b * C.Qi τ))
    rw [← hmul _ (hmem a ha) _ (hmem b hb)]
    rw [show C.Q τ * a * C.Qi τ * (C.Q τ * b * C.Qi τ) = C.Q τ * (a * b) * C.Qi τ by
      simp only [Matrix.mul_assoc, hB]]
  · intro g hg x
    exact hiso _ (hmem g hg) x

/- English proof (translation)
Take `⟨h1, h2, h3, -⟩` from `C.isT τ`. Establish `hγ : (uMat γ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat γ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ))` using `γ.2`. Establish `hA : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]`. Establish `hB : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M` using `fun M => by`.

Rewrite using `[← Matrix.mul_assoc, h2, Matrix.one_mul]`. Establish `hC : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (uMat γ)ᴴ * (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (uMat γ * M)) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hγ]`. Use `show (C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS`. Rewrite using `[← h3]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hA, hB, hC]`.
-/
private theorem conj_mem_lemma (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    C.Qi τ * uMat γ * C.Q τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  have hγ : (uMat γ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat γ = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := γ.2
  have hA : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]
  have hB : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Q τ * (C.Qi τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hC : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      (uMat γ)ᴴ * (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (uMat γ * M)) = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hγ]
  show (C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ) =
    Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
  rw [← h3]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hA, hB, hC]

/- English proof (translation)
Unfold `wT`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨γ, hγ⟩`. Apply `hm` to reduce the goal to its premises. Take `⟨h1, h2, -, -⟩` from `C.isT τ`.

Establish `hA : ∀ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, C.Qi τ * (C.Q τ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`. Establish `hm' : m = C.Qi τ * uMat γ * C.Q τ`. Rewrite using `[hγ]`. Simplify using `only [Matrix.mul_assoc, h1, Matrix.mul_one, hA]`.

Rewrite using `[hm']`. Conclude with `conj_mem_lemma C τ γ`.
-/
theorem wT_off (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) (m : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (hm : m ∉ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) : wT C u τ m = 0 := by
  unfold wT
  rw [dif_neg]
  rintro ⟨γ, hγ⟩
  apply hm
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hA : ∀ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      C.Qi τ * (C.Q τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hm' : m = C.Qi τ * uMat γ * C.Q τ := by
    rw [hγ]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one, hA]
  rw [hm']
  exact conj_mem_lemma C τ γ

/- English proof (translation)
Take `⟨h1, h2, -, -⟩` from `C.isT τ`. Establish `hB : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, C.Q τ * (C.Qi τ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, h2, Matrix.one_mul]`. Establish `hex : ∃ γ' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ' = C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ` using `⟨γ, by simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hB]⟩`. Unfold `wT`.

Rewrite using `[dif_pos hex]`. Establish `heq : uMat hex.choose = uMat γ`. Rewrite using `[hex.choose_spec]`. Simplify using `only [Matrix.mul_assoc, h2, Matrix.mul_one, hB]`. Establish `hc : hex.choose = γ` using `Subtype.ext (Units.ext heq)`.

Rewrite using `[hc]`.
-/
theorem wT_at (C : Choice X θ) (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    wT C u τ (C.Qi τ * uMat γ * C.Q τ) = X.Wloc u (vOf X τ) γ := by
  obtain ⟨h1, h2, -, -⟩ := C.isT τ
  have hB : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, C.Q τ * (C.Qi τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hex : ∃ γ' : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), uMat γ' = C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ :=
    ⟨γ, by simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hB]⟩
  unfold wT
  rw [dif_pos hex]
  have heq : uMat hex.choose = uMat γ := by
    rw [hex.choose_spec]
    simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hB]
  have hc : hex.choose = γ := Subtype.ext (Units.ext heq)
  rw [hc]

end Facts

section Side

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

def cS (D : D7) : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ)

/- English proof (translation)
Establish `hka : 0 < D.host.ka`. Unfold `Formalism.BasicNotions.Host.ka`. Conclude with `div_pos Real.pi_pos (host_v_pos' D)`. Establish `hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast (D.host.g_prime 0).ne_zero`. Establish `hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0` using `by exact_mod_cast (D.host.g_prime 1).ne_zero`.

Unfold `cS`. Conclude with `Complex.ofReal_ne_zero.mpr (div_ne_zero (mul_ne_zero two_ne_zero hka.ne') (mul_ne_zero hg0 hg1))`.
-/
theorem cS_ne (D : D7) : cS D ≠ 0 := by
  have hka : 0 < D.host.ka := by
    unfold Formalism.BasicNotions.Host.ka
    exact div_pos Real.pi_pos (host_v_pos' D)
  have hg0 : ((D.host.g 0 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 0).ne_zero
  have hg1 : ((D.host.g 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (D.host.g_prime 1).ne_zero
  unfold cS
  exact Complex.ofReal_ne_zero.mpr (div_ne_zero (mul_ne_zero two_ne_zero hka.ne') (mul_ne_zero hg0 hg1))

/- English proof (translation)
Conclude with `conj_mem_lemma C τ γ`.
-/
theorem conjUH (C : Choice X θ) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    C.Qi τ * uMat γ * C.Q τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  exact conj_mem_lemma C τ γ

/- English proof (translation)
Simplify using `[Formalism.QuantumDeterminants.psi, Complex.norm_exp]`.
-/
theorem norm_psi (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (m : Formalism.FourierDecayAlt.B.Mat k r) :
    ‖Formalism.QuantumDeterminants.psi k r z c m‖ = 1 := by
  simp [Formalism.QuantumDeterminants.psi, Complex.norm_exp]

/- English proof (translation)
Take `⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩` from `hLF u τ`. Establish `hθ` using `theta_pos C u τ`. Take `⟨h, hgap, hok⟩` from `hGp D hG τ`. Take `⟨hz, hTz⟩` from `Formalism.L2.SG.Pf.zTr C u τ`. Establish `hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ)` using `by rw [hTz]; exact Tr_pos D u`.

Take `⟨h1, h2, hg, -⟩` from `C.isT τ`. Establish `hy` using `C.y_mem τ`. Take `⟨hrep, hiso⟩` from `sigB_rep C τ`. Establish `hHG` using `haarTr C τ`. Establish `hHGB` using `haarG_B' (n_eq' X) (X.B.I.ε (vOf X τ)) h2 hg`.

Establish `hty : IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (C.Q τ) (C.Qi τ) u τ)` using `hCols u τ`. Establish `hπ` using `Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT hty`. Establish `hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D θ)` using `Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ)`. Establish `hmaps : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), x * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)` using `fun x hx => Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models x (C.y τ) hx hy`. Use `⟨h, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, hgap, hok, hz, hT, cS_ne D, hty, ?_, hHG, C.muW_haar u τ, hN, C.nuS_q u τ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨P, hP, hmem⟩` from `C.y_low τ`. Use `⟨P, hP, ?_, hmem⟩` and prove the remaining obligations. Use `show ‖X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))‖ = 1`. Use `hiso (C.y τ) hy (X.B.w (vOf X τ))` as an intermediate fact. Rewrite using `[← hw1]`.

Conclude with `this`. Conclude with `hWc.comp (continuous_id.matrix_mul continuous_const).continuousOn hmaps`. Introduce `hh hhU m hm g hgU show wT C u τ (hh * m * g * C.y τ) = _ • _`. Rewrite using `[show hh * m * g * C.y τ = hh * m * (g * C.y τ) by simp only [Matrix.mul_assoc]]`. Conclude with `hWe hh hhU m hm _ (hmaps g hgU)`.

Conclude with `hRT D.R.k D.R.rS _ hHGB _ _ hrep hiso _ _ _ _ hy hWr`. Establish `hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖`. Introduce and unpack `_ ⟨h0, hh0, n0, hn0, rfl⟩ x hx`. Rewrite using `[hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, norm_psi, one_mul, hπ.2.1 h0 hh0]`. Establish `heq` using `hL2 D.R.k D.R.rS _ hz hT _ _ _ hHG hSH (C.nuS_q u τ) _ (wT C u τ) hWc (wT_off C u τ) hinv (C.y τ) hy`.

Rewrite using `[heq]`. Conclude with `⟨hne, hfin⟩`.
-/
theorem sideQ (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp) {C : Choice X θ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hLF : LocFactor C) (hCols : ∀ u τ, ColsTypeTr C u τ) (u : D.what₂.Word) (τ : D.what₂.Tau) :
    ∃ h : ℝ, Formalism.QuantumDeterminants.IsHCParam (lamD D τ) ∧
      IsDSHpk D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) ∧
      Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamD D τ) h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h ∧
      Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧ 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) ∧
      cS D ≠ 0 ∧
      IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (C.Q τ) (C.Qi τ) u τ) ∧
      IsLowUnitH D.R.k D.R.rS (epsSH D.R) (lamD D τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) ∧
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)) (C.muW u τ) ∧
      Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D θ) ∧
      Formalism.MainNotions.S.IsQuotMeas (muGB X (C.Q τ) (C.Qi τ) τ) (muS (C.muW u τ) (muNB D θ)) (C.nuS u τ) ∧
      ContinuousOn (fun x => wT C u τ (x * C.y τ)) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) ∧
      IsSPsiEquiv (zB X (C.Qi τ) u τ) (Formalism.QuantumDeterminants.psi D.R.k D.R.rS (zB X (C.Qi τ) u τ) (cS D))
        (piB X (C.Q τ) (C.Qi τ) u τ) (fun x => wT C u τ (x * C.y τ)) ∧
      (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
        Integrable (fun g : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
          eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ) (Matrix.of g) •
            (fun x => wT C u τ (x * C.y τ)) (x * Matrix.of g)) (muGB X (C.Q τ) (C.Qi τ) τ) ∧
        rconv (muGB X (C.Q τ) (C.Qi τ) τ) (eFun (muGB X (C.Q τ) (C.Qi τ) τ) (sigB X (C.Q τ) (C.Qi τ) τ) (v0Of C τ))
          (fun x => wT C u τ (x * C.y τ)) x = wT C u τ (x * C.y τ)) ∧
      l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) ≠ 0 ∧ l2SG (C.nuS u τ) (fun x => wT C u τ (x * C.y τ)) < ⊤ := by
  obtain ⟨hwsm, hw1, hSH, hWc, hWe, hWr, hne, hfin⟩ := hLF u τ
  have hθ := theta_pos C u τ
  obtain ⟨h, hgap, hok⟩ := hGp D hG τ
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  have hT : 0 < Formalism.QuantumDeterminants.Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by rw [hTz]; exact Tr_pos D u
  obtain ⟨h1, h2, hg, -⟩ := C.isT τ
  have hy := C.y_mem τ
  obtain ⟨hrep, hiso⟩ := sigB_rep C τ
  have hHG := haarTr C τ
  have hHGB := haarG_B' (n_eq' X) (X.B.I.ε (vOf X τ)) h2 hg
  have hty : IsHCTypeW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (fun i => ((D.hcW u τ).u i : ℝ)) (piB X (C.Q τ) (C.Qi τ) u τ) :=
    hCols u τ
  have hπ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved D.R.k D.R.rS _ _ _ _ hz hT hty
  have hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) (muNB D θ) :=
    Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ (kapN_ne_zero D hθ) (kapN_ne_top D θ)
  have hmaps : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS), x * C.y τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
    fun x hx => Formalism.MainNotions.S.Inh.mul_mem_UH_Hpk_nonempty_parameter_models x (C.y τ) hx hy
  refine ⟨h, Formalism.MainNotions.S.Inh.amp_isHCParam_lamD D τ, Formalism.L2.SG.Pf.dsTr C τ, hgap, hok, hz, hT, cS_ne D, hty, ?_, hHG,
    C.muW_haar u τ, hN, C.nuS_q u τ, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P, hP, hmem⟩ := C.y_low τ
    refine ⟨P, hP, ?_, hmem⟩
    show ‖X.B.σ (vOf X τ) (C.Q τ * C.y τ * C.Qi τ) (X.B.w (vOf X τ))‖ = 1
    have := hiso (C.y τ) hy (X.B.w (vOf X τ))
    rw [← hw1]
    exact this
  · exact hWc.comp (continuous_id.matrix_mul continuous_const).continuousOn hmaps
  · intro hh hhU m hm g hgU
    show wT C u τ (hh * m * g * C.y τ) = _ • _
    rw [show hh * m * g * C.y τ = hh * m * (g * C.y τ) by simp only [Matrix.mul_assoc]]
    exact hWe hh hhU m hm _ (hmaps g hgU)
  · exact hRT D.R.k D.R.rS _ hHGB _ _ hrep hiso _ _ _ _ hy hWr
  · have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS (zB X (C.Qi τ) u τ), ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS),
        ‖wT C u τ (s * x)‖ = ‖wT C u τ x‖ := by
      rintro _ ⟨h0, hh0, n0, hn0, rfl⟩ x hx
      rw [hWe h0 hh0 n0 hn0 x hx, norm_smul, psiS, norm_psi, one_mul, hπ.2.1 h0 hh0]
    have heq := hL2 D.R.k D.R.rS _ hz hT _ _ _ hHG hSH (C.nuS_q u τ) _ (wT C u τ) hWc (wT_off C u τ) hinv (C.y τ) hy
    rw [heq]
    exact ⟨hne, hfin⟩

end Side

/- English proof (translation)
Unfold `WuBesselOfLoc WuBessel`. Introduce `hG hBW hLF hDS hHaar hCols u τ`. Take `⟨h, hHC, hDSτ, hGap, hOK, hWb, hTz, hc, hType, hLow, hμG, hμW, hμN, hq, hcont, hspsi, hrep, hne, hlt⟩` from `sideQ hRT hL2 hGp hG hLF hCols u τ`. Take `⟨B, hBm, hBW'⟩` from `hBW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (cS D) (fun i => ((D.hcW u τ).u i : ℝ)) (lamD D τ) (epsSH D.R) h (X.B.H (vOf X τ)) (sigB X (C.Q τ) (C.Qi τ) τ) hHC hDSτ hGap hOK hWb hTz hc (X.Vloc u (vOf X τ)) (piB X (C.Q τ) (C.Qi τ) u τ) hType (v0Of C τ) hLow (muGB X (C.Q τ) (C.Qi τ) τ) (C. …`. Use `⟨B, hBm, fun γ => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2, h3, -⟩` from `C.isT τ`. Establish `hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `C.y_mem τ`. Establish `hd : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = 1`. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hJJ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, hd, Matrix.one_mul]`.

Establish `hA : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]`. Establish `hHinv : C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1`. Rewrite using `[← h3]`. Simplify using `only [Matrix.mul_assoc, hA, hJJ, h1]`.

Take `⟨yi, hyi⟩ : ∃ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, M = C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` from `⟨_, rfl⟩`. Establish `hyi1 : yi * C.y τ = 1`. Rewrite using `[hyi, show C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) by simp onl …`. Establish `hyi2 : C.y τ * yi = 1` using `by first`. Consider the case `exact mul_eq_one_comm.mp hyi1`.

Consider the case `exact (Matrix.mul_eq_one_comm (M := yi)).mp hyi1`. Consider the case `(letI := Matrix.invertibleOfLeftInverse (C.y τ) yi hyi1; exact Matrix.mul_invOf_self (C.y τ))`. Establish `hyiU : yiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * yi = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by`. Rewrite using `[hyi2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Establish `hmU : (C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS` using `conj_mem_lemma C τ γ`. Establish `hxU : C.Qi τ * uMat γ * C.Q τ * yi ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)` using `by show (C.Qi τ * uMat γ * C.Q τ * yi)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ * yi) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [hmU, hyiU]`. Establish `hxy : C.Qi τ * uMat γ * C.Q τ * yi * C.y τ = C.Qi τ * uMat γ * C.Q τ`. Rewrite using `[Matrix.mul_assoc _ yi, hyi1, Matrix.mul_one]`. Establish `hx'` using `hBW' _ hxU`.

Apply the tactic sequence `try simp only at hx'`. Rewrite `hx'` using `[hxy, wT_at]`. Rewrite using `[hx']`. Use `congr 1`. Take `⟨⟨-, hmul⟩, -⟩` from `sigB_rep C τ`.

Establish `hcomp` using `hmul _ hxU (C.y τ) (C.y_mem τ)`. Rewrite `hcomp` using `[hxy]`. Unfold `v0Of`. Rewrite using `[show sigB X (C.Q τ) (C.Qi τ) τ (C.Qi τ * uMat γ * C.Q τ * yi) (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) = sigB X (C.Q τ) (C.Qi τ) τ (C.Qi τ * uMat γ * C.Q τ) (X.B.w (vOf X τ)) by rw [hcomp]; rfl]`. Establish `hB2 : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, C.Q τ * (C.Qi τ * M) = M` using `fun M => by`.

Rewrite using `[← Matrix.mul_assoc, h2, Matrix.one_mul]`. Use `show X.B.σ (vOf X τ) (C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ) (X.B.w (vOf X τ)) = X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))`. Rewrite using `[show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ by`. Simplify using `only [Matrix.mul_assoc, h2, Matrix.mul_one, hB2]]`.
-/
theorem wuBesselOfLoc {D : D7} {X : HidaSetting D} {θ : ℝ} (hRT : ReproTr) (hL2 : L2RightTranslation) (hGp : GapOfHyp)
    (C : Choice X θ) : WuBesselOfLoc C := by
  unfold WuBesselOfLoc WuBessel
  intro hG hBW hLF hDS hHaar hCols u τ
  obtain ⟨h, hHC, hDSτ, hGap, hOK, hWb, hTz, hc, hType, hLow, hμG, hμW, hμN, hq, hcont, hspsi, hrep, hne, hlt⟩ :=
    sideQ hRT hL2 hGp hG hLF hCols u τ
  obtain ⟨B, hBm, hBW'⟩ := hBW D.R.k D.R.rS (zB X (C.Qi τ) u τ) (cS D) (fun i => ((D.hcW u τ).u i : ℝ))
    (lamD D τ) (epsSH D.R) h (X.B.H (vOf X τ)) (sigB X (C.Q τ) (C.Qi τ) τ) hHC hDSτ hGap hOK hWb hTz hc
    (X.Vloc u (vOf X τ)) (piB X (C.Q τ) (C.Qi τ) u τ) hType (v0Of C τ) hLow
    (muGB X (C.Q τ) (C.Qi τ) τ) (C.muW u τ) (muNB D θ) (C.nuS u τ) hμG hμW hμN hq
    (fun x => wT C u τ (x * C.y τ)) hcont hspsi hrep hne hlt
  refine ⟨B, hBm, fun γ => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := C.isT τ
  have hy : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have hd : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = 1 := by
    unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJJ : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hd, Matrix.one_mul]
  have hA : ∀ M : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ, (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one, Matrix.one_mul]
  have hHinv : C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← h3]
    simp only [Matrix.mul_assoc, hA, hJJ, h1]
  obtain ⟨yi, hyi⟩ : ∃ M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      M = C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS :=
    ⟨_, rfl⟩
  have hyi1 : yi * C.y τ = 1 := by
    rw [hyi, show C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ * (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS *
        C.y τ = C.Qi τ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Qi τ)ᴴ *
        ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) by simp only [Matrix.mul_assoc], hy, hHinv]
  have hyi2 : C.y τ * yi = 1 := by
    first
      | exact mul_eq_one_comm.mp hyi1
      | exact (Matrix.mul_eq_one_comm (M := yi)).mp hyi1
      | (letI := Matrix.invertibleOfLeftInverse (C.y τ) yi hyi1; exact Matrix.mul_invOf_self (C.y τ))
  have hyiU : yiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * yi = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
    calc yiᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * yi
        = yiᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ) * yi := by rw [hy]
      _ = (C.y τ * yi)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.y τ * yi) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by
          rw [hyi2, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hmU : (C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ) =
      Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := conj_mem_lemma C τ γ
  have hxU : C.Qi τ * uMat γ * C.Q τ * yi ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
    show (C.Qi τ * uMat γ * C.Q τ * yi)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ * yi) =
      Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
    calc (C.Qi τ * uMat γ * C.Q τ * yi)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ * yi)
        = yiᴴ * ((C.Qi τ * uMat γ * C.Q τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (C.Qi τ * uMat γ * C.Q τ)) * yi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := by rw [hmU, hyiU]
  have hxy : C.Qi τ * uMat γ * C.Q τ * yi * C.y τ = C.Qi τ * uMat γ * C.Q τ := by
    rw [Matrix.mul_assoc _ yi, hyi1, Matrix.mul_one]
  have hx' := hBW' _ hxU
  try simp only at hx'
  rw [hxy, wT_at] at hx'
  rw [hx']
  congr 1
  obtain ⟨⟨-, hmul⟩, -⟩ := sigB_rep C τ
  have hcomp := hmul _ hxU (C.y τ) (C.y_mem τ)
  rw [hxy] at hcomp
  unfold v0Of
  rw [show sigB X (C.Q τ) (C.Qi τ) τ (C.Qi τ * uMat γ * C.Q τ * yi)
      (sigB X (C.Q τ) (C.Qi τ) τ (C.y τ) (X.B.w (vOf X τ))) =
      sigB X (C.Q τ) (C.Qi τ) τ (C.Qi τ * uMat γ * C.Q τ) (X.B.w (vOf X τ)) by rw [hcomp]; rfl]
  have hB2 : ∀ M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ, C.Q τ * (C.Qi τ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  show X.B.σ (vOf X τ) (C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ) (X.B.w (vOf X τ)) =
    X.B.σ (vOf X τ) (uMat γ) (X.B.w (vOf X τ))
  rw [show C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ = uMat γ by
    simp only [Matrix.mul_assoc, h2, Matrix.mul_one, hB2]]

end Formalism.L2.SG.Pf.WuBL
