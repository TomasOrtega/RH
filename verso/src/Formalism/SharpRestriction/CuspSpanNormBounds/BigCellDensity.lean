import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.FiniteOrderIntersectionInSmooth
import Formalism.HermitianCurvature.StatementD
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDiagonalMap
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralIdentities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositiveOrbitOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian

noncomputable section

namespace Formalism.MainNotions.BigCellDensity

open MeasureTheory Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA
open scoped InnerProductSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def DensAt (CV : ℕ) : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (A ε : ℝ) (mm : ℕ) (F' : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (γ : Formalism.FourierDecayAlt.B.Mat k r)
    (O : Formalism.FourierDecayAlt.C6.OrbData D γ),
    1 ≤ r → 0 < ε → (r : ℝ) * Formalism.FourierDecayAlt.C6.AV CV r (2 * r + k + 1) ≤ A → Formalism.FourierDecayAlt.C6.mmV CV r ≤ mm →
    Formalism.FourierDecayAlt.B.InCC A mm F' →
    (∀ g ∈ Formalism.FourierDecayAlt.B.GV k r, F' g ≠ 0 → ε ≤ Gf k r D.z D.z' g) →
    (∀ g ∈ Formalism.FourierDecayAlt.C6.bigPos D, Formalism.FourierDecayAlt.B.JF D F' g = 0) →
    Formalism.FourierDecayAlt.C6.IsRelevant D γ → 0 < Gf k r D.z D.z' γ → O.J F' = 0

def StandardBesselSetting : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0), L.c = cStd →
    IsSection (k0 + 1) r L.z L.z' μsec → L.κN ≠ 0 → L.κN ≠ ⊤ →
    ∃ D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq, D.z = L.z ∧ D.z' = L.z' ∧ D.π = L.π ∧ D.π' = L.π' ∧
      D.μW = L.μW ∧ D.μN = L.μN ∧ D.μW' = L.μW' ∧ D.μsec = μsec

/- English proof (translation)
Introduce `k0 r L μsec hc hsec hκ0 hκ1`. Take `⟨μG, hG⟩` from `Formalism.MainNotions.BridgeLemma₅.lb_haarG (k0 + 1) r`. Take `⟨χ, hχ1, hχ2, hχ3⟩` from `Formalism.FourierDecayAlt.P.character_exists_alt`. Take `⟨p1, p2, p3⟩` from `Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ`. Take `⟨q1, q2, q3⟩` from `Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'`.

Establish `hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset (k0 + 1) r) L.μN` using `Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1)`. Conclude with `⟨{ z := L.z, z' := L.z', π := L.π, π' := L.π', μG := μG, μW := L.μW, μN := L.μN, μW' := L.μW', μsec := μsec χ := χ, k_pos := by omega, z_mem := L.hz.1, z'_mem := L.hz'.1, T_pos := L.hz.2, T'_pos := L.hz'.2 π_rep := p1, π'_rep := q1, π_unitary := p2, π'_unitary := q2, π_cont := p3 …`.
-/
theorem settingTie : StandardBesselSetting := by
  intro k0 r L μsec hc hsec hκ0 hκ1
  obtain ⟨μG, hG⟩ := Formalism.MainNotions.BridgeLemma₅.lb_haarG (k0 + 1) r
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := Formalism.FourierDecayAlt.P.character_exists_alt
  obtain ⟨p1, p2, p3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  obtain ⟨q1, q2, q3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  have hN : Formalism.FourierDecayAlt.B.IsHaarOn (Nset (k0 + 1) r) L.μN :=
    Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 _ _ _ (Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1)
  exact ⟨{ z := L.z, z' := L.z', π := L.π, π' := L.π', μG := μG, μW := L.μW, μN := L.μN, μW' := L.μW', μsec := μsec
           χ := χ, k_pos := by omega, z_mem := L.hz.1, z'_mem := L.hz'.1, T_pos := L.hz.2, T'_pos := L.hz'.2
           π_rep := p1, π'_rep := q1, π_unitary := p2, π'_unitary := q2, π_cont := p3, π'_cont := q3, haarG := hG
           haarW := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ L.hz.1 L.hz.2 L.hμW.1, haarN := hN
           haarW' := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.1 _ _ _ _ L.hz'.1 L.hz'.2 L.hμW'.1
           sec := hsec, χ_smooth := hχ1, χ_supp := hχ2, χ_int := hχ3 }, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def CCRight : Prop :=
  ∀ (k r : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (mm : ℕ)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E), 0 ≤ A → IsCC k r A mm F → ∀ m ≤ mm,
      Formalism.FourierDecayAlt.B.CkOn (m : ℕ∞) (Formalism.FourierDecayAlt.B.GV k r) F ∧ ∃ c : ℝ, ∀ v : List (Formalism.FourierDecayAlt.B.Mat k r),
        (∀ X ∈ v, Formalism.FourierDecayAlt.B.unitLie k r X) → v.length ≤ m →
          ∀ g ∈ Formalism.FourierDecayAlt.B.GV k r, Formalism.FourierDecayAlt.B.gN g ^ A * ‖Formalism.FourierDecayAlt.B.Rw v F g‖ ≤ c

def BigCellJ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (A : ℝ) (mm : ℕ) (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)),
    (r = 0 ∨ 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A) → Formalism.FourierDecayAlt.B.InCC A mm F →
    (∀ q : (Fin r → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) → Tz k r D.z * Tz k r D.z' < Complex.normSq q.2 →
      Formalism.FourierDecayAlt.B.JF D F (bigCell k r q.1 (D.μsec q.2)) = 0) →
    ∀ g ∈ Formalism.FourierDecayAlt.C6.bigPos D, Formalism.FourierDecayAlt.B.JF D F g = 0

/- English proof (translation)
Take `⟨hU, hfix, hz⟩` from `hh`. Establish `hH : IsUnit (Hpk k r).det` using `Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1`. Take `⟨hdet, hUinv⟩` from `(Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hH).2.2 h hU`. Establish `key : ∀ v, Matrix.mulVec h v = v → Matrix.mulVec h⁻¹ v = v`. Introduce `v hv`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨hUinv, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩`.
-/
theorem uw_inv {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : h⁻¹ ∈ UWset k r z := by
  obtain ⟨hU, hfix, hz⟩ := hh
  have hH : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  obtain ⟨hdet, hUinv⟩ := (Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) hH).2.2 h hU
  have key : ∀ v, Matrix.mulVec h v = v → Matrix.mulVec h⁻¹ v = v := by
    intro v hv
    calc Matrix.mulVec h⁻¹ v = Matrix.mulVec h⁻¹ (Matrix.mulVec h v) := by rw [hv]
      _ = Matrix.mulVec (h⁻¹ * h) v := Matrix.mulVec_mulVec _ _ _
      _ = v := by rw [Matrix.nonsing_inv_mul h hdet, Matrix.one_mulVec]
  exact ⟨hUinv, fun a => ⟨key _ (hfix a).1, key _ (hfix a).2⟩, key _ hz⟩

/- English proof (translation)
Establish `h1` using `(Formalism.QuantumDeterminants.nSubgroup k r).1`. Establish `hell` using `Formalism.QuantumDeterminants.ellAdd k r z hz 1 h1 1 h1`. Rewrite `hell` using `[Matrix.mul_one]`. Establish `h0 : ell k r z 1 = 0` using `by linear_combination -hell`. Simplify using `[psi, h0]`.
-/
theorem psi_one {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (hz : inWb k r z) : psi k r z c 1 = 1 := by
  have h1 := (Formalism.QuantumDeterminants.nSubgroup k r).1
  have hell := Formalism.QuantumDeterminants.ellAdd k r z hz 1 h1 1 h1
  rw [Matrix.mul_one] at hell
  have h0 : ell k r z 1 = 0 := by linear_combination -hell
  simp [psi, h0]

def OrbTie : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → D.z = L.z → D.z' = L.z' → D.π = L.π → D.π' = L.π' → D.μW = L.μW →
    D.μN = L.μN → D.μW' = L.μW' →
    ∀ (γ : Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ)
      (μR : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ →
      IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
        ∃ O : Formalism.FourierDecayAlt.C6.OrbData D g, ∀ F, O.J F = OrbInt L F g ν

def GTie : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ),
    g ∈ UH (Hpk k r) → Zhat k r z z' g = ptMat γ → Gf k r z z' g = ThB.Gpt (Tz k r z) (Tz k r z') γ

/- English proof (translation)
Introduce `k r z z' γ g _ hZ`. Simplify using `only [Gf, Dmin, ThB.Gpt, leadMinor, hZ]`.
-/
theorem gTie : GTie := by
  intro k r z z' γ g _ hZ
  simp only [Gf, Dmin, ThB.Gpt, leadMinor, hZ]

def KappaEdge : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r), L.c = cStd → L.κN = 0 ∨ L.κN = ⊤ →
    ∀ (F : GramWordSpace.GFn L) (γ : Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ)
      (μR : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L F g ν = 0

def KappaTop : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r), L.c = cStd → L.κN = ⊤ →
    ∀ (F : GramWordSpace.GFn L) (γ : Point ℂ (r + 1)) (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ)
      (μR : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L F g ν = 0

/- English proof (translation)
Simplify using `[cStd]`.
-/
theorem ucStd : ‖cStd‖ = 2 := by simp [cStd]

/- English proof (translation)
Introduce `h0`. Establish `h2` using `h.2`. Rewrite `h2` using `[h0, Measure.map_zero]`. Establish `hv : (volume : Measure ((rootPat γ) → ℂ)) Set.univ ≠ 0` using `Measure.measure_univ_ne_zero.mpr (NeZero.ne _)`. Establish `hpos : (0 : ℝ) < (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card`.

Rewrite using `[hc, ucStd]`. Check the signs of the components of the expression. Establish `h3` using `congrArg (fun μ : Measure ((rootPat γ) → ℂ) => μ Set.univ) h2`. Simplify using `only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul] at h3`. Break down `mul_eq_zero.1 h3.symm with h4 | h4` into its components or cases.

Rewrite `h4` using `[ENNReal.ofReal_eq_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hv h4`.
-/
theorem muR_ne_zero {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hc : L.c = cStd) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (μR : Measure (Mt (k0 + 1) r))
    (h : IsRootMeas L γ g μR) : μR ≠ 0 := by
  intro h0
  have h2 := h.2
  rw [h0, Measure.map_zero] at h2
  have hv : (volume : Measure ((rootPat γ) → ℂ)) Set.univ ≠ 0 :=
    Measure.measure_univ_ne_zero.mpr (NeZero.ne _)
  have hpos : (0 : ℝ) < (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card := by
    rw [hc, ucStd]
    positivity
  have h3 := congrArg (fun μ : Measure ((rootPat γ) → ℂ) => μ Set.univ) h2
  simp only [Measure.coe_zero, Pi.zero_apply, Measure.smul_apply, smul_eq_mul] at h3
  rcases mul_eq_zero.1 h3.symm with h4 | h4
  · rw [ENNReal.ofReal_eq_zero] at h4
    linarith
  · exact hv h4

def LevelOneB (D : D7) (CB : ℝ) : Prop := D.R.rS = 0 → OnePlaceEstimates.PositivityTheoremP D CB

def InPair {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (p : PairSp (k0 + 1) r) : Prop :=
  Matrix.of p.1.1 ∈ UWset (k0 + 1) r L.z ∧ Matrix.of p.1.2 ∈ Nset (k0 + 1) r ∧
    Matrix.of p.2.1 ∈ UWset (k0 + 1) r L.z' ∧ Matrix.of p.2.2 ∈ Nset (k0 + 1) r

/- English proof (translation)
The claim follows from `((Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1)).2.2 g hg).1`.
-/
theorem det_unit_of_UH {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    IsUnit g.det :=
  ((Formalism.QuantumDeterminants.uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1)).2.2 g hg).1

/- English proof (translation)
Establish `hN` using `Formalism.QuantumDeterminants.nSubgroup (k0 + 1) r`. Establish `hainv : a⁻¹ ∈ Nset (k0 + 1) r` using `hN.2.2 a ha.1`. Establish `hbinv : (g⁻¹ * a * g)⁻¹ ∈ Nset (k0 + 1) r` using `hN.2.2 _ ha.2`. Establish `hda` using `det_unit_of_UH ha.1.1`. Establish `hdb` using `det_unit_of_UH ha.2.1`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3, h4⟩`. Use `⟨h1, ?_, h3, ?_⟩` and prove the remaining obligations. Use `hN.2.1 _ hainv _ h2` as an intermediate fact. Establish `e : a⁻¹ * (a * Matrix.of x.1.2) = Matrix.of x.1.2`.

Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]`. Rewrite using `[← e]`. Conclude with `this`. Use `hN.2.1 _ hbinv _ h4` as an intermediate fact. Establish `e : (g⁻¹ * a * g)⁻¹ * (g⁻¹ * a * g * Matrix.of x.2.2) = Matrix.of x.2.2`.

Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdb, Matrix.one_mul]`. Rewrite using `[← e]`. Conclude with `this`. Introduce and unpack `⟨h1, h2, h3, h4⟩`. Conclude with `⟨h1, hN.2.1 _ ha.1 _ h2, h3, hN.2.1 _ ha.2 _ h4⟩`.
-/
theorem inPair_act_iff {k0 r : ℕ} (L : LocBessel (k0 + 1) r)
    {g a : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (ha : a ∈ RStab (k0 + 1) r g)
    (x : PairSp (k0 + 1) r) : InPair L (stabAct g a x) ↔ InPair L x := by
  have hN := Formalism.QuantumDeterminants.nSubgroup (k0 + 1) r
  have hainv : a⁻¹ ∈ Nset (k0 + 1) r := hN.2.2 a ha.1
  have hbinv : (g⁻¹ * a * g)⁻¹ ∈ Nset (k0 + 1) r := hN.2.2 _ ha.2
  have hda := det_unit_of_UH ha.1.1
  have hdb := det_unit_of_UH ha.2.1
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · have := hN.2.1 _ hainv _ h2
      have e : a⁻¹ * (a * Matrix.of x.1.2) = Matrix.of x.1.2 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hda, Matrix.one_mul]
      rw [← e]
      exact this
    · have := hN.2.1 _ hbinv _ h4
      have e : (g⁻¹ * a * g)⁻¹ * (g⁻¹ * a * g * Matrix.of x.2.2) = Matrix.of x.2.2 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdb, Matrix.one_mul]
      rw [← e]
      exact this
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, hN.2.1 _ ha.1 _ h2, h3, hN.2.1 _ ha.2 _ h4⟩

/- English proof (translation)
Establish `hda` using `det_unit_of_UH ha.1.1`. Establish `hdg` using `det_unit_of_UH hg`. Take `⟨h1, h2, h3, h4⟩` from `hx`. Establish `harg : (Matrix.of x.1.1)⁻¹ * (a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2) * Matrix.of x.2.1 = (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 * Matrix.of x.2.1`. Establish `e : (a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2) = (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2`.

Rewrite using `[Matrix.mul_inv_rev]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv g hdg, Matrix.mul_one, Matrix.nonsing_inv_mul a hda, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = (Matrix.of x.1.1)⁻¹ * ((Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2) * Matrix.of x.2.1 := by rw [e]`. Use `_ = _ := by simp only [Matrix.mul_assoc]`. Establish `hz` using `L.hz.1`. Establish `hz'` using `L.hz'.1`. Establish `hchar : psi (k0 + 1) r L.z L.c (a * Matrix.of x.1.2) * star (psi (k0 + 1) r L.z' L.c (g⁻¹ * a * g * Matrix.of x.2.2)) = psi (k0 + 1) r L.z L.c (Matrix.of x.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of x.2.2))`.

Rewrite using `[(Formalism.QuantumDeterminants.psiChar _ _ L.z L.c hz a ha.1).1 _ h2, (Formalism.QuantumDeterminants.psiChar _ _ L.z' L.c hz' _ ha.2).1 _ h4, ← hrel a ha, star_mul]`. Establish `hn : star (psi (k0 + 1) r L.z L.c a) * psi (k0 + 1) r L.z L.c a = 1`. Establish `h` using `(Formalism.QuantumDeterminants.psiChar _ _ L.z L.c hz a ha.1).2`. Rewrite using `[mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]`. Simplify using the standard rewrite rules.

Combine the equalities or inequalities in the displayed calculation. Establish `hs11 : Matrix.of (stabAct g a x).1.1 = Matrix.of x.1.1` using `rfl`. Establish `hs12 : Matrix.of (stabAct g a x).1.2 = a * Matrix.of x.1.2` using `rfl`. Establish `hs21 : Matrix.of (stabAct g a x).2.1 = Matrix.of x.2.1` using `rfl`. Establish `hs22 : Matrix.of (stabAct g a x).2.2 = g⁻¹ * a * g * Matrix.of x.2.2` using `rfl`.

Simplify using `only [besselIntg, hs11, hs12, hs21, hs22, harg, hchar]`.
-/
theorem besselIntg_act {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hc : L.c = cStd) (F : GramWordSpace.GFn L)
    {g a : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (hg : g ∈ UH (Hpk (k0 + 1) r))
    (hrel : IsRelStab L g) (ha : a ∈ RStab (k0 + 1) r g) (x : PairSp (k0 + 1) r) (hx : InPair L x) :
    besselIntg L F g (stabAct g a x) = besselIntg L F g x := by
  have hda := det_unit_of_UH ha.1.1
  have hdg := det_unit_of_UH hg
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have harg : (Matrix.of x.1.1)⁻¹ * (a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2) * Matrix.of x.2.1 =
      (Matrix.of x.1.1)⁻¹ * (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 * Matrix.of x.2.1 := by
    have e : (a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2) = (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 := by
      rw [Matrix.mul_inv_rev]
      calc (Matrix.of x.1.2)⁻¹ * a⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2)
          = (Matrix.of x.1.2)⁻¹ * (a⁻¹ * (g * g⁻¹) * a) * g * Matrix.of x.2.2 := by simp only [Matrix.mul_assoc]
        _ = (Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2 := by
          rw [Matrix.mul_nonsing_inv g hdg, Matrix.mul_one, Matrix.nonsing_inv_mul a hda, Matrix.mul_one]
    calc _ = (Matrix.of x.1.1)⁻¹ * ((a * Matrix.of x.1.2)⁻¹ * g * (g⁻¹ * a * g * Matrix.of x.2.2)) * Matrix.of x.2.1 := by
          simp only [Matrix.mul_assoc]
      _ = (Matrix.of x.1.1)⁻¹ * ((Matrix.of x.1.2)⁻¹ * g * Matrix.of x.2.2) * Matrix.of x.2.1 := by rw [e]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hz := L.hz.1
  have hz' := L.hz'.1
  have hchar : psi (k0 + 1) r L.z L.c (a * Matrix.of x.1.2) *
      star (psi (k0 + 1) r L.z' L.c (g⁻¹ * a * g * Matrix.of x.2.2)) =
      psi (k0 + 1) r L.z L.c (Matrix.of x.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of x.2.2)) := by
    rw [(Formalism.QuantumDeterminants.psiChar _ _ L.z L.c hz a ha.1).1 _ h2, (Formalism.QuantumDeterminants.psiChar _ _ L.z' L.c hz' _ ha.2).1 _ h4,
      ← hrel a ha, star_mul]
    have hn : star (psi (k0 + 1) r L.z L.c a) * psi (k0 + 1) r L.z L.c a = 1 := by
      have h := (Formalism.QuantumDeterminants.psiChar _ _ L.z L.c hz a ha.1).2
      rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
      simp
    calc _ = (star (psi (k0 + 1) r L.z L.c a) * psi (k0 + 1) r L.z L.c a) *
          (psi (k0 + 1) r L.z L.c (Matrix.of x.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of x.2.2))) := by ring
      _ = _ := by rw [hn, one_mul]
  have hs11 : Matrix.of (stabAct g a x).1.1 = Matrix.of x.1.1 := rfl
  have hs12 : Matrix.of (stabAct g a x).1.2 = a * Matrix.of x.1.2 := rfl
  have hs21 : Matrix.of (stabAct g a x).2.1 = Matrix.of x.2.1 := rfl
  have hs22 : Matrix.of (stabAct g a x).2.2 = g⁻¹ * a * g * Matrix.of x.2.2 := rfl
  simp only [besselIntg, hs11, hs12, hs21, hs22, harg, hchar]

/- English proof (translation)
Establish `: SecondCountableTopology (Mt k r × Mt k r)` using `inferInstance`. Establish `: SecondCountableTopologyEither (Mt k r × Mt k r) (Mt k r × Mt k r)` using `inferInstance`. Establish `: BorelSpace (Mt k r × Mt k r)` using `inferInstance`. Conclude with `Prod.borelSpace`.
-/
theorem pairSp_borel (k r : ℕ) : BorelSpace (PairSp k r) := by
  have : SecondCountableTopology (Mt k r × Mt k r) := inferInstance
  have : SecondCountableTopologyEither (Mt k r × Mt k r) (Mt k r × Mt k r) := inferInstance
  have : BorelSpace (Mt k r × Mt k r) := inferInstance
  exact Prod.borelSpace

attribute [local instance] pairSp_borel

/- English proof (translation)
Establish `: SecondCountableTopology (PairSp k r)` using `inferInstance`. Establish `: SecondCountableTopologyEither (PairSp k r) (Mt k r)` using `inferInstance`. Conclude with `Prod.borelSpace`.
-/
theorem pairSpMt_borel (k r : ℕ) : BorelSpace (PairSp k r × Mt k r) := by
  have : SecondCountableTopology (PairSp k r) := inferInstance
  have : SecondCountableTopologyEither (PairSp k r) (Mt k r) := inferInstance
  exact Prod.borelSpace

attribute [local instance] pairSpMt_borel

/- English proof (translation)
Unfold `stabAct`. Use `fun_prop`.
-/
theorem cont_act {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Continuous (fun q : Mt k r × PairSp k r => stabAct g (Matrix.of q.1) q.2) := by
  unfold stabAct
  fun_prop

/- English proof (translation)
Establish `h` using `(cont_act g).comp continuous_swap`. Conclude with `h.measurable`.
-/
theorem meas_act {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Measurable (fun q : PairSp k r × Mt k r => stabAct g (Matrix.of q.2) q.1) := by
  have h := (cont_act g).comp continuous_swap
  exact h.measurable

/- English proof (translation)
The claim follows from `(meas_act g).comp (measurable_const.prodMk measurable_id)`.
-/
theorem meas_act' {k r : ℕ} (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : PairSp k r) :
    Measurable (fun a : Mt k r => stabAct g (Matrix.of a) x) :=
  (meas_act g).comp (measurable_const.prodMk measurable_id)

/- English proof (translation)
Rewrite using `[Real.enorm_eq_ofReal_abs]`. Break down `le_total 0 y with h | h` into its components or cases. Simplify using `[abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h)]`. Simplify using `[abs_of_nonpos h, ENNReal.ofReal_of_nonpos h]`.
-/
theorem enorm_split (y : ℝ) : ‖y‖ₑ = ENNReal.ofReal y + ENNReal.ofReal (-y) := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 y with h | h
  · simp [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.2 h)]
  · simp [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h]

/- English proof (translation)
Establish `hm : ∀ w : PairSp k r → ENNReal, Measurable w → Measurable fun x => ∫⁻ a, w (stabAct g (Matrix.of a) x) ∂μR` using `fun w hw => Measurable.lintegral_prod_right' (hw.comp (meas_act g))`. Establish `hmp : Measurable fun p => ENNReal.ofReal (u p)` using `ENNReal.measurable_ofReal.comp hu`. Establish `hmm : Measurable fun p => ENNReal.ofReal (-u p)` using `ENNReal.measurable_ofReal.comp hu.neg`. Establish `eP` using `hq _ hmp`. Establish `eM` using `hq _ hmm`.

Establish `hle1 : ∀ p, ENNReal.ofReal (u p) ≤ ‖u p‖ₑ` using `fun p => by rw [enorm_split]; exact le_self_add`. Establish `hle2 : ∀ p, ENNReal.ofReal (-u p) ≤ ‖u p‖ₑ` using `fun p => by rw [enorm_split]; exact le_add_self`. Establish `hfinP : ∫⁻ x, ENNReal.ofReal (u x) ∂P ≠ ⊤` using `ne_top_of_le_ne_top hi.2.ne (lintegral_mono hle1)`. Establish `hfinM : ∫⁻ x, ENNReal.ofReal (-u x) ∂P ≠ ⊤` using `ne_top_of_le_ne_top hi.2.ne (lintegral_mono hle2)`. Establish `hApm` using `hm _ hmp`.

Establish `hAmm` using `hm _ hmm`. Establish `hfinP'` using `hfinP`. Establish `hfinM'` using `hfinM`. Rewrite `hfinP'` using `[eP]`. Rewrite `hfinM'` using `[eM]`.

Establish `hApfin` using `ae_lt_top hApm hfinP'`. Establish `hAmfin` using `ae_lt_top hAmm hfinM'`. Establish `hInt : ∀ᵐ x ∂ν, Integrable (fun a => u (stabAct g (Matrix.of a) x)) μR` using `by filter_upwards [hApfin, hAmfin] with x h1 h2`. Use `⟨(hu.comp (meas_act' g x)).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `show ∫⁻ a, ‖u (stabAct g (Matrix.of a) x)‖ₑ ∂μR < ⊤`.

Repeatedly rewrite using `[enorm_split]`. Establish `hmeas : Measurable (fun a => ENNReal.ofReal (u (stabAct g (Matrix.of a) x)))` using `hmp.comp (meas_act' g x)`. Rewrite using `[lintegral_add_left hmeas]`. Conclude with `ENNReal.add_lt_top.2 ⟨h1, h2⟩`. Establish `hinner : ∀ᵐ x ∂ν, ∫ a, u (stabAct g (Matrix.of a) x) ∂μR = (∫⁻ a, ENNReal.ofReal (u (stabAct g (Matrix.of a) x)) ∂μR).toReal - (∫⁻ a, ENNReal.ofReal (-u (stabAct g (Matrix.of a) x)) ∂μR).toReal` using `by filter_upwards [hInt] with x hx`.

Conclude with `integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx`. Establish `iP` using `integrable_toReal_of_lintegral_ne_top hApm.aemeasurable hfinP'`. Establish `iM` using `integrable_toReal_of_lintegral_ne_top hAmm.aemeasurable hfinM'`. Use `⟨hInt, (iP.sub iM).congr (hinner.mono fun x hx => hx.symm), ?_⟩` and prove the remaining obligations. Rewrite using `[integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, eP, eM, integral_congr_ae hinner, integral_sub iP iM, integral_toReal hApm.aemeasurable hApfin, integral_toReal hAmm.aemeasurable hAmfin]`.
-/
theorem weil_real {k r : ℕ} (P : Measure (PairSp k r)) (μR : Measure (Mt k r)) [SFinite μR]
    (ν : Measure (PairSp k r)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ f : PairSp k r → ENNReal, Measurable f →
      ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) ∂ν)
    (u : PairSp k r → ℝ) (hu : Measurable u) (hi : Integrable u P) :
    (∀ᵐ x ∂ν, Integrable (fun a => u (stabAct g (Matrix.of a) x)) μR) ∧
      Integrable (fun x => ∫ a, u (stabAct g (Matrix.of a) x) ∂μR) ν ∧
      ∫ x, u x ∂P = ∫ x, (∫ a, u (stabAct g (Matrix.of a) x) ∂μR) ∂ν := by
  have hm : ∀ w : PairSp k r → ENNReal, Measurable w →
      Measurable fun x => ∫⁻ a, w (stabAct g (Matrix.of a) x) ∂μR := fun w hw =>
    Measurable.lintegral_prod_right' (hw.comp (meas_act g))
  have hmp : Measurable fun p => ENNReal.ofReal (u p) := ENNReal.measurable_ofReal.comp hu
  have hmm : Measurable fun p => ENNReal.ofReal (-u p) := ENNReal.measurable_ofReal.comp hu.neg
  have eP := hq _ hmp
  have eM := hq _ hmm
  have hle1 : ∀ p, ENNReal.ofReal (u p) ≤ ‖u p‖ₑ := fun p => by rw [enorm_split]; exact le_self_add
  have hle2 : ∀ p, ENNReal.ofReal (-u p) ≤ ‖u p‖ₑ := fun p => by rw [enorm_split]; exact le_add_self
  have hfinP : ∫⁻ x, ENNReal.ofReal (u x) ∂P ≠ ⊤ := ne_top_of_le_ne_top hi.2.ne (lintegral_mono hle1)
  have hfinM : ∫⁻ x, ENNReal.ofReal (-u x) ∂P ≠ ⊤ := ne_top_of_le_ne_top hi.2.ne (lintegral_mono hle2)
  have hApm := hm _ hmp
  have hAmm := hm _ hmm
  have hfinP' := hfinP
  have hfinM' := hfinM
  rw [eP] at hfinP'
  rw [eM] at hfinM'
  have hApfin := ae_lt_top hApm hfinP'
  have hAmfin := ae_lt_top hAmm hfinM'
  have hInt : ∀ᵐ x ∂ν, Integrable (fun a => u (stabAct g (Matrix.of a) x)) μR := by
    filter_upwards [hApfin, hAmfin] with x h1 h2
    refine ⟨(hu.comp (meas_act' g x)).aestronglyMeasurable, ?_⟩
    show ∫⁻ a, ‖u (stabAct g (Matrix.of a) x)‖ₑ ∂μR < ⊤
    simp_rw [enorm_split]
    have hmeas : Measurable (fun a => ENNReal.ofReal (u (stabAct g (Matrix.of a) x))) := hmp.comp (meas_act' g x)
    rw [lintegral_add_left hmeas]
    exact ENNReal.add_lt_top.2 ⟨h1, h2⟩
  have hinner : ∀ᵐ x ∂ν, ∫ a, u (stabAct g (Matrix.of a) x) ∂μR =
      (∫⁻ a, ENNReal.ofReal (u (stabAct g (Matrix.of a) x)) ∂μR).toReal -
        (∫⁻ a, ENNReal.ofReal (-u (stabAct g (Matrix.of a) x)) ∂μR).toReal := by
    filter_upwards [hInt] with x hx
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hx
  have iP := integrable_toReal_of_lintegral_ne_top hApm.aemeasurable hfinP'
  have iM := integrable_toReal_of_lintegral_ne_top hAmm.aemeasurable hfinM'
  refine ⟨hInt, (iP.sub iM).congr (hinner.mono fun x hx => hx.symm), ?_⟩
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, eP, eM, integral_congr_ae hinner,
    integral_sub iP iM, integral_toReal hApm.aemeasurable hApfin, integral_toReal hAmm.aemeasurable hAmfin]

/- English proof (translation)
Take `⟨hn1, hn2, -⟩` from `weil_real P μR ν g hq (fun p => ‖h p‖) hh.norm.measurable hi.norm`. Establish `hInt : ∀ᵐ x ∂ν, Integrable (fun a => h (stabAct g (Matrix.of a) x)) μR` using `by filter_upwards [hn1] with x hx`. Conclude with `(integrable_norm_iff ((hh.comp_measurable (meas_act' g x)).aestronglyMeasurable)).1 hx`. Use `⟨hInt, ?_⟩` and prove the remaining obligations. Establish `hHm : StronglyMeasurable (fun x => ∫ a, h (stabAct g (Matrix.of a) x) ∂μR)`.

Establish `: StronglyMeasurable (Function.uncurry fun x (a : Mt k r) => h (stabAct g (Matrix.of a) x))` using `hh.comp_measurable (meas_act g)`. Conclude with `this.integral_prod_right'`. Establish `hHi : Integrable (fun x => ∫ a, h (stabAct g (Matrix.of a) x) ∂μR) ν` using `Integrable.mono' hn2 hHm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => norm_integral_le_integral_norm _)`. Assume the negation of the conclusion as `hne`. Take `⟨ℓ, hℓ⟩` from `SeparatingDual.exists_ne_zero (R := ℝ) (sub_ne_zero.2 hne)`.

Apply `hℓ` to reduce the goal to its premises. Rewrite using `[map_sub, sub_eq_zero, ← ℓ.integral_comp_comm hi, ← ℓ.integral_comp_comm hHi]`. Establish `hr` using `(weil_real P μR ν g hq (fun p => ℓ (h p)) (ℓ.continuous.comp_stronglyMeasurable hh).measurable (ℓ.integrable_comp hi)).2.2`. Rewrite using `[hr]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hInt] with x hx`. Conclude with `ℓ.integral_comp_comm hx`.
-/
theorem weil_vec {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (P : Measure (PairSp k r)) (μR : Measure (Mt k r)) [SFinite μR]
    (ν : Measure (PairSp k r)) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hq : ∀ f : PairSp k r → ENNReal, Measurable f →
      ∫⁻ x, f x ∂P = ∫⁻ x, (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR) ∂ν)
    (h : PairSp k r → E) (hh : StronglyMeasurable h) (hi : Integrable h P) :
    (∀ᵐ x ∂ν, Integrable (fun a => h (stabAct g (Matrix.of a) x)) μR) ∧
      ∫ x, h x ∂P = ∫ x, (∫ a, h (stabAct g (Matrix.of a) x) ∂μR) ∂ν := by
  obtain ⟨hn1, hn2, -⟩ := weil_real P μR ν g hq (fun p => ‖h p‖) hh.norm.measurable hi.norm
  have hInt : ∀ᵐ x ∂ν, Integrable (fun a => h (stabAct g (Matrix.of a) x)) μR := by
    filter_upwards [hn1] with x hx
    exact (integrable_norm_iff ((hh.comp_measurable (meas_act' g x)).aestronglyMeasurable)).1 hx
  refine ⟨hInt, ?_⟩
  have hHm : StronglyMeasurable (fun x => ∫ a, h (stabAct g (Matrix.of a) x) ∂μR) := by
    have : StronglyMeasurable (Function.uncurry fun x (a : Mt k r) => h (stabAct g (Matrix.of a) x)) :=
      hh.comp_measurable (meas_act g)
    exact this.integral_prod_right'
  have hHi : Integrable (fun x => ∫ a, h (stabAct g (Matrix.of a) x) ∂μR) ν :=
    Integrable.mono' hn2 hHm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => norm_integral_le_integral_norm _)
  by_contra hne
  obtain ⟨ℓ, hℓ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) (sub_ne_zero.2 hne)
  apply hℓ
  rw [map_sub, sub_eq_zero, ← ℓ.integral_comp_comm hi, ← ℓ.integral_comp_comm hHi]
  have hr := (weil_real P μR ν g hq (fun p => ℓ (h p)) (ℓ.continuous.comp_stronglyMeasurable hh).measurable
    (ℓ.integrable_comp hi)).2.2
  rw [hr]
  refine integral_congr_ae ?_
  filter_upwards [hInt] with x hx
  exact ℓ.integral_comp_comm hx

/- English proof (translation)
Establish `hW` using `(Formalism.FourierDecayAlt.P.weyl_subgroup_closed (k0 + 1) r L.z).closed`. Establish `hW'` using `(Formalism.FourierDecayAlt.P.weyl_subgroup_closed (k0 + 1) r L.z').closed`. Establish `hNc` using `(Formalism.FourierDecayAlt.P.unipotent_radical_closed (k0 + 1) r).closed`. Establish `hcl : IsClosed {p : PairSp (k0 + 1) r | InPair L p}`. Use `((hW.preimage (continuous_fst.comp continuous_fst)).inter (hNc.preimage (continuous_snd.comp continuous_fst))).inter ((hW'.preimage (continuous_fst.comp continuous_snd)).inter (hNc.preimage (continuous_snd.comp continuous_snd)))` as an intermediate fact.

Establish `hset : {p : PairSp (k0 + 1) r | InPair L p} = (Prod.fst ∘ Prod.fst ⁻¹' UWset (k0 + 1) r L.z ∩ Prod.snd ∘ Prod.fst ⁻¹' Nset (k0 + 1) r ∩ (Prod.fst ∘ Prod.snd ⁻¹' UWset (k0 + 1) r L.z' ∩ Prod.snd ∘ Prod.snd ⁻¹' Nset (k0 + 1) r))`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, b, c, d⟩`. Conclude with `⟨⟨a, b⟩, c, d⟩`.

Introduce and unpack `⟨⟨a, b⟩, c, d⟩`. Conclude with `⟨a, b, c, d⟩`. Rewrite using `[hset]`. Conclude with `this`. Establish `hS : MeasurableSet {p : PairSp (k0 + 1) r | ¬ InPair L p}` using `hcl.measurableSet.compl`.

Establish `: SigmaFinite L.μW` using `L.hμW.1.1`. Establish `: SigmaFinite L.μW'` using `L.hμW'.1.1`. Establish `hNH` using `Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1`. Establish `: SigmaFinite L.μN` using `hNH.1`. Establish `n1 : L.μW {x | Matrix.of x ∉ UWset (k0 + 1) r L.z} = 0` using `L.hμW.1.2.2.1`.

Establish `n2 : L.μN {x | Matrix.of x ∉ Nset (k0 + 1) r} = 0` using `hNH.2.2.1`. Establish `n3 : L.μW' {x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} = 0` using `L.hμW'.1.2.2.1`. Establish `hP0 : pairMeas L {p | ¬ InPair L p} = 0`. Establish `hsub : {p : PairSp (k0 + 1) r | ¬ InPair L p} ⊆ ((({x | Matrix.of x ∉ UWset (k0 + 1) r L.z} ×ˢ Set.univ) ×ˢ Set.univ) ∪ ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}) ×ˢ Set.univ)) ∪ ((Set.univ ×ˢ ({x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} ×ˢ Set.univ)) ∪ (Set.univ ×ˢ (Set.un …`. Introduce `p hp`.

Simplify using `only [Set.mem_setOf_eq, InPair, not_and_or] at hp`. Apply the tactic sequence `rcases hp with h | h | h | h <;> simp [h]`. Use `measure_mono_null hsub ?_` and prove the remaining obligations. Simplify using `only [pairMeas]`. Apply the tactic sequence `refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>`.

Apply the tactic sequence `rw [Measure.prod_prod, Measure.prod_prod] <;> simp [n1, n2, n3]`. Establish `h` using `hq ({p | ¬ InPair L p}.indicator 1) (measurable_one.indicator hS)`. Rewrite `h` using `[lintegral_indicator_one hS, hP0]`. Establish `hμR : μR Set.univ ≠ 0` using `Measure.measure_univ_ne_zero.mpr hne`. Establish `hae_a : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab (k0 + 1) r g`.

Rewrite using `[ae_iff]`. Simplify using `using hconc`. Establish `hlow : ∀ x, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ≤ ∫⁻ a, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator 1 (stabAct g (Matrix.of a) x) ∂μR`. Introduce `x`. Distinguish the cases in `hx : x ∈ {p : PairSp (k0 + 1) r | ¬ InPair L p}`.

Rewrite using `[Set.indicator_of_mem hx]`. Combine the equalities or inequalities in the displayed calculation. Establish `hm : stabAct g (Matrix.of a) x ∈ {p : PairSp (k0 + 1) r | ¬ InPair L p}` using `fun hin => hx ((inPair_act_iff L ha x).1 hin)`. Simplify using `[Set.indicator_of_mem hm])`. Rewrite using `[Set.indicator_of_notMem hx]`.

Conclude with `zero_le`. Establish `h2 : ∫⁻ x, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ∂ν = 0` using `le_antisymm ((lintegral_mono hlow).trans h.symm.le) zero_le`. Rewrite `h2` using `[lintegral_indicator_const hS]`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `absurd h3 hμR`.

Conclude with `ae_iff.2 h3`.
-/
theorem nu_inPair_gen {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤)
    {g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ}
    {μR : Measure (Mt (k0 + 1) r)} {ν : Measure (PairSp (k0 + 1) r)}
    (hconc : μR {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0) (hne : μR ≠ 0) (hq : IsOrbQuot L g μR ν) :
    ∀ᵐ x ∂ν, InPair L x := by
  have hW := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed (k0 + 1) r L.z).closed
  have hW' := (Formalism.FourierDecayAlt.P.weyl_subgroup_closed (k0 + 1) r L.z').closed
  have hNc := (Formalism.FourierDecayAlt.P.unipotent_radical_closed (k0 + 1) r).closed
  have hcl : IsClosed {p : PairSp (k0 + 1) r | InPair L p} := by
    have := ((hW.preimage (continuous_fst.comp continuous_fst)).inter
      (hNc.preimage (continuous_snd.comp continuous_fst))).inter
      ((hW'.preimage (continuous_fst.comp continuous_snd)).inter (hNc.preimage (continuous_snd.comp continuous_snd)))
    have hset : {p : PairSp (k0 + 1) r | InPair L p} =
        (Prod.fst ∘ Prod.fst ⁻¹' UWset (k0 + 1) r L.z ∩ Prod.snd ∘ Prod.fst ⁻¹' Nset (k0 + 1) r ∩
          (Prod.fst ∘ Prod.snd ⁻¹' UWset (k0 + 1) r L.z' ∩ Prod.snd ∘ Prod.snd ⁻¹' Nset (k0 + 1) r)) := by
      ext p
      constructor
      · rintro ⟨a, b, c, d⟩
        exact ⟨⟨a, b⟩, c, d⟩
      · rintro ⟨⟨a, b⟩, c, d⟩
        exact ⟨a, b, c, d⟩
    rw [hset]
    exact this
  have hS : MeasurableSet {p : PairSp (k0 + 1) r | ¬ InPair L p} := hcl.measurableSet.compl
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hNH := Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1
  have : SigmaFinite L.μN := hNH.1
  have n1 : L.μW {x | Matrix.of x ∉ UWset (k0 + 1) r L.z} = 0 := L.hμW.1.2.2.1
  have n2 : L.μN {x | Matrix.of x ∉ Nset (k0 + 1) r} = 0 := hNH.2.2.1
  have n3 : L.μW' {x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} = 0 := L.hμW'.1.2.2.1
  have hP0 : pairMeas L {p | ¬ InPair L p} = 0 := by
    have hsub : {p : PairSp (k0 + 1) r | ¬ InPair L p} ⊆
        ((({x | Matrix.of x ∉ UWset (k0 + 1) r L.z} ×ˢ Set.univ) ×ˢ Set.univ) ∪
          ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}) ×ˢ Set.univ)) ∪
        ((Set.univ ×ˢ ({x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} ×ˢ Set.univ)) ∪
          (Set.univ ×ˢ (Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}))) := by
      intro p hp
      simp only [Set.mem_setOf_eq, InPair, not_and_or] at hp
      rcases hp with h | h | h | h <;> simp [h]
    refine measure_mono_null hsub ?_
    simp only [pairMeas]
    refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>
      rw [Measure.prod_prod, Measure.prod_prod] <;> simp [n1, n2, n3]
  have h := hq ({p | ¬ InPair L p}.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS, hP0] at h
  have hμR : μR Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hne
  have hae_a : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab (k0 + 1) r g := by
    rw [ae_iff]
    simpa using hconc
  have hlow : ∀ x, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ≤
      ∫⁻ a, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator 1 (stabAct g (Matrix.of a) x) ∂μR := by
    intro x
    by_cases hx : x ∈ {p : PairSp (k0 + 1) r | ¬ InPair L p}
    · rw [Set.indicator_of_mem hx]
      calc μR Set.univ = ∫⁻ _a, (1 : ENNReal) ∂μR := by simp
        _ ≤ _ := lintegral_mono_ae (hae_a.mono fun a ha => by
              have hm : stabAct g (Matrix.of a) x ∈ {p : PairSp (k0 + 1) r | ¬ InPair L p} :=
                fun hin => hx ((inPair_act_iff L ha x).1 hin)
              simp [Set.indicator_of_mem hm])
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have h2 : ∫⁻ x, {p : PairSp (k0 + 1) r | ¬ InPair L p}.indicator (fun _ => μR Set.univ) x ∂ν = 0 :=
    le_antisymm ((lintegral_mono hlow).trans h.symm.le) zero_le
  rw [lintegral_indicator_const hS] at h2
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd h3 hμR
  · exact ae_iff.2 h3

/- English proof (translation)
Establish `: CompleteSpace L.Wp` using `FiniteDimensional.complete ℂ L.Wp`. Use `set f := fun p => θ p • besselIntg L F g p with hfdef`. Use `set h := hint.aestronglyMeasurable.mk f with hhdef`. Establish `hh : StronglyMeasurable h` using `hint.aestronglyMeasurable.stronglyMeasurable_mk`. Establish `hfh : f =ᵐ[pairMeas L] h` using `hint.aestronglyMeasurable.ae_eq_mk`.

Establish `hhi : Integrable h (pairMeas L)` using `hint.congr hfh`. Take `⟨-, hW⟩` from `weil_vec (pairMeas L) μR ν g hq h hh hhi`. Use `set N1 := toMeasurable (pairMeas L) {p | f p ≠ h p} with hN1def`. Establish `hN1m : MeasurableSet N1` using `measurableSet_toMeasurable _ _`. Establish `hN1 : pairMeas L N1 = 0`.

Rewrite using `[measure_toMeasurable]`. Conclude with `hfh`. Establish `hq1` using `hq (N1.indicator 1) (measurable_one.indicator hN1m)`. Rewrite `hq1` using `[lintegral_indicator_one hN1m, hN1]`. Establish `hmeasI : Measurable (fun x => ∫⁻ a, N1.indicator 1 (stabAct g (Matrix.of a) x) ∂μR)` using `Measurable.lintegral_prod_right' ((measurable_one.indicator hN1m).comp (meas_act g))`.

Establish `hae1 : ∀ᵐ x ∂ν, ∫⁻ a, N1.indicator 1 (stabAct g (Matrix.of a) x) ∂μR = 0` using `(lintegral_eq_zero_iff hmeasI).1 hq1.symm`. Establish `hνS` using `nu_inPair_gen L hκ0 hκ1 hconc hne hq`. Establish `hroot_ae : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab (k0 + 1) r g`. Rewrite using `[ae_iff]`. Simplify using `using hconc`.

Establish `key : ∀ᵐ x ∂ν, ∫ a, h (stabAct g (Matrix.of a) x) ∂μR = besselIntg L F g x` using `by filter_upwards [hae1, hνS] with x hx1 hx2`. Establish `hnot : ∀ᵐ a ∂μR, stabAct g (Matrix.of a) x ∉ N1`. Establish `h0` using `(lintegral_eq_zero_iff ((measurable_one.indicator hN1m).comp (meas_act' g x))).1 hx1`. Use `filter_upwards [h0] with a ha hmem`. Simplify using `[Function.comp, Set.indicator_of_mem hmem] at ha`.

Establish `heq : ∀ᵐ a ∂μR, h (stabAct g (Matrix.of a) x) = θ (stabAct g (Matrix.of a) x) • besselIntg L F g x` using `by filter_upwards [hnot, hroot_ae] with a ha1 ha2`. Establish `hfh' : f (stabAct g (Matrix.of a) x) = h (stabAct g (Matrix.of a) x)`. Assume the negation of the conclusion as `hne`. Conclude with `ha1 (subset_toMeasurable _ _ hne)`. Rewrite using `[← hfh', hfdef]`.

Simplify using `only`. Rewrite using `[besselIntg_act L hc F hg hrel ha2 x hx2]`. Rewrite using `[integral_congr_ae heq, integral_smul_const, hθ1 x hx2, one_smul]`. Rewrite using `[integral_congr_ae hfh, hW]`. Conclude with `integral_congr_ae key`.
-/
theorem weil_L_gen {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hc : L.c = cStd) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤)
    {g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ}
    {μR : Measure (Mt (k0 + 1) r)} [SFinite μR] {ν : Measure (PairSp (k0 + 1) r)}
    (hg : g ∈ UH (Hpk (k0 + 1) r)) (hrel : IsRelStab L g)
    (hconc : μR {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0) (hne : μR ≠ 0) (hq : IsOrbQuot L g μR ν)
    (F : GramWordSpace.GFn L) (θ : PairSp (k0 + 1) r → ℝ)
    (hθ1 : ∀ p, InPair L p → ∫ x, θ (stabAct g (Matrix.of x) p) ∂μR = 1)
    (hint : Integrable (fun p => θ p • besselIntg L F g p) (pairMeas L)) :
    ∫ p, θ p • besselIntg L F g p ∂(pairMeas L) = OrbInt L F g ν := by
  have : CompleteSpace L.Wp := FiniteDimensional.complete ℂ L.Wp
  set f := fun p => θ p • besselIntg L F g p with hfdef
  set h := hint.aestronglyMeasurable.mk f with hhdef
  have hh : StronglyMeasurable h := hint.aestronglyMeasurable.stronglyMeasurable_mk
  have hfh : f =ᵐ[pairMeas L] h := hint.aestronglyMeasurable.ae_eq_mk
  have hhi : Integrable h (pairMeas L) := hint.congr hfh
  obtain ⟨-, hW⟩ := weil_vec (pairMeas L) μR ν g hq h hh hhi
  set N1 := toMeasurable (pairMeas L) {p | f p ≠ h p} with hN1def
  have hN1m : MeasurableSet N1 := measurableSet_toMeasurable _ _
  have hN1 : pairMeas L N1 = 0 := by
    rw [measure_toMeasurable]
    exact hfh
  have hq1 := hq (N1.indicator 1) (measurable_one.indicator hN1m)
  rw [lintegral_indicator_one hN1m, hN1] at hq1
  have hmeasI : Measurable (fun x => ∫⁻ a, N1.indicator 1 (stabAct g (Matrix.of a) x) ∂μR) :=
    Measurable.lintegral_prod_right' ((measurable_one.indicator hN1m).comp (meas_act g))
  have hae1 : ∀ᵐ x ∂ν, ∫⁻ a, N1.indicator 1 (stabAct g (Matrix.of a) x) ∂μR = 0 :=
    (lintegral_eq_zero_iff hmeasI).1 hq1.symm
  have hνS := nu_inPair_gen L hκ0 hκ1 hconc hne hq
  have hroot_ae : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab (k0 + 1) r g := by
    rw [ae_iff]
    simpa using hconc
  have key : ∀ᵐ x ∂ν, ∫ a, h (stabAct g (Matrix.of a) x) ∂μR = besselIntg L F g x := by
    filter_upwards [hae1, hνS] with x hx1 hx2
    have hnot : ∀ᵐ a ∂μR, stabAct g (Matrix.of a) x ∉ N1 := by
      have h0 := (lintegral_eq_zero_iff ((measurable_one.indicator hN1m).comp (meas_act' g x))).1 hx1
      filter_upwards [h0] with a ha hmem
      simp [Function.comp, Set.indicator_of_mem hmem] at ha
    have heq : ∀ᵐ a ∂μR, h (stabAct g (Matrix.of a) x) = θ (stabAct g (Matrix.of a) x) • besselIntg L F g x := by
      filter_upwards [hnot, hroot_ae] with a ha1 ha2
      have hfh' : f (stabAct g (Matrix.of a) x) = h (stabAct g (Matrix.of a) x) := by
        by_contra hne
        exact ha1 (subset_toMeasurable _ _ hne)
      rw [← hfh', hfdef]
      simp only
      rw [besselIntg_act L hc F hg hrel ha2 x hx2]
    rw [integral_congr_ae heq, integral_smul_const, hθ1 x hx2, one_smul]
  rw [integral_congr_ae hfh, hW]
  exact integral_congr_ae key

/- English proof (translation)
Establish `hxi : Formalism.FourierDecayAlt.B.xiTau D (1, 1) p = psi (k0 + 1) r L.z L.c (Matrix.of p.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of p.2.2))`. Simplify using `only [Formalism.FourierDecayAlt.B.xiTau, Formalism.FourierDecayAlt.B.lam, psi, hz, hz', hc, one_mul]`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`.

Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [besselIntg, Formalism.FourierDecayAlt.B.rho, Formalism.FourierDecayAlt.B.sgs, hxi, hπ, hπ']`.
-/
theorem integrand_eq {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (hc : L.c = cStd) (hz : D.z = L.z) (hz' : D.z' = L.z') (hπ : D.π = L.π) (hπ' : D.π' = L.π') (F : GramWordSpace.GFn L)
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (p : PairSp (k0 + 1) r) :
    Formalism.FourierDecayAlt.B.xiTau D (1, 1) p • Formalism.FourierDecayAlt.B.rho D p F g = besselIntg L F g p := by
  have hxi : Formalism.FourierDecayAlt.B.xiTau D (1, 1) p =
      psi (k0 + 1) r L.z L.c (Matrix.of p.1.2) * star (psi (k0 + 1) r L.z' L.c (Matrix.of p.2.2)) := by
    simp only [Formalism.FourierDecayAlt.B.xiTau, Formalism.FourierDecayAlt.B.lam, psi, hz, hz', hc, one_mul]
    rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    push_cast
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [besselIntg, Formalism.FourierDecayAlt.B.rho, Formalism.FourierDecayAlt.B.sgs, hxi, hπ, hπ']

def RootHaar : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (μR : Measure (Mt (k0 + 1) r)),
    L.c = cStd → 0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset g) μR

/- English proof (translation)
Take `⟨j, hj⟩` from `D.R.m_even`. Establish `hm` using `D.R.two_le_m`. Simplify using `only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rank_eq (D : D7) : D.R.r = 2 * D.R.rS + D.R.k + 1 := by
  obtain ⟨j, hj⟩ := D.R.m_even
  have hm := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

def CellRepl : Prop :=
  ∀ (D : D7) (k0 : ℕ), k0 + 1 = D.R.k → ∀ (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (γ : Point ℂ (D.R.rS + 1)) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L),
      OnePlaceEstimates.IsCellOpAt (GramWordSpace.levOf L μsec) (OnePlaceEstimates.endsC 0 γ.1) o dP Θ → GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ A : ℝ, ∀ F : GramWordSpace.GFn L, (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∃ F' : GramWordSpace.GFn L,
          (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - dP - 3 * ((D.R.rS : ℝ) + 1) * ((mm : ℝ) + o)) mm F') ∧
          SuppGe (GramWordSpace.levOf L μsec) ε F' ∧
          (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
            Tz (k0 + 1) D.R.rS L.z * Tz (k0 + 1) D.R.rS L.z' < Complex.normSq q.2 →
            L.J F' (bigCell (k0 + 1) D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ (g : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ)
            (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
            0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
            IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
              OrbInt L (Θ F) g ν = OrbInt L F' g ν

def LevelOneA (D : D7) (CB : ℝ) : Prop := D.R.rS = 0 → OnePlaceEstimates.FrameIntegrationFormula D CB

def TieForms : Prop :=
  ∃ C₀ : ℝ, ∀ (D : D7) (k0 : ℕ) (X : GramWordSpace.Dat D k0) (CB : ℝ), C₀ ≤ CB → OnePlaceEstimates.StdShort X CB →
    (∀ v, (X.B v).κN ≠ 0 ∧ (X.B v).κN ≠ ⊤) → ∀ v : D.what₂.Tau,
    ∃ (T : Formalism.FourierDecayAlt.D.LevTower (k0 + 1) D.R.rS (X.B v).Wp (X.B v).Wq) (ω : ∀ j : ℕ, Point ℂ j → ℝ),
      Formalism.FourierDecayAlt.D.TowerNormalised T ∧ T.base.z = (X.B v).z ∧ T.base.z' = (X.B v).z' ∧ T.base.π = (X.B v).π ∧
      T.base.π' = (X.B v).π' ∧ T.base.μsec = X.μsec v ∧ (∀ j p, 0 < ω j p) ∧
      ∀ (χ : ℝ → ℝ), IsCutoff χ → ∀ ε : ℝ, 0 < ε →
      ∀ (j : ℕ) (hj : j ≤ D.R.rS) (w : Word), w.length ≤ OnePlaceEstimates.NS D → ∀ (p p' : Point ℂ j),
        X.gramLow v j hj w (X.Fv χ ε v) p p' =
          ((ω j p * ω j p' : ℝ) : ℂ) * Formalism.FourierDecayAlt.D.RRplace T ((X.sg v : ℝ) : ℂ) (fun _ => 0) 1 (fun _ _ _ _ => 0)
            (X.Fv χ ε v) j w (p.1.map Prod.swap) (p'.1.map Prod.swap)

def FirstAdmissibilityFiniteKappa (D : D7) (CV : ℝ) : Prop :=
  ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (γ : Point ℂ (D.R.rS + 1)) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L),
      OnePlaceEstimates.IsCellOpAt (GramWordSpace.levOf L μsec) (OnePlaceEstimates.endsC 0 γ.1) o dP Θ → GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ A : ℝ,
        (D.R.rS : ℝ) * (CV * ((D.R.rS : ℝ) ^ 3 * D.R.r + (D.R.r : ℝ) ^ 2 + (D.R.rS : ℝ) ^ 4)) ≤
          A - dP - 3 * ((D.R.rS : ℝ) + 1) * (CV * ((D.R.rS : ℝ) ^ 2 + 1) + o) →
        CV * ((D.R.rS : ℝ) + 1) ^ 2 * ((o : ℝ) + (D.R.rS : ℝ) * D.R.r + 1) ≤ A - 3 * ((D.R.rS : ℝ) + 1) * o →
        ∀ F : GramWordSpace.GFn L, (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
          SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∀ (g : ThB.Mx (k0 + 1) D.R.rS) (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
          0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
          IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L (Θ F) g ν = 0

def SecondAdmissibilityFiniteKappa (D : D7) (CB : ℝ) : Prop :=
  ∀ (k0 : ℕ) (_hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (A : ℝ) (mm : ℕ), Big CB (GramWordSpace.levOf L μsec) 0 A mm →
    ∀ F : GramWordSpace.GFn L, IsCC (k0 + 1) D.R.rS A mm F → ∀ ε : ℝ, 0 < ε → SuppGe (GramWordSpace.levOf L μsec) ε F →
      (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
        Tz (k0 + 1) D.R.rS L.z * Tz (k0 + 1) D.R.rS L.z' < Complex.normSq q.2 →
        L.J F (bigCell (k0 + 1) D.R.rS q.1 (μsec q.2)) = 0) →
      ∀ (γ : Point ℂ (D.R.rS + 1)) (g : ThB.Mx (k0 + 1) D.R.rS) (μR : Measure (Mt (k0 + 1) D.R.rS))
        (ν : Measure (PairSp (k0 + 1) D.R.rS)),
        0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
        IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → OrbInt L F g ν = 0

def c3 : ℝ := Classical.choose Formalism.FourierDecayAlt.P.orbital_integral_converges

def A0 (k r : ℕ) : ℝ := c3 * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1)

def TopLevelBesselStatement : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (ν' : Fin (2 * r + (k0 + 1) + 1) → ℂ) (m₀ : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r),
    L.c = cStd → 0 < L.κN → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' →
    Ds.μW = L.μW → Ds.μN = L.μN → Ds.μW' = L.μW' → Formalism.FourierDecayAlt.D.IsBaseFrame Ds ν' m₀ →
    ∃ c : List ℕ → ℝ, (∀ s, 0 < c s) ∧
      ∀ (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)), IsKFinCoefH L.σ F →
        Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
        0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ → (∃ g, IsPtRep L γ g ∧ IsRelStab L g) →
        ThB.orbSq L F γ = ENNReal.ofReal (c (γ.1.map Prod.snd) *
          (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))
            (Formalism.FourierDecayAlt.D.vecV Ds ν' m₀ F (γ.1.map Prod.swap))).re)

/- English proof (translation)
Proceed by induction on `l generalizing a b with`. Consider the case `nil => rfl`. Consider the case `cons x l ih`. Take `⟨t, s⟩` from `x`. Simplify using `only [List.map_cons, Prod.swap_prod_mk, Formalism.FourierDecayAlt.D.ptEntry, ptEntry, ih]`.
-/
theorem ptEntry_swap (l : List (ℂ × ℕ)) (a b : ℕ) :
    Formalism.FourierDecayAlt.D.ptEntry (l.map Prod.swap) a b = ptEntry l a b := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [List.map_cons, Prod.swap_prod_mk, Formalism.FourierDecayAlt.D.ptEntry, ptEntry, ih]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Formalism.FourierDecayAlt.D.ptMatN, ptMat, ptEntry_swap]`.
-/
theorem ptMatN_swap {r : ℕ} (γ : Point ℂ (r + 1)) :
    Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) = ptMat γ := by
  ext a b
  simp [Formalism.FourierDecayAlt.D.ptMatN, ptMat, ptEntry_swap]

/- English proof (translation)
Take `⟨l, hl, hs⟩` from `γ`. Use `⟨fun b hb => ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 hb`. Conclude with `⟨(hl x hx).2, (hl x hx).1⟩`. Simplify using `only [Formalism.FourierDecayAlt.D.ptSize, List.map_map]`.

Establish `e : (Prod.fst ∘ Prod.swap : ℂ × ℕ → ℕ) = Prod.snd` using `rfl`. Rewrite using `[e]`. Conclude with `hs`.
-/
theorem isLocPt_swap {r : ℕ} (γ : Point ℂ (r + 1)) : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1) := by
  obtain ⟨l, hl, hs⟩ := γ
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact ⟨(hl x hx).2, (hl x hx).1⟩
  · simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_map]
    have e : (Prod.fst ∘ Prod.swap : ℂ × ℕ → ℕ) = Prod.snd := rfl
    rw [e]
    exact hs

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.D.ptG ThB.Gpt leadMinor`. Rewrite using `[ptMatN_swap]`. Use `congr 3`. Use `congr 1`. Use extensionality with `a b`.

Simplify using `[Formalism.FourierDecayAlt.D.ptMatN, ptMat, ptEntry_swap]`.
-/
theorem ptG_eq_GPoint {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    Formalism.FourierDecayAlt.D.ptG (T * T') r (γ.1.map Prod.swap) = ThB.Gpt T T' γ := by
  unfold Formalism.FourierDecayAlt.D.ptG ThB.Gpt leadMinor
  rw [ptMatN_swap]
  congr 3
  congr 1
  ext a b
  simp [Formalism.FourierDecayAlt.D.ptMatN, ptMat, ptEntry_swap]

def bI : List ℕ → ℕ → ℕ
  | [], _ => 0
  | s :: ss, p => if p < s then 0 else 1 + bI ss (p - s)

/- English proof (translation)
Proceed by induction on `l generalizing p with`. Consider the case `nil => rfl`. Consider the case `cons x l ih`. Take `⟨t, s⟩` from `x`. Simplify using `only [blockIdx, bI, List.map_cons, ih]`.
-/
theorem blockIdx_eq (l : List (ℂ × ℕ)) (p : ℕ) : blockIdx l p = bI (l.map Prod.snd) p := by
  induction l generalizing p with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [blockIdx, bI, List.map_cons, ih]

def pc (r : ℕ) (s : List ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (r + 1) × Fin (r + 1))).filter fun q => q.1 < q.2 ∧ bI s q.1.val = bI s q.2.val).card

/- English proof (translation)
Unfold `rootPat pc`. Simplify using `only [blockIdx_eq]`.
-/
theorem card_rootPat {r : ℕ} (γ : Point ℂ (r + 1)) : (rootPat γ).card = pc r (γ.1.map Prod.snd) := by
  unfold rootPat pc
  simp only [blockIdx_eq]

/- English proof (translation)
Simplify using `[hsInner, Formalism.FourierDecayAlt.B.hsInner, Formalism.FourierDecayAlt.B.hsVec, PiLp.inner_apply]`.
-/
theorem hsInner_eq {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) :
    hsInner A B = Formalism.FourierDecayAlt.B.hsInner A B := by
  simp [hsInner, Formalism.FourierDecayAlt.B.hsInner, Formalism.FourierDecayAlt.B.hsVec, PiLp.inner_apply]

/- English proof (translation)
Rewrite using `[show t • A = (t : ℂ) • A from (Complex.coe_smul t A).symm]`. Simplify using `only [hsNormSq, hsInner, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← Finset.mul_sum]`. Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hsNormSq_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (t : ℝ) (A : Wq →L[ℂ] Wp) :
    hsNormSq (t • A) = t ^ 2 * hsNormSq A := by
  rw [show t • A = (t : ℂ) • A from (Complex.coe_smul t A).symm]
  simp only [hsNormSq, hsInner, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, ← Finset.mul_sum]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

/- English proof (translation)
Introduce `f hf`. Rewrite using `[h f hf, lintegral_smul_measure]`. Repeatedly rewrite using `[lintegral_smul_measure]`. Conclude with `lintegral_const_mul' a _ ha1`.
-/
theorem isOrbQuot_rescale {k r : ℕ} (L : LocBessel k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μ : Measure (Mt k r)} {ν : Measure (PairSp k r)} (a : ENNReal) (ha1 : a ≠ ⊤)
    (h : IsOrbQuot L g (a • μ) ν) : IsOrbQuot L g μ (a • ν) := by
  intro f hf
  rw [h f hf, lintegral_smul_measure]
  simp_rw [lintegral_smul_measure]
  exact lintegral_const_mul' a _ ha1

/- English proof (translation)
Unfold `Formalism.FourierDecayAlt.D.orbJ`. Rewrite using `[dif_pos hcut]`. Take `⟨⟨_, _, hθ1⟩, hint⟩` from `hcut.choose_spec`. Generalize the expression as in `hcut.choose = θ at hθ1 hint ⊢`. Establish `hμS : Ds.μSS = pairMeas L`.

Simplify using `only [Formalism.FourierDecayAlt.B.RealPlaceData.μSS, pairMeas, hW, hN, hW']`. Establish `hI : (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p) = fun p => θ p • besselIntg L F g p`. Use function extensionality and compare the values at `p`. Rewrite using `[show Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p = Formalism.FourierDecayAlt.B.xiTau Ds (1, 1) p • Formalism.FourierDecayAlt.B.rho Ds p F g from rfl, integrand_eq L Ds hc hz hz' hπ hπ' F g p]`. Rewrite `hint`, the goal using `[hI, hμS]`.

Use `weil_L_gen L hc hκ0 hκ1 hg hrel hconc hne hq F _ (fun p hp => hθ1 p ?_) hint` and prove the remaining obligations. Unfold `Formalism.FourierDecayAlt.B.RealPlaceData.inSS`. Rewrite using `[hz, hz']`. Conclude with `hp`.
-/
theorem orbJ_eq {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (hc : L.c = cStd) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤) (hz : Ds.z = L.z) (hz' : Ds.z' = L.z')
    (hπ : Ds.π = L.π) (hπ' : Ds.π' = L.π') (hW : Ds.μW = L.μW) (hN : Ds.μN = L.μN) (hW' : Ds.μW' = L.μW')
    {g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (hg : g ∈ UH (Hpk (k0 + 1) r))
    (hrel : IsRelStab L g) {μ : Measure (Mt (k0 + 1) r)} [SFinite μ]
    (hconc : μ {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0) (hne : μ ≠ 0) {ν : Measure (PairSp (k0 + 1) r)}
    (hq : IsOrbQuot L g μ ν) (F : GramWordSpace.GFn L)
    (hcut : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut Ds g μ θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p) Ds.μSS) :
    Formalism.FourierDecayAlt.D.orbJ Ds g μ F = OrbInt L F g ν := by
  unfold Formalism.FourierDecayAlt.D.orbJ
  rw [dif_pos hcut]
  obtain ⟨⟨_, _, hθ1⟩, hint⟩ := hcut.choose_spec
  generalize hcut.choose = θ at hθ1 hint ⊢
  have hμS : Ds.μSS = pairMeas L := by
    simp only [Formalism.FourierDecayAlt.B.RealPlaceData.μSS, pairMeas, hW, hN, hW']
  have hI : (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p) =
      fun p => θ p • besselIntg L F g p := by
    funext p
    rw [show Formalism.FourierDecayAlt.D.orbIntegrand Ds g F p = Formalism.FourierDecayAlt.B.xiTau Ds (1, 1) p • Formalism.FourierDecayAlt.B.rho Ds p F g from rfl,
      integrand_eq L Ds hc hz hz' hπ hπ' F g p]
  rw [hI, hμS] at hint ⊢
  refine weil_L_gen L hc hκ0 hκ1 hg hrel hconc hne hq F _ (fun p hp => hθ1 p ?_) hint
  unfold Formalism.FourierDecayAlt.B.RealPlaceData.inSS
  rw [hz, hz']
  exact hp

/- English proof (translation)
Unfold `ThB.orbSq`. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_` and prove the remaining obligations. Rewrite using `[hall g μR ν h]`. Take `⟨g, μR, ν, h⟩` from `hex`.

Use `le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le h ?_)))` and prove the remaining obligations. Rewrite using `[hall g μR ν h]`.
-/
theorem orbSq_eq_of {k r : ℕ} (L : LocBessel k r) (F : ThB.Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)) (v : ℝ)
    (hall : ∀ g μR ν, IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν →
      hsNormSq (OrbInt L F g ν) = v)
    (hex : ∃ g μR ν, IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μR ∧ IsOrbQuot L g μR ν) :
    ThB.orbSq L F γ = ENNReal.ofReal v := by
  unfold ThB.orbSq
  apply le_antisymm
  · refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_
    rw [hall g μR ν h]
  · obtain ⟨g, μR, ν, h⟩ := hex
    refine le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le h ?_)))
    rw [hall g μR ν h]

def RootMeasOfMuR : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq) (γ : Point ℂ (r + 1))
    (g : ThB.Mx (k0 + 1) r) (hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1)),
    L.c = cStd → Ds.z = L.z → Ds.z' = L.z' → g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r →
    Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) →
    IsRootMeas L γ g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) •
      Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap)))

def QuotExists : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (γ : Point ℂ (r + 1)) (g : ThB.Mx (k0 + 1) r) (μR : Measure (Mt (k0 + 1) r)),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR →
    ∃ ν : Measure (PairSp (k0 + 1) r), IsOrbQuot L g μR ν

def CutKFin : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq) (γ : Point ℂ (r + 1))
    (g : ThB.Mx (k0 + 1) r) (hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1))
    (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)),
    L.c = cStd → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' → Ds.μW = L.μW → Ds.μN = L.μN →
    Ds.μW' = L.μW' → IsKFinCoefH L.σ F → Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
    0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ →
    g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r → Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) →
    ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) θ ∧
      Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F q) Ds.μSS

def RepIndep : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq)
    (F : ThB.Mx (k0 + 1) r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1)),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → Ds.z = L.z → Ds.z' = L.z' → Ds.π = L.π → Ds.π' = L.π' → Ds.μW = L.μW →
    Ds.μN = L.μN → Ds.μW' = L.μW' → IsKFinCoefH L.σ F →
    Formalism.FourierDecayAlt.B.InCC (A0 (k0 + 1) r) 1 F →
    0 < ThB.Gpt (Tz (k0 + 1) r L.z) (Tz (k0 + 1) r L.z') γ →
    ∀ (g₁ : ThB.Mx (k0 + 1) r) (μ₁ : Measure (Mt (k0 + 1) r)) (ν₁ : Measure (PairSp (k0 + 1) r))
      (g₂ : ThB.Mx (k0 + 1) r) (μ₂ : Measure (Mt (k0 + 1) r)) (ν₂ : Measure (PairSp (k0 + 1) r)),
      (IsPtRep L γ g₁ ∧ IsRelStab L g₁ ∧ IsRootMeas L γ g₁ μ₁ ∧ IsOrbQuot L g₁ μ₁ ν₁) →
      (IsPtRep L γ g₂ ∧ IsRelStab L g₂ ∧ IsRootMeas L γ g₂ μ₂ ∧ IsOrbQuot L g₂ μ₂ ν₂) →
      hsNormSq (OrbInt L F g₁ ν₁) = hsNormSq (OrbInt L F g₂ ν₂)

def bD : List (ℕ × ℂ) → ℕ → ℕ
  | [], _ => 0
  | (s, _) :: rest, p => if p < s then 0 else 1 + bD rest (p - s)

def GoodL (l : List (ℕ × ℂ)) : Prop := ∀ b ∈ l, 1 ≤ b.1 ∧ b.2 ≠ 0

/- English proof (translation)
Introduce `b hb` and use `h b (List.mem_cons_of_mem _ hb)`.
-/
theorem goodL_tail {x : ℕ × ℂ} {l : List (ℕ × ℂ)} (h : GoodL (x :: l)) : GoodL l :=
  fun b hb => h b (List.mem_cons_of_mem _ hb)

/- English proof (translation)
Proceed by induction on `l generalizing a with`. Consider the case `nil => simp [Formalism.FourierDecayAlt.D.ptSize] at ha`. Consider the case `cons x l ih`. Take `⟨s, t⟩` from `x`. Simplify using `only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at ha`.

Simplify using `only [Formalism.FourierDecayAlt.D.ptPartner]`. Distinguish the cases in `h : a < s`. Simplify using `only [if_pos h]`. Rewrite using `[if_pos (show s - 1 - a < s by omega)]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [if_neg h]`. Rewrite using `[if_neg (show ¬ (s + Formalism.FourierDecayAlt.D.ptPartner l (a - s) < s) by omega), Nat.add_sub_cancel_left, ih (a - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem partner_partner (l : List (ℕ × ℂ)) (a : ℕ) (ha : a < Formalism.FourierDecayAlt.D.ptSize l) :
    Formalism.FourierDecayAlt.D.ptPartner l (Formalism.FourierDecayAlt.D.ptPartner l a) = a := by
  induction l generalizing a with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at ha
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at ha
    simp only [Formalism.FourierDecayAlt.D.ptPartner]
    by_cases h : a < s
    · simp only [if_pos h]
      rw [if_pos (show s - 1 - a < s by omega)]
      omega
    · simp only [if_neg h]
      rw [if_neg (show ¬ (s + Formalism.FourierDecayAlt.D.ptPartner l (a - s) < s) by omega), Nat.add_sub_cancel_left,
        ih (a - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)]
      omega

/- English proof (translation)
Proceed by induction on `l generalizing a b with`. Consider the case `nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb`. Consider the case `cons x l ih`. Take `⟨s, t⟩` from `x`. Establish `hs` using `(hl (s, t) (List.mem_cons_self)).1`.

Simplify using `only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb`. Simplify using `only [bD, Formalism.FourierDecayAlt.D.ptPartner]`. Distinguish the cases in `hbs : b < s`. Establish `has : a < s` using `by omega`. Simplify using `only [if_pos hbs, if_pos has]`.

Prove the components needed by the constructor for the conclusion. Introduce `_`. Use linear arithmetic over natural numbers and integers. Introduce `_`. Discharge the goal by the elementary cases of `trivial`.

Distinguish the cases in `has : a < s`. Simplify using `only [if_pos has, if_neg hbs]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Use linear arithmetic over natural numbers and integers. Simplify using `only [if_neg has, if_neg hbs]`. Use `ih (goodL_tail hl) (a - s) (b - s) (by omega) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)` as an intermediate fact. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : bD l (a - s) = bD l (b - s)` using `by omega`. Use `this.1 h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Establish `h' : Formalism.FourierDecayAlt.D.ptPartner l (b - s) < Formalism.FourierDecayAlt.D.ptPartner l (a - s)` using `by omega`. Use `this.2 h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem partner_order (l : List (ℕ × ℂ)) (hl : GoodL l) (a b : ℕ) (hab : a < b)
    (hb : b < Formalism.FourierDecayAlt.D.ptSize l) :
    (bD l a = bD l b ↔ Formalism.FourierDecayAlt.D.ptPartner l b < Formalism.FourierDecayAlt.D.ptPartner l a) := by
  induction l generalizing a b with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    have hs := (hl (s, t) (List.mem_cons_self)).1
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [bD, Formalism.FourierDecayAlt.D.ptPartner]
    by_cases hbs : b < s
    · have has : a < s := by omega
      simp only [if_pos hbs, if_pos has]
      constructor
      · intro _; omega
      · intro _; trivial
    · by_cases has : a < s
      · simp only [if_pos has, if_neg hbs]
        constructor
        · intro h; omega
        · intro h; omega
      · simp only [if_neg has, if_neg hbs]
        have := ih (goodL_tail hl) (a - s) (b - s) (by omega) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)
        constructor
        · intro h
          have h' : bD l (a - s) = bD l (b - s) := by omega
          have := this.1 h'
          omega
        · intro h
          have h' : Formalism.FourierDecayAlt.D.ptPartner l (b - s) < Formalism.FourierDecayAlt.D.ptPartner l (a - s) := by omega
          have := this.2 h'
          omega

/- English proof (translation)
Proceed by induction on `l generalizing a b with`. Consider the case `nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb`. Consider the case `cons x l ih`. Take `⟨s, t⟩` from `x`. Simplify using `only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb`.

Simplify using `only [Formalism.FourierDecayAlt.D.ptEntry, Formalism.FourierDecayAlt.D.ptPartner, Formalism.FourierDecayAlt.D.ptScal]`. Distinguish the cases in `hbs : b < s`. Simplify using `only [if_pos hbs]`. Distinguish the cases in `has : a < s`. Rewrite using `[if_pos ⟨has, hbs⟩]`.

Distinguish the cases in `e : a + b + 1 = s`. Rewrite using `[if_pos e, if_pos (show a = s - 1 - b by omega)]`. Rewrite using `[if_neg e, if_neg (show ¬ a = s - 1 - b by omega)]`. Rewrite using `[if_neg (show ¬ (a < s ∧ b < s) by omega), if_neg (show ¬ (s ≤ a ∧ s ≤ b) by omega), if_neg (show ¬ a = s - 1 - b by omega)]`. Simplify using `only [if_neg hbs]`.

Distinguish the cases in `has : a < s`. Rewrite using `[if_neg (show ¬ (a < s ∧ b < s) by omega), if_neg (show ¬ (s ≤ a ∧ s ≤ b) by omega), if_neg (show ¬ a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]`. Rewrite using `[if_neg (show ¬ (a < s ∧ b < s) by omega), if_pos (show s ≤ a ∧ s ≤ b by omega), ih (a - s) (b - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)]`. Distinguish the cases in `e : a - s = Formalism.FourierDecayAlt.D.ptPartner l (b - s)`. Rewrite using `[if_pos e, if_pos (show a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]`.

Rewrite using `[if_neg e, if_neg (show ¬ a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]`.
-/
theorem ptEntry_partner (l : List (ℕ × ℂ)) (a b : ℕ) (hb : b < Formalism.FourierDecayAlt.D.ptSize l) :
    Formalism.FourierDecayAlt.D.ptEntry l a b = if a = Formalism.FourierDecayAlt.D.ptPartner l b then Formalism.FourierDecayAlt.D.ptScal l b else 0 := by
  induction l generalizing a b with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [Formalism.FourierDecayAlt.D.ptEntry, Formalism.FourierDecayAlt.D.ptPartner, Formalism.FourierDecayAlt.D.ptScal]
    by_cases hbs : b < s
    · simp only [if_pos hbs]
      by_cases has : a < s
      · rw [if_pos ⟨has, hbs⟩]
        by_cases e : a + b + 1 = s
        · rw [if_pos e, if_pos (show a = s - 1 - b by omega)]
        · rw [if_neg e, if_neg (show ¬ a = s - 1 - b by omega)]
      · rw [if_neg (show ¬ (a < s ∧ b < s) by omega), if_neg (show ¬ (s ≤ a ∧ s ≤ b) by omega),
          if_neg (show ¬ a = s - 1 - b by omega)]
    · simp only [if_neg hbs]
      by_cases has : a < s
      · rw [if_neg (show ¬ (a < s ∧ b < s) by omega), if_neg (show ¬ (s ≤ a ∧ s ≤ b) by omega),
          if_neg (show ¬ a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]
      · rw [if_neg (show ¬ (a < s ∧ b < s) by omega), if_pos (show s ≤ a ∧ s ≤ b by omega),
          ih (a - s) (b - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)]
        by_cases e : a - s = Formalism.FourierDecayAlt.D.ptPartner l (b - s)
        · rw [if_pos e, if_pos (show a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]
        · rw [if_neg e, if_neg (show ¬ a = s + Formalism.FourierDecayAlt.D.ptPartner l (b - s) by omega)]

/- English proof (translation)
Proceed by induction on `l generalizing b with`. Consider the case `nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb`. Consider the case `cons x l ih`. Take `⟨s, t⟩` from `x`. Simplify using `only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb`.

Simplify using `only [Formalism.FourierDecayAlt.D.ptScal]`. Use `split_ifs with h`. Conclude with `(hl (s, t) List.mem_cons_self).2`. Conclude with `ih (goodL_tail hl) (b - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)`.
-/
theorem ptScal_ne (l : List (ℕ × ℂ)) (hl : GoodL l) (b : ℕ) (hb : b < Formalism.FourierDecayAlt.D.ptSize l) :
    Formalism.FourierDecayAlt.D.ptScal l b ≠ 0 := by
  induction l generalizing b with
  | nil => simp [Formalism.FourierDecayAlt.D.ptSize] at hb
  | cons x l ih =>
    obtain ⟨s, t⟩ := x
    simp only [Formalism.FourierDecayAlt.D.ptSize, List.map_cons, List.sum_cons] at hb
    simp only [Formalism.FourierDecayAlt.D.ptScal]
    split_ifs with h
    · exact (hl (s, t) List.mem_cons_self).2
    · exact ih (goodL_tail hl) (b - s) (by simp only [Formalism.FourierDecayAlt.D.ptSize]; omega)

/- English proof (translation)
Proceed by induction on `l generalizing p with`. Consider the case `nil => rfl`. Consider the case `cons x l ih`. Take `⟨t, s⟩` from `x`. Simplify using `only [blockIdx, bD, List.map_cons, Prod.swap_prod_mk, ih]`.
-/
theorem blockIdx_bD (l : List (ℂ × ℕ)) (p : ℕ) : blockIdx l p = bD (l.map Prod.swap) p := by
  induction l generalizing p with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨t, s⟩ := x
    simp only [blockIdx, bD, List.map_cons, Prod.swap_prod_mk, ih]

/- English proof (translation)
Substitute `h` using the available equality. Both sides reduce to the same expression.
-/
theorem cast_perm_val {n m : ℕ} (h : n = m) (e : Equiv.Perm (Fin n)) (x : Fin m) :
    ((h ▸ e) x).val = (e ⟨x.val, h ▸ x.isLt⟩).val := by
  subst h
  rfl

/- English proof (translation)
Introduce `b hb`. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 hb`. Conclude with `⟨(γ.2.1 x hx).2, (γ.2.1 x hx).1⟩`.
-/
theorem goodL_swap {r : ℕ} (γ : Point ℂ (r + 1)) : GoodL (γ.1.map Prod.swap) := by
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  exact ⟨(γ.2.1 x hx).2, (γ.2.1 x hx).1⟩

def wPt {r : ℕ} (γ : Point ℂ (r + 1)) : Equiv.Perm (Fin (r + 1)) :=
  (isLocPt_swap γ).2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap)

def dPt {r : ℕ} (γ : Point ℂ (r + 1)) : Fin (r + 1) → ℂ := fun a => Formalism.FourierDecayAlt.D.ptScal (γ.1.map Prod.swap) a.val

/- English proof (translation)
Unfold `wPt`. Rewrite using `[cast_perm_val]`. Conclude with `(Formalism.FourierDecayAlt.P.ptPerm_spec _ (r + 1) (isLocPt_swap γ)).1 _`.
-/
theorem wPt_val {r : ℕ} (γ : Point ℂ (r + 1)) (x : Fin (r + 1)) :
    (wPt γ x).val = Formalism.FourierDecayAlt.D.ptPartner (γ.1.map Prod.swap) x.val := by
  unfold wPt
  rw [cast_perm_val]
  exact (Formalism.FourierDecayAlt.P.ptPerm_spec _ (r + 1) (isLocPt_swap γ)).1 _

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[wPt_val, wPt_val]`. Conclude with `partner_partner _ _ (by rw [(isLocPt_swap γ).2]; exact x.isLt)`.
-/
theorem wPt_invol {r : ℕ} (γ : Point ℂ (r + 1)) (x : Fin (r + 1)) : wPt γ (wPt γ x) = x := by
  apply Fin.ext
  rw [wPt_val, wPt_val]
  exact partner_partner _ _ (by rw [(isLocPt_swap γ).2]; exact x.isLt)

/- English proof (translation)
The claim follows from `(wPt γ).symm_apply_eq.mpr (wPt_invol γ x).symm`.
-/
theorem wPt_symm {r : ℕ} (γ : Point ℂ (r + 1)) (x : Fin (r + 1)) : (wPt γ).symm x = wPt γ x :=
  (wPt γ).symm_apply_eq.mpr (wPt_invol γ x).symm

/- English proof (translation)
The claim follows from `ptScal_ne _ (goodL_swap γ) _ (by rw [(isLocPt_swap γ).2]; exact a.isLt)`.
-/
theorem dPt_ne {r : ℕ} (γ : Point ℂ (r + 1)) (a : Fin (r + 1)) : dPt γ a ≠ 0 :=
  ptScal_ne _ (goodL_swap γ) _ (by rw [(isLocPt_swap γ).2]; exact a.isLt)

/- English proof (translation)
Use extensionality with `i a`. Simplify using `only [Formalism.FourierDecayAlt.D.ptMatN, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]`. Rewrite using `[ptEntry_partner _ _ _ (by rw [(isLocPt_swap γ).2]; exact a.isLt)]`. Establish `: (i = wPt γ a) ↔ (i.val = Formalism.FourierDecayAlt.D.ptPartner (γ.1.map Prod.swap) a.val)`. Rewrite using `[Fin.ext_iff, wPt_val]`.

Distinguish the cases in `h : i = wPt γ a`. Rewrite using `[if_pos (this.1 h), if_pos h]`. Both sides reduce to the same expression. Rewrite using `[if_neg (fun h' => h (this.2 h')), if_neg h]`.
-/
theorem ptMatN_mono {r : ℕ} (γ : Point ℂ (r + 1)) :
    Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by
  ext i a
  simp only [Formalism.FourierDecayAlt.D.ptMatN, Formalism.FourierDecayAlt.C2.monoP, Matrix.of_apply]
  rw [ptEntry_partner _ _ _ (by rw [(isLocPt_swap γ).2]; exact a.isLt)]
  have : (i = wPt γ a) ↔ (i.val = Formalism.FourierDecayAlt.D.ptPartner (γ.1.map Prod.swap) a.val) := by
    rw [Fin.ext_iff, wPt_val]
  by_cases h : i = wPt γ a
  · rw [if_pos (this.1 h), if_pos h]
    rfl
  · rw [if_neg (fun h' => h (this.2 h')), if_neg h]

/- English proof (translation)
Rewrite using `[blockIdx_bD, blockIdx_bD, wPt_symm, wPt_symm, Fin.lt_def, wPt_val, wPt_val]`. Conclude with `partner_order _ (goodL_swap γ) a.val b.val hab (by rw [(isLocPt_swap γ).2]; exact b.isLt)`.
-/
theorem root_iff {r : ℕ} (γ : Point ℂ (r + 1)) (a b : Fin (r + 1)) (hab : a < b) :
    blockIdx γ.1 a.val = blockIdx γ.1 b.val ↔ (wPt γ).symm b < (wPt γ).symm a := by
  rw [blockIdx_bD, blockIdx_bD, wPt_symm, wPt_symm, Fin.lt_def, wPt_val, wPt_val]
  exact partner_order _ (goodL_swap γ) a.val b.val hab (by rw [(isLocPt_swap γ).2]; exact b.isLt)

def eRoot {r : ℕ} (γ : Point ℂ (r + 1)) : (rootPat γ) ≃ Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) where
  toFun p := ⟨(p.1.2, p.1.1), by
    have hp := p.2
    simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact ⟨hp.1, (root_iff γ _ _ hp.1).1 hp.2⟩⟩
  invFun q := ⟨(q.1.2, q.1.1), by
    simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨q.2.1, (root_iff γ _ _ q.2.1).2 q.2.2⟩⟩
  left_inv p := by rfl
  right_inv q := by rfl

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hj` using `j.isLt`. Simplify using `only [Hpk, esI, eI, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem hpk_esI (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) j = if j = eI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Unfold `herm bvec`. Simplify using `only [dotProduct, Pi.star_apply, Pi.single_apply, apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Simplify using `only [Matrix.mulVec, dotProduct, hpk_esI, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
theorem herm_esI (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  unfold herm bvec
  simp only [dotProduct, Pi.star_apply, Pi.single_apply, apply_ite star, star_one, star_zero, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, hpk_esI, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/- English proof (translation)
Unfold `flagMat Formalism.FourierDecayAlt.C2.uMap`. Rewrite using `[dif_pos ha, dif_pos ha, herm_esI]`.
-/
theorem flag_eq_uMap (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (ρ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (a b : Fin (r + 1)) (ha : a.val < r) : flagMat k r z ρ a b = Formalism.FourierDecayAlt.C2.uMap k r z ρ a b := by
  unfold flagMat Formalism.FourierDecayAlt.C2.uMap
  rw [dif_pos ha, dif_pos ha, herm_esI]

def Tmap {r : ℕ} (γ : Point ℂ (r + 1)) (x : Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ) : (rootPat γ) → ℂ :=
  fun p => (starRingEnd ℂ) (x (eRoot γ p))

def Tinv {r : ℕ} (γ : Point ℂ (r + 1)) (y : (rootPat γ) → ℂ) : Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ :=
  fun q => (starRingEnd ℂ) (y ((eRoot γ).symm q))

/- English proof (translation)
Use function extensionality and compare the values at `q`. Simplify using `[Tinv, Tmap]`.
-/
theorem Tinv_Tmap {r : ℕ} (γ : Point ℂ (r + 1)) (x : Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ) : Tinv γ (Tmap γ x) = x := by
  funext q
  simp [Tinv, Tmap]

/- English proof (translation)
Establish `h1` using `volume_measurePreserving_piCongrLeft (fun _ : (rootPat γ) => ℂ) (eRoot γ).symm`. Establish `h2 : MeasurePreserving (fun (y : (rootPat γ) → ℂ) (p : rootPat γ) => (Complex.conjLIE : ℂ → ℂ) (y p)) volume volume` using `volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving`. Establish `h3` using `h2.comp h1`. Use `h3 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x p`.

Simplify using `[Tmap, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]`.
-/
theorem Tmap_mp {r : ℕ} (γ : Point ℂ (r + 1)) : MeasurePreserving (Tmap γ) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ : (rootPat γ) => ℂ) (eRoot γ).symm
  have h2 : MeasurePreserving (fun (y : (rootPat γ) → ℂ) (p : rootPat γ) => (Complex.conjLIE : ℂ → ℂ) (y p)) volume volume :=
    volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving
  have h3 := h2.comp h1
  convert h3 using 1
  funext x p
  simp [Tmap, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/- English proof (translation)
Establish `hT` using `Tmap_mp γ`. Establish `hmT : Measurable (Tinv γ)`. Unfold `Tinv`. Use `fun_prop`. Use `⟨hmT, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hT.map_eq, Measure.map_map hmT hT.measurable]`. Establish `: Tinv γ ∘ Tmap γ = id` using `funext (Tinv_Tmap γ)`. Rewrite using `[this, Measure.map_id]`.
-/
theorem Tinv_mp {r : ℕ} (γ : Point ℂ (r + 1)) : MeasurePreserving (Tinv γ) volume volume := by
  have hT := Tmap_mp γ
  have hmT : Measurable (Tinv γ) := by
    unfold Tinv
    fun_prop
  refine ⟨hmT, ?_⟩
  rw [← hT.map_eq, Measure.map_map hmT hT.measurable]
  have : Tinv γ ∘ Tmap γ = id := funext (Tinv_Tmap γ)
  rw [this, Measure.map_id]

/- English proof (translation)
Distinguish the cases in `hB : w (Fin.last r) = Fin.last r`. Conclude with `⟨Formalism.FourierDecayAlt.P.Dx2.Rad.ex_degen D hγ hd hZ hB, Formalism.FourierDecayAlt.P.Dx2.Rad.inj_degen D hγ hd hZ hB, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.lst_gen D hγ hd hZ hρ⟩`. Establish `hpos` using `Formalism.FourierDecayAlt.P.Dx2.Rad.pos_of_w D hd hZ hB`. Conclude with `⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho D hγ hpos hd hZ, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj D hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩`.
-/
theorem good_of {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) {γ : Formalism.FourierDecayAlt.B.Mat k r}
    {w : Equiv.Perm (Fin (r + 1))} {d : Fin (r + 1) → ℂ} (hγ : γ ∈ Formalism.FourierDecayAlt.B.GV k r) (hd : ∀ a, d a ≠ 0)
    (hZ : Zhat k r D.z D.z' γ = Formalism.FourierDecayAlt.C2.monoP w d) : Formalism.FourierDecayAlt.P.Dx2.Rad.Good D γ w d := by
  by_cases hB : w (Fin.last r) = Fin.last r
  · exact ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.ex_degen D hγ hd hZ hB, Formalism.FourierDecayAlt.P.Dx2.Rad.inj_degen D hγ hd hZ hB,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.lst_gen D hγ hd hZ hρ⟩
  · have hpos := Formalism.FourierDecayAlt.P.Dx2.Rad.pos_of_w D hd hZ hB
    exact ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho D hγ hpos hd hZ, Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj D hγ hpos hd hZ,
      fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩

/- English proof (translation)
Rewrite using `[Measure.smul_apply, h.conc, smul_zero] left a ha := by rw [Measure.map_smul, h.left a ha] right a ha := by rw [Measure.map_smul, h.right a ha] finite_compact K hK := by`. Rewrite using `[Measure.smul_apply, smul_eq_mul]`. Conclude with `ENNReal.mul_lt_top h1.lt_top (h.finite_compact K hK)`. Use `ne_zero := by`. Introduce `h'`.

Apply `h.ne_zero` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero]`. Use `congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h'` as an intermediate fact. Simplify using `only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply] at this`. Conclude with `(mul_eq_zero.1 this).resolve_left h0`.
-/
theorem isHaarOn_smul {k r : ℕ} {U : Set (Formalism.FourierDecayAlt.B.Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ)
    {c : ENNReal} (h0 : c ≠ 0) (h1 : c ≠ ⊤) : Formalism.FourierDecayAlt.B.IsHaarOn U (c • μ) where
  conc := by rw [Measure.smul_apply, h.conc, smul_zero]
  left a ha := by rw [Measure.map_smul, h.left a ha]
  right a ha := by rw [Measure.map_smul, h.right a ha]
  finite_compact K hK := by
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top h1.lt_top (h.finite_compact K hK)
  ne_zero := by
    intro h'
    apply h.ne_zero
    rw [← Measure.measure_univ_eq_zero]
    have := congrArg (fun ν : Measure (Mt k r) => ν Set.univ) h'
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply] at this
    exact (mul_eq_zero.1 this).resolve_left h0

/- English proof (translation)
Use `Continuous.measurable (continuous_pi fun p => ?_)` and prove the remaining obligations. Unfold `rootCoords flagMat`. Apply the tactic sequence `split_ifs <;> first | exact continuous_const | fun_prop`.
-/
theorem meas_rootCoords {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (γ : Point ℂ (r + 1)) :
    Measurable (rootCoords k r z γ) := by
  refine Continuous.measurable (continuous_pi fun p => ?_)
  unfold rootCoords flagMat
  split_ifs <;> first | exact continuous_const | fun_prop

section root
variable {k0 r : ℕ} (L : LocBessel (k0 + 1) r) {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp']
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] (Ds : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r Wp' Wq')
  (hz : Ds.z = L.z) (γ : Point ℂ (r + 1)) {g : Formalism.FourierDecayAlt.B.Mat (k0 + 1) r} (hg : g ∈ Formalism.FourierDecayAlt.B.GV (k0 + 1) r)
  (hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ))
include hz hg hZ

/- English proof (translation)
Establish `hG` using `good_of Ds hg (dPt_ne γ) hZ`. Establish `hs` using `(Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg (dPt_ne γ) hG (Tinv γ y)).2`. Use function extensionality and compare the values at `p`. Establish `hp` using `p.2`. Simplify using `only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp`.

Establish `ha : p.1.1.val < r`. Establish `h1` using `p.1.2.isLt`. Establish `h2` using `Fin.lt_def.1 hp.1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [rootCoords, Equiv.apply_symm_apply]`.

Rewrite using `[flag_eq_uMap _ _ _ _ _ _ ha, ← hz, hs, Matrix.conjTranspose_apply]`. Establish `hc` using `Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord (wPt γ) (Tinv γ y) (eRoot γ p)`. Simplify using `only [eRoot, Equiv.coe_fn_mk] at hc`. Rewrite using `[hc]`. Simplify using `[Tinv, eRoot]`.
-/
theorem rootCoords_psi (y : (rootPat γ) → ℂ) :
    rootCoords (k0 + 1) r L.z γ (Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) = y := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hs := (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg (dPt_ne γ) hG (Tinv γ y)).2
  funext p
  have hp := p.2
  simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have ha : p.1.1.val < r := by
    have h1 := p.1.2.isLt
    have h2 := Fin.lt_def.1 hp.1
    omega
  simp only [rootCoords, Equiv.apply_symm_apply]
  rw [flag_eq_uMap _ _ _ _ _ _ ha, ← hz, hs, Matrix.conjTranspose_apply]
  have hc := Formalism.FourierDecayAlt.P.Dx2.Rad.low_coord (wPt γ) (Tinv γ y) (eRoot γ p)
  simp only [eRoot, Equiv.coe_fn_mk] at hc
  rw [hc]
  simp [Tinv, eRoot]

/- English proof (translation)
Establish `hG` using `good_of Ds hg (dPt_ne γ) hZ`. Establish `hu` using `Formalism.FourierDecayAlt.P.Dx2.Rad.u_eq_low Ds hg (dPt_ne γ) hG (ρ := Matrix.of x) hx`. Establish `hphi : Formalism.FourierDecayAlt.P.Dx2.Rad.phi0 Ds (wPt γ) (Matrix.of.symm (Matrix.of x)) = Tinv γ (rootCoords (k0 + 1) r L.z γ x)`. Use function extensionality and compare the values at `q`. Establish `hb : q.1.2.val < r`.

Establish `h1` using `q.1.1.isLt`. Establish `h2` using `Fin.lt_def.1 q.2.1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.Rad.phi0, Tinv, rootCoords, Equiv.apply_symm_apply, eRoot, Equiv.coe_fn_symm_mk]`. Rewrite using `[flag_eq_uMap _ _ _ _ _ _ hb, hz]`.

Establish `hρ` using `Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_unique Ds hg (dPt_ne γ) hG (Tinv γ (rootCoords (k0 + 1) r L.z γ x)) hx (by rw [← hphi, ← hu, Matrix.conjTranspose_conjTranspose])`. Rewrite using `[← hρ]`. Both sides reduce to the same expression.
-/
theorem psi_rootCoords (x : Mt (k0 + 1) r) (hx : Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g) :
    Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r L.z γ x))) = x := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hu := Formalism.FourierDecayAlt.P.Dx2.Rad.u_eq_low Ds hg (dPt_ne γ) hG (ρ := Matrix.of x) hx
  have hphi : Formalism.FourierDecayAlt.P.Dx2.Rad.phi0 Ds (wPt γ) (Matrix.of.symm (Matrix.of x)) =
      Tinv γ (rootCoords (k0 + 1) r L.z γ x) := by
    funext q
    have hb : q.1.2.val < r := by
      have h1 := q.1.1.isLt
      have h2 := Fin.lt_def.1 q.2.1
      omega
    simp only [Formalism.FourierDecayAlt.P.Dx2.Rad.phi0, Tinv, rootCoords, Equiv.apply_symm_apply, eRoot, Equiv.coe_fn_symm_mk]
    rw [flag_eq_uMap _ _ _ _ _ _ hb, hz]
  have hρ := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_unique Ds hg (dPt_ne γ) hG (Tinv γ (rootCoords (k0 + 1) r L.z γ x)) hx
    (by rw [← hphi, ← hu, Matrix.conjTranspose_conjTranspose])
  rw [← hρ]
  rfl

/- English proof (translation)
Establish `hG` using `good_of Ds hg (dPt_ne γ) hZ`. Establish `hm` using `Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG`. Use `show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)).map _ = _`. Rewrite using `[Measure.map_map (meas_rootCoords _ γ) hm]`. Establish `e : (rootCoords (k0 + 1) r L.z γ ∘ fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) = Tmap γ`.

Use function extensionality and compare the values at `x`. Use `rootCoords_psi L Ds hz γ hg hZ (Tmap γ x)` as an intermediate fact. Rewrite `this` using `[Tinv_Tmap]`. Conclude with `this`. Rewrite using `[e]`.

Conclude with `(Tmap_mp γ).map_eq`.
-/
theorem muR_map_root :
    (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)).map (rootCoords (k0 + 1) r L.z γ) = volume := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG
  show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)).map _ = _
  rw [Measure.map_map (meas_rootCoords _ γ) hm]
  have e : (rootCoords (k0 + 1) r L.z γ ∘ fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) = Tmap γ := by
    funext x
    have := rootCoords_psi L Ds hz γ hg hZ (Tmap γ x)
    rw [Tinv_Tmap] at this
    exact this
  rw [e]
  exact (Tmap_mp γ).map_eq

/- English proof (translation)
Establish `hG` using `good_of Ds hg (dPt_ne γ) hZ`. Establish `hm` using `Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG`. Establish `hcl : IsClosed {x : Mt (k0 + 1) r | Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g}` using `(Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (Formalism.FourierDecayAlt.P.Dx2.Rad.isUnit_G hg)).closed`. Use `show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) _ = 0`. Rewrite using `[show {x : Mt (k0 + 1) r | Matrix.of x ∉ RStab (k0 + 1) r g} = {x | Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g}ᶜ from rfl, Measure.map_apply hm hcl.measurableSet.compl]`.

Use `measure_empty (μ := (volume : Measure (Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ)))` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Equiv.apply_symm_apply, Set.mem_empty_iff_false, iff_false, not_not]`. Conclude with `(Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg (dPt_ne γ) hG x).1`.
-/
theorem muR_conc : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0 := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG
  have hcl : IsClosed {x : Mt (k0 + 1) r | Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g} :=
    (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR (Formalism.FourierDecayAlt.P.Dx2.Rad.isUnit_G hg)).closed
  show (volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)) _ = 0
  rw [show {x : Mt (k0 + 1) r | Matrix.of x ∉ RStab (k0 + 1) r g} = {x | Matrix.of x ∈ Formalism.FourierDecayAlt.C6.Rset g}ᶜ from rfl,
    Measure.map_apply hm hcl.measurableSet.compl]
  convert measure_empty (μ := (volume : Measure (Formalism.FourierDecayAlt.C2.Lstidx (wPt γ) → ℂ)))
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq, Equiv.apply_symm_apply, Set.mem_empty_iff_false,
    iff_false, not_not]
  exact (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_spec Ds hg (dPt_ne γ) hG x).1

/- English proof (translation)
Establish `hG` using `good_of Ds hg (dPt_ne γ) hZ`. Establish `hm` using `Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG`. Establish `hψ : Measurable fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))` using `hm.comp (Tinv_mp γ).measurable`. Establish `hae : ∀ᵐ x ∂μ, Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r L.z γ x))) = x`. Establish `h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ RStab (k0 + 1) r g`.

Rewrite using `[ae_iff]`. Simplify using `using hμ.1`. Use `filter_upwards [h1] with x hx using psi_rootCoords L Ds hz γ hg hZ x hx`. Establish `hcst : (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card = Real.pi⁻¹ ^ (rootPat γ).card`. Rewrite using `[hc, ucStd]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hμ.2, hcst, Measure.map_smul]`. Use `congr 1`.

Use `show _ = volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)`. Rewrite using `[← (Tinv_mp γ).map_eq, Measure.map_map hm (Tinv_mp γ).measurable]`. Both sides reduce to the same expression.
-/
theorem rootMeas_unique (hc : L.c = cStd) (μ : Measure (Mt (k0 + 1) r)) (hμ : IsRootMeas L γ g μ) :
    μ = ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) := by
  have hG := good_of Ds hg (dPt_ne γ) hZ
  have hm := Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF_meas Ds hg (dPt_ne γ) hG
  have hψ : Measurable fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y)) :=
    hm.comp (Tinv_mp γ).measurable
  have hae : ∀ᵐ x ∂μ, Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ (rootCoords (k0 + 1) r L.z γ x))) = x := by
    have h1 : ∀ᵐ x ∂μ, Matrix.of x ∈ RStab (k0 + 1) r g := by
      rw [ae_iff]
      simpa using hμ.1
    filter_upwards [h1] with x hx using psi_rootCoords L Ds hz γ hg hZ x hx
  have hcst : (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card = Real.pi⁻¹ ^ (rootPat γ).card := by
    rw [hc, ucStd]
    congr 1
    field_simp
  calc μ = μ.map id := Measure.map_id.symm
    _ = μ.map ((fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) ∘ rootCoords (k0 + 1) r L.z γ) :=
        Measure.map_congr (hae.mono fun x hx => hx.symm)
    _ = (μ.map (rootCoords (k0 + 1) r L.z γ)).map (fun y => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) (Tinv γ y))) :=
        (Measure.map_map hψ (meas_rootCoords _ γ)).symm
    _ = ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) := by
        rw [hμ.2, hcst, Measure.map_smul]
        congr 1
        show _ = volume.map fun x => Matrix.of.symm (Formalism.FourierDecayAlt.P.Dx2.Rad.rhoF Ds g (wPt γ) x)
        rw [← (Tinv_mp γ).map_eq, Measure.map_map hm (Tinv_mp γ).measurable]
        rfl

end root

/- English proof (translation)
Introduce `k0 r L Ds γ g hp hc hz hz' hg hZ'`. Establish `hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ)`. Rewrite using `[hZ', ptMatN_mono]`. Use `show IsRootMeas L γ g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • Formalism.FourierDecayAlt.D.muR Ds g (wPt γ))`. Establish `hcst : (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card = Real.pi⁻¹ ^ (rootPat γ).card`.

Rewrite using `[hc, ucStd]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, muR_conc L Ds hz γ hg hZ, smul_zero]`.

Rewrite using `[Measure.map_smul, muR_map_root L Ds hz γ hg hZ, hcst]`.
-/
theorem root_measure_of_mu_R : RootMeasOfMuR := by
  intro k0 r L Ds γ g hp hc hz hz' hg hZ'
  have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by
    rw [hZ', ptMatN_mono]
  show IsRootMeas L γ g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • Formalism.FourierDecayAlt.D.muR Ds g (wPt γ))
  have hcst : (‖L.c‖ / (2 * Real.pi)) ^ (rootPat γ).card = Real.pi⁻¹ ^ (rootPat γ).card := by
    rw [hc, ucStd]
    congr 1
    field_simp
  refine ⟨?_, ?_⟩
  · rw [Measure.smul_apply, muR_conc L Ds hz γ hg hZ, smul_zero]
  · rw [Measure.map_smul, muR_map_root L Ds hz γ hg hZ, hcst]

/- English proof (translation)
Establish `: SigmaFinite L.μW` using `L.hμW.1.1`. Establish `: SigmaFinite L.μW'` using `L.hμW'.1.1`. Establish `hNH` using `Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1`. Establish `: SigmaFinite L.μN` using `hNH.1`. Establish `n1 : L.μW {x | Matrix.of x ∉ UWset (k0 + 1) r L.z} = 0` using `L.hμW.1.2.2.1`.

Establish `n2 : L.μN {x | Matrix.of x ∉ Nset (k0 + 1) r} = 0` using `hNH.2.2.1`. Establish `n3 : L.μW' {x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} = 0` using `L.hμW'.1.2.2.1`. Rewrite using `[ae_iff]`. Establish `hsub : {p : PairSp (k0 + 1) r | ¬ InPair L p} ⊆ ((({x | Matrix.of x ∉ UWset (k0 + 1) r L.z} ×ˢ Set.univ) ×ˢ Set.univ) ∪ ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}) ×ˢ Set.univ)) ∪ ((Set.univ ×ˢ ({x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} ×ˢ Set.univ)) ∪ (Set.univ ×ˢ (Set.un …`. Introduce `p hp`.

Simplify using `only [Set.mem_setOf_eq, InPair, not_and_or] at hp`. Apply the tactic sequence `rcases hp with h | h | h | h <;> simp [h]`. Use `measure_mono_null hsub ?_` and prove the remaining obligations. Simplify using `only [pairMeas]`. Apply the tactic sequence `refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>`.

Apply the tactic sequence `rw [Measure.prod_prod, Measure.prod_prod] <;> simp [n1, n2, n3]`.
-/
theorem pair_inPair {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤) :
    ∀ᵐ p ∂(pairMeas L), InPair L p := by
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hNH := Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1
  have : SigmaFinite L.μN := hNH.1
  have n1 : L.μW {x | Matrix.of x ∉ UWset (k0 + 1) r L.z} = 0 := L.hμW.1.2.2.1
  have n2 : L.μN {x | Matrix.of x ∉ Nset (k0 + 1) r} = 0 := hNH.2.2.1
  have n3 : L.μW' {x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} = 0 := L.hμW'.1.2.2.1
  rw [ae_iff]
  have hsub : {p : PairSp (k0 + 1) r | ¬ InPair L p} ⊆
      ((({x | Matrix.of x ∉ UWset (k0 + 1) r L.z} ×ˢ Set.univ) ×ˢ Set.univ) ∪
        ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}) ×ˢ Set.univ)) ∪
      ((Set.univ ×ˢ ({x | Matrix.of x ∉ UWset (k0 + 1) r L.z'} ×ˢ Set.univ)) ∪
        (Set.univ ×ˢ (Set.univ ×ˢ {x | Matrix.of x ∉ Nset (k0 + 1) r}))) := by
    intro p hp
    simp only [Set.mem_setOf_eq, InPair, not_and_or] at hp
    rcases hp with h | h | h | h <;> simp [h]
  refine measure_mono_null hsub ?_
  simp only [pairMeas]
  refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>
    rw [Measure.prod_prod, Measure.prod_prod] <;> simp [n1, n2, n3]

/- English proof (translation)
Establish `: SigmaFinite L.μW` using `L.hμW.1.1`. Establish `: SigmaFinite L.μW'` using `L.hμW'.1.1`. Establish `hNH` using `Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1`. Establish `: SigmaFinite L.μN` using `hNH.1`. Establish `hl : ∀ b ∈ Nset (k0 + 1) r, MeasurePreserving (lmulM (k` using `k0 + 1) (r := r) b) L.μN L.μN := fun b hb => ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.contL b |>.measurable, hNH.2.2.2 b hb⟩`.

Establish `e : stabAct g a = Prod.map (Prod.map id (lmulM (k` using `k0 + 1) (r := r) a)) (Prod.map id (lmulM (k := k0 + 1) (r := r) (g⁻¹ * a * g))) := by`. Use function extensionality and compare the values at `p`. Both sides reduce to the same expression. Rewrite using `[e]`. Unfold `pairMeas`.

Conclude with `((MeasurePreserving.id _).prod (hl a ha.1)).prod ((MeasurePreserving.id _).prod (hl _ ha.2))`.
-/
theorem mp_stab {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (hκ0 : L.κN ≠ 0) (hκ1 : L.κN ≠ ⊤)
    {g a : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ} (ha : a ∈ RStab (k0 + 1) r g) :
    MeasurePreserving (stabAct g a) (pairMeas L) (pairMeas L) := by
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have hNH := Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1
  have : SigmaFinite L.μN := hNH.1
  have hl : ∀ b ∈ Nset (k0 + 1) r, MeasurePreserving (lmulM (k := k0 + 1) (r := r) b) L.μN L.μN := fun b hb =>
    ⟨Formalism.FourierDecayAlt.P.Dx2.OrbJ.contL b |>.measurable, hNH.2.2.2 b hb⟩
  have e : stabAct g a =
      Prod.map (Prod.map id (lmulM (k := k0 + 1) (r := r) a)) (Prod.map id (lmulM (k := k0 + 1) (r := r) (g⁻¹ * a * g))) := by
    funext p
    rfl
  rw [e]
  unfold pairMeas
  exact ((MeasurePreserving.id _).prod (hl a ha.1)).prod ((MeasurePreserving.id _).prod (hl _ ha.2))

/- English proof (translation)
Take `⟨p1, p2, p3⟩` from `Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ`. Take `⟨q1, q2, q3⟩` from `Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'`. Take `⟨Ds, hz, hz', -⟩` from `Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists (k0 + 1) r L.Wp L.Wq L.z L.z' L.π L.π' (by omega) L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 p1 q1 p2 q2 p3 q3`. Establish `hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ)`. Rewrite using `[hz, hz', hrep.2, ← ptMatN_swap, ptMatN_mono]`.

Establish `hG` using `good_of Ds hrep.1 (dPt_ne γ) hZ`. Rewrite using `[rootMeas_unique L Ds hz γ hrep.1 hZ hc μR hroot]`. Use `⟨isHaarOn_smul (Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Ds hrep.1 (dPt_ne γ) hG) (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top, fun M hM => ?_⟩` and prove the remaining obligations. Conclude with `(Formalism.FourierDecayAlt.P.Dx3.intR Ds hrep.1 (dPt_ne γ) hG hM).smul_measure ENNReal.ofReal_ne_top`.
-/
theorem rootHaar_gen {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (γ : Point ℂ (r + 1))
    (g : Matrix (Fin (2 * r + (k0 + 1) + 1)) (Fin (2 * r + (k0 + 1) + 1)) ℂ) (μR : Measure (Mt (k0 + 1) r))
    (hc : L.c = cStd) (hrep : IsPtRep L γ g) (hroot : IsRootMeas L γ g μR) :
    Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset g) μR ∧
      ∀ M : ℝ, 2 * ((r : ℝ) + 1) ^ 2 < M → Integrable (fun x : Mt (k0 + 1) r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-M)) μR := by
  obtain ⟨p1, p2, p3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z L.u L.Wp L.π L.hz.1 L.hz.2 L.hπ
  obtain ⟨q1, q2, q3⟩ := Formalism.MainNotions.BridgeLemma₃.lbRepOfHC_proved (k0 + 1) r L.z' L.u' L.Wq L.π' L.hz'.1 L.hz'.2 L.hπ'
  obtain ⟨Ds, hz, hz', -⟩ := Formalism.FourierDecayAlt.P.setting_with_prescribed_data_exists (k0 + 1) r L.Wp L.Wq L.z L.z' L.π L.π' (by omega)
    L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 p1 q1 p2 q2 p3 q3
  have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by
    rw [hz, hz', hrep.2, ← ptMatN_swap, ptMatN_mono]
  have hG := good_of Ds hrep.1 (dPt_ne γ) hZ
  rw [rootMeas_unique L Ds hz γ hrep.1 hZ hc μR hroot]
  refine ⟨isHaarOn_smul (Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Ds hrep.1 (dPt_ne γ) hG)
    (ENNReal.ofReal_pos.2 (by positivity)).ne' ENNReal.ofReal_ne_top, fun M hM => ?_⟩
  exact (Formalism.FourierDecayAlt.P.Dx3.intR Ds hrep.1 (dPt_ne γ) hG hM).smul_measure ENNReal.ofReal_ne_top

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `k0 r L γ g μR hc hκ0 hκ1 hrep hrel hroot`. Take `⟨hH, hI⟩` from `rootHaar_gen L γ g μR hc hrep hroot`. Establish `: SigmaFinite μR` using `Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hH`. Establish `: SigmaFinite L.μW` using `L.hμW.1.1`. Establish `: SigmaFinite L.μW'` using `L.hμW'.1.1`.

Establish `: SigmaFinite L.μN` using `(Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1).1`. Establish `hgu : IsUnit g.det` using `det_unit_of_UH hrep.1`. Establish `: SFinite (pairMeas L)` using `by unfold pairMeas; infer_instance`. Use `set M : ℝ := 2 * ((r : ℝ) + 1) ^ 2 + 1 with hMdef`. Establish `hM : 2 * ((r : ℝ) + 1) ^ 2 < M` using `by rw [hMdef]; linarith`.

Establish `hM0 : (0 : ℝ) ≤ M` using `by rw [hMdef]; positivity`. Use `set θ := Formalism.FourierDecayAlt.P.Dx3.cut μR M with hθdef`. Establish `hθm : Measurable θ` using `Formalism.FourierDecayAlt.P.Dx3.cut_meas M`. Establish `hθ0 : ∀ p, 0 ≤ θ p` using `Formalism.FourierDecayAlt.P.Dx3.cut_nonneg μR M`. Establish `hθ1 : ∀ p : PairSp (k0 + 1) r, InPair L p → ∫ x, θ (stabAct g (Matrix.of x) p) ∂μR = 1` using `fun p hp => Formalism.FourierDecayAlt.P.Dx3.cut_norm hH hM0 (hI M hM) p hp.2.1`.

Use `⟨(pairMeas L).withDensity (fun p => ENNReal.ofReal (θ p)), ?_⟩` and prove the remaining obligations. Introduce `f hf`. Establish `hdens : Measurable fun p => ENNReal.ofReal (θ p)` using `ENNReal.measurable_ofReal.comp hθm`. Establish `hinner : Measurable fun x => ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR` using `Measurable.lintegral_prod_right' (hf.comp (meas_act g))`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hdens hinner]`.

Simplify using `only [Pi.mul_apply]`. Establish `e1 : ∀ x, ENNReal.ofReal (θ x) * ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR = ∫⁻ a, ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x) ∂μR` using `fun x => (lintegral_const_mul _ (hf.comp (meas_act' g x))).symm`. Repeatedly rewrite using `[e1]`. Establish `hm2 : Measurable (Function.uncurry fun (x : PairSp (k0 + 1) r) (a : Mt (k0 + 1) r) => ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x))` using `(hdens.comp measurable_fst).mul (hf.comp (meas_act g))`. Rewrite using `[lintegral_lintegral_swap hm2.aemeasurable]`.

Establish `hinv : μR.map Formalism.FourierDecayAlt.B2.invM = μR` using `Formalism.FourierDecayAlt.P.haar_measure_inversion (k0 + 1) r _ μR (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR hgu) hH`. Establish `haem : AEMeasurable Formalism.FourierDecayAlt.B2.invM μR`. Assume the negation of the conclusion as `h`. Establish `h0` using `Measure.map_of_not_aemeasurable h`. Rewrite `h0` using `[hinv]`.

Conclude with `hH.ne_zero h0`. Use `set G : Mt (k0 + 1) r → PairSp (k0 + 1) r → ENNReal := fun a y => ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) * f y with hGdef`. Establish `e2 : ∀ᵐ a ∂μR, ∫⁻ x, ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x) ∂(pairMeas L) = ∫⁻ y, G a y ∂(pairMeas L)` using `by filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hH] with a ha`. Establish `hmp` using `mp_stab L hκ0 hκ1 (g := g) (a := Matrix.of a) ha`. Establish `hau : IsUnit (Matrix.of a : Matrix _ _ ℂ).det` using `Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N ha.1`.

Establish `hGm : Measurable (G a)` using `(ENNReal.measurable_ofReal.comp (hθm.comp ((meas_act g).comp (measurable_id.prodMk measurable_const)))).mul hf`. Rewrite using `[← hmp.lintegral_comp hGm]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Establish `hx : stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) (stabAct g (Matrix.of a) x) = x` using `Formalism.FourierDecayAlt.P.Dx2.OrbJ.act_act g hgu hau x`. Simplify using `only [hGdef, hx]`.

Rewrite using `[lintegral_congr_ae e2]`. Establish `hm3 : AEMeasurable (Function.uncurry G) (μR.prod (pairMeas L))`. Establish `h1 : AEMeasurable (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r => (Formalism.FourierDecayAlt.B2.invM q.1, q.2)) (μR.prod (pairMeas L))` using `(haem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk measurable_snd.aemeasurable`. Establish `h2 : Measurable (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r => ENNReal.ofReal (θ (stabAct g (Matrix.of q.1) q.2)) * f q.2)` using `(ENNReal.measurable_ofReal.comp (hθm.comp (cont_act g).measurable)).mul (hf.comp measurable_snd)`. Establish `e : Function.uncurry G = (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r => ENNReal.ofReal (θ (stabAct g (Matrix.of q.1) q.2)) * f q.2) ∘ (fun q => (Formalism.FourierDecayAlt.B2.invM q.1, q.2))`.

Use function extensionality and compare the values at `q`. Simplify using `only [Function.uncurry, Function.comp_apply, hGdef]`. Rewrite using `[e]`. Conclude with `h2.comp_aemeasurable h1`. Rewrite using `[lintegral_lintegral_swap hm3]`.

Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [pair_inPair L hκ0 hκ1] with y hy`. Simplify using `only [hGdef]`. Establish `ham : AEMeasurable (fun b : Mt (k0 + 1) r => ENNReal.ofReal (θ (stabAct g (Matrix.of b) y))) μR` using `(ENNReal.measurable_ofReal.comp (hθm.comp (meas_act' g y))).aemeasurable`. Rewrite using `[lintegral_mul_const'' _ (by`.

Use `(ENNReal.measurable_ofReal.comp (hθm.comp (meas_act' g y))).comp_aemeasurable haem` as an intermediate fact. Conclude with `this)]`. Establish `e3 : ∫⁻ a, ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) ∂μR = ∫⁻ b, ENNReal.ofReal (θ (stabAct g (Matrix.of b) y)) ∂μR`. Combine the equalities or inequalities in the displayed calculation. Establish `hint : Integrable (fun b : Mt (k0 + 1) r => θ (stabAct g (Matrix.of b) y)) μR`.

Assume the negation of the conclusion as `h`. Establish `h1` using `hθ1 y hy`. Rewrite `h1` using `[integral_undef h]`. Conclude with `zero_ne_one h1`. Rewrite using `[e3, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun b => hθ0 _), hθ1 y hy, ENNReal.ofReal_one, one_mul]`.
-/
theorem quotient_exists : QuotExists := by
  intro k0 r L γ g μR hc hκ0 hκ1 hrep hrel hroot
  obtain ⟨hH, hI⟩ := rootHaar_gen L γ g μR hc hrep hroot
  have : SigmaFinite μR := Formalism.FourierDecayAlt.P.Dx2.OrbJ.sigmaF hH
  have : SigmaFinite L.μW := L.hμW.1.1
  have : SigmaFinite L.μW' := L.hμW'.1.1
  have : SigmaFinite L.μN := (Formalism.MainNotions.BridgeCSB.haarLieN (k0 + 1) r L.κN hκ0 hκ1).1
  have hgu : IsUnit g.det := det_unit_of_UH hrep.1
  have : SFinite (pairMeas L) := by unfold pairMeas; infer_instance
  set M : ℝ := 2 * ((r : ℝ) + 1) ^ 2 + 1 with hMdef
  have hM : 2 * ((r : ℝ) + 1) ^ 2 < M := by rw [hMdef]; linarith
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; positivity
  set θ := Formalism.FourierDecayAlt.P.Dx3.cut μR M with hθdef
  have hθm : Measurable θ := Formalism.FourierDecayAlt.P.Dx3.cut_meas M
  have hθ0 : ∀ p, 0 ≤ θ p := Formalism.FourierDecayAlt.P.Dx3.cut_nonneg μR M
  have hθ1 : ∀ p : PairSp (k0 + 1) r, InPair L p → ∫ x, θ (stabAct g (Matrix.of x) p) ∂μR = 1 :=
    fun p hp => Formalism.FourierDecayAlt.P.Dx3.cut_norm hH hM0 (hI M hM) p hp.2.1
  refine ⟨(pairMeas L).withDensity (fun p => ENNReal.ofReal (θ p)), ?_⟩
  intro f hf
  have hdens : Measurable fun p => ENNReal.ofReal (θ p) := ENNReal.measurable_ofReal.comp hθm
  have hinner : Measurable fun x => ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR :=
    Measurable.lintegral_prod_right' (hf.comp (meas_act g))
  rw [lintegral_withDensity_eq_lintegral_mul _ hdens hinner]
  simp only [Pi.mul_apply]
  have e1 : ∀ x, ENNReal.ofReal (θ x) * ∫⁻ a, f (stabAct g (Matrix.of a) x) ∂μR =
      ∫⁻ a, ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x) ∂μR := fun x =>
    (lintegral_const_mul _ (hf.comp (meas_act' g x))).symm
  simp_rw [e1]
  have hm2 : Measurable (Function.uncurry fun (x : PairSp (k0 + 1) r) (a : Mt (k0 + 1) r) =>
      ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x)) :=
    (hdens.comp measurable_fst).mul (hf.comp (meas_act g))
  rw [lintegral_lintegral_swap hm2.aemeasurable]
  have hinv : μR.map Formalism.FourierDecayAlt.B2.invM = μR :=
    Formalism.FourierDecayAlt.P.haar_measure_inversion (k0 + 1) r _ μR (Formalism.FourierDecayAlt.P.Dx2.OrbJ.closedR hgu) hH
  have haem : AEMeasurable Formalism.FourierDecayAlt.B2.invM μR := by
    by_contra h
    have h0 := Measure.map_of_not_aemeasurable h
    rw [hinv] at h0
    exact hH.ne_zero h0
  set G : Mt (k0 + 1) r → PairSp (k0 + 1) r → ENNReal :=
    fun a y => ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) * f y with hGdef
  have e2 : ∀ᵐ a ∂μR, ∫⁻ x, ENNReal.ofReal (θ x) * f (stabAct g (Matrix.of a) x) ∂(pairMeas L) =
      ∫⁻ y, G a y ∂(pairMeas L) := by
    filter_upwards [Formalism.FourierDecayAlt.P.Dx2.OrbJ.ae_mem hH] with a ha
    have hmp := mp_stab L hκ0 hκ1 (g := g) (a := Matrix.of a) ha
    have hau : IsUnit (Matrix.of a : Matrix _ _ ℂ).det := Formalism.FourierDecayAlt.P.Dx2.OrbJ.isUnit_of_N ha.1
    have hGm : Measurable (G a) :=
      (ENNReal.measurable_ofReal.comp (hθm.comp ((meas_act g).comp (measurable_id.prodMk measurable_const)))).mul hf
    rw [← hmp.lintegral_comp hGm]
    refine lintegral_congr fun x => ?_
    have hx : stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) (stabAct g (Matrix.of a) x) = x :=
      Formalism.FourierDecayAlt.P.Dx2.OrbJ.act_act g hgu hau x
    simp only [hGdef, hx]
  rw [lintegral_congr_ae e2]
  have hm3 : AEMeasurable (Function.uncurry G) (μR.prod (pairMeas L)) := by
    have h1 : AEMeasurable (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r => (Formalism.FourierDecayAlt.B2.invM q.1, q.2))
        (μR.prod (pairMeas L)) :=
      (haem.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk measurable_snd.aemeasurable
    have h2 : Measurable (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r =>
        ENNReal.ofReal (θ (stabAct g (Matrix.of q.1) q.2)) * f q.2) :=
      (ENNReal.measurable_ofReal.comp (hθm.comp (cont_act g).measurable)).mul (hf.comp measurable_snd)
    have e : Function.uncurry G = (fun q : Mt (k0 + 1) r × PairSp (k0 + 1) r =>
        ENNReal.ofReal (θ (stabAct g (Matrix.of q.1) q.2)) * f q.2) ∘ (fun q => (Formalism.FourierDecayAlt.B2.invM q.1, q.2)) := by
      funext q
      simp only [Function.uncurry, Function.comp_apply, hGdef]
    rw [e]
    exact h2.comp_aemeasurable h1
  rw [lintegral_lintegral_swap hm3]
  refine lintegral_congr_ae ?_
  filter_upwards [pair_inPair L hκ0 hκ1] with y hy
  simp only [hGdef]
  have ham : AEMeasurable (fun b : Mt (k0 + 1) r => ENNReal.ofReal (θ (stabAct g (Matrix.of b) y))) μR :=
    (ENNReal.measurable_ofReal.comp (hθm.comp (meas_act' g y))).aemeasurable
  rw [lintegral_mul_const'' _ (by
    have := (ENNReal.measurable_ofReal.comp (hθm.comp (meas_act' g y))).comp_aemeasurable haem
    exact this)]
  have e3 : ∫⁻ a, ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) ∂μR =
      ∫⁻ b, ENNReal.ofReal (θ (stabAct g (Matrix.of b) y)) ∂μR := by
    calc ∫⁻ a, ENNReal.ofReal (θ (stabAct g (Matrix.of (Formalism.FourierDecayAlt.B2.invM a)) y)) ∂μR
        = ∫⁻ b, ENNReal.ofReal (θ (stabAct g (Matrix.of b) y)) ∂(μR.map Formalism.FourierDecayAlt.B2.invM) :=
          (lintegral_map' (by rw [hinv]; exact ham) haem).symm
      _ = _ := by rw [hinv]
  have hint : Integrable (fun b : Mt (k0 + 1) r => θ (stabAct g (Matrix.of b) y)) μR := by
    by_contra h
    have h1 := hθ1 y hy
    rw [integral_undef h] at h1
    exact zero_ne_one h1
  rw [e3, ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun b => hθ0 _), hθ1 y hy,
    ENNReal.ofReal_one, one_mul]

def OrbJNormIndep : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (p : Formalism.FourierDecayAlt.C.LPt) (hp : Formalism.FourierDecayAlt.D.IsLocPt p (r + 1))
    (g₁ g₂ : Formalism.FourierDecayAlt.B.Mat k r), g₁ ∈ Formalism.FourierDecayAlt.B.GV k r → g₂ ∈ Formalism.FourierDecayAlt.B.GV k r →
    Zhat k r D.z D.z' g₁ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) → Zhat k r D.z D.z' g₂ = Formalism.FourierDecayAlt.D.ptMatN p (r + 1) →
    0 < Formalism.FourierDecayAlt.D.ptG (Tz k r D.z * Tz k r D.z') r p →
    (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D g₁ (Formalism.FourierDecayAlt.D.muR D g₁ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) θ ∧
      Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand D g₁ F q) D.μSS) →
    (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D g₂ (Formalism.FourierDecayAlt.D.muR D g₂ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) θ ∧
      Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand D g₂ F q) D.μSS) →
    (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ D g₁ (Formalism.FourierDecayAlt.D.muR D g₁ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)
      (Formalism.FourierDecayAlt.D.orbJ D g₁ (Formalism.FourierDecayAlt.D.muR D g₁ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)).re =
    (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ D g₂ (Formalism.FourierDecayAlt.D.muR D g₂ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)
      (Formalism.FourierDecayAlt.D.orbJ D g₂ (Formalism.FourierDecayAlt.D.muR D g₂ (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm p)) F)).re

/- English proof (translation)
Introduce `k0 r L Ds F γ hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hK hdec hpos g₁ μ₁ ν₁ g₂ μ₂ ν₂ h₁ h₂`. Establish `hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1)` using `isLocPt_swap γ`. Establish `hcard_pos : (0 : ℝ) < Real.pi⁻¹ ^ (rootPat γ).card` using `by positivity`. Use `set t : ℝ := (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal with ht`. Establish `htpos : 0 < t` using `by rw [ht, ENNReal.toReal_ofReal hcard_pos.le]; exact hcard_pos`.

Establish `hl0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0`. Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `hcard_pos`. Establish `key : ∀ (g : ThB.Mx (k0 + 1) r) (μ : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)), (IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μ ∧ IsOrbQuot L g μ ν) → Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) ∧ (∃ θ, Formal …`. Introduce `g μ ν ⟨hrep, hrel, hroot, hq⟩`.

Establish `hZ' : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1)`. Rewrite using `[hz, hz', hrep.2, ptMatN_swap]`. Establish `hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ)` using `by rw [hZ', ptMatN_mono]`. Establish `hμ` using `rootMeas_unique L Ds hz γ hrep.1 hZ hc μ hroot`. Rewrite `hq`, `hroot` using `[hμ]`.

Establish `hq'` using `isOrbQuot_rescale L _ ENNReal.ofReal_ne_top hq`. Establish `hconc : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0` using `muR_conc L Ds hz γ hrep.1 hZ`. Establish `hne : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) ≠ 0`. Introduce `h0`. Apply `muR_ne_zero L hc γ g _ hroot` to reduce the goal to its premises.

Rewrite using `[h0, smul_zero]`. Establish `: SFinite (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ))`. Unfold `Formalism.FourierDecayAlt.D.muR`. Use `infer_instance`. Establish `hcut` using `hCut k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hrep.1 hZ'`.

Establish `hJ` using `orbJ_eq L Ds hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hrep.1 hrel hconc hne hq' F hcut`. Use `⟨hZ', hcut, ?_⟩` and prove the remaining obligations. Establish `hsm : OrbInt L F g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • ν) = t • OrbInt L F g ν`. Unfold `OrbInt`. Rewrite using `[integral_smul_measure]`.

Use `show (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) F) (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) F)).re = _`. Rewrite using `[hJ, hsm, ← hsInner_eq, ← hsNormSq, hsNormSq_smul]`. Take `⟨hZ1, hc1, e1⟩` from `key g₁ μ₁ ν₁ h₁`. Take `⟨hZ2, hc2, e2⟩` from `key g₂ μ₂ ν₂ h₂`. Establish `hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz (k0 + 1) r Ds.z * Tz (k0 + 1) r Ds.z') r (γ.1.map Prod.swap)`.

Rewrite using `[ptG_eq_GPoint, hz, hz']`. Conclude with `hpos`. Establish `hEq` using `hON (k0 + 1) r L.Wp L.Wq Ds F (γ.1.map Prod.swap) hp g₁ g₂ h₁.1.1 h₂.1.1 hZ1 hZ2 hG hc1 hc2`. Rewrite `hEq` using `[e1, e2]`. Establish `ht2 : t ^ 2 ≠ 0` using `by positivity`.

Conclude with `mul_left_cancel₀ ht2 hEq`.
-/
theorem repIndep_of (hCut : CutKFin) (hON : OrbJNormIndep) : RepIndep := by
  intro k0 r L Ds F γ hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hK hdec hpos g₁ μ₁ ν₁ g₂ μ₂ ν₂ h₁ h₂
  have hp : Formalism.FourierDecayAlt.D.IsLocPt (γ.1.map Prod.swap) (r + 1) := isLocPt_swap γ
  have hcard_pos : (0 : ℝ) < Real.pi⁻¹ ^ (rootPat γ).card := by positivity
  set t : ℝ := (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card)).toReal with ht
  have htpos : 0 < t := by rw [ht, ENNReal.toReal_ofReal hcard_pos.le]; exact hcard_pos
  have hl0 : ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]
    exact hcard_pos
  have key : ∀ (g : ThB.Mx (k0 + 1) r) (μ : Measure (Mt (k0 + 1) r)) (ν : Measure (PairSp (k0 + 1) r)),
      (IsPtRep L γ g ∧ IsRelStab L g ∧ IsRootMeas L γ g μ ∧ IsOrbQuot L g μ ν) →
      Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) ∧
      (∃ θ, Formalism.FourierDecayAlt.D.IsNormCut Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) θ ∧
        Integrable (fun q => θ q • Formalism.FourierDecayAlt.D.orbIntegrand Ds g F q) Ds.μSS) ∧
      (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) F)
        (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (hp.2 ▸ Formalism.FourierDecayAlt.D.ptPerm (γ.1.map Prod.swap))) F)).re =
        t ^ 2 * hsNormSq (OrbInt L F g ν) := by
    intro g μ ν ⟨hrep, hrel, hroot, hq⟩
    have hZ' : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.D.ptMatN (γ.1.map Prod.swap) (r + 1) := by
      rw [hz, hz', hrep.2, ptMatN_swap]
    have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by rw [hZ', ptMatN_mono]
    have hμ := rootMeas_unique L Ds hz γ hrep.1 hZ hc μ hroot
    rw [hμ] at hq hroot
    have hq' := isOrbQuot_rescale L _ ENNReal.ofReal_ne_top hq
    have hconc : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) {x | Matrix.of x ∉ RStab (k0 + 1) r g} = 0 := muR_conc L Ds hz γ hrep.1 hZ
    have hne : Formalism.FourierDecayAlt.D.muR Ds g (wPt γ) ≠ 0 := by
      intro h0
      apply muR_ne_zero L hc γ g _ hroot
      rw [h0, smul_zero]
    have : SFinite (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) := by
      unfold Formalism.FourierDecayAlt.D.muR
      infer_instance
    have hcut := hCut k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hrep.1 hZ'
    have hJ := orbJ_eq L Ds hc hκ0 hκ1 hz hz' hπ hπ' hW hN hW' hrep.1 hrel hconc hne hq' F hcut
    refine ⟨hZ', hcut, ?_⟩
    have hsm : OrbInt L F g (ENNReal.ofReal (Real.pi⁻¹ ^ (rootPat γ).card) • ν) = t • OrbInt L F g ν := by
      unfold OrbInt
      rw [integral_smul_measure]
    show (Formalism.FourierDecayAlt.B.hsInner (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) F)
      (Formalism.FourierDecayAlt.D.orbJ Ds g (Formalism.FourierDecayAlt.D.muR Ds g (wPt γ)) F)).re = _
    rw [hJ, hsm, ← hsInner_eq, ← hsNormSq, hsNormSq_smul]
  obtain ⟨hZ1, hc1, e1⟩ := key g₁ μ₁ ν₁ h₁
  obtain ⟨hZ2, hc2, e2⟩ := key g₂ μ₂ ν₂ h₂
  have hG : 0 < Formalism.FourierDecayAlt.D.ptG (Tz (k0 + 1) r Ds.z * Tz (k0 + 1) r Ds.z') r (γ.1.map Prod.swap) := by
    rw [ptG_eq_GPoint, hz, hz']
    exact hpos
  have hEq := hON (k0 + 1) r L.Wp L.Wq Ds F (γ.1.map Prod.swap) hp g₁ g₂ h₁.1.1 h₂.1.1 hZ1 hZ2 hG hc1 hc2
  rw [e1, e2] at hEq
  have ht2 : t ^ 2 ≠ 0 := by positivity
  exact mul_left_cancel₀ ht2 hEq

section HSinv
variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/- English proof (translation)
Unfold `hsNormSq hsInner`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[inner_self_eq_norm_sq_to_K]`. Use `norm_cast`.
-/
theorem hsNormSq_eq_sum (A : V →L[ℂ] W) : hsNormSq A = ∑ i, ‖A (stdOrthonormalBasis ℂ V i)‖ ^ 2 := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/- English proof (translation)
Rewrite using `[hsNormSq_eq_sum, hsNormSq_eq_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, hU]`.
-/
theorem hsNormSq_isom_comp (U : W →L[ℂ] W) (hU : ∀ x, ‖U x‖ = ‖x‖) (A : V →L[ℂ] W) :
    hsNormSq (U.comp A) = hsNormSq A := by
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.comp_apply, hU]

/- English proof (translation)
The claim follows from `FiniteDimensional.complete ℂ V haveI := FiniteDimensional.complete ℂ W ∑ i, ‖A (b i)‖ ^ 2 = ∑ j, ‖(ContinuousLinearMap.adjoint A) (c j)‖ ^ 2 := by have := FiniteDimensional.complete ℂ V have := FiniteDimensional.complete ℂ W calc ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ∑ j, ‖⟪c j, A (b i)⟫_ℂ‖ …`.
-/
theorem sum_norm_sq_basis [FiniteDimensional ℂ W] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ V) (c : OrthonormalBasis κ ℂ W) (A : V →L[ℂ] W) :
    haveI := FiniteDimensional.complete ℂ V
    haveI := FiniteDimensional.complete ℂ W
    ∑ i, ‖A (b i)‖ ^ 2 = ∑ j, ‖(ContinuousLinearMap.adjoint A) (c j)‖ ^ 2 := by
  have := FiniteDimensional.complete ℂ V
  have := FiniteDimensional.complete ℂ W
  calc ∑ i, ‖A (b i)‖ ^ 2 = ∑ i, ∑ j, ‖⟪c j, A (b i)⟫_ℂ‖ ^ 2 := by
        simp_rw [c.sum_sq_norm_inner_right]
    _ = ∑ j, ∑ i, ‖⟪c j, A (b i)⟫_ℂ‖ ^ 2 := Finset.sum_comm
    _ = ∑ j, ∑ i, ‖⟪(ContinuousLinearMap.adjoint A) (c j), b i⟫_ℂ‖ ^ 2 := by
        simp_rw [ContinuousLinearMap.adjoint_inner_left]
    _ = _ := by simp_rw [b.sum_sq_norm_inner_left]

/- English proof (translation)
Set `li : V →ₗᵢ[ℂ] V` to `⟨U.toLinearMap, hU⟩`. Set `e : V ≃ₗᵢ[ℂ] V` to `li.toLinearIsometryEquiv rfl`. Establish `he : ∀ x, e x = U x` using `fun x => rfl`. Rewrite using `[hsNormSq_eq_sum, hsNormSq_eq_sum]`. Establish `h1` using `sum_norm_sq_basis ((stdOrthonormalBasis ℂ V).map e) (stdOrthonormalBasis ℂ W) A`.

Establish `h2` using `sum_norm_sq_basis (stdOrthonormalBasis ℂ V) (stdOrthonormalBasis ℂ W) A`. Rewrite using `[h2, ← h1]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[he]`.
-/
theorem hsNormSq_comp_isom [FiniteDimensional ℂ W] (A : V →L[ℂ] W) (U : V →L[ℂ] V)
    (hU : ∀ x, ‖U x‖ = ‖x‖) : hsNormSq (A.comp U) = hsNormSq A := by
  let li : V →ₗᵢ[ℂ] V := ⟨U.toLinearMap, hU⟩
  let e : V ≃ₗᵢ[ℂ] V := li.toLinearIsometryEquiv rfl
  have he : ∀ x, e x = U x := fun x => rfl
  rw [hsNormSq_eq_sum, hsNormSq_eq_sum]
  have h1 := sum_norm_sq_basis ((stdOrthonormalBasis ℂ V).map e) (stdOrthonormalBasis ℂ W) A
  have h2 := sum_norm_sq_basis (stdOrthonormalBasis ℂ V) (stdOrthonormalBasis ℂ W) A
  rw [h2, ← h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [he]

end HSinv

/- English proof (translation)
Introduce `k r Wp Wq _ _ _ _ _ _ D F p hp g₁ g₂ hg₁ hg₂ hZ₁ hZ₂ hG _ _`. Establish `hpos₁ : 0 < Gf k r D.z D.z' g₁`. Rewrite using `[← Formalism.FourierDecayAlt.P.ptG_spec k r D.z D.z' p g₁ hp hZ₁]`. Conclude with `hG`. Take `⟨s, hs, s', hs', he⟩` from `Formalism.FourierDecayAlt.P.fibre_orbit_description k r D.z D.z' (Formalism.FourierDecayAlt.P.Dx2.Rad.std D) g₁ hg₁ g₂ hg₂ hpos₁ (by rw [hZ₁, hZ₂])`.

Take `⟨hA, hhA, nA, hnA, hfA, rfl⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z D) hs`. Take `⟨hB, hhB, nB, hnB, hfB, rfl⟩` from `Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime D) hs'`. Establish `key` using `Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt D p hp hg₁ hZ₁ hpos₁ hhA hnA hfA hhB hnB hfB F`. Substitute `he` using the available equality. Rewrite using `[← key, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply, ← hsInner_eq, ← hsInner_eq, ← hsNormSq, ← hsNormSq]`.

Unfold `Formalism.FourierDecayAlt.P.Dx2.VV.Cin`. Rewrite using `[hsNormSq_isom_comp _ (D.π_unitary hA hhA), hsNormSq_comp_isom _ _ (D.π'_unitary _ (uw_inv hhB))]`.
-/
theorem orbital_norm_independence : OrbJNormIndep := by
  intro k r Wp Wq _ _ _ _ _ _ D F p hp g₁ g₂ hg₁ hg₂ hZ₁ hZ₂ hG _ _
  have hpos₁ : 0 < Gf k r D.z D.z' g₁ := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec k r D.z D.z' p g₁ hp hZ₁]
    exact hG
  obtain ⟨s, hs, s', hs', he⟩ := Formalism.FourierDecayAlt.P.fibre_orbit_description k r D.z D.z' (Formalism.FourierDecayAlt.P.Dx2.Rad.std D) g₁ hg₁ g₂ hg₂
    hpos₁ (by rw [hZ₁, hZ₂])
  obtain ⟨hA, hhA, nA, hnA, hfA, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z D) hs
  obtain ⟨hB, hhB, nB, hnB, hfB, rfl⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.stabilizer_decomp_unitary_mul_unipotent (Formalism.FourierDecayAlt.P.Dx2.VV.std_vector_z_prime D) hs'
  have key := Formalism.FourierDecayAlt.P.Dx2.VV.orbJ_pt D p hp hg₁ hZ₁ hpos₁ hhA hnA hfA hhB hnB hfB F
  subst he
  rw [← key, Formalism.FourierDecayAlt.P.Dx2.VV.CinL_apply, ← hsInner_eq, ← hsInner_eq, ← hsNormSq, ← hsNormSq]
  unfold Formalism.FourierDecayAlt.P.Dx2.VV.Cin
  rw [hsNormSq_isom_comp _ (D.π_unitary hA hhA), hsNormSq_comp_isom _ _ (D.π'_unitary _ (uw_inv hhB))]

/- English proof (translation)
Introduce `k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hg hZ'`. Establish `hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ)` using `by rw [hZ', ptMatN_mono]`. Establish `hG : 0 < Gf (k0 + 1) r Ds.z Ds.z' g`. Rewrite using `[← Formalism.FourierDecayAlt.P.ptG_spec (k0 + 1) r Ds.z Ds.z' _ g hp hZ', ptG_eq_GPoint, hz, hz']`. Conclude with `hpos`.

Establish `hrel` using `Formalism.FourierDecayAlt.P.relevant_points_holds (k0 + 1) r L.Wp L.Wq Ds _ g hp hg hZ'`. Conclude with `Classical.choose_spec Formalism.FourierDecayAlt.P.orbital_integral_converges (k0 + 1) r L.Wp L.Wq Ds g (wPt γ) (dPt γ) (A0 (k0 + 1) r) F hg hrel (dPt_ne γ) hZ hG le_rfl hdec`.
-/
theorem K_finite_decay : CutKFin := by
  intro k0 r L Ds γ g hp F hc hz hz' hπ hπ' hW hN hW' hK hdec hpos hg hZ'
  have hZ : Zhat (k0 + 1) r Ds.z Ds.z' g = Formalism.FourierDecayAlt.C2.monoP (wPt γ) (dPt γ) := by rw [hZ', ptMatN_mono]
  have hG : 0 < Gf (k0 + 1) r Ds.z Ds.z' g := by
    rw [← Formalism.FourierDecayAlt.P.ptG_spec (k0 + 1) r Ds.z Ds.z' _ g hp hZ', ptG_eq_GPoint, hz, hz']
    exact hpos
  have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds (k0 + 1) r L.Wp L.Wq Ds _ g hp hg hZ'
  exact Classical.choose_spec Formalism.FourierDecayAlt.P.orbital_integral_converges (k0 + 1) r L.Wp L.Wq Ds g (wPt γ) (dPt γ) (A0 (k0 + 1) r) F hg
    hrel (dPt_ne γ) hZ hG le_rfl hdec

def chi0 (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1)

def chiE (Lt : Lev) (E : List ℕ) (δ : ℝ) (g : Mat Lt.k0 Lt.r) : ℝ :=
  (E.map fun l => if hl : l < Lt.r + 2 then
    chi0 (Complex.normSq (Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩) / δ) else 1).prod

open Classical in

def cellF (Lt : Lev) (E : List ℕ) {N : ℕ}
    (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)) (δ : ℝ) (F : Lt.GF) : Lt.GF := fun g =>
  if g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) ∧ g ∈ OnePlaceEstimates.minorsNe Lt E ∧ 0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g then
    ∑ n, a n g (Lt.Eword (ws n) (fun y => ((chiE Lt E δ y : ℝ) : ℂ) • F y) g)
  else 0

open scoped ContDiff in

def CellBudget : Prop :=
  ∀ (Lt : Lev) (E : List ℕ) (o : ℕ) (dP : ℝ) (N : ℕ)
    (ws : Fin N → List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)))
    (a : Fin N → Mat Lt.k0 Lt.r → (Lt.Hom →L[ℂ] Lt.Hom)),
    (∀ n, (ws n).length ≤ o) →
    (∀ n, ∃ U : Set (Mat Lt.k0 Lt.r), IsOpen U ∧
      UH (Hpk (Lt.k0 + 1) Lt.r) ∩ OnePlaceEstimates.minorsNe Lt E ∩ {g | 0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g} ⊆ U ∧
      ContDiffOn ℝ ∞ (a n) U) →
    (∀ n, ∀ w : List (Fin (2 * Lt.r + (Lt.k0 + 1) + 1) × Fin (2 * Lt.r + (Lt.k0 + 1) + 1)), ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      ∃ C : ℝ, ∀ g ∈ UH (Hpk (Lt.k0 + 1) Lt.r), ε ≤ Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g →
        (∀ l ∈ E, ∀ hl : l < Lt.r + 2, δ ≤ Complex.normSq (Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g ⟨l, hl⟩)) →
        ‖Lt.EwordV w (a n) g‖ ≤ C * (1 + Lev.matNorm g) ^ (dP + 3 * ((Lt.r : ℝ) + 1) * w.length)) →
    ∀ (A : ℝ) (F : Lt.GF), (∀ mm : ℕ, IsCC (Lt.k0 + 1) Lt.r (A - 3 * ((Lt.r : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε → SuppGe Lt ε F →
    ∀ δ : ℝ, 0 < δ → ∀ mm : ℕ,
      IsCC (Lt.k0 + 1) Lt.r (A - dP - 3 * ((Lt.r : ℝ) + 1) * ((mm : ℝ) + o)) mm (cellF Lt E ws a δ F)

def cJ : ℝ := 12

section jc12
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

end jc12

open scoped ContDiff in

def CellVanish : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0), L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ →
    IsSection (k0 + 1) r L.z L.z' μsec →
    ∀ (E : List ℕ) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L) (N : ℕ)
      (ws : Fin N → List (Fin (2 * r + (k0 + 1) + 1) × Fin (2 * r + (k0 + 1) + 1)))
      (a : Fin N → Mat k0 r → ((L.Wq →L[ℂ] L.Wp) →L[ℂ] (L.Wq →L[ℂ] L.Wp))),
      GramWordSpace.IsInvC (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) Θ → (∀ n, (ws n).length ≤ o) →
      (∀ n, ∃ U : Set (Mat k0 r), IsOpen U ∧
        UH (Hpk (k0 + 1) r) ∩ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E ∩ {g | 0 < Gf (k0 + 1) r L.z L.z' g} ⊆ U ∧
        ContDiffOn ℝ ∞ (a n) U) →
      (∀ F : GramWordSpace.GFn L, ∀ g ∈ UH (Hpk (k0 + 1) r),
        g ∈ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E → 0 < Gf (k0 + 1) r L.z L.z' g →
        GramWordSpace.CkAt (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) F g →
        Θ F g = ∑ n, a n g ((GramWordSpace.levOf L μsec).Eword (ws n) F g)) →
      GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ (A : ℝ) (F : GramWordSpace.GFn L), (∀ mm : ℕ, IsCC (k0 + 1) r (A - 3 * ((r : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        cJ * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + (r : ℝ) * ((2 * r + (k0 + 1) + 1 : ℕ) : ℝ) + 1) +
          5 * ((r : ℝ) + 1) * ((o : ℝ) + 1) ≤ A →
        ∀ δ : ℝ, 0 < δ →
        ∀ q : (Fin r → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) → Tz (k0 + 1) r L.z * Tz (k0 + 1) r L.z' < Complex.normSq q.2 →
          L.J (cellF (GramWordSpace.levOf L μsec) E ws a δ F) (bigCell (k0 + 1) r q.1 (μsec q.2)) = 0

def deltaPt {r : ℕ} (γ : Point ℂ (r + 1)) : ℝ :=
  (1 / 2) * ((OnePlaceEstimates.endsC 0 γ.1).map fun e => if h : e ≤ r + 1 then
    min 1 (Complex.normSq ((ptMat γ).submatrix (Fin.castLE h) (Fin.castLE h)).det) else 1).prod

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih`. Simplify using `only [List.prod_cons]`. Establish `hx0` using `h0 x List.mem_cons_self`.

Establish `hx1` using `h1 x List.mem_cons_self`. Establish `hl0 : 0 ≤ l.prod` using `List.prod_nonneg fun z hz => h0 z (List.mem_cons_of_mem _ hz)`. Use `ih (fun z hz => h0 z (List.mem_cons_of_mem _ hz)) (fun z hz => h1 z (List.mem_cons_of_mem _ hz))` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem prod_le_one' (l : List ℝ) (h0 : ∀ x ∈ l, 0 ≤ x) (h1 : ∀ x ∈ l, x ≤ 1) : l.prod ≤ 1 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.prod_cons]
    have hx0 := h0 x List.mem_cons_self
    have hx1 := h1 x List.mem_cons_self
    have hl0 : 0 ≤ l.prod := List.prod_nonneg fun z hz => h0 z (List.mem_cons_of_mem _ hz)
    have := ih (fun z hz => h0 z (List.mem_cons_of_mem _ hz)) (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
    nlinarith

def CellReplT : Prop :=
  ∀ (D : D7) (k0 : ℕ), k0 + 1 = D.R.k → ∀ (L : LocBessel (k0 + 1) D.R.rS) (μsec : GramWordSpace.Sec k0),
    L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → IsSection (k0 + 1) D.R.rS L.z L.z' μsec →
    ∀ (γ : Point ℂ (D.R.rS + 1)) (o : ℕ) (dP : ℝ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L),
      OnePlaceEstimates.IsCellOpAt (GramWordSpace.levOf L μsec) (OnePlaceEstimates.endsC 0 γ.1) o dP Θ → GramWordSpace.RadZeroC (GramWordSpace.levOf L μsec) o Θ →
      ∀ A : ℝ, cJ * ((D.R.rS : ℝ) + 1) ^ 2 * ((o : ℝ) + (D.R.rS : ℝ) * D.R.r + 1) +
        5 * ((D.R.rS : ℝ) + 1) * ((o : ℝ) + 1) ≤ A → ∀ F : GramWordSpace.GFn L, (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - 3 * ((D.R.rS : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        ∃ F' : GramWordSpace.GFn L,
          (∀ mm : ℕ, IsCC (k0 + 1) D.R.rS (A - dP - 3 * ((D.R.rS : ℝ) + 1) * ((mm : ℝ) + o)) mm F') ∧
          SuppGe (GramWordSpace.levOf L μsec) ε F' ∧
          (∀ q : (Fin D.R.rS → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) →
            Tz (k0 + 1) D.R.rS L.z * Tz (k0 + 1) D.R.rS L.z' < Complex.normSq q.2 →
            L.J F' (bigCell (k0 + 1) D.R.rS q.1 (μsec q.2)) = 0) ∧
          ∀ (g : Matrix (Fin (2 * D.R.rS + (k0 + 1) + 1)) (Fin (2 * D.R.rS + (k0 + 1) + 1)) ℂ)
            (μR : Measure (Mt (k0 + 1) D.R.rS)) (ν : Measure (PairSp (k0 + 1) D.R.rS)),
            0 < ThB.Gpt (Tz (k0 + 1) D.R.rS L.z) (Tz (k0 + 1) D.R.rS L.z') γ →
            IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
              OrbInt L (Θ F) g ν = OrbInt L F' g ν

section HSadj
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def hsE : (Wq →L[ℂ] Wp) ≃ₗ[ℂ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) where
  toFun A := WithLp.toLp 2 fun i => A (stdOrthonormalBasis ℂ Wq i)
  invFun v := LinearMap.toContinuousLinearMap ((stdOrthonormalBasis ℂ Wq).toBasis.constr ℂ (fun i => (WithLp.ofLp v) i))
  map_add' A B := by ext i; simp
  map_smul' c A := by ext i; simp
  left_inv A := by
    apply ContinuousLinearMap.coe_injective
    refine (stdOrthonormalBasis ℂ Wq).toBasis.ext fun i => ?_
    simp
  right_inv v := by
    ext i
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hsInner_hsE (A B : Wq →L[ℂ] Wp) : Formalism.FourierDecayAlt.B.hsInner A B = ⟪hsE B, hsE A⟫_ℂ := rfl

def adjHS (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  LinearMap.toContinuousLinearMap ((hsE.symm.toLinearMap) ∘ₗ
    (LinearMap.adjoint (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap)) ∘ₗ hsE.toLinearMap)

/- English proof (translation)
Rewrite using `[hsInner_hsE, hsInner_hsE]`. Establish `e1 : hsE (T A) = (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) (hsE A)` using `by simp`. Establish `e2 : hsE (adjHS T B) = LinearMap.adjoint (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) (hsE B)`. Simplify using `[adjHS]`. Rewrite using `[e1, e2, LinearMap.adjoint_inner_left]`.
-/
theorem adjHS_spec (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (A B : Wq →L[ℂ] Wp) :
    Formalism.FourierDecayAlt.B.hsInner (T A) B = Formalism.FourierDecayAlt.B.hsInner A (adjHS T B) := by
  rw [hsInner_hsE, hsInner_hsE]
  have e1 : hsE (T A) = (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) (hsE A) := by simp
  have e2 : hsE (adjHS T B) = LinearMap.adjoint (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) (hsE B) := by
    simp [adjHS]
  rw [e1, e2, LinearMap.adjoint_inner_left]

end HSadj

section HSadj2
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Simplify using `[adjHS, LinearMap.comp_add, LinearMap.add_comp, map_add]`.
-/
theorem adjHS_add (T₁ T₂ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjHS (T₁ + T₂) = adjHS T₁ + adjHS T₂ := by
  apply ContinuousLinearMap.coe_injective
  simp [adjHS, LinearMap.comp_add, LinearMap.add_comp, map_add]

/- English proof (translation)
Apply `ContinuousLinearMap.coe_injective` to reduce the goal to its premises. Establish `e : (hsE.toLinearMap ∘ₗ (c • T).toLinearMap ∘ₗ hsE.symm.toLinearMap : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →ₗ[ℂ] _) = c • (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap)`. Use extensionality with `v`. Simplify using the standard rewrite rules. Simplify using `only [adjHS, LinearMap.coe_toContinuousLinearMap']`.

Rewrite using `[e, LinearMap.adjoint.map_smulₛₗ]`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem adjHS_smul (c : ℂ) (T : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) : adjHS (c • T) = (starRingEnd ℂ c) • adjHS T := by
  apply ContinuousLinearMap.coe_injective
  have e : (hsE.toLinearMap ∘ₗ (c • T).toLinearMap ∘ₗ hsE.symm.toLinearMap : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) →ₗ[ℂ] _) =
      c • (hsE.toLinearMap ∘ₗ T.toLinearMap ∘ₗ hsE.symm.toLinearMap) := by
    ext v
    simp
  simp only [adjHS, LinearMap.coe_toContinuousLinearMap']
  rw [e, LinearMap.adjoint.map_smulₛₗ]
  ext x
  simp

def adjHSR : ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) →ₗ[ℝ] ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) where
  toFun := adjHS
  map_add' := adjHS_add
  map_smul' c T := by
    have h1 : c • T = ((c : ℂ)) • T := (Complex.coe_smul c T).symm
    have h2 : c • adjHS T = ((c : ℂ)) • adjHS T := (Complex.coe_smul c (adjHS T)).symm
    simp only [RingHom.id_apply]
    rw [h1, h2, adjHS_smul, Complex.conj_ofReal]

end HSadj2

section cellOp
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def cellTerms (w : List (Formalism.MainNotions.BridgeLemma₃.cal_Ix k r)) (a : Formalism.FourierDecayAlt.B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) :
    List (Formalism.FourierDecayAlt.B.DTerm k r Wp Wq) :=
  (Formalism.MainNotions.BridgeLemma₃.cal_expE w).attach.map fun cv =>
    { coef := fun g => cv.1.1 • a g
      coefAdj := fun g => adjHS (cv.1.1 • a g)
      word := cv.1.2
      word_lie := fun X hX => Formalism.MainNotions.BridgeLemma₃.cal_expE_lie w cv.1 cv.2 X hX
      adj_id := by
        intro x A B
        exact adjHS_spec (cv.1.1 • a x) A B }

def cellOp {N : ℕ} (ws : Fin N → List (Formalism.MainNotions.BridgeLemma₃.cal_Ix k r))
    (a : Fin N → Formalism.FourierDecayAlt.B.Mat k r → ((Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))) : Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq :=
  (List.finRange N).flatMap fun n => cellTerms (ws n) (a n)

end cellOp

section cellOp2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end cellOp2

section cellOp3
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end cellOp3

def CkAtE (Lt : Lev) (o : ℕ) (F : Lt.GF) (g₀ : Mat Lt.k0 Lt.r) : Prop :=
  ∃ (U : Set (Mat Lt.k0 Lt.r)) (F' : Lt.GF), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ o F' U ∧
    ∀ g ∈ U, g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) → F g = F' g

/- English proof (translation)
Simplify using `only [Formalism.FourierDecayAlt.B.xiTau, Formalism.FourierDecayAlt.B.lam, psi, one_mul]`. Rewrite using `[Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem xi_eq {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (p : Formalism.FourierDecayAlt.B.SS k r) :
    Formalism.FourierDecayAlt.B.xiTau D (1, 1) p = psi k r D.z cStd (Matrix.of p.1.2) * star (psi k r D.z' cStd (Matrix.of p.2.2)) := by
  simp only [Formalism.FourierDecayAlt.B.xiTau, Formalism.FourierDecayAlt.B.lam, psi, one_mul]
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/- English proof (translation)
Rewrite using `[xi_eq, hz, hz']`. Simplify using `only [Lev.act, Formalism.FourierDecayAlt.B.rho, Formalism.FourierDecayAlt.B.sgs, hπ, hπ']`. Both sides reduce to the same expression.
-/
theorem act_eq {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0)
    (D : Formalism.FourierDecayAlt.B.RealPlaceData (k0 + 1) r L.Wp L.Wq) (hz : D.z = L.z) (hz' : D.z' = L.z') (hπ : D.π = L.π)
    (hπ' : D.π' = L.π') (p : Formalism.FourierDecayAlt.B.SS (k0 + 1) r) (J : GramWordSpace.GFn L) (g : Mat k0 r) :
    (GramWordSpace.levOf L μsec).act (Matrix.of p.1.1) (Matrix.of p.1.2) (Matrix.of p.2.1) (Matrix.of p.2.2) J g =
      Formalism.FourierDecayAlt.B.xiTau D (1, 1) p • Formalism.FourierDecayAlt.B.rho D p J g := by
  rw [xi_eq, hz, hz']
  simp only [Lev.act, Formalism.FourierDecayAlt.B.rho, Formalism.FourierDecayAlt.B.sgs, hπ, hπ']
  rfl

section zeroOp
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def zeroOp (o : ℕ) : Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq :=
  [{ coef := fun _ => 0
     coefAdj := fun _ => 0
     word := List.replicate o 0
     word_lie := fun X hX => by
       rw [List.eq_of_mem_replicate hX]
       simp [Formalism.FourierDecayAlt.B.inLie]
     adj_id := fun x A B => by simp [hsInner_hsE] }]

end zeroOp

def bigPosE (Lt : Lev) : Set (Mat Lt.k0 Lt.r) :=
  {g | g ∈ UH (Hpk (Lt.k0 + 1) Lt.r) ∧ (∀ l : Fin (Lt.r + 2), Dmin (Lt.k0 + 1) Lt.r Lt.z Lt.z' g l ≠ 0) ∧
    0 < Gf (Lt.k0 + 1) Lt.r Lt.z Lt.z' g}

open scoped ContDiff in

def CellVanishE : Prop :=
  ∀ (k0 r : ℕ) (L : LocBessel (k0 + 1) r) (μsec : GramWordSpace.Sec k0), L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ →
    IsSection (k0 + 1) r L.z L.z' μsec →
    ∀ (E : List ℕ) (o : ℕ) (Θ : GramWordSpace.GFn L → GramWordSpace.GFn L) (N : ℕ)
      (ws : Fin N → List (Fin (2 * r + (k0 + 1) + 1) × Fin (2 * r + (k0 + 1) + 1)))
      (a : Fin N → Mat k0 r → ((L.Wq →L[ℂ] L.Wp) →L[ℂ] (L.Wq →L[ℂ] L.Wp))),
      (∀ h ∈ UWset (k0 + 1) r L.z, ∀ n ∈ Nset (k0 + 1) r, ∀ h' ∈ UWset (k0 + 1) r L.z', ∀ n' ∈ Nset (k0 + 1) r,
        ∀ F : GramWordSpace.GFn L,
        (∀ g ∈ UH (Hpk (k0 + 1) r), CkAtE (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) F g) →
        ∀ g ∈ UH (Hpk (k0 + 1) r), Θ ((GramWordSpace.levOf L μsec).act h n h' n' F) g =
          (GramWordSpace.levOf L μsec).act h n h' n' (Θ F) g) →
      (∀ n, (ws n).length ≤ o) →
      (∀ n, ∃ U : Set (Mat k0 r), IsOpen U ∧
        UH (Hpk (k0 + 1) r) ∩ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E ∩ {g | 0 < Gf (k0 + 1) r L.z L.z' g} ⊆ U ∧
        ContDiffOn ℝ ∞ (a n) U) →
      (∀ F : GramWordSpace.GFn L, ∀ g ∈ UH (Hpk (k0 + 1) r),
        g ∈ OnePlaceEstimates.minorsNe (GramWordSpace.levOf L μsec) E → 0 < Gf (k0 + 1) r L.z L.z' g →
        CkAtE (GramWordSpace.levOf L μsec) (Finset.univ.sup fun n => (ws n).length) F g →
        Θ F g = ∑ n, a n g ((GramWordSpace.levOf L μsec).Eword (ws n) F g)) →
      (∀ J : GramWordSpace.GFn L, (∀ g ∈ bigPosE (GramWordSpace.levOf L μsec), CkAtE (GramWordSpace.levOf L μsec) o J g) →
        (∀ h ∈ UWset (k0 + 1) r L.z, ∀ n ∈ Nset (k0 + 1) r, ∀ h' ∈ UWset (k0 + 1) r L.z', ∀ n' ∈ Nset (k0 + 1) r,
          ∀ g ∈ bigPosE (GramWordSpace.levOf L μsec), (GramWordSpace.levOf L μsec).act h n h' n' J g = J g) →
        ∀ g ∈ bigPosE (GramWordSpace.levOf L μsec), Θ J g = 0) →
      ∀ (A : ℝ) (F : GramWordSpace.GFn L), (∀ mm : ℕ, IsCC (k0 + 1) r (A - 3 * ((r : ℝ) + 1) * mm) mm F) → ∀ ε : ℝ, 0 < ε →
        SuppGe (GramWordSpace.levOf L μsec) ε F →
        cJ * ((r : ℝ) + 1) ^ 2 * ((o : ℝ) + (r : ℝ) * ((2 * r + (k0 + 1) + 1 : ℕ) : ℝ) + 1) +
          5 * ((r : ℝ) + 1) * ((o : ℝ) + 1) ≤ A →
        ∀ δ : ℝ, 0 < δ →
        ∀ q : (Fin r → ℂ) × ℂ, (∀ i, q.1 i ≠ 0) → Tz (k0 + 1) r L.z * Tz (k0 + 1) r L.z' < Complex.normSq q.2 →
          L.J (cellF (GramWordSpace.levOf L μsec) E ws a δ F) (bigCell (k0 + 1) r q.1 (μsec q.2)) = 0

end Formalism.MainNotions.BigCellDensity
