import Formalism.SharpRestriction.CuspSpanNormBounds.ContinuousRootCoords
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockExponentKappaIdentity
import Formalism.SharpRestriction.CuspSpanNormBounds.FrameFactorGe
import Formalism.SharpRestriction.CuspSpanNormBounds.TheoremBConstants

open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.MainNotions.FrameBoundFromBesselTorus

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates

def OneBesselTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (f : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (κ₀ κ τ : ℝ),
    0 < κ₀ → 0 < κ → 0 < τ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 + ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    IsKFinCoefH L.σ f →
    ∃ (f₁ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (C : ℂ), C ≠ 0 ∧ IsKFinCoefH L.σ f₁ ∧
      (∀ (c : Fin D.R.rS → ℂ) (μ : Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ), (∀ a, c a ≠ 0) →
        μᴴ * Hb D.R.k * μ = Hb D.R.k →
        L.J (fun x => f₁ (cj D.R.k D.R.rS κ τ x)) (bigCell D.R.k D.R.rS c μ) =
          C • L.J f (bigCell D.R.k D.R.rS c μ)) ∧
      (∀ (γ : Point ℂ (D.R.rS + 1)) (g : Mx D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS))
        (ν : Measure (PairSp D.R.k D.R.rS)),
        Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g →
        IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
        OrbInt L (fun x => f₁ (cj D.R.k D.R.rS κ τ x)) g ν = C • OrbInt L f g ν)

section Dat

variable {k r : ℕ} {κ τ : ℝ}

/- English proof (translation)
Take `⟨h1, h2⟩` from `L.hz`. Unfold `inWb Tz at *`. Use `⟨fun i hi => by simp [h1 i hi], ?_⟩` and prove the remaining obligations. Unfold `herm at *`. Establish `e : star ((τ : ℂ) • L.z) ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z) = ((τ : ℂ) * τ) * (star L.z ⬝ᵥ Hpk k r *ᵥ L.z)`.

Rewrite using `[star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Establish `hp : 0 < τ * τ` using `mul_pos hτ hτ`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem hzTr (L : LocBessel k r) (hτ : 0 < τ) : inWb k r ((τ : ℂ) • L.z) ∧ 0 < Tz k r ((τ : ℂ) • L.z) := by
  obtain ⟨h1, h2⟩ := L.hz
  unfold inWb Tz at *
  refine ⟨fun i hi => by simp [h1 i hi], ?_⟩
  unfold herm at *
  have e : star ((τ : ℂ) • L.z) ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z) =
      ((τ : ℂ) * τ) * (star L.z ⬝ᵥ Hpk k r *ᵥ L.z) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hp : 0 < τ * τ := mul_pos hτ hτ
  nlinarith

/- English proof (translation)
Take `⟨h1, h2⟩` from `L.hz'`. Unfold `inWb Tz at *`. Use `⟨fun i hi => by simp [h1 i hi], ?_⟩` and prove the remaining obligations. Unfold `herm at *`. Establish `e : star ((τ : ℂ) • L.z') ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z') = ((τ : ℂ) * τ) * (star L.z' ⬝ᵥ Hpk k r *ᵥ L.z')`.

Rewrite using `[star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]`. Simplify using `only [Complex.star_def, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]`. Establish `hp : 0 < τ * τ` using `mul_pos hτ hτ`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem hzTr' (L : LocBessel k r) (hτ : 0 < τ) : inWb k r ((τ : ℂ) • L.z') ∧ 0 < Tz k r ((τ : ℂ) • L.z') := by
  obtain ⟨h1, h2⟩ := L.hz'
  unfold inWb Tz at *
  refine ⟨fun i hi => by simp [h1 i hi], ?_⟩
  unfold herm at *
  have e : star ((τ : ℂ) • L.z') ⬝ᵥ Hpk k r *ᵥ ((τ : ℂ) • L.z') =
      ((τ : ℂ) * τ) * (star L.z' ⬝ᵥ Hpk k r *ᵥ L.z') := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    ring
  rw [e, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  have hp : 0 < τ * τ := mul_pos hτ hτ
  nlinarith

abbrev trDat (L : LocBessel k r) (κ τ : ℝ) (hκ : 0 < κ) (hτ : 0 < τ) : LocBessel k r :=
  trD L κ τ (L.κN * ENNReal.ofReal (deltaN k r κ τ)) (hzTr L hτ) (hzTr' L hτ)
    (isHCTypeW_cjI hκ hτ L.hz.1 L.hπ) (isHCTypeW_cjI hκ hτ L.hz'.1 L.hπ')
    ⟨isHaarOn_map_cjT hκ hτ L.hz.1 L.hμW.1, by rw [map_cjT_univ]; exact L.hμW.2⟩
    ⟨isHaarOn_map_cjT hκ hτ L.hz'.1 L.hμW'.1, by rw [map_cjT_univ]; exact L.hμW'.2⟩

/- English proof (translation)
Unfold `alphaPt tF`. Check the signs of the components of the expression.
-/
theorem alphaPt_pos (hκ : 0 < κ) (hτ : 0 < τ) (γ : Point ℂ (r + 1)) : 0 < alphaPt κ τ γ := by
  unfold alphaPt tF
  positivity

/- English proof (translation)
Unfold `IsPtRep`. Apply `and_congr (cj_mem_UH_iff hκ hτ g)` to reduce the goal to its premises. Use `show Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) = ptMat (ptTr κ τ hκ hτ γ) ↔ Zhat k r L.z L.z' g = ptMat γ`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use extensionality with `a b`. Establish `h1 : Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) a b = ptMat (ptTr κ τ hκ hτ γ) a b`. Rewrite using `[h]`. Rewrite `h1` using `[Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ]`. Establish `hne : ((tF r κ τ a * tF r κ τ b : ℝ) : ℂ) ≠ 0`.

Establish `hp : 0 < tF r κ τ a * tF r κ τ b`. Unfold `tF`. Check the signs of the components of the expression. Conclude with `hp.ne'` after adjusting the coercions. Conclude with `mul_left_cancel₀ hne h1`.

Introduce `h`. Use extensionality with `a b`. Rewrite using `[Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ, h]`.
-/
theorem isPtRep_trDat (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (γ : Point ℂ (r + 1)) (g : Mx k r) :
    IsPtRep (trDat L κ τ hκ hτ) (ptTr κ τ hκ hτ γ) (cj k r κ τ g) ↔ IsPtRep L γ g := by
  unfold IsPtRep
  apply and_congr (cj_mem_UH_iff hκ hτ g)
  show Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) = ptMat (ptTr κ τ hκ hτ γ) ↔
    Zhat k r L.z L.z' g = ptMat γ
  constructor
  · intro h
    ext a b
    have h1 : Zhat k r ((τ : ℂ) • L.z) ((τ : ℂ) • L.z') (cj k r κ τ g) a b = ptMat (ptTr κ τ hκ hτ γ) a b := by
      rw [h]
    rw [Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ] at h1
    have hne : ((tF r κ τ a * tF r κ τ b : ℝ) : ℂ) ≠ 0 := by
      have hp : 0 < tF r κ τ a * tF r κ τ b := by
        unfold tF
        positivity
      exact_mod_cast hp.ne'
    exact mul_left_cancel₀ hne h1
  · intro h
    ext a b
    rw [Zhat_cj hκ hτ L.hz.1 L.hz'.1, ptMat_ptTr hκ hτ, h]

/- English proof (translation)
Establish `hα` using `alphaPt_pos hκ hτ γ`. Use `set α := alphaPt κ τ γ with hαdef`. Establish `hpat : rootPat (ptTr κ τ hκ hτ γ) = rootPat γ` using `rootPat_ptTr hκ hτ γ`. Establish `hrel : ∀ g, IsRelStab (trDat L κ τ hκ hτ) (cj k r κ τ g) ↔ IsRelStab L g` using `fun g => isRelStab_iff hκ hτ L (trDat L κ τ hκ hτ) L.hz.1 L.hz'.1 rfl rfl rfl g`. Establish `hroot : ∀ g μR, IsRootMeas (trDat L κ τ hκ hτ) (ptTr κ τ hκ hτ γ) (cj k r κ τ g) (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ↔ IsRootMeas L γ g μR` using `fun g μR => IsRootMeas_trD_iff hκ hτ L _ _ _ _ _ _ _ hpat g μR`.

Establish `hquot : ∀ g μR ν, IsOrbQuot (trDat L κ τ hκ hτ) (cj k r κ τ g) (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν) ↔ IsOrbQuot L g μR ν` using `fun g μR ν => IsOrbQuot_trD_iff hκ hτ L _ _ _ _ _ _ g μR ν hα`. Establish `key : ∀ g μR ν, IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν → ENNReal.ofReal (hsNormSq (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g) ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) = ENNReal.ofReal (α⁻¹ ^ 2 * ‖C‖ ^ 2) * ENNReal.ofReal (hsNormS …`. Introduce `g μR ν h1 h2 h3 h4`. Use `show ENNReal.ofReal (@hsNormSq L.Wp L.Wq _ _ _ _ _ (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g) ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) = _`. Rewrite using `[OrbInt_trD hκ hτ L _ _ _ _ _ _ _ F₁ g _ ν, hO g μR ν h1 h2 h3 h4, smul_smul, hsNormSq_smul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hα.le, ← ENNReal.ofReal_mul (by positivity)]`.

Use `congr 1`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hα, mul_pow]`. Unfold `orbSq`. Apply `le_antisymm` to reduce the goal to its premises. Use `iSup_le fun g₁ => iSup_le fun μR₁ => iSup_le fun ν₁ => iSup_le fun h => ?_` and prove the remaining obligations.

Take `⟨g, rfl⟩ : ∃ g, g₁ = cj k r κ τ g` from `⟨cjI k r κ τ g₁, (cj_cjI hκ hτ g₁).symm⟩`. Take `⟨μR, rfl⟩ : ∃ μR, μR₁ = ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR` from `⟨_, (map_cjT_cjIT_smul hκ hτ hα μR₁).symm⟩`. Take `⟨ν, rfl⟩ : ∃ ν, ν₁ = (ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν` from `⟨_, (use₉ hκ hτ hα ν₁).symm⟩`. Take `⟨h1, h2, h3, h4⟩` from `h`. Establish `h1'` using `(isPtRep_trDat hκ hτ L γ g).mp h1`.

Establish `h2'` using `(hrel g).mp h2`. Establish `h3'` using `(hroot g μR).mp h3`. Establish `h4'` using `(hquot g μR ν).mp h4`. Rewrite using `[key g μR ν h1' h2' h3' h4']`. Use `gcongr`.

Conclude with `le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le ⟨h1', h2', h3', h4'⟩ le_rfl)))`. Repeatedly rewrite using `[ENNReal.mul_iSup]`. Use `iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_` and prove the remaining obligations. Take `⟨h1, h2, h3, h4⟩` from `h`. Rewrite using `[← key g μR ν h1 h2 h3 h4]`.

Conclude with `le_iSup_of_le (cj k r κ τ g) (le_iSup_of_le (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) (le_iSup_of_le ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν) (le_iSup_of_le ⟨(isPtRep_trDat hκ hτ L γ g).mpr h1, (hrel g).mpr h2, (hroot g μR).mpr h3, (hquot g μR ν).mpr h4⟩ le_r …`.
-/
theorem orbSq_trDat (hκ : 0 < κ) (hτ : 0 < τ) (L : LocBessel k r) (F F₁ : Mx k r → (L.Wq →L[ℂ] L.Wp))
    (γ : Point ℂ (r + 1)) (C : ℂ)
    (hO : ∀ (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)), IsPtRep L γ g → IsRelStab L g →
      IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
      OrbInt L (fun x => F₁ (cj k r κ τ x)) g ν = C • OrbInt L F g ν) :
    orbSq (trDat L κ τ hκ hτ) F₁ (ptTr κ τ hκ hτ γ) =
      ENNReal.ofReal ((alphaPt κ τ γ)⁻¹ ^ 2 * ‖C‖ ^ 2) * orbSq L F γ := by
  have hα := alphaPt_pos hκ hτ γ
  set α := alphaPt κ τ γ with hαdef
  have hpat : rootPat (ptTr κ τ hκ hτ γ) = rootPat γ := rootPat_ptTr hκ hτ γ
  have hrel : ∀ g, IsRelStab (trDat L κ τ hκ hτ) (cj k r κ τ g) ↔ IsRelStab L g := fun g =>
    isRelStab_iff hκ hτ L (trDat L κ τ hκ hτ) L.hz.1 L.hz'.1 rfl rfl rfl g
  have hroot : ∀ g μR, IsRootMeas (trDat L κ τ hκ hτ) (ptTr κ τ hκ hτ γ) (cj k r κ τ g)
      (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ↔ IsRootMeas L γ g μR := fun g μR =>
    IsRootMeas_trD_iff hκ hτ L _ _ _ _ _ _ _ hpat g μR
  have hquot : ∀ g μR ν, IsOrbQuot (trDat L κ τ hκ hτ) (cj k r κ τ g)
      (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR) ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν) ↔
      IsOrbQuot L g μR ν := fun g μR ν => IsOrbQuot_trD_iff hκ hτ L _ _ _ _ _ _ g μR ν hα
  have key : ∀ g μR ν, IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR → IsOrbQuot L g μR ν →
      ENNReal.ofReal (hsNormSq (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g)
        ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) =
      ENNReal.ofReal (α⁻¹ ^ 2 * ‖C‖ ^ 2) * ENNReal.ofReal (hsNormSq (OrbInt L F g ν)) := by
    intro g μR ν h1 h2 h3 h4
    show ENNReal.ofReal (@hsNormSq L.Wp L.Wq _ _ _ _ _ (OrbInt (trDat L κ τ hκ hτ) F₁ (cj k r κ τ g)
      ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν))) = _
    rw [OrbInt_trD hκ hτ L _ _ _ _ _ _ _ F₁ g _ ν, hO g μR ν h1 h2 h3 h4, smul_smul, hsNormSq_smul,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hα.le, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hα, mul_pow]
  unfold orbSq
  apply le_antisymm
  · refine iSup_le fun g₁ => iSup_le fun μR₁ => iSup_le fun ν₁ => iSup_le fun h => ?_
    obtain ⟨g, rfl⟩ : ∃ g, g₁ = cj k r κ τ g := ⟨cjI k r κ τ g₁, (cj_cjI hκ hτ g₁).symm⟩
    obtain ⟨μR, rfl⟩ : ∃ μR, μR₁ = ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR :=
      ⟨_, (map_cjT_cjIT_smul hκ hτ hα μR₁).symm⟩
    obtain ⟨ν, rfl⟩ : ∃ ν, ν₁ = (ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν :=
      ⟨_, (use₉ hκ hτ hα ν₁).symm⟩
    obtain ⟨h1, h2, h3, h4⟩ := h
    have h1' := (isPtRep_trDat hκ hτ L γ g).mp h1
    have h2' := (hrel g).mp h2
    have h3' := (hroot g μR).mp h3
    have h4' := (hquot g μR ν).mp h4
    rw [key g μR ν h1' h2' h3' h4']
    gcongr
    exact le_iSup_of_le g (le_iSup_of_le μR (le_iSup_of_le ν (le_iSup_of_le ⟨h1', h2', h3', h4'⟩ le_rfl)))
  · simp_rw [ENNReal.mul_iSup]
    refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun h => ?_
    obtain ⟨h1, h2, h3, h4⟩ := h
    rw [← key g μR ν h1 h2 h3 h4]
    exact le_iSup_of_le (cj k r κ τ g) (le_iSup_of_le (ENNReal.ofReal α • Measure.map (cjT k r κ τ) μR)
      (le_iSup_of_le ((ENNReal.ofReal α)⁻¹ • Measure.map (phiP k r κ τ) ν)
        (le_iSup_of_le ⟨(isPtRep_trDat hκ hτ L γ g).mpr h1, (hrel g).mpr h2, (hroot g μR).mpr h3,
          (hquot g μR ν).mpr h4⟩ le_rfl)))

/- English proof (translation)
Unfold `jacBig tF`. Establish `key : ∀ n : ℕ, 2 * ∑ i ∈ Finset.range n, (n - i) = n * (n + 1)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ]`. Establish `h2 : ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, ((n - i) + 1)` using `Finset.sum_congr rfl fun i hi => by`. Use `Finset.mem_range.mp hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]`. Establish `h3 : n + 1 - n = 1` using `by omega`. Rewrite using `[h3]`. Use polynomial arithmetic with `[ih]`. Establish `hsum : ∑ a : Fin r, 4 * (r - (a : ℕ)) = 2 * r * (r + 1)`.

Rewrite using `[← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => r - i) r]`. Use `key r` as an intermediate fact. Use polynomial arithmetic with `[this]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← pow_mul, mul_comm (r - (a : ℕ)) 4]`. Use `_ = τ ^ (4 * r) * κ ^ (∑ a : Fin r, 4 * (r - (a : ℕ))) * τ ^ 4 := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, Finset.prod_pow_eq_pow_sum]`. Use `_ = τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1)) := by`.

Rewrite using `[hsum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacBig_eq (r : ℕ) (κ τ : ℝ) : jacBig r κ τ = τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1)) := by
  unfold jacBig tF
  have key : ∀ n : ℕ, 2 * ∑ i ∈ Finset.range n, (n - i) = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h2 : ∑ i ∈ Finset.range n, (n + 1 - i) = ∑ i ∈ Finset.range n, ((n - i) + 1) :=
        Finset.sum_congr rfl fun i hi => by
          have := Finset.mem_range.mp hi
          omega
      rw [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
      have h3 : n + 1 - n = 1 := by omega
      rw [h3]
      nlinarith [ih]
  have hsum : ∑ a : Fin r, 4 * (r - (a : ℕ)) = 2 * r * (r + 1) := by
    rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i => r - i) r]
    have := key r
    nlinarith [this]
  calc (∏ a : Fin r, (τ * κ ^ (r - (a : ℕ))) ^ 4) * τ ^ 4
      = (∏ a : Fin r, (τ ^ 4 * κ ^ (4 * (r - (a : ℕ))))) * τ ^ 4 := by
        congr 1
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [mul_pow, ← pow_mul, mul_comm (r - (a : ℕ)) 4]
    _ = τ ^ (4 * r) * κ ^ (∑ a : Fin r, 4 * (r - (a : ℕ))) * τ ^ 4 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
          Finset.prod_pow_eq_pow_sum]
    _ = τ ^ (4 * (r + 1)) * κ ^ (2 * r * (r + 1)) := by
        rw [hsum]
        ring

/- English proof (translation)
Unfold `wBig Wbig Mdim`. Rewrite using `[Fin.prod_univ_castSucc]`. Use `congr 1`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.coe_castSucc, ← pow_mul]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.val_last, tF, Nat.sub_self, pow_zero, mul_one, Nat.mul_zero, zero_add]`. Rewrite using `[← pow_mul]`.
-/
theorem wBig_eq_Wbig (hk : 1 ≤ k) (r : ℕ) (κ τ : ℝ) : wBig k r κ τ = Wbig k r κ τ := by
  unfold wBig Wbig Mdim
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [Fin.coe_castSucc, ← pow_mul]
    congr 1
    omega
  · simp only [Fin.val_last, tF, Nat.sub_self, pow_zero, mul_one, Nat.mul_zero, zero_add]
    rw [← pow_mul]

end Dat

end Formalism.MainNotions.FrameBoundFromBesselTorus
