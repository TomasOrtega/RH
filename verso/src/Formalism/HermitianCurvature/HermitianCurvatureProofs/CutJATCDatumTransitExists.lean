import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitPt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSGen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDtrSIo

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

/- English proof (translation)
Rewrite using `[fam_in (by omega), three_part_frame_zero (by show i.val - r = 0; omega)]`.
-/
theorem frame_family_middle_index {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    {i : Fin (2 * r + k + 1)} (hi : i.val = r) : fam k r (mk3 k v0 F zz) i = v0 := by
  rw [fam_in (by omega), three_part_frame_zero (by show i.val - r = 0; omega)]

/- English proof (translation)
Rewrite using `[fam_in (by omega), three_part_frame_last hk (by show i.val - r = k; omega)]`.
-/
theorem frame_family_last_index {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hk : 1 ≤ k)
    {i : Fin (2 * r + k + 1)} (hi : i.val = r + k) : fam k r (mk3 k v0 F zz) i = zz := by
  rw [fam_in (by omega), three_part_frame_last hk (by show i.val - r = k; omega)]

/- English proof (translation)
Rewrite using `[fam_in (by omega), three_part_frame_middle (by show i.val - r ≠ 0; omega) (by show i.val - r ≠ k; omega)]`.
-/
theorem frame_family_middle_range {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    {i : Fin (2 * r + k + 1)} (hi : r + 1 ≤ i.val ∧ i.val < r + k) :
    fam k r (mk3 k v0 F zz) i = F ⟨i.val - r - 1, by omega⟩ := by
  rw [fam_in (by omega), three_part_frame_middle (by show i.val - r ≠ 0; omega) (by show i.val - r ≠ k; omega)]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Unfold `SSn.wbP bvec`. Use `split_ifs with hp`. Rewrite using `[Pi.single_apply, if_neg (by rintro rfl; omega)]; rfl`. Both sides reduce to the same expression.
-/
theorem blockProjection_basisVector_eq_zero {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) : SSn.wbP k r (bvec i) = 0 := by
  funext p
  unfold SSn.wbP bvec
  split_ifs with hp
  · rw [Pi.single_apply, if_neg (by rintro rfl; omega)]; rfl
  · rfl

/- English proof (translation)
Unfold `SSn.prWv`. Rewrite using `[blockProjection_basisVector_eq_zero hi]`. Simplify using `[herm]`.
-/
theorem prWv_bvec_out (z' : Fin (2 * r + k + 1) → ℂ) {i : Fin (2 * r + k + 1)} (hi : i.val < r ∨ r + k < i.val) :
    SSn.prWv k r z' (bvec i) = 0 := by
  unfold SSn.prWv
  rw [blockProjection_basisVector_eq_zero hi]
  simp [herm]

/- English proof (translation)
Rewrite using `[DU.prWv_of hz', FrameEntries.herm_self]`. Establish `hT0 : ((Tz k r z' : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hT'.ne'`. Rewrite using `[neg_div, div_self hT0, neg_smul, one_smul, add_neg_cancel]`.
-/
theorem prWv_self {z' : Fin (2 * r + k + 1) → ℂ} (hz' : inWb k r z') (hT' : 0 < Tz k r z') :
    SSn.prWv k r z' z' = 0 := by
  rw [DU.prWv_of hz', FrameEntries.herm_self]
  have hT0 : ((Tz k r z' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  rw [neg_div, div_self hT0, neg_smul, one_smul, add_neg_cancel]

/- English proof (translation)
Simplify using `[herm]`.
-/
theorem herm_zero_l (w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) 0 w = 0 := by simp [herm]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

/- English proof (translation)
Take `⟨-, -, -, -, -, -, h11, hfix⟩` from `pt_facts hz hz' hT hT' hsec hζ`. Rewrite using `[ioMulVec]`. Distinguish the cases in `hout : i.val < r ∨ r + k < i.val`. Rewrite using `[fam_out hout, prWv_bvec_out z' hout, herm_zero_l, zero_smul, sub_zero, Matrix.mulVec_zero, dif_neg (by omega)]`. Distinguish the cases in `h0 : i.val = r`.

Rewrite using `[frame_family_middle_index h0, hfix, h11, one_smul, sub_self, Matrix.mulVec_zero, dif_neg (by omega)]`. Distinguish the cases in `hl : i.val = r + k`. Rewrite using `[frame_family_last_index (by omega) hl, TF.prWv_smul, prWv_self hz' hT', smul_zero, herm_zero_l, zero_smul, sub_zero, Matrix.mulVec_zero, dif_neg (by omega)]`. Establish `hm : r + 1 ≤ i.val ∧ i.val < r + k` using `by omega`. Rewrite using `[frame_family_middle_range hm, dif_pos hm, DU.prWv_fix (hFr.1 _) (hFr.2.2 _ z' (by simp)), hFr.2.2 _ _ (by simp), zero_smul, sub_zero]`.
-/
theorem io_fam (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ} (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) (c : ℂ)
    (i : Fin (2 * r + k + 1)) :
    SSn.io0 k r z z' μsec ζ *ᵥ fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ) Fr (c • z')) i =
      if h : r + 1 ≤ i.val ∧ i.val < r + k then NF.muZ k r μsec ζ *ᵥ Fr ⟨i.val - r - 1, by omega⟩ else 0 := by
  obtain ⟨-, -, -, -, -, -, h11, hfix⟩ := pt_facts hz hz' hT hT' hsec hζ
  rw [ioMulVec]
  by_cases hout : i.val < r ∨ r + k < i.val
  · rw [fam_out hout, prWv_bvec_out z' hout, herm_zero_l, zero_smul, sub_zero, Matrix.mulVec_zero,
      dif_neg (by omega)]
  · by_cases h0 : i.val = r
    · rw [frame_family_middle_index h0, hfix, h11, one_smul, sub_self, Matrix.mulVec_zero, dif_neg (by omega)]
    · by_cases hl : i.val = r + k
      · rw [frame_family_last_index (by omega) hl, TF.prWv_smul, prWv_self hz' hT', smul_zero, herm_zero_l, zero_smul, sub_zero,
          Matrix.mulVec_zero, dif_neg (by omega)]
      · have hm : r + 1 ≤ i.val ∧ i.val < r + k := by omega
        rw [frame_family_middle_range hm, dif_pos hm,
          DU.prWv_fix (hFr.1 _) (hFr.2.2 _ z' (by simp)), hFr.2.2 _ _ (by simp), zero_smul, sub_zero]

end pt

/- English proof (translation)
The claim follows from `Matrix.isUnit_det_of_left_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1`.
-/
theorem hpk_det_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

/- English proof (translation)
Establish `hs : 0 < Real.sqrt (Tz k r z)` using `Real.sqrt_pos.2 hT`. Use `⟨Qx8.inWb_smul hz _, ?_, by exact_mod_cast (inv_pos.2 hs).ne'⟩` and prove the remaining obligations. Rewrite using `[DU.hsmul_l, DU.hsmul_r, FrameEntries.herm_self, Complex.conj_ofReal]`. Establish `hsq : Real.sqrt (Tz k r z) ^ 2 = Tz k r z` using `Real.sq_sqrt hT.le`. Establish `hsq' : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ^ 2 = ((Tz k r z : ℝ) : ℂ)` using `by exact_mod_cast hsq`.

Establish `hne : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hs.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hsq']`.
-/
theorem cz_facts {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) :
    inWb k r ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) ∧
    herm (Hpk k r) ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) ((((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) • z) = -1 ∧
    (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) ≠ 0 := by
  have hs : 0 < Real.sqrt (Tz k r z) := Real.sqrt_pos.2 hT
  refine ⟨Qx8.inWb_smul hz _, ?_, by exact_mod_cast (inv_pos.2 hs).ne'⟩
  rw [DU.hsmul_l, DU.hsmul_r, FrameEntries.herm_self, Complex.conj_ofReal]
  have hsq : Real.sqrt (Tz k r z) ^ 2 = Tz k r z := Real.sq_sqrt hT.le
  have hsq' : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ^ 2 = ((Tz k r z : ℝ) : ℂ) := by exact_mod_cast hsq
  have hne : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  push_cast
  field_simp
  rw [hsq']

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ComplexConjugate Matrix

noncomputable section

open DT in
/- English proof (translation)
Introduce `k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂`. Take `⟨Fr₁, hFr₁⟩` from `frame'_exists hk hz hz' hT hT' hsec h₁`. Take `⟨Fr₂, hFr₂⟩` from `frame'_exists hk hz hz' hT hT' hsec h₂`. Take `⟨hW₁, hνz₁, hνν₁, -, hW₁', hνz₁', hνν₁', -⟩` from `pt_facts hz hz' hT hT' hsec h₁`. Take `⟨hW₂, hνz₂, hνν₂, -, hW₂', hνz₂', hνν₂', -⟩` from `pt_facts hz hz' hT hT' hsec h₂`.

Take `⟨mW₁, mO₁, mz₁, mν₁⟩` from `mu_frame hz hz' hT hT' hsec h₁ hFr₁`. Take `⟨mW₂, mO₂, mz₂, mν₂⟩` from `mu_frame hz hz' hT hT' hsec h₂ hFr₂`. Take `⟨czW, czz, cz0⟩` from `cz_facts hz hT`. Take `⟨czW', czz', cz0'⟩` from `cz_facts hz' hT'`. Use `set c := (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) with hc`.

Use `set c' := (((Real.sqrt (Tz k r z'))⁻¹ : ℝ) : ℂ) with hc'`. Establish `hνc : ∀ ν, herm (Hpk k r) ν z = 0 → herm (Hpk k r) ν (c • z) = 0` using `fun ν h => by`. Rewrite using `[DU.hsmul_r, h, mul_zero]`. Establish `hνc' : ∀ ν, herm (Hpk k r) ν z' = 0 → herm (Hpk k r) ν (c' • z') = 0` using `fun ν h => by`. Rewrite using `[DU.hsmul_r, h, mul_zero]`.

Establish `hFz' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}, Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) z' = 0` using `fun hF j => hF.2.2 j z' (by simp)`. Establish `hFν' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}, Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0` using `fun hF j => hF.2.2 j _ (by simp)`. Establish `oX'` using `three_part_frame_orthonormal hk hW₁' czW' hFr₁.1 hνν₁' czz' (hνc' _ hνz₁') (hFν' hFr₁) (fun j => hνc' _ (hFz' hFr₁ j)) hFr₁.2.1`. Establish `oY'` using `three_part_frame_orthonormal hk hW₂' czW' hFr₂.1 hνν₂' czz' (hνc' _ hνz₂') (hFν' hFr₂) (fun j => hνc' _ (hFz' hFr₂ j)) hFr₂.2.1`. Establish `oX` using `three_part_frame_orthonormal hk hW₁ czW mW₁ hνν₁ czz (hνc _ hνz₁) mν₁ (fun j => hνc _ (mz₁ j)) mO₁`.

Establish `oY` using `three_part_frame_orthonormal hk hW₂ czW mW₂ hνν₂ czz (hνc _ hνz₂) mν₂ (fun j => hνc _ (mz₂ j)) mO₂`. Use `set x' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₁) Fr₁ (c' • z')) with hx'`. Use `set y' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₂) Fr₂ (c' • z')) with hy'`. Use `set x := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₁) (fun j => NF.muZ k r μsec ζ₁ *ᵥ Fr₁ j) (c • z)) with hx`. Use `set y := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₂) (fun j => NF.muZ k r μsec ζ₂ *ᵥ Fr₂ j) (c • z)) with hy`.

Take `⟨h', hh'U, hh'⟩` from `wittGram _ (Hpk k r) hpk_det_unit x' y' (famGram oX') (famGram oY')`. Take `⟨h, hhU, hh⟩` from `wittGram _ (Hpk k r) hpk_det_unit x y (famGram oX) (famGram oY)`. Establish `pr : r ≤ r ∧ r ≤ r + k` using `by omega`. Set `iR : Fin (2 * r + k + 1)` to `⟨r, by omega⟩`. Set `iL : Fin (2 * r + k + 1)` to `⟨r + k, by omega⟩`.

Establish `fixOut : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (e e' : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ), (∀ i, g *ᵥ fam k r e i = fam k r e' i) → ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)`. Introduce `g e e' hg a`. Establish `h1` using `hg (eI k r a)`. Establish `h2` using `hg (esI k r a)`. Rewrite `h1` using `[fam_out (by simp [eI]), fam_out (by simp [eI])]`.

Rewrite `h2` using `[fam_out (by simp [esI]; omega), fam_out (by simp [esI]; omega)]`. Conclude with `⟨h1, h2⟩`. Establish `fixZ : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (w : Fin (2 * r + k + 1) → ℂ) (t : ℂ), t ≠ 0 → g *ᵥ (t • w) = t • w → g *ᵥ w = w`. Introduce `g w t ht h`. Rewrite `h` using `[Matrix.mulVec_smul]`.

Conclude with `smul_right_injective _ ht h`. Establish `hhz : h *ᵥ z = z`. Use `hh iL` as an intermediate fact. Rewrite `this` using `[hx, hy, frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl]`. Conclude with `fixZ h z c cz0 this`.

Establish `hh'z : h' *ᵥ z' = z'`. Use `hh' iL` as an intermediate fact. Rewrite `this` using `[hx', hy', frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl]`. Conclude with `fixZ h' z' c' cz0' this`. Establish `hmem : h ∈ UWset k r z` using `⟨hhU, fixOut h _ _ hh, hhz⟩`.

Establish `hmem' : h' ∈ UWset k r z'` using `⟨hh'U, fixOut h' _ _ hh', hh'z⟩`. Use `⟨h, hmem, h', hmem', ?_, ?_, ?_⟩` and prove the remaining obligations. Use `hh iR` as an intermediate fact. Rewrite `this` using `[hx, hy, frame_family_middle_index rfl, frame_family_middle_index rfl]`. Conclude with `this`.

Use `hh' iR` as an intermediate fact. Rewrite `this` using `[hx', hy', frame_family_middle_index rfl, frame_family_middle_index rfl]`. Conclude with `this`. Establish `key : h * SSn.io0 k r z z' μsec ζ₁ = SSn.io0 k r z z' μsec ζ₂ * h'`. Use `extGram _ (Hpk k r) hpk_det_unit x' (famGram oX') _ _ fun i => ?_` and prove the remaining obligations.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh' i, hx', io_fam hk hz hz' hT hT' hsec h₁ hFr₁ c' i, hy', io_fam hk hz hz' hT hT' hsec h₂ hFr₂ c' i]`. Distinguish the cases in `hm : r + 1 ≤ i.val ∧ i.val < r + k`. Rewrite using `[dif_pos hm, dif_pos hm]`. Use `hh i` as an intermediate fact. Rewrite `this` using `[hx, hy, frame_family_middle_range hm, frame_family_middle_range hm]`.

Conclude with `this`. Rewrite using `[dif_neg hm, dif_neg hm, Matrix.mulVec_zero]`. Rewrite using `[key, Matrix.mul_assoc, FrameEntries.mul_inv_uh hh'U, Matrix.mul_one]`.
-/
theorem datum_transit_existence : DTExists := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  obtain ⟨Fr₁, hFr₁⟩ := frame'_exists hk hz hz' hT hT' hsec h₁
  obtain ⟨Fr₂, hFr₂⟩ := frame'_exists hk hz hz' hT hT' hsec h₂
  obtain ⟨hW₁, hνz₁, hνν₁, -, hW₁', hνz₁', hνν₁', -⟩ := pt_facts hz hz' hT hT' hsec h₁
  obtain ⟨hW₂, hνz₂, hνν₂, -, hW₂', hνz₂', hνν₂', -⟩ := pt_facts hz hz' hT hT' hsec h₂
  obtain ⟨mW₁, mO₁, mz₁, mν₁⟩ := mu_frame hz hz' hT hT' hsec h₁ hFr₁
  obtain ⟨mW₂, mO₂, mz₂, mν₂⟩ := mu_frame hz hz' hT hT' hsec h₂ hFr₂
  obtain ⟨czW, czz, cz0⟩ := cz_facts hz hT
  obtain ⟨czW', czz', cz0'⟩ := cz_facts hz' hT'
  set c := (((Real.sqrt (Tz k r z))⁻¹ : ℝ) : ℂ) with hc
  set c' := (((Real.sqrt (Tz k r z'))⁻¹ : ℝ) : ℂ) with hc'
  have hνc : ∀ ν, herm (Hpk k r) ν z = 0 → herm (Hpk k r) ν (c • z) = 0 := fun ν h => by
    rw [DU.hsmul_r, h, mul_zero]
  have hνc' : ∀ ν, herm (Hpk k r) ν z' = 0 → herm (Hpk k r) ν (c' • z') = 0 := fun ν h => by
    rw [DU.hsmul_r, h, mul_zero]
  have hFz' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ},
      Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) z' = 0 :=
    fun hF j => hF.2.2 j z' (by simp)
  have hFν' : ∀ {ζ : ℂ} {Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ},
      Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr → ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 :=
    fun hF j => hF.2.2 j _ (by simp)

  have oX' := three_part_frame_orthonormal hk hW₁' czW' hFr₁.1 hνν₁' czz' (hνc' _ hνz₁') (hFν' hFr₁) (fun j => hνc' _ (hFz' hFr₁ j)) hFr₁.2.1
  have oY' := three_part_frame_orthonormal hk hW₂' czW' hFr₂.1 hνν₂' czz' (hνc' _ hνz₂') (hFν' hFr₂) (fun j => hνc' _ (hFz' hFr₂ j)) hFr₂.2.1
  have oX := three_part_frame_orthonormal hk hW₁ czW mW₁ hνν₁ czz (hνc _ hνz₁) mν₁ (fun j => hνc _ (mz₁ j)) mO₁
  have oY := three_part_frame_orthonormal hk hW₂ czW mW₂ hνν₂ czz (hνc _ hνz₂) mν₂ (fun j => hνc _ (mz₂ j)) mO₂
  set x' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₁) Fr₁ (c' • z')) with hx'
  set y' := fam k r (mk3 k (SSn.nu0' k r z z' μsec ζ₂) Fr₂ (c' • z')) with hy'
  set x := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₁) (fun j => NF.muZ k r μsec ζ₁ *ᵥ Fr₁ j) (c • z)) with hx
  set y := fam k r (mk3 k (SSn.nu0 k r z z' μsec ζ₂) (fun j => NF.muZ k r μsec ζ₂ *ᵥ Fr₂ j) (c • z)) with hy
  obtain ⟨h', hh'U, hh'⟩ := wittGram _ (Hpk k r) hpk_det_unit x' y' (famGram oX') (famGram oY')
  obtain ⟨h, hhU, hh⟩ := wittGram _ (Hpk k r) hpk_det_unit x y (famGram oX) (famGram oY)
  have pr : r ≤ r ∧ r ≤ r + k := by omega
  let iR : Fin (2 * r + k + 1) := ⟨r, by omega⟩
  let iL : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩
  have fixOut : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
      (e e' : Fin (k + 1) → Fin (2 * r + k + 1) → ℂ), (∀ i, g *ᵥ fam k r e i = fam k r e' i) →
      ∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a) := by
    intro g e e' hg a
    have h1 := hg (eI k r a)
    have h2 := hg (esI k r a)
    rw [fam_out (by simp [eI]), fam_out (by simp [eI])] at h1
    rw [fam_out (by simp [esI]; omega), fam_out (by simp [esI]; omega)] at h2
    exact ⟨h1, h2⟩
  have fixZ : ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (w : Fin (2 * r + k + 1) → ℂ) (t : ℂ),
      t ≠ 0 → g *ᵥ (t • w) = t • w → g *ᵥ w = w := by
    intro g w t ht h
    rw [Matrix.mulVec_smul] at h
    exact smul_right_injective _ ht h
  have hhz : h *ᵥ z = z := by
    have := hh iL
    rw [hx, hy, frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl] at this
    exact fixZ h z c cz0 this
  have hh'z : h' *ᵥ z' = z' := by
    have := hh' iL
    rw [hx', hy', frame_family_last_index (by omega) rfl, frame_family_last_index (by omega) rfl] at this
    exact fixZ h' z' c' cz0' this
  have hmem : h ∈ UWset k r z := ⟨hhU, fixOut h _ _ hh, hhz⟩
  have hmem' : h' ∈ UWset k r z' := ⟨hh'U, fixOut h' _ _ hh', hh'z⟩
  refine ⟨h, hmem, h', hmem', ?_, ?_, ?_⟩
  · have := hh iR
    rw [hx, hy, frame_family_middle_index rfl, frame_family_middle_index rfl] at this
    exact this
  · have := hh' iR
    rw [hx', hy', frame_family_middle_index rfl, frame_family_middle_index rfl] at this
    exact this
  · have key : h * SSn.io0 k r z z' μsec ζ₁ = SSn.io0 k r z z' μsec ζ₂ * h' := by
      refine extGram _ (Hpk k r) hpk_det_unit x' (famGram oX') _ _ fun i => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh' i, hx', io_fam hk hz hz' hT hT' hsec h₁ hFr₁ c' i,
        hy', io_fam hk hz hz' hT hT' hsec h₂ hFr₂ c' i]
      by_cases hm : r + 1 ≤ i.val ∧ i.val < r + k
      · rw [dif_pos hm, dif_pos hm]
        have := hh i
        rw [hx, hy, frame_family_middle_range hm, frame_family_middle_range hm] at this
        exact this
      · rw [dif_neg hm, dif_neg hm, Matrix.mulVec_zero]
    rw [key, Matrix.mul_assoc, FrameEntries.mul_inv_uh hh'U, Matrix.mul_one]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
