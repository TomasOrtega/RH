import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCDatumTransitFam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepDatumUnit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASSnRepThtFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT

noncomputable section

variable {k r : ℕ}

def mk3 (k : ℕ) {n : ℕ} (v0 : Fin n → ℂ) (F : Fin (k - 1) → Fin n → ℂ) (zz : Fin n → ℂ) : Fin (k + 1) → Fin n → ℂ :=
  fun a => if h0 : a.val = 0 then v0 else if hk : a.val = k then zz else F ⟨a.val - 1, by have := a.isLt; omega⟩

/- English proof (translation)
Unfold `mk3`. Rewrite using `[dif_pos h]`.
-/
theorem three_part_frame_zero {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h : a.val = 0) :
    mk3 k v0 F zz a = v0 := by
  unfold mk3; rw [dif_pos h]

/- English proof (translation)
Unfold `mk3; rw [dif_neg (by omega), dif_pos h]`.
-/
theorem three_part_frame_last {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} (hk : 1 ≤ k) {a : Fin (k + 1)}
    (h : a.val = k) : mk3 k v0 F zz a = zz := by
  unfold mk3; rw [dif_neg (by omega), dif_pos h]

/- English proof (translation)
Unfold `mk3`. Rewrite using `[dif_neg h0, dif_neg hk]`.
-/
theorem three_part_frame_middle {n : ℕ} {v0 zz : Fin n → ℂ} {F : Fin (k - 1) → Fin n → ℂ} {a : Fin (k + 1)} (h0 : a.val ≠ 0)
    (hk : a.val ≠ k) : mk3 k v0 F zz a = F ⟨a.val - 1, by have := a.isLt; omega⟩ := by
  unfold mk3; rw [dif_neg h0, dif_neg hk]

/- English proof (translation)
Establish `hz0 : herm (Hpk k r) zz v0 = 0` using `by rw [DU.hswap, h0z, map_zero]`. Establish `h0F : ∀ j, herm (Hpk k r) v0 (F j) = 0` using `fun j => by rw [DU.hswap, hF0 j, map_zero]`. Establish `hzF : ∀ j, herm (Hpk k r) zz (F j) = 0` using `fun j => by rw [DU.hswap, hFz j, map_zero]`. Prove the components needed by the constructor for the conclusion. Introduce `a`.

Distinguish the cases in `h0 : a.val = 0`. Rewrite using `[three_part_frame_zero h0]`. Conclude with `hv0`. Distinguish the cases in `hl : a.val = k`. Rewrite using `[three_part_frame_last (by omega) hl]; exact hzz`.

Rewrite using `[three_part_frame_middle h0 hl]`. Conclude with `hF _`. Introduce `a b`. Distinguish the cases in `ha0 : a.val = 0`. Rewrite using `[three_part_frame_zero ha0]`.

Distinguish the cases in `hb0 : b.val = 0`. Rewrite using `[three_part_frame_zero hb0, h00, if_pos (Fin.ext (by omega)), if_neg (by omega)]`. Rewrite using `[if_neg (fun h => hb0 (by rw [← h]; exact ha0))]`. Distinguish the cases in `hbl : b.val = k`. Rewrite using `[three_part_frame_last (by omega) hbl, h0z]`.

Rewrite using `[three_part_frame_middle hb0 hbl, h0F]`. Distinguish the cases in `hal : a.val = k`. Rewrite using `[three_part_frame_last (by omega) hal]`. Distinguish the cases in `hb0 : b.val = 0`. Rewrite using `[three_part_frame_zero hb0, hz0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]`.

Distinguish the cases in `hbl : b.val = k`. Rewrite using `[three_part_frame_last (by omega) hbl, hzz1, if_pos (Fin.ext (by omega)), if_pos hal]`. Rewrite using `[three_part_frame_middle hb0 hbl, hzF, if_neg (fun h => hbl (by rw [← h]; exact hal))]`. Rewrite using `[three_part_frame_middle ha0 hal]`. Distinguish the cases in `hb0 : b.val = 0`.

Rewrite using `[three_part_frame_zero hb0, hF0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]`. Distinguish the cases in `hbl : b.val = k`. Rewrite using `[three_part_frame_last (by omega) hbl, hFz, if_neg (fun h => hal (by rw [h]; exact hbl))]`. Rewrite using `[three_part_frame_middle hb0 hbl, hFF]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl, if_neg hal]`. Establish `hv : a.val ≠ b.val` using `fun h => hab (Fin.ext h)`. Rewrite using `[if_neg (fun h => hv (by have := congrArg Fin.val h; simp at this; omega)), if_neg hab]`.
-/
theorem three_part_frame_orthonormal (hk : 2 ≤ k) {v0 zz : Fin (2 * r + k + 1) → ℂ} {F : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hv0 : inWb k r v0) (hzz : inWb k r zz) (hF : ∀ j, inWb k r (F j))
    (h00 : herm (Hpk k r) v0 v0 = 1) (hzz1 : herm (Hpk k r) zz zz = -1) (h0z : herm (Hpk k r) v0 zz = 0)
    (hF0 : ∀ j, herm (Hpk k r) (F j) v0 = 0) (hFz : ∀ j, herm (Hpk k r) (F j) zz = 0)
    (hFF : ∀ i j, herm (Hpk k r) (F i) (F j) = if i = j then 1 else 0) : ONb k r (mk3 k v0 F zz) := by
  have hz0 : herm (Hpk k r) zz v0 = 0 := by rw [DU.hswap, h0z, map_zero]
  have h0F : ∀ j, herm (Hpk k r) v0 (F j) = 0 := fun j => by rw [DU.hswap, hF0 j, map_zero]
  have hzF : ∀ j, herm (Hpk k r) zz (F j) = 0 := fun j => by rw [DU.hswap, hFz j, map_zero]
  constructor
  · intro a
    by_cases h0 : a.val = 0
    · rw [three_part_frame_zero h0]; exact hv0
    · by_cases hl : a.val = k
      · rw [three_part_frame_last (by omega) hl]; exact hzz
      · rw [three_part_frame_middle h0 hl]; exact hF _
  · intro a b
    by_cases ha0 : a.val = 0
    · rw [three_part_frame_zero ha0]
      by_cases hb0 : b.val = 0
      · rw [three_part_frame_zero hb0, h00, if_pos (Fin.ext (by omega)), if_neg (by omega)]
      · rw [if_neg (fun h => hb0 (by rw [← h]; exact ha0))]
        by_cases hbl : b.val = k
        · rw [three_part_frame_last (by omega) hbl, h0z]
        · rw [three_part_frame_middle hb0 hbl, h0F]
    · by_cases hal : a.val = k
      · rw [three_part_frame_last (by omega) hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hz0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hzz1, if_pos (Fin.ext (by omega)), if_pos hal]
          · rw [three_part_frame_middle hb0 hbl, hzF, if_neg (fun h => hbl (by rw [← h]; exact hal))]
      · rw [three_part_frame_middle ha0 hal]
        by_cases hb0 : b.val = 0
        · rw [three_part_frame_zero hb0, hF0, if_neg (fun h => ha0 (by rw [h]; exact hb0))]
        · by_cases hbl : b.val = k
          · rw [three_part_frame_last (by omega) hbl, hFz, if_neg (fun h => hal (by rw [h]; exact hbl))]
          · rw [three_part_frame_middle hb0 hbl, hFF]
            by_cases hab : a = b
            · subst hab; rw [if_pos rfl, if_pos rfl, if_neg hal]
            · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
              rw [if_neg (fun h => hv (by have := congrArg Fin.val h; simp at this; omega)), if_neg hab]

section pt

variable {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `DU.base hz hz' hT hT' hsec hζ`. Establish `hG` using `NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)`. Establish `hGi` using `FrameEntries.glev_inv hG`. Establish `hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z')` using `Qx8.inWb_mulVec hG hz'`. Establish `hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)` using `Qx8.inWb_mulVec hGi hz`.

Establish `hνW : inWb k r (SSn.nu0 k r z z' μsec ζ)` using `by show inWb k r (SSn.unitH k r (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')))`. Unfold `SSn.unitH`. Conclude with `Qx8.inWb_smul (DU.prWv_inWb hz hy) _`. Establish `hνW' : inWb k r (SSn.nu0' k r z z' μsec ζ)` using `by show inWb k r (SSn.unitH k r (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)))`. Unfold `SSn.unitH`.

Conclude with `Qx8.inWb_smul (DU.prWv_inWb hz' hyi) _`. Use `⟨hνW, ?_, h2, h1, hνW', ?_, h4, h3⟩` and prove the remaining obligations. Rewrite using `[← h1]`. Conclude with `DU.prWv_perp hT hνW`. Rewrite using `[← h3]`.

Conclude with `DU.prWv_perp hT' hνW'`.
-/
theorem pt_facts (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (SSn.nu0 k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) z = 0 ∧
    herm (Hpk k r) (SSn.nu0 k r z z' μsec ζ) (SSn.nu0 k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z (SSn.nu0 k r z z' μsec ζ) = SSn.nu0 k r z z' μsec ζ ∧
    inWb k r (SSn.nu0' k r z z' μsec ζ) ∧ herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) z' = 0 ∧
    herm (Hpk k r) (SSn.nu0' k r z z' μsec ζ) (SSn.nu0' k r z z' μsec ζ) = 1 ∧
    SSn.prWv k r z' (SSn.nu0' k r z z' μsec ζ) = SSn.nu0' k r z z' μsec ζ := by
  obtain ⟨h1, h2, h3, h4⟩ := DU.base hz hz' hT hT' hsec hζ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (NF.muZ k r μsec ζ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hνW : inWb k r (SSn.nu0 k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z (NF.muZ k r μsec ζ *ᵥ z')))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz hy) _
  have hνW' : inWb k r (SSn.nu0' k r z z' μsec ζ) := by
    show inWb k r (SSn.unitH k r (SSn.prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z)))
    unfold SSn.unitH
    exact Qx8.inWb_smul (DU.prWv_inWb hz' hyi) _
  refine ⟨hνW, ?_, h2, h1, hνW', ?_, h4, h3⟩
  · rw [← h1]; exact DU.prWv_perp hT hνW
  · rw [← h3]; exact DU.prWv_perp hT' hνW'

/- English proof (translation)
Take `⟨-, -, hνν, -, -, -, hν'ν', -⟩` from `pt_facts hz hz' hT hT' hsec hζ`. Use `set μ := NF.muZ k r μsec ζ with hμ`. Establish `hG` using `NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)`. Establish `hU : μ ∈ UH (Hpk k r)` using `hG.1`. Establish `hGi` using `FrameEntries.glev_inv hG`.

Establish `hy : inWb k r (μ *ᵥ z')` using `Qx8.inWb_mulVec hG hz'`. Establish `hyi : inWb k r (μ⁻¹ *ᵥ z)` using `Qx8.inWb_mulVec hGi hz`. Establish `hFz' : ∀ j, herm (Hpk k r) (Fr j) z' = 0` using `fun j => hFr.2.2 j z' (by simp)`. Establish `hFν' : ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0` using `fun j => hFr.2.2 j _ (by simp)`. Establish `hz0 : ∀ j, herm (Hpk k r) (μ *ᵥ Fr j) z = 0`.

Introduce `j`. Rewrite using `[FrameEntries.herm_inv hU]`. Use `set t : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) (SSn.prWv k r z' (μ⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ) with ht`. Establish `hν' : SSn.nu0' k r z z' μsec ζ = t • SSn.prWv k r z' (μ⁻¹ *ᵥ z)` using `rfl`. Establish `ht0 : t ≠ 0`.

Introduce `h0`. Rewrite `hν'ν'` using `[hν', h0, zero_smul]`. Simplify using `[herm] at hν'ν'`. Establish `h1` using `hFν' j`. Rewrite `h1` using `[hν', DU.hsmul_r]`.

Establish `h2 : herm (Hpk k r) (Fr j) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) = 0`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd ((map_eq_zero (starRingEnd ℂ)).1 h) ht0`. Conclude with `h`. Rewrite `h2` using `[DU.prWv_of hyi, DU.hadd_r, DU.hsmul_r, hFz' j, mul_zero, add_zero]`.

Conclude with `h2`. Use `⟨fun j => Qx8.inWb_mulVec hG (hFr.1 j), fun i j => by rw [Qx2.herm_uh hU]; exact hFr.2.1 i j, hz0, ?_⟩` and prove the remaining obligations. Introduce `j`. Use `set s : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (μ *ᵥ z')) (SSn.prWv k r z (μ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ)`. Establish `hν : SSn.nu0 k r z z' μsec ζ = s • SSn.prWv k r z (μ *ᵥ z')` using `rfl`.

Rewrite using `[hν, DU.hsmul_r, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hz0 j, Qx2.herm_uh hU, hFz' j]`. Simplify using the standard rewrite rules.
-/
theorem mu_frame (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ)
    {m : ℕ} {Fr : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hFr : Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr) :
    (∀ j, inWb k r (NF.muZ k r μsec ζ *ᵥ Fr j)) ∧
    (∀ i j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr i) (NF.muZ k r μsec ζ *ᵥ Fr j) = if i = j then 1 else 0) ∧
    (∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) z = 0) ∧
    ∀ j, herm (Hpk k r) (NF.muZ k r μsec ζ *ᵥ Fr j) (SSn.nu0 k r z z' μsec ζ) = 0 := by
  obtain ⟨-, -, hνν, -, -, -, hν'ν', -⟩ := pt_facts hz hz' hT hT' hsec hζ
  set μ := NF.muZ k r μsec ζ with hμ
  have hG := NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hζ)
  have hU : μ ∈ UH (Hpk k r) := hG.1
  have hGi := FrameEntries.glev_inv hG
  have hy : inWb k r (μ *ᵥ z') := Qx8.inWb_mulVec hG hz'
  have hyi : inWb k r (μ⁻¹ *ᵥ z) := Qx8.inWb_mulVec hGi hz
  have hFz' : ∀ j, herm (Hpk k r) (Fr j) z' = 0 := fun j => hFr.2.2 j z' (by simp)
  have hFν' : ∀ j, herm (Hpk k r) (Fr j) (SSn.nu0' k r z z' μsec ζ) = 0 := fun j => hFr.2.2 j _ (by simp)

  have hz0 : ∀ j, herm (Hpk k r) (μ *ᵥ Fr j) z = 0 := by
    intro j
    rw [FrameEntries.herm_inv hU]
    set t : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) (SSn.prWv k r z' (μ⁻¹ *ᵥ z))).re)⁻¹ : ℝ) : ℂ)
      with ht
    have hν' : SSn.nu0' k r z z' μsec ζ = t • SSn.prWv k r z' (μ⁻¹ *ᵥ z) := rfl
    have ht0 : t ≠ 0 := by
      intro h0
      rw [hν', h0, zero_smul] at hν'ν'
      simp [herm] at hν'ν'
    have h1 := hFν' j
    rw [hν', DU.hsmul_r] at h1
    have h2 : herm (Hpk k r) (Fr j) (SSn.prWv k r z' (μ⁻¹ *ᵥ z)) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd ((map_eq_zero (starRingEnd ℂ)).1 h) ht0
      · exact h
    rw [DU.prWv_of hyi, DU.hadd_r, DU.hsmul_r, hFz' j, mul_zero, add_zero] at h2
    exact h2
  refine ⟨fun j => Qx8.inWb_mulVec hG (hFr.1 j), fun i j => by rw [Qx2.herm_uh hU]; exact hFr.2.1 i j, hz0, ?_⟩
  intro j
  set s : ℂ := (((Real.sqrt (herm (Hpk k r) (SSn.prWv k r z (μ *ᵥ z')) (SSn.prWv k r z (μ *ᵥ z'))).re)⁻¹ : ℝ) : ℂ)
  have hν : SSn.nu0 k r z z' μsec ζ = s • SSn.prWv k r z (μ *ᵥ z') := rfl
  rw [hν, DU.hsmul_r, DU.prWv_of hy, DU.hadd_r, DU.hsmul_r, hz0 j, Qx2.herm_uh hU, hFz' j]
  simp

/- English proof (translation)
Take `⟨-, -, -, -, hW', hz'0, h11, -⟩` from `pt_facts hz hz' hT hT' hsec hζ`. Conclude with `Topx1.typ_frame_exists k r (by omega) z' _ hz' hT' hW' hz'0 h11`.
-/
theorem frame'_exists (hk : 2 ≤ k) (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) {ζ : ℂ} (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    ∃ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [z', SSn.nu0' k r z z' μsec ζ] Fr := by
  obtain ⟨-, -, -, -, hW', hz'0, h11, -⟩ := pt_facts hz hz' hT hT' hsec hζ
  exact Topx1.typ_frame_exists k r (by omega) z' _ hz' hT' hW' hz'0 h11

end pt

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC.DT
