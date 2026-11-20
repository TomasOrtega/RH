import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FubiniHeadLastPart
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixOneZero

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

open Formalism.FourierDecayAlt.P.PBJ

section core

variable {k ρ ph m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/- English proof (translation)
Use `set RR := U.RC k (ph + m) ρ × U.RC k (ph + m) ρ`. Establish `sR` using `Dx2.SL.sigma_RC k (ph + m) ρ`. Use `set μR : Measure RR := (U.muRC k (ph + m) ρ).prod (U.muRC k (ph + m) ρ)`. Establish `s1` using `Fub.sfXiH ph m σh`. Establish `s2` using `Fub.sfXiH m 0 σb`.

Establish `s3 : SFinite (U.muXiH (ph + m) 0 (Fub.sigQ σh σb))` using `Fub.sfXiH (ph + m) 0 (Fub.sigQ σh σb)`. Set `g : RR × (U.XiH ph m σh × U.XiH m 0 σb) → E` to `fun y => U.psiH U.betaU σb y.2.2 • (U.psiStar (p := ph) (s := m) k ρ σh z z' (y.1, y.2.1) • F (U.gaXi (p := ph) (s := m) k ρ σh dh (y.1, y.2.1) (Matrix.of.symm (U.ZjH (p := m) (s := 0) σb db y.2.2 (fun x => x.elim0))) γ))`. Set `Φ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) ≃ᵐ RR × (U.XiH ph m σh × U.XiH m 0 σb)` to `MeasurableEquiv.prodCongr (MeasurableEquiv.refl RR) (Fub.xiE σh σb)`. Establish `hΦ : MeasurePreserving Φ (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb)) (μR.prod (volume.prod volume))` using `(MeasurePreserving.id μR).prod (Fub.xiE_mp σh σb)`. Establish `hfg : (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) => U.psiStar (p` using `ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ • F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ)) = g ∘ Φ := by`.

Use function extensionality and compare the values at `ξ`. Take `⟨x, ⟨a0, b0⟩, v, u⟩` from `ξ`. Rewrite using `[Function.comp_apply]`. Rewrite using `[show Φ (x, ((a0, b0), v, u)) = (x, Fub.xiE σh σb ((a0, b0), v, u)) from rfl, Fub.xiE_apply]`. Simplify using `only [g, U.psiStar, U.gaXi, U.ZjH, Dx2.SL.zj_zero, Fub.zj_split, Equiv.apply_symm_apply]`.

Rewrite using `[Fub.psiH_split σh σb U.betaU a0 b0 (Dx2.SL.uniqueT m).toInhabited.default v u, smul_smul]`. Use `congr 1`. Establish `e1 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z cStd (U.Rn k (ph + m + 0) ρ x.1) = Formalism.QuantumDeterminants.psi k (ph + m + ρ) z cStd (U.Rn k (ph + m) ρ x.1)` using `rfl`. Establish `e2 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z' cStd (U.Rn k (ph + m + 0) ρ x.2) = Formalism.QuantumDeterminants.psi k (ph + m + ρ) z' cStd (U.Rn k (ph + m) ρ x.2)` using `rfl`. Rewrite using `[e1, e2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hg : Integrable g (μR.prod (volume.prod volume))`. Use `hint` as an intermediate fact. Rewrite `this` using `[hfg]`. Conclude with `(hΦ.integrable_comp_emb Φ.measurableEmbedding).mp this`.

Establish `hL : U.PhiFun (p` using `ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ = ∫ y, g y ∂(μR.prod (volume.prod volume)) := by`. Unfold `U.PhiFun`. Rewrite using `[hfg]`. Conclude with `hΦ.integral_comp' g`. Establish `hA : MeasurePreserving (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _) ((μR.prod volume).prod volume) (μR.prod (volume.prod volume))` using `Dx2.SL.assoc_mp μR volume volume`.

Set `g' : (RR × U.XiH ph m σh) × U.XiH m 0 σb → E` to `fun w => g (w.1.1, (w.1.2, w.2))`. Establish `eg : g ∘ (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _) = g'` using `rfl`. Establish `hg' : Integrable g' ((μR.prod volume).prod volume)`. Rewrite using `[← eg]`. Conclude with `(hA.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hg`.

Establish `hA' : ∫ y, g y ∂(μR.prod (volume.prod volume)) = ∫ w, g' w ∂((μR.prod volume).prod volume)` using `(hA.integral_comp' g).symm`. Rewrite using `[hL, hA', MeasureTheory.integral_prod_symm g' hg']`. Unfold `U.PhiTop`. Rewrite using `[show U.muXiH m 0 σb = volume from rfl]`. Use `congr 1`.

Use function extensionality and compare the values at `w`. Simplify using `only [g', g]`. Rewrite using `[integral_smul]`. Both sides reduce to the same expression.
-/
theorem coreQ (σh : Equiv.Perm (Fin ph)) (dh : Fin ph → ℂ) (σb : Equiv.Perm (Fin m)) (db : Fin m → ℂ)
    (z z' : Fin (2 * (ph + m + ρ) + k + 1) → ℂ) (F : B.Mat k (ph + m + ρ) → E) (γ : B.Mat k ρ)
    (hint : Integrable (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
        U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
          F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ))
      (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb))) :
    U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      U.PhiTop (p := m) (s := 0) U.betaU σb db
        (fun Z => U.PhiFun (p := ph) (s := m) k ρ σh dh z z' F Z γ) (fun x => x.elim0) := by
  set RR := U.RC k (ph + m) ρ × U.RC k (ph + m) ρ
  have sR := Dx2.SL.sigma_RC k (ph + m) ρ
  set μR : Measure RR := (U.muRC k (ph + m) ρ).prod (U.muRC k (ph + m) ρ)
  have s1 := Fub.sfXiH ph m σh
  have s2 := Fub.sfXiH m 0 σb
  have s3 : SFinite (U.muXiH (ph + m) 0 (Fub.sigQ σh σb)) := Fub.sfXiH (ph + m) 0 (Fub.sigQ σh σb)
  let g : RR × (U.XiH ph m σh × U.XiH m 0 σb) → E := fun y =>
    U.psiH U.betaU σb y.2.2 •
      (U.psiStar (p := ph) (s := m) k ρ σh z z' (y.1, y.2.1) • F (U.gaXi (p := ph) (s := m) k ρ σh dh (y.1, y.2.1)
        (Matrix.of.symm (U.ZjH (p := m) (s := 0) σb db y.2.2 (fun x => x.elim0))) γ))
  let Φ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) ≃ᵐ RR × (U.XiH ph m σh × U.XiH m 0 σb) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.refl RR) (Fub.xiE σh σb)
  have hΦ : MeasurePreserving Φ (U.muXi k (ph + m) 0 ρ (Fub.sigQ σh σb)) (μR.prod (volume.prod volume)) :=
    (MeasurePreserving.id μR).prod (Fub.xiE_mp σh σb)
  have hfg : (fun ξ : U.Xi k (ph + m) 0 ρ (Fub.sigQ σh σb) =>
      U.psiStar (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) z z' ξ •
        F (U.gaXi (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) ξ (fun a => a.elim0) γ)) = g ∘ Φ := by
    funext ξ
    obtain ⟨x, ⟨a0, b0⟩, v, u⟩ := ξ
    rw [Function.comp_apply]
    rw [show Φ (x, ((a0, b0), v, u)) = (x, Fub.xiE σh σb ((a0, b0), v, u)) from rfl, Fub.xiE_apply]
    simp only [g, U.psiStar, U.gaXi, U.ZjH, Dx2.SL.zj_zero, Fub.zj_split, Equiv.apply_symm_apply]
    rw [Fub.psiH_split σh σb U.betaU a0 b0 (Dx2.SL.uniqueT m).toInhabited.default v u, smul_smul]
    congr 1
    have e1 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z cStd (U.Rn k (ph + m + 0) ρ x.1) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z cStd (U.Rn k (ph + m) ρ x.1) := rfl
    have e2 : Formalism.QuantumDeterminants.psi k (ph + m + 0 + ρ) z' cStd (U.Rn k (ph + m + 0) ρ x.2) =
        Formalism.QuantumDeterminants.psi k (ph + m + ρ) z' cStd (U.Rn k (ph + m) ρ x.2) := rfl
    rw [e1, e2]
    ring
  have hg : Integrable g (μR.prod (volume.prod volume)) := by
    have := hint; rw [hfg] at this
    exact (hΦ.integrable_comp_emb Φ.measurableEmbedding).mp this
  have hL : U.PhiFun (p := ph + m) (s := 0) k ρ (Fub.sigQ σh σb) (Fub.dQ dh db) z z' F (fun a => a.elim0) γ =
      ∫ y, g y ∂(μR.prod (volume.prod volume)) := by
    unfold U.PhiFun
    rw [hfg]
    exact hΦ.integral_comp' g
  have hA : MeasurePreserving (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _)
      ((μR.prod volume).prod volume) (μR.prod (volume.prod volume)) := Dx2.SL.assoc_mp μR volume volume
  let g' : (RR × U.XiH ph m σh) × U.XiH m 0 σb → E := fun w => g (w.1.1, (w.1.2, w.2))
  have eg : g ∘ (MeasurableEquiv.prodAssoc : (RR × U.XiH ph m σh) × U.XiH m 0 σb ≃ᵐ _) = g' := rfl
  have hg' : Integrable g' ((μR.prod volume).prod volume) := by
    rw [← eg]; exact (hA.integrable_comp_emb MeasurableEquiv.prodAssoc.measurableEmbedding).mpr hg
  have hA' : ∫ y, g y ∂(μR.prod (volume.prod volume)) = ∫ w, g' w ∂((μR.prod volume).prod volume) :=
    (hA.integral_comp' g).symm
  rw [hL, hA', MeasureTheory.integral_prod_symm g' hg']
  unfold U.PhiTop
  rw [show U.muXiH m 0 σb = volume from rfl]
  congr 1
  funext w
  simp only [g', g]
  rw [integral_smul]
  rfl

end core

section wrap

/- English proof (translation)
Rewrite using `[show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]`. Rewrite using `[Dx2.SL.partner_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]`. Distinguish the cases in `h1 : a < D.ptSize h + (n + 1)`. Rewrite using `[if_pos h1, Dx2.SL.partner_append (n + 1) t h a h1]`. Distinguish the cases in `h2 : a < D.ptSize h`.

Rewrite using `[if_pos h2, if_pos h2]`. Rewrite using `[if_neg h2, if_neg h2, if_pos h1]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg h1, if_neg (by omega), if_neg h1]; omega`.
-/
theorem partner_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptPartner (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptPartner h a else if a < D.ptSize h + (n + 1) then D.ptSize h + (n - (a - D.ptSize h))
        else a := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.partner_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.partner_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]; omega
  · rw [if_neg h1, if_neg (by omega), if_neg h1]; omega

/- English proof (translation)
Rewrite using `[show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]`. Rewrite using `[Dx2.SL.scal_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]`. Distinguish the cases in `h1 : a < D.ptSize h + (n + 1)`. Rewrite using `[if_pos h1, Dx2.SL.scal_append (n + 1) t h a h1]`. Distinguish the cases in `h2 : a < D.ptSize h`.

Rewrite using `[if_pos h2, if_pos h2]`. Rewrite using `[if_neg h2, if_neg h2, if_pos h1]`. Rewrite using `[if_neg h1, if_neg (by omega), if_neg h1]`.
-/
theorem scal_two (h : C.LPt) (n : ℕ) (t c : ℂ) (a : ℕ) (ha : a < D.ptSize h + (n + 1 + 1)) :
    D.ptScal (h ++ [(n + 1, t), (1, c)]) a =
      if a < D.ptSize h then D.ptScal h a else if a < D.ptSize h + (n + 1) then t else c := by
  rw [show h ++ [(n + 1, t), (1, c)] = (h ++ [(n + 1, t)]) ++ [(1, c)] by simp]
  rw [Dx2.SL.scal_append 1 c (h ++ [(n + 1, t)]) a (by rw [Dx2.SL.ptSize_append]; omega), Dx2.SL.ptSize_append]
  by_cases h1 : a < D.ptSize h + (n + 1)
  · rw [if_pos h1, Dx2.SL.scal_append (n + 1) t h a h1]
    by_cases h2 : a < D.ptSize h
    · rw [if_pos h2, if_pos h2]
    · rw [if_neg h2, if_neg h2, if_pos h1]
  · rw [if_neg h1, if_neg (by omega), if_neg h1]

/- English proof (translation)
Rewrite using `[Dx2.SL.norm_betaU, show (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi by field_simp, Dx2.SL.card_UT' n, Fintype.card_fin]`. Establish `hp : (0 : ℝ) < Real.pi` using `Real.pi_pos`. Establish `hN : (n + 1) * (n + 4) / 2 = n + 1 + ((n + 1) * n / 2 + (n + 1))`. Establish `h2 : 2 ∣ (n + 1) * n` using `(Nat.even_mul_pred_self (n + 1)).two_dvd`. Take `⟨q, hq⟩` from `h2`.

Establish `e : (n + 1) * (n + 4) = 2 * (q + 2 * (n + 1))` using `by nlinarith`. Rewrite using `[e, hq]`. Use linear arithmetic over natural numbers and integers. Unfold `kapB`. Rewrite using `[NNReal.coe_pow, Real.coe_toNNReal _ (by positivity), hN, ← mul_pow, mul_one_div_cancel hp.ne', one_pow]`.
-/
theorem kapB_mul (n : ℕ) :
    kapB n * ((Real.toNNReal (‖U.betaU‖ / (2 * Real.pi)) ^ (Fintype.card (Fin (n + 1)) +
        (Fintype.card (G.UT (n + 1)) + Fintype.card (Fin (n + 1)))) : NNReal) : ℝ) = 1 := by
  rw [Dx2.SL.norm_betaU, show (2 : ℝ) / (2 * Real.pi) = 1 / Real.pi by field_simp, Dx2.SL.card_UT' n,
    Fintype.card_fin]
  have hp : (0 : ℝ) < Real.pi := Real.pi_pos
  have hN : (n + 1) * (n + 4) / 2 = n + 1 + ((n + 1) * n / 2 + (n + 1)) := by
    have h2 : 2 ∣ (n + 1) * n := (Nat.even_mul_pred_self (n + 1)).two_dvd
    obtain ⟨q, hq⟩ := h2
    have e : (n + 1) * (n + 4) = 2 * (q + 2 * (n + 1)) := by nlinarith
    rw [e, hq]; omega
  unfold kapB
  rw [NNReal.coe_pow, Real.coe_toNNReal _ (by positivity), hN, ← mul_pow, mul_one_div_cancel hp.ne', one_pow]

end wrap

section final

/- English proof (translation)
Introduce `k r E _ _ _ z z' F h p n t c hp hle γ hloc hint`. Substitute `hp` using the available equality. Establish `hP : D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1)` using `ptSize_two h n t c`. Establish `hlocH : D.IsLocPt h (D.ptSize h)` using `⟨fun b hb => hloc.1 b (List.mem_append_left _ hb), rfl⟩`. Establish `hspec` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1`.

Establish `hspec'` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1`. Use `set ph := D.ptSize h with hph`. Establish `hσ : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])), ((Fub.sigQ (D.ptPerm h) (Om.σB (n + 1))) (Fin.cast hP a)).val = (D.ptPerm (h ++ [(n + 1, t), (1, c)]) a).val`. Introduce `a`. Establish `ha : a.val < ph + (n + 1 + 1)` using `by have := a.isLt; omega`.

Rewrite using `[hspec a, partner_two h n t c a.val ha]`. Distinguish the cases in `h1 : a.val < ph`. Rewrite using `[if_pos h1]`. Establish `e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[e, Fub.sigQ_castAdd]`.

Conclude with `hspec' ⟨a.val, h1⟩`. Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e, Fub.sigQ_natAdd, Fin.val_natAdd]`. Distinguish the cases in `h2 : a.val < ph + (n + 1)`.

Rewrite using `[if_pos h2]`. Establish `e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩` using `Fin.ext rfl`. Rewrite using `[e2, Om.σB, Fub.sigQ_castAdd, Fin.val_castAdd]`. Simplify using `only [Fin.revPerm_apply, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg h2]`. Establish `e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1)` using `Fin.ext (by simp; omega)`. Rewrite using `[e2, Om.σB, Fub.sigQ_natAdd, Fin.val_natAdd]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish `hd : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])), Fub.dQ (D.ptDiag h) (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) (Fin.cast hP a) = D.ptDiag (h ++ [(n + 1, t), (1, c)]) a`. Introduce `a`. Establish `ha : a.val < ph + (n + 1 + 1)` using `by have := a.isLt; omega`. Simplify using `only [D.ptDiag]`. Rewrite using `[scal_two h n t c a.val ha]`.

Distinguish the cases in `h1 : a.val < ph`. Rewrite using `[if_pos h1]`. Establish `e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[e, Fub.dQ, Fin.addCases_left]`. Both sides reduce to the same expression.

Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩` using `Fin.ext (by simp; omega)`. Rewrite using `[e, Fub.dQ, Fin.addCases_right]`. Distinguish the cases in `h2 : a.val < ph + (n + 1)`. Rewrite using `[if_pos h2]`.

Establish `e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩` using `Fin.ext rfl`. Rewrite using `[e2, Fub.dQ, Fin.addCases_left]`. Rewrite using `[if_neg h2]`. Establish `e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1)` using `Fin.ext (by simp; omega)`. Rewrite using `[e2, Fub.dQ, Fin.addCases_right]`.

Take `⟨hT1, hT2⟩` from `Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) hP _ _ hσ _ _ hd (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) γ`. Establish `hc` using `coreQ (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) (D.ptPerm h) (D.ptDiag h) (Om.σB (n + 1)) (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) _ _ _ γ (hT1 hint)`. Unfold `D.sliceAt`. Rewrite using `[dif_pos hle, hT2, hc, Om.omBlock_eq, smul_smul, ← Complex.ofReal_mul]`. Rewrite using `[kapB_mul n, Complex.ofReal_one, one_smul]`.

Simplify using `only [Dx2.SL.castV_castV, Dx2.SL.castF_castF]`.
-/
theorem sliceOmBlock : SliceOmBlock := by
  intro k r E _ _ _ z z' F h p n t c hp hle γ hloc hint
  subst hp
  have hP : D.ptSize (h ++ [(n + 1, t), (1, c)]) = D.ptSize h + (n + 1 + 1) := ptSize_two h n t c
  have hlocH : D.IsLocPt h (D.ptSize h) := ⟨fun b hb => hloc.1 b (List.mem_append_left _ hb), rfl⟩
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  set ph := D.ptSize h with hph
  have hσ : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      ((Fub.sigQ (D.ptPerm h) (Om.σB (n + 1))) (Fin.cast hP a)).val =
        (D.ptPerm (h ++ [(n + 1, t), (1, c)]) a).val := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    rw [hspec a, partner_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.sigQ_castAdd]
      exact hspec' ⟨a.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.sigQ_natAdd, Fin.val_natAdd]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Om.σB, Fub.sigQ_castAdd, Fin.val_castAdd]
        simp only [Fin.revPerm_apply, Fin.val_rev]
        omega
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Om.σB, Fub.sigQ_natAdd, Fin.val_natAdd]
        simp
        omega
  have hd : ∀ a : Fin (D.ptSize (h ++ [(n + 1, t), (1, c)])),
      Fub.dQ (D.ptDiag h) (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) (Fin.cast hP a) =
        D.ptDiag (h ++ [(n + 1, t), (1, c)]) a := by
    intro a
    have ha : a.val < ph + (n + 1 + 1) := by have := a.isLt; omega
    simp only [D.ptDiag]
    rw [scal_two h n t c a.val ha]
    by_cases h1 : a.val < ph
    · rw [if_pos h1]
      have e : Fin.cast hP a = Fin.castAdd (n + 1 + 1) ⟨a.val, h1⟩ := Fin.ext rfl
      rw [e, Fub.dQ, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP a = Fin.natAdd ph ⟨a.val - ph, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, Fub.dQ, Fin.addCases_right]
      by_cases h2 : a.val < ph + (n + 1)
      · rw [if_pos h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.castAdd 1 ⟨a.val - ph, by omega⟩ := Fin.ext rfl
        rw [e2, Fub.dQ, Fin.addCases_left]
      · rw [if_neg h2]
        have e2 : (⟨a.val - ph, by omega⟩ : Fin (n + 1 + 1)) = Fin.natAdd (n + 1) (0 : Fin 1) :=
          Fin.ext (by simp; omega)
        rw [e2, Fub.dQ, Fin.addCases_right]
  obtain ⟨hT1, hT2⟩ := Dx2.SL.phi_transport (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) hP _ _ hσ _ _ hd
    (D.castV (by omega) z) (D.castV (by omega) z') (D.castF (by omega) F) γ
  have hc := coreQ (k := k) (ρ := r - D.ptSize (h ++ [(n + 1, t), (1, c)])) (D.ptPerm h) (D.ptDiag h) (Om.σB (n + 1))
    (Fub.dQ (fun _ : Fin (n + 1) => t) (fun _ : Fin 1 => c)) _ _ _ γ (hT1 hint)
  unfold D.sliceAt
  rw [dif_pos hle, hT2, hc, Om.omBlock_eq, smul_smul, ← Complex.ofReal_mul]
  rw [kapB_mul n, Complex.ofReal_one, one_smul]
  simp only [Dx2.SL.castV_castV, Dx2.SL.castF_castF]

end final

end Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory.sliceOmBlock`.
-/
theorem Formalism.FourierDecayAlt.P.slice_orbital_block : Formalism.FourierDecayAlt.P.FormNormSumIdentities.SliceOmBlock := Formalism.FourierDecayAlt.P.FormNormSumIdentities.GlobalTheory.sliceOmBlock
