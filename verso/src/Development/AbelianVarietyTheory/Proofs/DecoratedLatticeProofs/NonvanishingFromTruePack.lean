import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PtRows
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueDOfTruePack
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamShareOfFreeT
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamBigOfRamShare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HdNumbers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagCorollary
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeWindow
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiveLeHalfKfk
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinrankKerPuLeHsDev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConstantsExistForBundleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegreeHypothesisAllMembersStatement

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop

open GlobalTheory.Core.Rk

/- English proof (translation)
The claim follows from `let ⟨B, X, I, l, Z, e, ⟨w⟩⟩ := h; ⟨B, X, I, l, Z, e, w, w.S.pin⟩`.
-/
theorem trueE_of_trueD {D : D7} (h : TrueD D) : TrueE D :=
  let ⟨B, X, I, l, Z, e, ⟨w⟩⟩ := h; ⟨B, X, I, l, Z, e, w, w.S.pin⟩

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Set `FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u` to `(D.s_Cu u).symm.toLinearMap ∘ₗ Submodule.inclusion (inf_le_left : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0)`. Establish `hFF : Function.Injective FF` using `(D.s_Cu u).symm.injective.comp (Submodule.inclusion_injective _)`. Establish `hle : Module.finrank ℂ (D.mem u).A.Mram ≤ Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH))`.

Set `g : (D.mem u).A.Mram →ₗ[ℂ] LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)` to `FF.codRestrict _ (fun φ => by rw [LinearMap.mem_ker]; exact hne φ)`. Conclude with `LinearMap.finrank_le_finrank_of_injective (f := g) (fun x y h => hFF (congrArg Subtype.val h))`. Establish `hk` using `finrank_ker_Pu_le_hsDev D u`. Take `⟨-, hbig⟩` from `hR`. Establish `hU : (GlobalTheory.Core.Rk.dU D u : ℝ) ≤ (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ)`.

Unfold `GlobalTheory.Core.Rk.dU`. Conclude with `hle` after adjusting the coercions. Establish `hd' : (0 : ℝ) < (d0 D u : ℝ)` using `by exact_mod_cast hd`. Unfold `DiagS at hS`. Establish `: (1 - δ) * (d0 D u : ℝ) ≤ e * (d0 D u : ℝ)` using `by linarith`.

Use `le_of_mul_le_mul_right this hd'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem puNZ_at (D : D7) (u : D.what₂.Word) (e δ : ℝ) (hS : DiagS D u e) (hR : RamBig D u δ) (hlt : e < 1 - δ)
    (hd : 0 < d0 D u) : ∃ φ : (D.mem u).A.Mram, D.s.Pu u ((D.s_Cu u).symm ⟨φ.1, φ.2.1⟩) ≠ 0 := by
  by_contra hne
  push_neg at hne
  let FF : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u :=
    (D.s_Cu u).symm.toLinearMap ∘ₗ Submodule.inclusion (inf_le_left : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0)
  have hFF : Function.Injective FF := (D.s_Cu u).symm.injective.comp (Submodule.inclusion_injective _)
  have hle : Module.finrank ℂ (D.mem u).A.Mram ≤
      Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) := by
    let g : (D.mem u).A.Mram →ₗ[ℂ] LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH) :=
      FF.codRestrict _ (fun φ => by rw [LinearMap.mem_ker]; exact hne φ)
    exact LinearMap.finrank_le_finrank_of_injective (f := g) (fun x y h => hFF (congrArg Subtype.val h))
  have hk := finrank_ker_Pu_le_hsDev D u
  obtain ⟨-, hbig⟩ := hR
  have hU : (GlobalTheory.Core.Rk.dU D u : ℝ) ≤ (Module.finrank ℂ (LinearMap.ker (D.s.Pu u : D.s.Cu u →ₗ[ℂ] D.s.HH)) : ℝ) := by
    unfold GlobalTheory.Core.Rk.dU; exact_mod_cast hle
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold DiagS at hS
  have : (1 - δ) * (d0 D u : ℝ) ≤ e * (d0 D u : ℝ) := by linarith
  have := le_of_mul_le_mul_right this hd'
  linarith

/- English proof (translation)
Introduce `u`. Take `⟨hm, hT, hd, -⟩` from `hd_numbers D u _ C' Cl Cg cb Cu cT CT hH`. Establish `hG : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D large₂.sc.L` using `by rw [large₂.Gam_eq u]; unfold mfL; ring`. Establish `hw : 1 + 2 * C * mfL D large₂.sc.L ≤ 2 * Real.log (D.mem u).A.GamP` using `by rw [hG]; nlinarith`. Establish `hCm : 5 ≤ C * mfL D large₂.sc.L` using `by nlinarith`.

Establish `hdiag` using `diag_corollary.2.1 D u _ C (by linarith) (hS u) ((levelPrime_window D u).2.2 _ C (hmu u) hw)`. Establish `hf : D.R.f ≠ 0`. Introduce `h0`. Unfold `mfL at hm`. Rewrite `hm` using `[h0]`.

Evaluate the numerical expressions using `at hm`. Establish `hR` using `ramBig_of_ramShare D u (ramShare_of_trueD D u hD) hd (by omega)`. Establish `h2` using `two_eDiag_lt D u _ C hCm hT`. Establish `h0 : 0 ≤ eDiag D large₂.sc.L C` using `by unfold eDiag; positivity`. Conclude with `puNZ_at D u _ _ hdiag hR (by linarith) hd`.
-/
theorem puNZ_of_sDiag {D : D7} (large₂ : SizeData₂ D) {C C' Cl Cg cb Cu cT CT : ℝ} (hC : 1 ≤ C) (hCG : C + 1 ≤ large₂.CGam) (hD : TrueD D)
    (hH : GlobalTheory.Core.Rk.HD D large₂.sc.L C' Cl Cg cb Cu cT CT) (hmu : ∀ u, RankMu D u) (hS : ∀ u, SDiag D u large₂.sc.L C) : PuNZ D := by
  intro u
  obtain ⟨hm, hT, hd, -⟩ := hd_numbers D u _ C' Cl Cg cb Cu cT CT hH
  have hG : Real.log (D.mem u).A.GamP = large₂.CGam * mfL D large₂.sc.L := by rw [large₂.Gam_eq u]; unfold mfL; ring
  have hw : 1 + 2 * C * mfL D large₂.sc.L ≤ 2 * Real.log (D.mem u).A.GamP := by rw [hG]; nlinarith
  have hCm : 5 ≤ C * mfL D large₂.sc.L := by nlinarith
  have hdiag := diag_corollary.2.1 D u _ C (by linarith) (hS u) ((levelPrime_window D u).2.2 _ C (hmu u) hw)
  have hf : D.R.f ≠ 0 := by
    intro h0
    unfold mfL at hm
    rw [h0] at hm
    norm_num at hm
  have hR := ramBig_of_ramShare D u (ramShare_of_trueD D u hD) hd (by omega)
  have h2 := two_eDiag_lt D u _ C hCm hT
  have h0 : 0 ≤ eDiag D large₂.sc.L C := by unfold eDiag; positivity
  exact puNZ_at D u _ _ hdiag hR (by linarith) hd

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ => ⟨⟨0, fun _ => 0, fun l => J (l.getD 6 0 + 1) (l.getD 13 0), fun _ => 0⟩, fun C _ _ hL => ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ => hL.2.2.1 C.CGam (by simp [Formalism.MainNotions.Inhab.FC.cMid])⟩⟩⟩⟩⟩`.
-/
theorem evP_cGam (J : ℝ → ℝ → ℝ) : EvP fun κ _ => J (κ.C.P.CYL + 1) κ.C.CTu ≤ κ.C.CGam :=
  ⟨1, one_pos, fun _ _ _ _ _ _ _ _ _ =>
    ⟨⟨0, fun _ => 0, fun l => J (l.getD 6 0 + 1) (l.getD 13 0), fun _ => 0⟩, fun C _ _ hL =>
      ⟨0, fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ => hL.2.2.1 C.CGam (by simp [Formalism.MainNotions.Inhab.FC.cMid])⟩⟩⟩⟩⟩

/- English proof (translation)
Introduce `hRow hL p hTP`. Establish `hR` using `fun Cg CT : ℝ => hRow Cg (1 / 4) 3 (1 / 2) CT (by norm_num) (by norm_num)`. Use `choose Cf Af Bf hC hrow using hR`. Establish `h1` using `GlobalTheory.T.constants_exist_for_bundle hL p (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)`. Establish `h2` using `GlobalTheory.T.degree_hypothesis_all_members hL p (fun C => Af (C.P.CYL + 1) C.CTu) (fun C => Bf (C.P.CYL + 1) C.CTu)`.

Establish `h3 : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun κ _ _ _ _ => Cf (κ.C.P.CYL + 1) κ.C.CTu + 1 ≤ κ.C.CGam)` using `EvP.mono (fun _ _ _ h _ _ _ _ _ => h) (evP_cGam fun a b => Cf a b + 1)`. Use `(((hTP.and h1).and h2).and h3).imp fun κ K β c b hk _ _ h => ?_` and prove the remaining obligations. Take `⟨⟨⟨hT, -, -, -, -, -, -, -, ⟨t1, t2, -, t4, t5⟩, -, hmu, -⟩, hH⟩, hG⟩` from `h`. Establish `hD : TrueD β.D` using `trueD_of_truePack _ hT`. Establish `hCG : β.O.L.CGam = κ.C.CGam` using `by rw [← hk.1]; exact β.val.CGam_eq`.

Establish `hC1` using `hC (κ.C.P.CYL + 1) κ.C.CTu`. Use `puNZ_of_sDiag β.O.L hC1 (hCG ▸ hG) hD ⟨t1, t2, hH, t4, t5⟩ hmu fun u => ?_` and prove the remaining obligations. Conclude with `hrow _ _ _ _ (le_max_left _ _) (le_max_left _ _) β.D _ u (trueE_of_trueD hD) ⟨⟨β.O.L, rfl, by rw [hCG]; exact le_max_right _ _, by rw [hCG]; linarith⟩, hmu⟩ ⟨t1, t2, hH, t4, t5⟩`.
-/
theorem puNZ_member : GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Bl.Prm hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ _ _ _ b => TruePack (packB b)) → GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p) (fun _ D _ _ _ => GlobalTheory.MiTop.PuNZ D) := by
  intro hRow hL p hTP
  have hR := fun Cg CT : ℝ => hRow Cg (1 / 4) 3 (1 / 2) CT (by norm_num) (by norm_num)
  choose Cf Af Bf hC hrow using hR
  have h1 := GlobalTheory.T.constants_exist_for_bundle hL p (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
  have h2 := GlobalTheory.T.degree_hypothesis_all_members hL p (fun C => Af (C.P.CYL + 1) C.CTu) (fun C => Bf (C.P.CYL + 1) C.CTu)
  have h3 : GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (Bl.IsLinked p)
      (fun κ _ _ _ _ => Cf (κ.C.P.CYL + 1) κ.C.CTu + 1 ≤ κ.C.CGam) :=
    EvP.mono (fun _ _ _ h _ _ _ _ _ => h) (evP_cGam fun a b => Cf a b + 1)
  refine (((hTP.and h1).and h2).and h3).imp fun κ K β c b hk _ _ h => ?_
  obtain ⟨⟨⟨hT, -, -, -, -, -, -, -, ⟨t1, t2, -, t4, t5⟩, -, hmu, -⟩, hH⟩, hG⟩ := h
  have hD : TrueD β.D := trueD_of_truePack _ hT
  have hCG : β.O.L.CGam = κ.C.CGam := by rw [← hk.1]; exact β.val.CGam_eq
  have hC1 := hC (κ.C.P.CYL + 1) κ.C.CTu
  refine puNZ_of_sDiag β.O.L hC1 (hCG ▸ hG) hD ⟨t1, t2, hH, t4, t5⟩ hmu fun u => ?_
  exact hrow _ _ _ _ (le_max_left _ _) (le_max_left _ _) β.D _ u (trueE_of_trueD hD)
    ⟨⟨β.O.L, rfl, by rw [hCG]; exact le_max_right _ _, by rw [hCG]; linarith⟩, hmu⟩ ⟨t1, t2, hH, t4, t5⟩

end GlobalTheory.MiTop
