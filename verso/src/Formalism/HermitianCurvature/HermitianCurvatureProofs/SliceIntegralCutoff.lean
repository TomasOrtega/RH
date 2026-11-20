import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceIntCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBE

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Take `⟨Cp, hCp0, hCp⟩` from `posCoreQ`. Use `⟨Cp, hCp0, ?_⟩` and prove the remaining obligations. Introduce `Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi hi1 w hw p hc hp hle a`. Choose the witnesses or unpack the hypotheses as in `⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by`. Establish `hne : p ≠ []`.

Introduce and unpack `rfl`. Use `hp.2` as an intermediate fact. Simplify using `[D.ptSize] at this`. Use linear arithmetic over natural numbers and integers. Use `⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩` and prove the remaining obligations.

Establish `h1 : 1 ≤ (p.getLast hne).1` using `(hp.1 _ (List.getLast_mem hne)).1`. Rewrite using `[Nat.sub_add_cancel h1]`. Conclude with `(List.dropLast_append_getLast hne).symm`. Take `⟨hpb, hps⟩` from `hp`. Substitute `hps` using the available equality.

Use `set ph := D.ptSize h with hph`. Establish `hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1)` using `Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t`. Establish `ht : t ≠ 0` using `(hpb (n + 1, t) (by simp)).2`. Establish `hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)]))` using `⟨hpb, rfl⟩`. Establish `hlocH` using `Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc`.

Establish `hd0 : ∀ q, D.ptDiag h q ≠ 0` using `fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2`. Use `set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ`. Establish `hsum : ph + (n + 1) + ρ = r` using `by omega`. Establish `hspec` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1`. Establish `hspec'` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1`.

Establish `hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])), ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n` using `n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by`. Introduce `q`. Rewrite using `[hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]`. Distinguish the cases in `h1 : q.val < D.ptSize h`. Rewrite using `[if_pos h1]`.

Establish `e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]`. Conclude with `hspec' ⟨q.val, h1⟩`. Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have` using `q.isLt; omega⟩ := Fin.ext (by simp; omega)`.

Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]`. Simplify using `only [Fin.val_natAdd, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Establish `hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])), Formalism.FourierDecayAlt.P.Dx2.SL.dP (n` using `n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by`. Introduce `q`.

Simplify using `only [D.ptDiag]`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]`. Distinguish the cases in `h1 : q.val < D.ptSize h`. Rewrite using `[if_pos h1]`. Establish `e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩` using `Fin.ext rfl`.

Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]`. Both sides reduce to the same expression. Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have` using `q.isLt; omega⟩ := Fin.ext (by simp; omega)`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]`.

Establish `hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n` using `n) (D.ptDiag h) t q ≠ 0 := by`. Introduce `q`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) q` and prove the remaining obligations. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]`. Conclude with `hd0 i`.

Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]`. Conclude with `ht`. Establish `hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h ++ [(n + 1, t)]) γ = U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) (fun a => a.elim0) γ := by`. Introduce `Gx γ`. Take `⟨-, hT2⟩` from `Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ`.

Unfold `D.sliceAt`. Rewrite using `[dif_pos (by omega), hT2]`. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]`. Establish `e1 : r = ph + (n + 1) + ρ` using `hsum.symm`. Establish `e2 : ph + (n + 1) + ρ = r` using `hsum`.

Establish `hj1 : 1 ≤ ph + (n + 1)` using `by omega`. Take `⟨Θ, hΘ, hΘF⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z') (by omega) w a hj1`. Establish `hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh → ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 → D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g = B.opApply Θ (D.castF e2 (D.cutF T.base χ hh …`. Introduce `hh hsm g hg hD`. Establish `hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε)` using `Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε`.

Establish `h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) = D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 (D.cutF T.base χ hh ε)) (ph + (n + 1)) (by omega) w a`. Rewrite using `[Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a`. Rewrite using `[h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]`. Establish `hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh → ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 → D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g = B.opApply Θ (fun x => ((χ (Gf k (ph + (n …`.

Introduce `hh hsm g hg hD`. Rewrite using `[hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]`. Use `set nd := 2 * r + k + 1 with hnd`. Use `set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs`. Take `⟨b1, b2, b3, b4, b5⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (ph + (n + 1)) hk2 hw (by omega)`.

Establish `hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r`. Simplify using `only [P5.mmUser, P5.nV, hPk, hPr, hnd]`. Establish `hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)`. Simplify using `only [P5.Auser, P5.nV, hPk, hPr, hnd]`. Apply the tactic sequence `try (push_cast; try ring)`.

Establish `hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3` using `by exact_mod_cast b5`. Establish `hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5`. Rewrite using `[hAs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hR1 : (1 : ℝ) ≤ (r : ℝ) + 1` using `by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith`. Establish `hsumR : (((ph + (n + 1) + ρ : ℕ) : ℝ)) = (r : ℝ)` using `by exact_mod_cast hsum`. Take `⟨ε', K, hε', hK0, hQ⟩` from `hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z') (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem) Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As (P5.mmUser P0 N) (P5.Au …`. Rewrite using `[hsumR, hAU, hAsR]`. Establish `hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3` using `one_le_pow₀ hR1`.

Establish `: 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)` using `by positivity`. Use the proof step `nlinarith)`. Use the proof step `(by`. Rewrite using `[hsumR, hAsR]`. Establish `hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4` using `by positivity`.

Establish `hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3` using `by linarith`. Establish `s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤ Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3))`. Apply `mul_le_mul_of_nonneg_left _ (by positivity); linarith` to reduce the goal to its premises. Establish `s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤ Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3))` using `mul_le_mul_of_nonneg_right hCc (by positivity)`. Establish `s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀`.

Establish `hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1` using `by rw [hnd]; push_cast; ring`. Rewrite using `[hndR]`. Conclude with `hA₀`. Use the proof step `nlinarith)`. Establish `hfun : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) (h ++ [(n + 1, t)])) = fun γ => U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi …`.

Introduce `hh`. Rewrite using `[Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]`. Use function extensionality and compare the values at `γ`. Conclude with `hS _ γ`. Establish `hz1 : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z`.

Establish `hzl : T.base.z = D.castV (by omega) (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z)` using `(T.z_lev _ hi).symm`. Rewrite using `[hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _`. Establish `hz1' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z'`. Establish `hzl' : T.base.z' = D.castV (by omega) (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z')` using `(T.z'_lev _ hi).symm`.

Rewrite using `[hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _`. Establish `hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0`. Unfold `G.detM`. Rewrite using `[Matrix.det_isEmpty]`.

Conclude with `one_ne_zero`. Introduce `hh c hsm hcl γ hγ`. Establish `I` using `(hQ (D.castF e2 hh) c (ccle_castF e2 hcl) _ (hFrel hh hsm)).2.2 γ hγ`. Establish `hσ' : ∀ q : Fin (ph + (n + 1)), (D.ptPerm (h ++ [(n + 1, t)]) (Fin.cast hP.symm q)).val = (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n` using `n) (D.ptPerm h) q).val := by`. Introduce `q`.

Use `hσ (Fin.cast hP.symm q)` as an intermediate fact. Simplify using `using this.symm`. Establish `hd' : ∀ q : Fin (ph + (n + 1)), D.ptDiag (h ++ [(n + 1, t)]) (Fin.cast hP.symm q) = Formalism.FourierDecayAlt.P.Dx2.SL.dP (n` using `n) (D.ptDiag h) t q := by`. Introduce `q`. Use `hd (Fin.cast hP.symm q)` as an intermediate fact.

Simplify using `using this.symm`. Establish `I2` using `(Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP.symm _ _ hσ' _ _ hd' (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a)) γ).1 I`. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF] at I2`. Conclude with `I2`.
-/
theorem levQInt : ∃ Cp : ℝ, 0 ≤ Cp ∧ ∀ Cc : ℝ, 16 * Cp ≤ Cc →
    ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (χ : ℝ → ℝ) (A₀ : ℝ) (N : ℕ) (P0 : M.Par),
    P0.k = k → P0.r = r → 2 ≤ k → C6.IsCut0 χ →
    Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀ →
    ∀ ε : ℝ, 0 < ε → ∀ (i : ℕ) (hi : i ≤ r), 1 ≤ i → ∀ (w : List C.Letter), w.length ≤ N →
      ∀ (p : C.LPt) (hc : r - i = r - D.ptSize p), D.IsLocPt p i → ∀ (hle : D.ptSize p ≤ r) (a : Wd.Ix (Fin w.length)),
      ∀ (hh : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), B.CkOn ⊤ (B.GV k r) hh →
        B.CCle A₀ (3 * (11 * (N * (2 * r + k + 1) ^ 2 + (2 * r + k + 1) ^ 3) + 5)) hh c →
      ∀ γ ∈ B.GV k (r - D.ptSize p),
        Integrable (fun ξ : U.Xi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p) =>
          U.psiStar k (r - D.ptSize p) (D.ptPerm p) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') ξ •
            D.castF (by omega) (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) i hi w a)
              (U.gaXi k (r - D.ptSize p) (D.ptPerm p) (D.ptDiag p) ξ (fun a => a.elim0) γ))
          (U.muXi k (D.ptSize p) 0 (r - D.ptSize p) (D.ptPerm p)) := by
  obtain ⟨Cp, hCp0, hCp⟩ := posCoreQ
  refine ⟨Cp, hCp0, ?_⟩
  intro Cc hCc k r Wp Wq _ _ _ _ _ _ T χ A₀ N P0 hPk hPr hk2 hχ hA₀ ε hε i hi hi1 w hw p hc hp hle a

  obtain ⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by
    have hne : p ≠ [] := by
      rintro rfl
      have := hp.2
      simp [D.ptSize] at this
      omega
    refine ⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩
    have h1 : 1 ≤ (p.getLast hne).1 := (hp.1 _ (List.getLast_mem hne)).1
    rw [Nat.sub_add_cancel h1]
    exact (List.dropLast_append_getLast hne).symm
  obtain ⟨hpb, hps⟩ := hp
  subst hps
  set ph := D.ptSize h with hph
  have hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1) := Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t
  have ht : t ≠ 0 := (hpb (n + 1, t) (by simp)).2
  have hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)])) := ⟨hpb, rfl⟩
  have hlocH := Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc
  have hd0 : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2
  set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ
  have hsum : ph + (n + 1) + ρ = r := by omega
  have hspec := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1
  have hspec' := (Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1
  have hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by
    intro q
    rw [hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]
      exact hspec' ⟨q.val, h1⟩
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]
      simp only [Fin.val_natAdd, Fin.val_rev]
      omega
  have hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])),
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by
    intro q
    simp only [D.ptDiag]
    rw [Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]
    by_cases h1 : q.val < D.ptSize h
    · rw [if_pos h1]
      have e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩ := Fin.ext rfl
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; rfl
    · rw [if_neg h1]
      have e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have := q.isLt; omega⟩ :=
        Fin.ext (by simp; omega)
      rw [e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]
  have hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q ≠ 0 := by
    intro q
    refine Fin.addCases (fun i => ?_) (fun i => ?_) q
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]; exact hd0 i
    · simp only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]; exact ht
  have hS : ∀ (Gx : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k ρ), D.sliceAt k r T.base.z T.base.z' Gx (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gx) (fun a => a.elim0) γ := by
    intro Gx γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gx) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  have hU : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (D.castF e2 (D.cutF T.base χ hh ε)) g := by
    intro hh hsm g hg hD
    have hFc : B.CkOn ⊤ (B.GV k r) (D.cutF T.base χ hh ε) := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF T.base hχ hsm ε
    have h1 : D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) =
        D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
          (D.castF e2 (D.cutF T.base χ hh ε)) (ph + (n + 1)) (by omega) w a := by
      rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
      exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a
    rw [h1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFc) g hg hD]
  have hFrel : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) hh →
      ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) g =
        B.opApply Θ (fun x => ((χ (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z)
          (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 hh x) g := by
    intro hh hsm g hg hD
    rw [hU hh hsm g hg hD, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_cutF e2]
  set nd := 2 * r + k + 1 with hnd
  set As := 11 * (N * nd ^ 2 + nd ^ 3) + 5 with hAs
  obtain ⟨b1, b2, b3, b4, b5⟩ := Formalism.FourierDecayAlt.P.JCTx6.Link2.budgetAs r k N w.length (ph + (n + 1)) hk2 hw (by omega)
  have hmmU : P5.mmUser P0 N = 5 + 3 * (r + 1) * (N + 2) * nd + N * r := by
    simp only [P5.mmUser, P5.nV, hPk, hPr, hnd]
  have hAU : P5.Auser P0 N = 127 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by
    simp only [P5.Auser, P5.nV, hPk, hPr, hnd]
    try (push_cast; try ring)
  have hX1 : (1 : ℝ) ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by exact_mod_cast b5
  have hAsR : (As : ℝ) = 11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5 := by
    rw [hAs]; push_cast; ring
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by have : (0 : ℝ) ≤ r := Nat.cast_nonneg r; linarith
  have hsumR : (((ph + (n + 1) + ρ : ℕ) : ℝ)) = (r : ℝ) := by exact_mod_cast hsum
  obtain ⟨ε', K, hε', hK0, hQ⟩ := hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
    (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
    Θ _ _ hΘ χ A₀ ε hχ hε (D.ptPerm h) (D.ptDiag h) t hd0 ht As (P5.mmUser P0 N) (P5.Auser P0 N + 1)
    b1 b2 (by rw [hmmU]; exact b3) (by rw [hsum]; exact b4)
    (by
      rw [hsumR, hAU, hAsR]
      have hR3 : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
      have : 0 ≤ ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) := by positivity
      nlinarith)
    (by
      rw [hsumR, hAsR]
      have hR4 : 0 ≤ ((r : ℝ) + 1) ^ 4 := by positivity
      have hX0 : 0 ≤ (N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3 := by linarith
      have s1 : Cp * ((r : ℝ) + 1) ^ 4 * (11 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) + 5) ≤
          Cp * ((r : ℝ) + 1) ^ 4 * (16 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      have s2 : 16 * Cp * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) ≤
          Cc * (((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3)) :=
        mul_le_mul_of_nonneg_right hCc (by positivity)
      have s3 : Cc * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (nd : ℝ) ^ 2 + (nd : ℝ) ^ 3) ≤ A₀ := by
        have hndR : (nd : ℝ) = 2 * (r : ℝ) + k + 1 := by rw [hnd]; push_cast; ring
        rw [hndR]; exact hA₀
      nlinarith)
  have hfun : ∀ hh : B.Mat k r → (Wq →L[ℂ] Wp),
      D.castF hc (D.sliceAt k r T.base.z T.base.z'
        (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a) (h ++ [(n + 1, t)])) =
      fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε) (D.ptSize (h ++ [(n + 1, t)])) hi w a))
        (fun a => a.elim0) γ := by
    intro hh
    rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
    funext γ
    exact hS _ γ
  have hz1 : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z := by
    have hzl : T.base.z = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z) :=
      (T.z_lev _ hi).symm
    rw [hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hz1' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z' := by
    have hzl' : T.base.z' = D.castV (by omega)
        (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z') :=
      (T.z'_lev _ hi).symm
    rw [hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _
  have hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0 := by
    unfold G.detM; rw [Matrix.det_isEmpty]; exact one_ne_zero
  intro hh c hsm hcl γ hγ
  have I := (hQ (D.castF e2 hh) c (ccle_castF e2 hcl) _ (hFrel hh hsm)).2.2 γ hγ
  have hσ' : ∀ q : Fin (ph + (n + 1)), (D.ptPerm (h ++ [(n + 1, t)]) (Fin.cast hP.symm q)).val =
      (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h) q).val := by
    intro q; have := hσ (Fin.cast hP.symm q); simpa using this.symm
  have hd' : ∀ q : Fin (ph + (n + 1)), D.ptDiag (h ++ [(n + 1, t)]) (Fin.cast hP.symm q) =
      Formalism.FourierDecayAlt.P.Dx2.SL.dP (n := n) (D.ptDiag h) t q := by
    intro q; have := hd (Fin.cast hP.symm q); simpa using this.symm
  have I2 := (Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP.symm _ _ hσ' _ _ hd' (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (D.castF e2 (D.uwG k r T.base.z T.base.z' (D.cutF T.base χ hh ε)
      (D.ptSize (h ++ [(n + 1, t)])) hi w a)) γ).1 I
  simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF] at I2
  exact I2

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

/- English proof (translation)
Take `⟨Cp, hCp0, hL⟩` from `Formalism.FourierDecayAlt.P.FormNormSumIdentities.levQInt`. Introduce `Wp Wq _ _ _ _ _ _ P0 T w f χ ε i hi hi1 hk2 hfs hR hχ hε p hp e γ hγ`. Take `⟨R, hR⟩` from `hR`. Take `⟨c, hcl⟩` from `Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hfs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P0.k P0.r R) (fun g hg hgC => by`. Assume the negation of the conclusion as `hne`.

Conclude with `hgC (hR g hg hne))`. Use the proof step `((16 * Cp) * ((P0.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 + (2 * (P0.r : ℝ) + P0.k + 1) ^ 3))`. Use the proof step `(3 * (11 * (w.length * (2 * P0.r + P0.k + 1) ^ 2 + (2 * P0.r + P0.k + 1) ^ 3) + 5))`. Establish `hle : D.ptSize p ≤ P0.r` using `hp.2 ▸ hi`. Establish `hc : P0.r - i = P0.r - D.ptSize p` using `by rw [hp.2]`.

Conclude with `hL (16 * Cp) le_rfl P0.k P0.r Wp Wq T χ _ w.length P0 rfl rfl hk2 hχ le_rfl ε hε i hi hi1 w le_rfl p hc hp hle e f c hfs hcl γ hγ`.
-/
theorem slice_integral_cutoff : Formalism.FourierDecayAlt.P.FormNormSumIdentities.SliceIntCut := by
  obtain ⟨Cp, hCp0, hL⟩ := Formalism.FourierDecayAlt.P.FormNormSumIdentities.levQInt
  intro Wp Wq _ _ _ _ _ _ P0 T w f χ ε i hi hi1 hk2 hfs hR hχ hε p hp e γ hγ
  obtain ⟨R, hR⟩ := hR
  obtain ⟨c, hcl⟩ := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hfs (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P0.k P0.r R)
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    ((16 * Cp) * ((P0.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P0.r : ℝ) + P0.k + 1) ^ 2 +
      (2 * (P0.r : ℝ) + P0.k + 1) ^ 3))
    (3 * (11 * (w.length * (2 * P0.r + P0.k + 1) ^ 2 + (2 * P0.r + P0.k + 1) ^ 3) + 5))
  have hle : D.ptSize p ≤ P0.r := hp.2 ▸ hi
  have hc : P0.r - i = P0.r - D.ptSize p := by rw [hp.2]
  exact hL (16 * Cp) le_rfl P0.k P0.r Wp Wq T χ _ w.length P0 rfl rfl hk2 hχ le_rfl ε hε i hi hi1 w le_rfl p hc hp
    hle e f c hfs hcl γ hγ

end Formalism.FourierDecayAlt.P
