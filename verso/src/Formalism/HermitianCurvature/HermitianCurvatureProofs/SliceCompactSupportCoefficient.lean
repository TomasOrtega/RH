import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBE

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Take `⟨Cp, _, hCp⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Pos.posCore Formalism.FourierDecayAlt.P.JCTx6.Int.intG Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable`. Choose the witnesses or unpack the hypotheses as in `⟨h, n, t, rfl⟩ : ∃ (h : C.LPt) (n : ℕ) (t : ℂ), p = h ++ [(n + 1, t)] := by`. Establish `hne : p ≠ []`. Introduce and unpack `rfl`. Use `hp.2` as an intermediate fact.

Simplify using `[D.ptSize] at this`. Use linear arithmetic over natural numbers and integers. Use `⟨p.dropLast, (p.getLast hne).1 - 1, (p.getLast hne).2, ?_⟩` and prove the remaining obligations. Establish `h1 : 1 ≤ (p.getLast hne).1` using `(hp.1 _ (List.getLast_mem hne)).1`. Rewrite using `[Nat.sub_add_cancel h1]`.

Conclude with `(List.dropLast_append_getLast hne).symm`. Take `⟨hpb, hps⟩` from `hp`. Substitute `hps` using the available equality. Use `set ph := D.ptSize h with hph`. Establish `hP : D.ptSize (h ++ [(n + 1, t)]) = ph + (n + 1)` using `Formalism.FourierDecayAlt.P.Dx2.SL.ptSize_append h (n + 1) t`.

Establish `ht : t ≠ 0` using `(hpb (n + 1, t) (by simp)).2`. Establish `hloc : D.IsLocPt (h ++ [(n + 1, t)]) (D.ptSize (h ++ [(n + 1, t)]))` using `⟨hpb, rfl⟩`. Establish `hlocH` using `Formalism.FourierDecayAlt.P.Dx2.SL.isLocPt_head hloc`. Establish `hd0 : ∀ q, D.ptDiag h q ≠ 0` using `fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hlocH.1 q q.2`. Use `set ρ := r - D.ptSize (h ++ [(n + 1, t)]) with hρ`.

Establish `hsum : ph + (n + 1) + ρ = r` using `by omega`. Establish `hspec` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hloc).1`. Establish `hspec'` using `(Formalism.FourierDecayAlt.P.ptPerm_spec _ _ hlocH).1`. Establish `hσ : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])), ((Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n` using `n) (D.ptPerm h)) (Fin.cast hP q)).val = (D.ptPerm (h ++ [(n + 1, t)]) q).val := by`. Introduce `q`.

Rewrite using `[hspec q, Formalism.FourierDecayAlt.P.Dx2.SL.partner_append (n + 1) t h q.val (by have := q.isLt; omega)]`. Distinguish the cases in `h1 : q.val < D.ptSize h`. Rewrite using `[if_pos h1]`. Establish `e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_castAdd]`.

Conclude with `hspec' ⟨q.val, h1⟩`. Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have` using `q.isLt; omega⟩ := Fin.ext (by simp; omega)`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.blockPerm_natAdd]`. Simplify using `only [Fin.val_natAdd, Fin.val_rev]`.

Use linear arithmetic over natural numbers and integers. Establish `hd : ∀ q : Fin (D.ptSize (h ++ [(n + 1, t)])), Formalism.FourierDecayAlt.P.Dx2.SL.dP (n` using `n) (D.ptDiag h) t (Fin.cast hP q) = D.ptDiag (h ++ [(n + 1, t)]) q := by`. Introduce `q`. Simplify using `only [D.ptDiag]`. Rewrite using `[Formalism.FourierDecayAlt.P.Dx2.SL.scal_append (n + 1) t h q.val (by have := q.isLt; omega)]`.

Distinguish the cases in `h1 : q.val < D.ptSize h`. Rewrite using `[if_pos h1]`. Establish `e : Fin.cast hP q = Fin.castAdd (n + 1) ⟨q.val, h1⟩` using `Fin.ext rfl`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]`. Both sides reduce to the same expression.

Rewrite using `[if_neg h1]`. Establish `e : Fin.cast hP q = Fin.natAdd (D.ptSize h) ⟨q.val - D.ptSize h, by have` using `q.isLt; omega⟩ := Fin.ext (by simp; omega)`. Rewrite using `[e, Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]`. Establish `hdP : ∀ q, Formalism.FourierDecayAlt.P.Dx2.SL.dP (n` using `n) (D.ptDiag h) t q ≠ 0 := by`. Introduce `q`.

Use `Fin.addCases (fun i => ?_) (fun i => ?_) q` and prove the remaining obligations. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_left]`. Conclude with `hd0 i`. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.dP, Fin.addCases_right]`. Conclude with `ht`.

Use `set Gw := D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi w a with hGw`. Establish `hS : ∀ γ : B.Mat k ρ, D.sliceAt k r T.base.z T.base.z' Gw (h ++ [(n + 1, t)]) γ = U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gw) (fun a => a.elim0) γ := by`. Introduce `γ`. Take `⟨-, hT2⟩` from `Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gw) γ`. Unfold `D.sliceAt`.

Rewrite using `[dif_pos (by omega), hT2]`. Simplify using `only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]`. Establish `e1 : r = ph + (n + 1) + ρ` using `hsum.symm`. Establish `e2 : ph + (n + 1) + ρ = r` using `hsum`. Establish `hj1 : 1 ≤ ph + (n + 1)` using `by omega`.

Take `⟨Θ, hΘ, hΘF⟩` from `Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z') (by omega) w a hj1`. Take `⟨hFs, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩` from `hF`. Establish `hG1 : D.castF e2 Gw = D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 F) (ph + (n + 1)) (by omega) w a`. Rewrite using `[hGw, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a`.

Establish `hGF : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 → D.castF e2 Gw g = B.opApply Θ (D.castF e2 F) g`. Introduce `g hg hD`. Rewrite using `[hG1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFs) g hg hD]`. Establish `hcut : ∀ x ∈ B.GV k (ph + (n + 1) + ρ), D.castF e2 F x = ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 F x`. Introduce `x hx`.

Distinguish the cases in `h0 : D.castF e2 F x = 0`. Rewrite using `[h0, smul_zero]`. Establish `hxG` using `castM_GV e2 hx`. Establish `h1 : ε ≤ Gf k r T.base.z T.base.z' (D.castM e2 x)` using `hGε _ hxG h0`. Rewrite using `[show Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x = Gf k r T.base.z T.base.z' (D.castM e2 x) from Gf_castM e2 _ _ x]`.

Rewrite using `[Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation.2.2 _ ((one_le_div hε).2 h1)]`. Simplify using the standard rewrite rules. Establish `hFrel : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 → D.castF e2 Gw g = B.opApply Θ (fun x => ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 F x) g`. Introduce `g hg hD`. Rewrite using `[hGF g hg hD]`.

Conclude with `opApply_congrGV Θ hcut g hg`. Establish `hfA : ∀ (A₀ : ℝ) (m : ℕ), B.InCC A₀ m (D.castF e2 F)` using `fun A₀ m => Formalism.FourierDecayAlt.P.JCTx6.Link2.inCC_castF e2 (Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs (isCompact_gN_le k r R) (fun g hg hgC => by`. Assume the negation of the conclusion as `h0`. Conclude with `hgC (hR g hg h0)) A₀ m)`. Establish `hmain : ∀ mm : ℕ, ∃ ε' : ℝ, 0 < ε' ∧ B.CkOn (mm : ℕ∞) (B.GV k ρ) (fun γ => U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 Gw) (fun a => a.elim0) γ) ∧ ∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ …`.

Introduce `mm`. Take `⟨ε', hε', h1, -, h3⟩` from `hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z') (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem) Θ _ _ hΘ (D.castF e2 F) Formalism.FourierDecayAlt.P.Topx2.chi0 (Cp * (((ph + (n + 1 …`. Conclude with `⟨ε', hε', h1, h3⟩`. Take `⟨Cs, hCs⟩` from `Formalism.FourierDecayAlt.P.block3_apply_embedding k (ph + (n + 1) + 0) ρ (by omega)`. Establish `hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0`.

Unfold `G.detM`. Rewrite using `[Matrix.det_isEmpty]`. Conclude with `one_ne_zero`. Use `set dh := (U.hMat (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t)).det with hdh`. Establish `hdh0 : dh ≠ 0` using `Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hdP`.

Use `set bd : ℝ := max Cs 0 * (max R 1) ^ (2 * (ph + (n + 1) + 0) + 1) / min 1 ‖dh * G.detM (fun a => a.elim0 : G.Mat 0)‖ ^ 2 with hbd`. Establish `hsupp : ∀ γ ∈ B.GV k ρ, U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 Gw) (fun a => a.elim0) γ ≠ 0 → B.gN γ ≤ bd := by`. Introduce `γ hγ hne`. Assume the negation of the conclusion as `hbig`. Apply `hne` to reduce the goal to its premises.

Establish `key : ∀ ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)), D.castF e2 Gw (U.gaXi (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ) = 0 := by`. Introduce `ξ`. Use `set g := U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ (fun a => a.elim0) γ with hg`. Establish `hgG : g ∈ B.GV k (ph + (n + 1) + 0 + ρ)` using `Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation _ _ hdP ξ _ hZ0 hγ`. Establish `hDj : U.DjU k (ph + (n + 1) + 0) ρ g = dh * G.detM (fun a => a.elim0 : G.Mat 0)` using `Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice _ _ ξ _ γ`.

Establish `hdetZ : (U.ZjH (p` using `ph + (n + 1)) (s := 0) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ.2 (fun a => a.elim0 : G.Mat 0)).det = dh * G.detM (fun a => a.elim0 : G.Mat 0) := Formalism.FourierDecayAlt.P.level_determinant_z _ _ _ _ _ _`. Establish `hgR : R < B.gN g`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`. Apply `hbig` to reduce the goal to its premises.

Establish `h5 : B.gN γ ≤ Cs * B.gN g ^ (2 * (ph + (n + 1) + 0) + 1) / min 1 ‖(U.ZjH (p` using `ph + (n + 1)) (s := 0) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ.2 (fun a => a.elim0 : G.Mat 0)).det‖ ^ 2 := (hCs ξ.1.1 ξ.1.2 _ γ (by rw [hdetZ]; exact mul_ne_zero hdh0 hZ0) hγ).2.2.2.2`. Rewrite `h5` using `[hdetZ]`. Establish `hg0 : 0 ≤ B.gN g` using `Real.sqrt_nonneg _`. Establish `hm : 0 ≤ min 1 ‖dh * G.detM (fun a => a.elim0 : G.Mat 0)‖ ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_max_left _ _`. Use `_ ≤ bd := by`. Rewrite using `[hbd]`. Apply `div_le_div_of_nonneg_right _ hm` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ (le_max_right _ _)` to reduce the goal to its premises.

Conclude with `pow_le_pow_left₀ hg0 (hle.trans (le_max_left _ _)) _`. Rewrite using `[hGF g hgG (by intro h0; apply mul_ne_zero hdh0 hZ0; rw [← hDj]; exact h0)]`. Use `opApply_zero_near Θ (U := {x | R < B.gN x}) (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous) (fun x hx hxU => ?_) g hgG hgR` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Use `hR _ (castM_GV e2 hx) h0` as an intermediate fact.

Rewrite `this` using `[gN_castM]`. Conclude with `absurd hxU (not_lt.2 this)`. Unfold `U.PhiFun`. Simplify using `only [key, smul_zero, MeasureTheory.integral_zero]`. Establish `hfun : D.castF hc (D.sliceAt k r T.base.z T.base.z' Gw (h ++ [(n + 1, t)])) = fun γ => U.PhiFun (p` using `ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z') (D.castF e2 Gw) (fun a => a.elim0) γ := by`.

Rewrite using `[Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]`. Use function extensionality and compare the values at `γ`. Conclude with `hS γ`. Rewrite using `[hfun]`. Establish `hz1 : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z) = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z`.

Establish `hzl : T.base.z = D.castV (by omega) (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z)` using `(T.z_lev _ hi).symm`. Rewrite using `[hzl, Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _`. Establish `hz1' : U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z') = (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z'`. Establish `hzl' : T.base.z' = D.castV (by omega) (liftVec k (D.ptSize (h ++ [(n + 1, t)])) ρ (T.bs (D.ptSize (h ++ [(n + 1, t)]))).z')` using `(T.z'_lev _ hi).symm`.

Rewrite using `[hzl', Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV]`. Conclude with `Formalism.FourierDecayAlt.P.JCTx6.Link2.lowV_liftVec hP.symm _ _`. Take `⟨ε', hε', -, h3⟩` from `hmain 0`. Use `⟨ckOn_top_of_nat fun m => (hmain m).choose_spec.2.1, ⟨bd, fun γ hγ hne => hsupp γ hγ hne⟩, ⟨ε', hε', fun γ hγ hne => ?_⟩⟩` and prove the remaining obligations. Use `h3 γ hγ hne` as an intermediate fact.

Rewrite `this` using `[hz1, hz1']`. Then use the resulting hypothesis.
-/
theorem slice_pos_cpt (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef T.base F)
    (i : ℕ) (hi : i ≤ r) (hi1 : 1 ≤ i) (w : List C.Letter) (p : C.LPt) (hc : r - i = r - D.ptSize p)
    (hp : D.IsLocPt p i) (a : Wd.Ix (Fin w.length)) :
    KB.CptCoef (T.bs i)
      (D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F i hi w a) p)) := by
  obtain ⟨Cp, _, hCp⟩ := Formalism.FourierDecayAlt.P.JCTx6.Pos.posCore Formalism.FourierDecayAlt.P.JCTx6.Int.intG Formalism.FourierDecayAlt.P.JCTx6.Int.orbit_slice_integrable

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
  set Gw := D.uwG k r T.base.z T.base.z' F (D.ptSize (h ++ [(n + 1, t)])) hi w a with hGw
  have hS : ∀ γ : B.Mat k ρ, D.sliceAt k r T.base.z T.base.z' Gw (h ++ [(n + 1, t)]) γ =
      U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z')
        (D.castF (by omega) Gw) (fun a => a.elim0) γ := by
    intro γ
    obtain ⟨-, hT2⟩ := Formalism.FourierDecayAlt.P.Dx2.SL.phi_transport (k := k) (ρ := ρ) hP _ _ hσ _ _ hd
      (D.castV (by omega) T.base.z) (D.castV (by omega) T.base.z') (D.castF (by omega) Gw) γ
    unfold D.sliceAt
    rw [dif_pos (by omega), hT2]
    simp only [Formalism.FourierDecayAlt.P.Dx2.SL.castV_castV, Formalism.FourierDecayAlt.P.Dx2.SL.castF_castF]
  have e1 : r = ph + (n + 1) + ρ := hsum.symm
  have e2 : ph + (n + 1) + ρ = r := hsum
  have hj1 : 1 ≤ ph + (n + 1) := by omega
  obtain ⟨Θ, hΘ, hΘF⟩ := Formalism.FourierDecayAlt.P.JCTx6.Let.lettersDD k (ph + (n + 1)) ρ Wp Wq (D.castV e1 T.base.z)
    (D.castV e1 T.base.z') (by omega) w a hj1
  obtain ⟨hFs, ⟨R, hR⟩, ⟨ε, hε, hGε⟩⟩ := hF
  have hG1 : D.castF e2 Gw = D.uwG k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
      (D.castF e2 F) (ph + (n + 1)) (by omega) w a := by
    rw [hGw, Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_uwG e2 _ _ _ _ hi (by omega)]
    exact Formalism.FourierDecayAlt.P.JCTx6.Link2.uwG_level _ _ _ hP _ _ w a
  have hGF : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 Gw g = B.opApply Θ (D.castF e2 F) g := by
    intro g hg hD
    rw [hG1, hΘF _ (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFs) g hg hD]
  have hcut : ∀ x ∈ B.GV k (ph + (n + 1) + ρ), D.castF e2 F x =
      ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) •
        D.castF e2 F x := by
    intro x hx
    by_cases h0 : D.castF e2 F x = 0
    · rw [h0, smul_zero]
    · have hxG := castM_GV e2 hx
      have h1 : ε ≤ Gf k r T.base.z T.base.z' (D.castM e2 x) := hGε _ hxG h0
      rw [show Gf k (ph + (n + 1) + ρ) (D.castV e1 T.base.z) (D.castV e1 T.base.z') x =
        Gf k r T.base.z T.base.z' (D.castM e2 x) from Gf_castM e2 _ _ x]
      rw [Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation.2.2 _ ((one_le_div hε).2 h1)]
      simp
  have hFrel : ∀ g ∈ B.GV k (ph + (n + 1) + ρ), U.DjU k (ph + (n + 1)) ρ g ≠ 0 →
      D.castF e2 Gw g = B.opApply Θ (fun x => ((Formalism.FourierDecayAlt.P.Topx2.chi0 (Gf k (ph + (n + 1) + ρ)
        (D.castV e1 T.base.z) (D.castV e1 T.base.z') x / ε) : ℝ) : ℂ) • D.castF e2 F x) g := by
    intro g hg hD
    rw [hGF g hg hD]
    exact opApply_congrGV Θ hcut g hg
  have hfA : ∀ (A₀ : ℝ) (m : ℕ), B.InCC A₀ m (D.castF e2 F) := fun A₀ m =>
    Formalism.FourierDecayAlt.P.JCTx6.Link2.inCC_castF e2 (Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs (isCompact_gN_le k r R)
      (fun g hg hgC => by
        by_contra h0
        exact hgC (hR g hg h0)) A₀ m)

  have hmain : ∀ mm : ℕ, ∃ ε' : ℝ, 0 < ε' ∧
      B.CkOn (mm : ℕ∞) (B.GV k ρ) (fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ
        (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z)
        (D.castV e1 T.base.z') (D.castF e2 Gw) (fun a => a.elim0) γ) ∧
      ∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ
        (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z)
        (D.castV e1 T.base.z') (D.castF e2 Gw) (fun a => a.elim0) γ ≠ 0 →
        ε' ≤ Gf k ρ (U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z))
          (U.lowV k (ph + (n + 1)) ρ (D.castV e1 T.base.z')) γ := by
    intro mm
    obtain ⟨ε', hε', h1, -, h3⟩ := hCp k ph n ρ Wp Wq (D.castV e1 T.base.z) (D.castV e1 T.base.z')
      (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z_mem) (Formalism.FourierDecayAlt.P.Dx1.SN.castV_inWb e1 _ T.base.z'_mem)
      Θ _ _ hΘ (D.castF e2 F) Formalism.FourierDecayAlt.P.Topx2.chi0
      (Cp * (((ph + (n + 1) + ρ : ℕ) : ℝ) + 1) ^ 4 *
        ((w.length * (ph + (n + 1)) + ((w.length * (ph + (n + 1)) + w.length * (ph + (n + 1)) ^ 2) +
          (ph + (n + 1)) * (w.length * (ph + (n + 1)))) + mm + (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3 : ℕ) : ℝ))
      ε (Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_castF e2 hFs) (fun m => hfA _ m) Formalism.FourierDecayAlt.P.Topx2.base_cutoff_is_truncation hε
      (D.castF e2 Gw) hFrel (D.ptPerm h) (D.ptDiag h) t hd0 ht
      (w.length * (ph + (n + 1)) + ((w.length * (ph + (n + 1)) + w.length * (ph + (n + 1)) ^ 2) +
          (ph + (n + 1)) * (w.length * (ph + (n + 1)))) + mm + (2 * (ph + (n + 1) + ρ) + k + 1) ^ 3)
      mm 0 (by omega) (by omega) (by omega) (by omega) (by positivity) le_rfl
    exact ⟨ε', hε', h1, h3⟩

  obtain ⟨Cs, hCs⟩ := Formalism.FourierDecayAlt.P.block3_apply_embedding k (ph + (n + 1) + 0) ρ (by omega)
  have hZ0 : G.detM (fun a => a.elim0 : G.Mat 0) ≠ 0 := by
    unfold G.detM; rw [Matrix.det_isEmpty]; exact one_ne_zero
  set dh := (U.hMat (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (n := n) (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t)).det
    with hdh
  have hdh0 : dh ≠ 0 := Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hdP
  set bd : ℝ := max Cs 0 * (max R 1) ^ (2 * (ph + (n + 1) + 0) + 1) / min 1 ‖dh * G.detM (fun a => a.elim0 : G.Mat 0)‖ ^ 2
    with hbd
  have hsupp : ∀ γ ∈ B.GV k ρ, U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ
        (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z)
        (D.castV e1 T.base.z') (D.castF e2 Gw) (fun a => a.elim0) γ ≠ 0 → B.gN γ ≤ bd := by
    intro γ hγ hne
    by_contra hbig
    apply hne
    have key : ∀ ξ : U.Xi k (ph + (n + 1)) 0 ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)),
        D.castF e2 Gw (U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ
          (fun a => a.elim0) γ) = 0 := by
      intro ξ
      set g := U.gaXi (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ
          (fun a => a.elim0) γ with hg
      have hgG : g ∈ B.GV k (ph + (n + 1) + 0 + ρ) :=
        Formalism.FourierDecayAlt.P.Ux10.gaXi_mem Formalism.FourierDecayAlt.P.slice_membership Formalism.FourierDecayAlt.P.radical_parametrisation _ _ hdP ξ _ hZ0 hγ
      have hDj : U.DjU k (ph + (n + 1) + 0) ρ g = dh * G.detM (fun a => a.elim0 : G.Mat 0) :=
        Formalism.FourierDecayAlt.P.Ux10.DjU_gaXi Formalism.FourierDecayAlt.P.hat_z_on_slice _ _ ξ _ γ
      have hdetZ : (U.ZjH (p := ph + (n + 1)) (s := 0) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ.2
          (fun a => a.elim0 : G.Mat 0)).det = dh * G.detM (fun a => a.elim0 : G.Mat 0) :=
        Formalism.FourierDecayAlt.P.level_determinant_z _ _ _ _ _ _
      have hgR : R < B.gN g := by
        by_contra hle
        push_neg at hle
        apply hbig
        have h5 : B.gN γ ≤ Cs * B.gN g ^ (2 * (ph + (n + 1) + 0) + 1) /
            min 1 ‖(U.ZjH (p := ph + (n + 1)) (s := 0) (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h)) (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) ξ.2
              (fun a => a.elim0 : G.Mat 0)).det‖ ^ 2 :=
          (hCs ξ.1.1 ξ.1.2 _ γ (by rw [hdetZ]; exact mul_ne_zero hdh0 hZ0) hγ).2.2.2.2
        rw [hdetZ] at h5
        have hg0 : 0 ≤ B.gN g := Real.sqrt_nonneg _
        have hm : 0 ≤ min 1 ‖dh * G.detM (fun a => a.elim0 : G.Mat 0)‖ ^ 2 := by positivity
        calc B.gN γ ≤ _ := h5
          _ ≤ max Cs 0 * B.gN g ^ (2 * (ph + (n + 1) + 0) + 1) /
              min 1 ‖dh * G.detM (fun a => a.elim0 : G.Mat 0)‖ ^ 2 := by
            gcongr
            exact le_max_left _ _
          _ ≤ bd := by
            rw [hbd]
            apply div_le_div_of_nonneg_right _ hm
            apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
            exact pow_le_pow_left₀ hg0 (hle.trans (le_max_left _ _)) _
      rw [hGF g hgG (by intro h0; apply mul_ne_zero hdh0 hZ0; rw [← hDj]; exact h0)]
      refine opApply_zero_near Θ (U := {x | R < B.gN x}) (isOpen_lt continuous_const Formalism.FourierDecayAlt.P.B6.gN_continuous)
        (fun x hx hxU => ?_) g hgG hgR
      by_contra h0
      have := hR _ (castM_GV e2 hx) h0
      rw [gN_castM] at this
      exact absurd hxU (not_lt.2 this)
    unfold U.PhiFun
    simp only [key, smul_zero, MeasureTheory.integral_zero]

  have hfun : D.castF hc (D.sliceAt k r T.base.z T.base.z' Gw (h ++ [(n + 1, t)])) =
      fun γ => U.PhiFun (p := ph + (n + 1)) (s := 0) k ρ (Formalism.FourierDecayAlt.P.Dx2.SL.sigP (D.ptPerm h))
        (Formalism.FourierDecayAlt.P.Dx2.SL.dP (D.ptDiag h) t) (D.castV e1 T.base.z) (D.castV e1 T.base.z')
        (D.castF e2 Gw) (fun a => a.elim0) γ := by
    rw [Formalism.FourierDecayAlt.P.JCTx6.Link2.castF_self]
    funext γ
    exact hS γ
  rw [hfun]
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
  obtain ⟨ε', hε', -, h3⟩ := hmain 0
  refine ⟨ckOn_top_of_nat fun m => (hmain m).choose_spec.2.1, ⟨bd, fun γ hγ hne => hsupp γ hγ hne⟩,
    ⟨ε', hε', fun γ hγ hne => ?_⟩⟩
  have := h3 γ hγ hne
  rwa [hz1, hz1'] at this

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `rfl : p = [] := by`. Consider the cases of `p with`. Consider the case `nil => rfl`. Consider the case `cons b p`. It suffices to derive a contradiction.

Establish `h1` using `(hp.1 b (by simp)).1`. Establish `h2` using `hp.2`. Simplify using `[D.ptSize] at h2`. Use linear arithmetic over natural numbers and integers. Establish `hfun : (D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F 0 hi w a) []) : B.Mat k (r - 0) → (Wq →L[ℂ] Wp)) = (if a = Wd.e1 then F else 0)`.

Use function extensionality and compare the values at `γ`. Establish `hcm : D.castM (k` using `k) (a := r - 0) (b := r - D.ptSize []) hc γ = γ := by`. Use extensionality with `i j`. Both sides reduce to the same expression. Simplify using `only [D.castF]`.

Rewrite using `[hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k r _ _ T.base.z_mem T.base.z'_mem, Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]`. Rewrite using `[hfun]`. Use `split_ifs`. Conclude with `hF`. Conclude with `⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩, ⟨0, fun g _ h => (h rfl).elim⟩, ⟨1, one_pos, fun g _ h => (h rfl).elim⟩⟩`.
-/
theorem slice_level_zero_compact_support (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (T : D.LevTower k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef T.base F)
    (hi : 0 ≤ r) (w : List C.Letter) (p : C.LPt) (hc : r - 0 = r - D.ptSize p)
    (hp : D.IsLocPt p 0) (a : Wd.Ix (Fin w.length)) :
    KB.CptCoef (T.bs 0)
      (D.castF hc (D.sliceAt k r T.base.z T.base.z' (D.uwG k r T.base.z T.base.z' F 0 hi w a) p)) := by
  obtain rfl : p = [] := by
    cases p with
    | nil => rfl
    | cons b p =>
      exfalso
      have h1 := (hp.1 b (by simp)).1
      have h2 := hp.2
      simp [D.ptSize] at h2
      omega
  have hfun : (D.castF hc (D.sliceAt k r T.base.z T.base.z'
      (D.uwG k r T.base.z T.base.z' F 0 hi w a) []) : B.Mat k (r - 0) → (Wq →L[ℂ] Wp)) =
      (if a = Wd.e1 then F else 0) := by
    funext γ
    have hcm : D.castM (k := k) (a := r - 0) (b := r - D.ptSize []) hc γ = γ := by
      ext i j; rfl
    simp only [D.castF]
    rw [hcm, Formalism.FourierDecayAlt.P.Dx1.SN.sliceAt_nil k r _ _ T.base.z_mem T.base.z'_mem, Formalism.FourierDecayAlt.P.Dx1.LZ.uwG_zero]
  rw [hfun]
  split_ifs
  · exact hF
  · exact ⟨fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
      ⟨0, fun g _ h => (h rfl).elim⟩, ⟨1, one_pos, fun g _ h => (h rfl).elim⟩⟩

end Formalism.FourierDecayAlt.P.PBE

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P p F j hj w a ha hF e`. Unfold `Formalism.FourierDecayAlt.KB.slv`. Break down `Nat.eq_zero_or_pos j with h0 | h1` into its components or cases. Substitute `h0` using the available equality. Conclude with `Formalism.FourierDecayAlt.P.PBE.slice_level_zero_compact_support P.k P.r Wp Wq p.T F hF hj w a _ ha e`.

Conclude with `Formalism.FourierDecayAlt.P.PBE.slice_pos_cpt P.k P.r Wp Wq p.T F hF j hj h1 w a _ ha e`.
-/
theorem slice_compact_support_coefficient : Formalism.FourierDecayAlt.KB.SliceCpt := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w a ha hF e
  unfold Formalism.FourierDecayAlt.KB.slv
  rcases Nat.eq_zero_or_pos j with h0 | h1
  · subst h0
    exact Formalism.FourierDecayAlt.P.PBE.slice_level_zero_compact_support P.k P.r Wp Wq p.T F hF hj w a _ ha e
  · exact Formalism.FourierDecayAlt.P.PBE.slice_pos_cpt P.k P.r Wp Wq p.T F hF j hj h1 w a _ ha e

end Formalism.FourierDecayAlt.P
