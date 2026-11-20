import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem

noncomputable section
open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.L2.SG.KappaOffDiagonal

namespace GlobalTheory.TypeAsm.GramPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
The claim follows from `X.pl.apply_symm_apply τ`.
-/
theorem pl_vOf (τ : D.what₂.Tau) : X.pl (vOf X τ) = τ := X.pl.apply_symm_apply τ

/- English proof (translation)
Use `conv_lhs => rw [← Formalism.L2.SG.Pf.toV_crd X x, ← Formalism.L2.SG.Pf.toV_crd X y, ← Formalism.L2.SG.Pf.toV_add, Formalism.L2.SG.Pf.crd_toV]`.
-/
theorem crd_add (x y : (VS D).V) : X.crd (x + y) = X.crd x + X.crd y := by
  conv_lhs => rw [← Formalism.L2.SG.Pf.toV_crd X x, ← Formalism.L2.SG.Pf.toV_crd X y, ← Formalism.L2.SG.Pf.toV_add,
    Formalism.L2.SG.Pf.crd_toV]

/- English proof (translation)
Use `conv_lhs => rw [← X.ιE.apply_symm_apply c, ← Formalism.L2.SG.Pf.toV_crd X x, ← Formalism.L2.SG.Pf.toV_smul, Formalism.L2.SG.Pf.crd_toV]`.
-/
theorem crd_smul (c : D.host.E) (x : (VS D).V) : X.crd (c • x) = X.ιE.symm c • X.crd x := by
  conv_lhs => rw [← X.ιE.apply_symm_apply c, ← Formalism.L2.SG.Pf.toV_crd X x, ← Formalism.L2.SG.Pf.toV_smul,
    Formalism.L2.SG.Pf.crd_toV]

/- English proof (translation)
Unfold `rv`. Rewrite using `[← Matrix.mulVec_add]`. Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem rv_add (v : InfinitePlace X.B.I.F) (a b : Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (a + b) = rv X.B.I v a + rv X.B.I v b := by
  unfold rv
  rw [← Matrix.mulVec_add]
  congr 1
  ext i
  simp

/- English proof (translation)
Unfold `rv`. Rewrite using `[← Matrix.mulVec_smul]`. Use `congr 1`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem rv_smul (v : InfinitePlace X.B.I.F) (c : X.B.I.E) (a : Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (c • a) = X.B.I.φ v c • rv X.B.I v a := by
  unfold rv
  rw [← Matrix.mulVec_smul]
  congr 1
  ext i
  simp

/- English proof (translation)
Unfold `GlobalTheory.TypeAsm.phiV`. Rewrite using `[crd_add, rv_add, Matrix.mulVec_add]`.
-/
theorem phiV_add (C : Choice X 1) (τ : D.what₂.Tau) (x y : (VS D).V) :
    GlobalTheory.TypeAsm.phiV C τ (x + y) = GlobalTheory.TypeAsm.phiV C τ x + GlobalTheory.TypeAsm.phiV C τ y := by
  unfold GlobalTheory.TypeAsm.phiV
  rw [crd_add, rv_add, Matrix.mulVec_add]

/- English proof (translation)
Unfold `GlobalTheory.TypeAsm.phiV`. Rewrite using `[crd_smul, rv_smul, Matrix.mulVec_smul, X.φ_eq, pl_vOf, RingEquiv.apply_symm_apply]`.
-/
theorem phiV_smul (C : Choice X 1) (τ : D.what₂.Tau) (c : D.host.E) (x : (VS D).V) :
    GlobalTheory.TypeAsm.phiV C τ (c • x) = embS D τ c • GlobalTheory.TypeAsm.phiV C τ x := by
  unfold GlobalTheory.TypeAsm.phiV
  rw [crd_smul, rv_smul, Matrix.mulVec_smul, X.φ_eq, pl_vOf, RingEquiv.apply_symm_apply]

/- English proof (translation)
Take `⟨_, hQQi, hH, _⟩` from `C.isT τ`. Establish `hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w` using `fun w => by`. Rewrite using `[Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]`. Unfold `Formalism.QuantumDeterminants.herm GlobalTheory.TypeAsm.phiV`. Rewrite using `[← hH, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.LTL.star_dot_conjT, hQ, hQ]`.

Establish `h2` using `Formalism.L2.SG.Pf.hJ_rv X (vOf X τ) (X.crd y) (X.crd x)`. Unfold `hJ at h2`. Rewrite using `[h2, X.φ_eq, pl_vOf, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]`. Both sides reduce to the same expression.
-/
theorem phiV_herm (C : Choice X 1) (τ : D.what₂.Tau) (x y : (VS D).V) :
    Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) (GlobalTheory.TypeAsm.phiV C τ x) (GlobalTheory.TypeAsm.phiV C τ y) =
      embS D τ ((GlobalTheory.TypeAsm.HV D).B x y) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  have hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  unfold Formalism.QuantumDeterminants.herm GlobalTheory.TypeAsm.phiV
  rw [← hH, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Formalism.L2.SG.Pf.LTL.star_dot_conjT, hQ, hQ]
  have h2 := Formalism.L2.SG.Pf.hJ_rv X (vOf X τ) (X.crd y) (X.crd x)
  unfold hJ at h2
  rw [h2, X.φ_eq, pl_vOf, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
  rfl

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm.GramPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Take `⟨hQiQ, _, _, _⟩` from `C.isT τ`. Establish `hP : (X.B.I.P (vOf X τ))⁻¹ * X.B.I.P (vOf X τ) = 1` using `Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _))`. Establish `hb : ∀ i : Fin X.B.I.n, C.Qi τ *ᵥ ((X.B.I.P (vOf X τ))⁻¹ *ᵥ Pi.single i 1) ∈ Set.range (GlobalTheory.TypeAsm.phiV C τ)`. Introduce `i`. Use `⟨Formalism.L2.SG.Pf.toV X (Pi.single i 1), ?_⟩` and prove the remaining obligations.

Unfold `GlobalTheory.TypeAsm.phiV rv`. Rewrite using `[Formalism.L2.SG.Pf.crd_toV]`. Use `congr 2`. Use extensionality with `j`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Rewrite using `[eq_top_iff]`. Introduce `w _`.

Establish `e : C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ * X.B.I.P (vOf X τ) * C.Q τ = 1`. Rewrite using `[Matrix.mul_assoc (C.Qi τ), hP, Matrix.mul_one, hQiQ]`. Establish `hw : w = C.Qi τ *ᵥ ((X.B.I.P (vOf X τ))⁻¹ *ᵥ (X.B.I.P (vOf X τ) *ᵥ (C.Q τ *ᵥ w)))`. Simplify using `only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, e, Matrix.one_mulVec]`. Rewrite using `[hw]`.

Use `set v := X.B.I.P (vOf X τ) *ᵥ (C.Q τ *ᵥ w)`. Rewrite using `[pi_eq_sum_univ v]`. Simplify using `only [Matrix.mulVec_sum, Matrix.mulVec_smul]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)` and prove the remaining obligations. Use `hb i` as an intermediate fact.

Use `this using 3` and compare the differences between its conclusion and the goal. Use extensionality with `j`. Simplify using `[Pi.single_apply, eq_comm]`.
-/
theorem phiV_span (C : Choice X 1) (τ : D.what₂.Tau) :
    Submodule.span ℂ (Set.range (GlobalTheory.TypeAsm.phiV C τ)) = ⊤ := by
  obtain ⟨hQiQ, _, _, _⟩ := C.isT τ
  have hP : (X.B.I.P (vOf X τ))⁻¹ * X.B.I.P (vOf X τ) = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (X.B.I.P_unit _))
  have hb : ∀ i : Fin X.B.I.n, C.Qi τ *ᵥ ((X.B.I.P (vOf X τ))⁻¹ *ᵥ Pi.single i 1) ∈
      Set.range (GlobalTheory.TypeAsm.phiV C τ) := by
    intro i
    refine ⟨Formalism.L2.SG.Pf.toV X (Pi.single i 1), ?_⟩
    unfold GlobalTheory.TypeAsm.phiV rv
    rw [Formalism.L2.SG.Pf.crd_toV]
    congr 2
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [eq_top_iff]
  intro w _
  have e : C.Qi τ * (X.B.I.P (vOf X τ))⁻¹ * X.B.I.P (vOf X τ) * C.Q τ = 1 := by
    rw [Matrix.mul_assoc (C.Qi τ), hP, Matrix.mul_one, hQiQ]
  have hw : w = C.Qi τ *ᵥ ((X.B.I.P (vOf X τ))⁻¹ *ᵥ (X.B.I.P (vOf X τ) *ᵥ (C.Q τ *ᵥ w))) := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, e, Matrix.one_mulVec]
  rw [hw]
  set v := X.B.I.P (vOf X τ) *ᵥ (C.Q τ *ᵥ w)
  rw [pi_eq_sum_univ v]
  simp only [Matrix.mulVec_sum, Matrix.mulVec_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  have := hb i
  convert this using 3
  ext j
  simp [Pi.single_apply, eq_comm]

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _`.
-/
theorem gamT_mem (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau) :
    GlobalTheory.TypeAsm.gamT C t τ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
  Formalism.L2.SG.Pf.LTL.trG_mem _ _ _ (C.isT τ).2.1 (C.isT τ).2.2.1 _

/- English proof (translation)
Take `⟨_, hQQi, _, _⟩` from `C.isT τ`. Take `⟨M, _, hM1, _, hM3⟩` from `t.rep.2.1`. Establish `hM1' : uMat (t.pt.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ)` using `hM1 _`. Establish `hM3' : X.crd (t.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y` using `hM3 y`. Unfold `GlobalTheory.TypeAsm.gamT GlobalTheory.TypeAsm.phiV Formalism.L2.SG.RealObj.trG`.

Rewrite using `[hM3', ← Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ), ← hM1']`. Establish `hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w` using `fun w => by`. Rewrite using `[Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]`. Simplify using `only [← Matrix.mulVec_mulVec]`. Rewrite using `[hQ]`.
-/
theorem gamT_act (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau)
    (y : (VS D).V) : GlobalTheory.TypeAsm.gamT C t τ *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (t.lin y) := by
  obtain ⟨_, hQQi, _, _⟩ := C.isT τ
  obtain ⟨M, _, hM1, _, hM3⟩ := t.rep.2.1
  have hM1' : uMat (t.pt.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ) := hM1 _
  have hM3' : X.crd (t.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3 y
  unfold GlobalTheory.TypeAsm.gamT GlobalTheory.TypeAsm.phiV Formalism.L2.SG.RealObj.trG
  rw [hM3', ← Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ), ← hM1']
  have hQ : ∀ w, C.Q τ *ᵥ (C.Qi τ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  rw [hQ]

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm.GramPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Establish `h : (frq X t.rep).fl = mapFlag t.lin t.rep.2.2.1 (X.Fu u)`. Unfold `frq mapLF`. Simplify using `only [dif_pos t.rep.2.2.1]`. Both sides reduce to the same expression. Rewrite using `[h]`.

Use `Fin.lastCases ?_ (fun b' => ?_) b` and prove the remaining obligations. Simplify using `only [FlagG.fvec, Fin.snoc_last]`. Both sides reduce to the same expression. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Both sides reduce to the same expression.
-/
theorem frq_fvec {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (b : Fin (D.R.rS + 1)) :
    (frq X t.rep).fl.fvec b = t.lin ((X.Fu u).fvec b) := by
  have h : (frq X t.rep).fl = mapFlag t.lin t.rep.2.2.1 (X.Fu u) := by
    unfold frq mapLF
    simp only [dif_pos t.rep.2.2.1]
    rfl
  rw [h]
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]
    rfl
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    rfl

/- English proof (translation)
Take `⟨_, hQQi, hH, _⟩` from `C.isT τ`. Take `⟨M, _, hM1, _, hM3⟩` from `t.rep.2.1`. Establish `hM1' : uMat (t.pt.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ)` using `hM1 _`. Establish `hM3' : ∀ y, X.crd (t.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y` using `hM3`. Establish `hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) a b = hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a) (uMat (t.pt.1 (vOf X τ)) *ᵥ (C.Q τ *ᵥ Forma …`.

Unfold `Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm GlobalTheory.TypeAsm.gamT Formalism.L2.SG.RealObj.trG hJ`. Rewrite using `[← hH, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT]`. Use `congr 1`. Simplify using `only [Matrix.mulVec_mulVec]`. Use `congr 1`.

Rewrite using `[show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ * (C.Qi τ * uMat (t.pt.1 (vOf X τ)) * C.Q τ) = (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) * uMat (t.pt.1 (vOf X τ)) * C.Q τ by`. Simplify using `only [Matrix.mul_assoc], hQQi]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Establish `hC : ∀ y, uMat (t.pt.1 (vOf X τ)) *ᵥ rv X.B.I (vOf X τ) y = rv X.B.I (vOf X τ) ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y)`. Introduce `y`.

Rewrite using `[hM1']`. Conclude with `Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ) _ y`. Rewrite using `[hA, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ a, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ b, Matrix.mulVec_smul, hC, ← hM3', Formalism.L2.SG.Pf.LTL.hJ_smul_real, Formalism.L2.SG.Pf.hJ_rv, X.φ_eq, pl_vOf, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]`. Unfold `Formalism.MainNotions.S.Zhat brS`. Rewrite using `[frq_fvec]`.
-/
theorem zhat_gamT (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau)
    (a b : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) a b =
      ((rhoF D a * rhoF D b : ℝ) : ℂ) * embS D τ (Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl a b) := by
  obtain ⟨_, hQQi, hH, _⟩ := C.isT τ
  obtain ⟨M, _, hM1, _, hM3⟩ := t.rep.2.1
  have hM1' : uMat (t.pt.1 (vOf X τ)) = (X.B.I.P (vOf X τ))⁻¹ *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ (vOf X τ)) * X.B.I.P (vOf X τ) := hM1 _
  have hM3' : ∀ y, X.crd (t.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3
  have hA : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) a b =
      hJ (X.B.I.ε (vOf X τ)) (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) a)
        (uMat (t.pt.1 (vOf X τ)) *ᵥ (C.Q τ *ᵥ Formalism.QuantumDeterminants.fvec D.R.k D.R.rS (zB X (C.Qi τ) u τ) b)) := by
    unfold Formalism.QuantumDeterminants.Zhat Formalism.QuantumDeterminants.herm GlobalTheory.TypeAsm.gamT Formalism.L2.SG.RealObj.trG hJ
    rw [← hH, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT]
    congr 1
    simp only [Matrix.mulVec_mulVec]
    congr 1
    rw [show (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * C.Q τ *
        (C.Qi τ * uMat (t.pt.1 (vOf X τ)) * C.Q τ) =
      (C.Q τ)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * (C.Q τ * C.Qi τ) * uMat (t.pt.1 (vOf X τ)) * C.Q τ by
        simp only [Matrix.mul_assoc], hQQi]
    simp only [Matrix.mul_one, Matrix.mul_assoc]
  have hC : ∀ y, uMat (t.pt.1 (vOf X τ)) *ᵥ rv X.B.I (vOf X τ) y =
      rv X.B.I (vOf X τ) ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) := by
    intro y
    rw [hM1']
    exact Formalism.L2.SG.Pf.rv_mulVec X (vOf X τ) _ y
  rw [hA, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ a, Formalism.L2.SG.Pf.LTL.Q_fvec C u τ b, Matrix.mulVec_smul, hC, ← hM3',
    Formalism.L2.SG.Pf.LTL.hJ_smul_real, Formalism.L2.SG.Pf.hJ_rv, X.φ_eq, pl_vOf, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
  unfold Formalism.MainNotions.S.Zhat brS
  rw [frq_fvec]

/- English proof (translation)
Establish `h : (Matrix.of fun i j => ρ i * ρ j * e (M i j)) = Matrix.diagonal ρ * e.mapMatrix M * Matrix.diagonal ρ`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, RingHom.map_det]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_scaled {K : Type*} [Field K] {N : ℕ} (ρ : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) K) (e : K →+* ℂ) :
    (Matrix.of fun i j => ρ i * ρ j * e (M i j)).det = (∏ i, ρ i) ^ 2 * e M.det := by
  have h : (Matrix.of fun i j => ρ i * ρ j * e (M i j)) = Matrix.diagonal ρ * e.mapMatrix M * Matrix.diagonal ρ := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, RingHom.map_det]
  ring

/- English proof (translation)
Establish `hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) = Matrix.of fun a b => ((rhoF D a : ℝ) : ℂ) * ((rhoF D b : ℝ) : ℂ) * embS D τ (Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl a b)`. Use extensionality with `a b`. Rewrite using `[zhat_gamT, Matrix.of_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `Formalism.QuantumDeterminants.Dmin Formalism.MainNotions.S.Dl leadMinorE`. Rewrite using `[dif_pos (by omega), hZ, ← det_scaled]`. Both sides reduce to the same expression.
-/
theorem dmin_gamT (C : Choice X 1) {Y : Full X} {u : D.what₂.Word} (t : GlobalTheory.TypeAsm.GT Y u) (τ : D.what₂.Tau)
    (l : Fin (D.R.rS + 1)) :
    Formalism.QuantumDeterminants.Dmin D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) l.castSucc =
      (∏ i : Fin l.val, ((rhoF D (Fin.castLE (by omega) i) : ℝ) : ℂ)) ^ 2 *
        embS D τ (Formalism.MainNotions.S.Dl (lf D (X.Fu u)).fl (frq X t.rep).fl l.val) := by
  have hZ : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) (GlobalTheory.TypeAsm.gamT C t τ) =
      Matrix.of fun a b => ((rhoF D a : ℝ) : ℂ) * ((rhoF D b : ℝ) : ℂ) *
        embS D τ (Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (frq X t.rep).fl a b) := by
    ext a b
    rw [zhat_gamT, Matrix.of_apply]
    push_cast
    ring
  unfold Formalism.QuantumDeterminants.Dmin Formalism.MainNotions.S.Dl leadMinorE
  rw [dif_pos (by omega), hZ, ← det_scaled]
  rfl

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm.GramPf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {X : HidaSetting D}

/- English proof (translation)
Unfold `Formalism.BasicNotions.Host.rdE`. Conclude with `Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _`.
-/
theorem rdE_pos' (D : D7) : 0 < D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero D.host.E))) _

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `zero => simp [frameExp]`. Consider the case `succ l ih`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [Fin.coe_castSucc, Fin.val_last]`.

Rewrite using `[← ih (by omega)]`. Unfold `frameExp`. Rewrite using `[show Finset.Icc 1 (l + 1) = Finset.Ioc 0 (l + 1) from Finset.val_inj.mp rfl, show Finset.Icc 1 l = Finset.Ioc 0 l from Finset.val_inj.mp rfl, Finset.sum_Ioc_succ_top (Nat.zero_le l)]`. Use `push_cast`. Rewrite using `[Nat.cast_sub (by omega)]`.
-/
theorem frameExp_cast (r l : ℕ) (hl : l ≤ r + 1) :
    (frameExp r l : ℝ) = ∑ i : Fin l, ((r : ℝ) - (i : ℕ)) := by
  induction l with
  | zero => simp [frameExp]
  | succ l ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← ih (by omega)]
    unfold frameExp
    rw [show Finset.Icc 1 (l + 1) = Finset.Ioc 0 (l + 1) from Finset.val_inj.mp rfl,
      show Finset.Icc 1 l = Finset.Ioc 0 l from Finset.val_inj.mp rfl, Finset.sum_Ioc_succ_top (Nat.zero_le l)]
    push_cast
    rw [Nat.cast_sub (by omega)]

/- English proof (translation)
Rewrite using `[frameExp_cast _ _ hl, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos (rdE_pos' D)]`. Both sides reduce to the same expression.
-/
theorem prod_rho (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    ∏ i : Fin l, rhoF D (Fin.castLE hl i) = D.host.rdE ^ (-(frameExp D.R.rS l : ℝ)) := by
  rw [frameExp_cast _ _ hl, ← Finset.sum_neg_distrib, Real.rpow_sum_of_pos (rdE_pos' D)]
  rfl

/- English proof (translation)
Rewrite using `[← Complex.ofReal_prod, prod_rho l hl, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (rdE_pos' D) _), ← Real.rpow_natCast, ← Real.rpow_mul (rdE_pos' D).le, mul_comm ‖x‖]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_dmin (l : ℕ) (hl : l ≤ D.R.rS + 1) (x : ℂ) :
    ‖(∏ i : Fin l, ((rhoF D (Fin.castLE hl i) : ℝ) : ℂ)) ^ 2 * x‖ =
      ‖x‖ * D.host.rdE ^ (-(2 * (frameExp D.R.rS l : ℝ))) := by
  rw [← Complex.ofReal_prod, prod_rho l hl, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (rdE_pos' D) _), ← Real.rpow_natCast,
    ← Real.rpow_mul (rdE_pos' D).le, mul_comm ‖x‖]
  congr 2
  push_cast
  ring

end GlobalTheory.TypeAsm.GramPf

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X Y u C τ`. Use `⟨⟨GramPf.phiV_add C τ, GramPf.phiV_smul C τ, GramPf.phiV_herm C τ, GramPf.phiV_span C τ⟩, fun t => ⟨GramPf.gamT_mem C t τ, GramPf.gamT_act C t τ, fun l => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[GramPf.dmin_gamT, GramPf.norm_dmin]`. Both sides reduce to the same expression.
-/
theorem gramC_holds : GramC := by
  intro D X Y u C τ
  refine ⟨⟨GramPf.phiV_add C τ, GramPf.phiV_smul C τ, GramPf.phiV_herm C τ, GramPf.phiV_span C τ⟩,
    fun t => ⟨GramPf.gamT_mem C t τ, GramPf.gamT_act C t τ, fun l => ?_⟩⟩
  rw [GramPf.dmin_gamT, GramPf.norm_dmin]
  rfl

end GlobalTheory.TypeAsm
