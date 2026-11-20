import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalDiscriminantIsUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalSplitTypeMixedSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairRelevantOfPoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRationalPointIsPoint

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocBaseRel

variable {D : D7}

/- English proof (translation)
Establish `e1 : (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE (brS (VS D) x y)` using `baseChangeAt_form Z.M p (Z.hcj p) x y`. Rewrite using `[(locH Z p).h_smul_left, (locH Z p).h_herm (b • baseChange₂ D p y) (baseChange₂ D p x), (locH Z p).h_smul_left, (locH Z p).h_herm (baseChange₂ D p x) (baseChange₂ D p y), map_mul, (Z.M p).L.cj_cj, e1]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hs_lemma (Z : LocDat D) (p : PlF D) (a b : (D.s.atP p).Ep) (x y : (VS D).V) :
    (locH Z p).h (a • baseChange₂ D p x) (b • baseChange₂ D p y) =
      a * (Z.M p).L.cj b * (D.s.atP p).ιE (brS (VS D) x y) := by
  have e1 : (locH Z p).h (baseChange₂ D p x) (baseChange₂ D p y) = (D.s.atP p).ιE (brS (VS D) x y) :=
    baseChangeAt_form Z.M p (Z.hcj p) x y
  rw [(locH Z p).h_smul_left, (locH Z p).h_herm (b • baseChange₂ D p y) (baseChange₂ D p x),
    (locH Z p).h_smul_left, (locH Z p).h_herm (baseChange₂ D p x) (baseChange₂ D p y), map_mul,
    (Z.M p).L.cj_cj, e1]
  ring

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]`. Simplify using `only [Formalism.MainNotions.S.Loc.HermSp.Zhat, Matrix.of_apply, scaled, frame]`. Rewrite using `[hs_lemma]`. Simplify using `only [Formalism.MainNotions.S.Zhat]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem zhat_scaled (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') :
    (locH Z p).Zhat (scaled Z p (frame F)) (scaled Z p (frame F')) =
      Matrix.diagonal (fun a => (Z.M p).L.cj (frFac Z.δ p a)) *
        (Formalism.MainNotions.S.Zhat F.fl F'.fl).map (D.s.atP p).ιE * Matrix.diagonal (fun b => frFac Z.δ p b) := by
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  simp only [Formalism.MainNotions.S.Loc.HermSp.Zhat, Matrix.of_apply, scaled, frame]
  rw [hs_lemma]
  simp only [Formalism.MainNotions.S.Zhat]
  ring

/- English proof (translation)
Establish `hA : ((locH Z p).Zhat (scaled Z p (frame F)) (scaled Z p (frame F'))).submatrix (Fin.castLE hl) (Fin.castLE hl) = Matrix.diagonal (fun i => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i))) * ((Formalism.MainNotions.S.Zhat F.fl F'.fl).map (D.s.atP p).ιE).submatrix (Fin.castLE hl) (Fi …`. Rewrite using `[zhat_scaled]`. Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Establish `hB : ((Formalism.MainNotions.S.Zhat F.fl F'.fl).map (D.s.atP p).ιE).submatrix (Fin.castLE hl) (Fin.castLE hl) = (D.s.atP p).ιE.mapMatrix ((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl))` using `rfl`.

Rewrite using `[Formalism.MainNotions.S.Loc.HermSp.Dl, dif_pos hl, hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, ← RingHom.map_det, Finset.prod_mul_distrib]`. Simplify using `only [Formalism.MainNotions.S.Dl, Formalism.MainNotions.S.leadMinorE, dif_pos hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dl_scaled (Z : LocDat D) (p : PlF D) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T)
    (F' : LFlag (VS D) D.R.rS T') (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    (locH Z p).Dl (scaled Z p (frame F)) (scaled Z p (frame F')) l =
      (∏ i : Fin l, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i)) * frFac Z.δ p (Fin.castLE hl i)) *
        (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F.fl F'.fl l) := by
  have hA : ((locH Z p).Zhat (scaled Z p (frame F)) (scaled Z p (frame F'))).submatrix (Fin.castLE hl)
      (Fin.castLE hl) =
      Matrix.diagonal (fun i => (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl i))) *
        ((Formalism.MainNotions.S.Zhat F.fl F'.fl).map (D.s.atP p).ιE).submatrix (Fin.castLE hl) (Fin.castLE hl) *
        Matrix.diagonal (fun i => frFac Z.δ p (Fin.castLE hl i)) := by
    rw [zhat_scaled]
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hB : ((Formalism.MainNotions.S.Zhat F.fl F'.fl).map (D.s.atP p).ιE).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      (D.s.atP p).ιE.mapMatrix ((Formalism.MainNotions.S.Zhat F.fl F'.fl).submatrix (Fin.castLE hl) (Fin.castLE hl)) := rfl
  rw [Formalism.MainNotions.S.Loc.HermSp.Dl, dif_pos hl, hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_diagonal, hB, ← RingHom.map_det, Finset.prod_mul_distrib]
  simp only [Formalism.MainNotions.S.Dl, Formalism.MainNotions.S.leadMinorE, dif_pos hl]
  ring

/- English proof (translation)
Introduce `hA hB hT hT' hG`. Establish `hl1 : D.R.rS + 1 ≤ D.R.rS + 1` using `le_refl _`. Establish `hl0 : D.R.rS ≤ D.R.rS + 1` using `Nat.le_succ _`. Establish `e1` using `dl_scaled Z p F F' (D.R.rS + 1) hl1`. Establish `e0` using `dl_scaled Z p F F' D.R.rS hl0`.

Establish `hlast : frFac Z.δ p (Fin.castLE hl1 (Fin.last D.R.rS)) = 1`. Establish `h1 : Fin.castLE hl1 (Fin.last D.R.rS) = Fin.last D.R.rS` using `Fin.ext rfl`. Rewrite using `[h1]`. Simplify using `[frFac]`. Establish `hc1 : (∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl1 i)) * frFac Z.δ p (Fin.castLE hl1 i)) = ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) * frFac Z.δ p (Fin.castLE hl0 i)`.

Rewrite using `[Fin.prod_univ_castSucc, hlast, map_one, one_mul, mul_one]`. Both sides reduce to the same expression. Establish `hU : ∀ a, IsUnit (frFac Z.δ p a)`. Introduce `a`. Establish `h` using `(Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow (D.R.rS - a.val)`.

Conclude with `h.ringInverse`. Establish `hcU : IsUnit (∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) * frFac Z.δ p (Fin.castLE hl0 i))` using `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => ((hU _).map (Z.M p).L.cj).mul (hU _))`. Establish `key : P.Gv = ((∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) * frFac Z.δ p (Fin.castLE hl0 i)) * (Z.M p).L.cj (∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) * frFac Z.δ p (Fin.castLE hl0 i))) * (D.s.atP p).ιE (Gval F F')`. Simplify using `only [Formalism.MainNotions.S.LocNG.FPair.Gv, Formalism.MainNotions.S.Loc.HermSp.Gdet, Formalism.MainNotions.S.Loc.HermSp.normE]`. Rewrite using `[hA, hB, hT, hT', e1, e0, hc1]`.

Simplify using `only [Gval, Formalism.MainNotions.S.Gflag, map_sub, map_mul, cj_iota (Z.hcj p), map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Introduce `h0`. Rewrite `h0` using `[(hcU.mul (hcU.map (Z.M p).L.cj)).mul_right_eq_zero]`.

Conclude with `(map_ne_zero (D.s.atP p).ιE).mpr hG h0`.
-/
theorem gv_ne_of (Z : LocDat D) (p : PlF D) (n n' : ℕ) (F : LFlag (VS D) D.R.rS ((n : ℕ) : D.host.E))
    (F' : LFlag (VS D) D.R.rS ((n' : ℕ) : D.host.E)) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS) :
    P.A.f = scaled Z p (frame F) → P.B.f = scaled Z p (frame F') → P.A.T = (n : (D.s.atP p).Fp) →
      P.B.T = (n' : (D.s.atP p).Fp) → Gval F F' ≠ 0 → P.Gv ≠ 0 := by
  intro hA hB hT hT' hG
  have hl1 : D.R.rS + 1 ≤ D.R.rS + 1 := le_refl _
  have hl0 : D.R.rS ≤ D.R.rS + 1 := Nat.le_succ _
  have e1 := dl_scaled Z p F F' (D.R.rS + 1) hl1
  have e0 := dl_scaled Z p F F' D.R.rS hl0
  have hlast : frFac Z.δ p (Fin.castLE hl1 (Fin.last D.R.rS)) = 1 := by
    have h1 : Fin.castLE hl1 (Fin.last D.R.rS) = Fin.last D.R.rS := Fin.ext rfl
    rw [h1]
    simp [frFac]
  have hc1 : (∏ i : Fin (D.R.rS + 1), (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl1 i)) *
      frFac Z.δ p (Fin.castLE hl1 i)) =
      ∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) * frFac Z.δ p (Fin.castLE hl0 i) := by
    rw [Fin.prod_univ_castSucc, hlast, map_one, one_mul, mul_one]
    rfl
  have hU : ∀ a, IsUnit (frFac Z.δ p a) := by
    intro a
    have h := (Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow (D.R.rS - a.val)
    exact h.ringInverse
  have hcU : IsUnit (∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) *
      frFac Z.δ p (Fin.castLE hl0 i)) :=
    Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
      (fun i _ => ((hU _).map (Z.M p).L.cj).mul (hU _))
  have key : P.Gv = ((∏ i : Fin D.R.rS, (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) *
      frFac Z.δ p (Fin.castLE hl0 i)) * (Z.M p).L.cj (∏ i : Fin D.R.rS,
        (Z.M p).L.cj (frFac Z.δ p (Fin.castLE hl0 i)) * frFac Z.δ p (Fin.castLE hl0 i))) *
      (D.s.atP p).ιE (Gval F F') := by
    simp only [Formalism.MainNotions.S.LocNG.FPair.Gv, Formalism.MainNotions.S.Loc.HermSp.Gdet, Formalism.MainNotions.S.Loc.HermSp.normE]
    rw [hA, hB, hT, hT', e1, e0, hc1]
    simp only [Gval, Formalism.MainNotions.S.Gflag, map_sub, map_mul, cj_iota (Z.hcj p), map_natCast]
    ring
  rw [key]
  intro h0
  rw [(hcU.mul (hcU.map (Z.M p).L.cj)).mul_right_eq_zero] at h0
  exact (map_ne_zero (D.s.atP p).ιE).mpr hG h0

/- English proof (translation)
Take `⟨-, -, -, -, -, hm⟩` from `Z.agree p`. Consider the cases of `hs : (D.s.atP p).split with`. Consider the case `none => simp only [hg, hs] at hm`. Consider the case `some sg`. Simplify using `only [hg, hs] at hm`.

Establish `hq : (g.q : (D.s.atP p).Fp) = ((Loc.resChar p : ℕ) : (D.s.atP p).Fp)`. Rewrite using `[hm.2]`. Conclude with `sg.q_eq`. Establish `hmem` using `(D.s_split p).mp (by simp [hs])`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hmem`.

Choose the witnesses or unpack the hypotheses as in `⟨m', hm'⟩ : (Loc.resChar p) ^ 2 ∣ D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by`. Apply the tactic sequence `rcases hmem with h | h <;> rw [h]`. Conclude with `⟨D.host.QS * D.host.q * D.host.d * D.host.g 1 ^ 2, by ring⟩`. Conclude with `⟨D.host.QS * D.host.q * D.host.d * D.host.g 0 ^ 2, by ring⟩`. Take `⟨π, -, hπ, hπ1⟩` from `D.T_norm u`.

Take `⟨x, hx⟩` from `Ideal.mem_span_singleton'.mp hπ1`. Rewrite `hx` using `[hm']`. Establish `hxE` using `congrArg (algebraMap (𝓞 D.host.E) D.host.E) hx`. Simplify using `only [map_mul, map_sub, map_one, map_natCast, ← RingOfIntegers.coe_eq_algebraMap] at hxE`. Move the coercions through the operations in `at hxE`.

Establish `hιπ : (D.s.atP p).ιE (π : D.host.E) = 1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E))`. Establish `h` using `congrArg (D.s.atP p).ιE hxE`. Simplify using `only [map_mul, map_sub, map_one, map_pow, map_natCast] at h`. Take the linear combination `-h`. Establish `hιπc : (D.s.atP p).ιE (D.host.conj (π : D.host.E)) = 1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)))`.

Rewrite using `[← D.conjF_eq, ← (D.s.atP p).cj_ιE, hιπ]`. Simplify using `only [map_add, map_one, map_mul, map_pow, map_natCast]`. Establish `hXO : (D.s.atP p).ιE (x : D.host.E) ∈ (D.s.atP p).O` using `PI.CntNotIntW.iE_mem_O D p x`. Establish `hXcO : (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) ∈ (D.s.atP p).O` using `Formalism.L2.SG.Pf.LocFacts.lf_cj_mem p _ hXO`. Establish `hYO : (m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E) + (m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E)) * ((m' : (D.s.atP p).Ep) * (D.s.atP p).cj (( …` using `add_mem (add_mem (mul_mem (natCast_mem _ _) hXO) (mul_mem (natCast_mem _ _) hXcO)) (mul_mem (mul_mem (pow_mem (natCast_mem _ _) _) (mul_mem (natCast_mem _ _) hXO)) (mul_mem (natCast_mem _ _) hXcO))`.

Establish `hT : ((Tu D u : ℕ) : (D.s.atP p).Ep) = 1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E) + (m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p …`. Establish `hTE : ((Tu D u : ℕ) : D.host.E) = (π : D.host.E) * D.host.conj (π : D.host.E)` using `hπ.symm`. Establish `h` using `congrArg (D.s.atP p).ιE hTE`. Rewrite `h` using `[map_natCast, map_mul, hιπ, hιπc]`. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc0` using `(D.s.atP p).char0`. Establish `hℓ0 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ≠ 0` using `Nat.cast_ne_zero.mpr (D.s.atP p).ellPrime.out.ne_zero`. Establish `hℓ2 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2 ≠ 0` using `pow_ne_zero 2 hℓ0`. Establish `hw0 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((((Tu D u : ℕ) : (D.s.atP p).Fp) - 1) / ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2) ∈ (D.s.atP p).O`.

Establish `hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2))` using `(isUnit_iff_ne_zero.mpr hℓ2).map _`. Establish `he : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((((Tu D u : ℕ) : (D.s.atP p).Fp) - 1) / ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2) = (m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E) + (m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) + ((Loc.resChar p : …`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, mul_div_cancel₀ _ hℓ2, map_sub, map_natCast, map_one, map_pow, map_natCast, hT]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[he]`. Conclude with `hYO`. Use `⟨⟨_, Formalism.L2.SG.Pf.LocFacts.lf_int_of_alg p _ hw0⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_Tu_eq_one_add_sq_mul (Z : LocDat D) (p : PlF D) (u : D.what₂.Word) (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L)
    (hg : (Z.M p).split = some g) :
    ∃ w : Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp), ((Tu D u : ℕ) : (D.s.atP p).Fp) =
      1 + (g.q : (D.s.atP p).Fp) ^ 2 * (w : (D.s.atP p).Fp) := by
  obtain ⟨-, -, -, -, -, hm⟩ := Z.agree p
  cases hs : (D.s.atP p).split with
  | none => simp only [hg, hs] at hm
  | some sg =>
    simp only [hg, hs] at hm
    have hq : (g.q : (D.s.atP p).Fp) = ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) := by
      rw [hm.2]
      exact sg.q_eq
    have hmem := (D.s_split p).mp (by simp [hs])
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    obtain ⟨m', hm'⟩ : (Loc.resChar p) ^ 2 ∣
        D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 := by
      rcases hmem with h | h <;> rw [h]
      · exact ⟨D.host.QS * D.host.q * D.host.d * D.host.g 1 ^ 2, by ring⟩
      · exact ⟨D.host.QS * D.host.q * D.host.d * D.host.g 0 ^ 2, by ring⟩
    obtain ⟨π, -, hπ, hπ1⟩ := D.T_norm u
    obtain ⟨x, hx⟩ := Ideal.mem_span_singleton'.mp hπ1
    rw [hm'] at hx
    have hxE := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hx
    simp only [map_mul, map_sub, map_one, map_natCast, ← RingOfIntegers.coe_eq_algebraMap] at hxE
    push_cast at hxE
    have hιπ : (D.s.atP p).ιE (π : D.host.E) = 1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 *
        ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E)) := by
      have h := congrArg (D.s.atP p).ιE hxE
      simp only [map_mul, map_sub, map_one, map_pow, map_natCast] at h
      linear_combination -h
    have hιπc : (D.s.atP p).ιE (D.host.conj (π : D.host.E)) = 1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 *
        ((m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E))) := by
      rw [← D.conjF_eq, ← (D.s.atP p).cj_ιE, hιπ]
      simp only [map_add, map_one, map_mul, map_pow, map_natCast]
    have hXO : (D.s.atP p).ιE (x : D.host.E) ∈ (D.s.atP p).O := PI.CntNotIntW.iE_mem_O D p x
    have hXcO : (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) ∈ (D.s.atP p).O :=
      Formalism.L2.SG.Pf.LocFacts.lf_cj_mem p _ hXO
    have hYO : (m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E) +
        (m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) +
        ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E)) *
          ((m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E))) ∈ (D.s.atP p).O :=
      add_mem (add_mem (mul_mem (natCast_mem _ _) hXO) (mul_mem (natCast_mem _ _) hXcO))
        (mul_mem (mul_mem (pow_mem (natCast_mem _ _) _) (mul_mem (natCast_mem _ _) hXO))
          (mul_mem (natCast_mem _ _) hXcO))
    have hT : ((Tu D u : ℕ) : (D.s.atP p).Ep) = 1 + ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 *
        ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E) +
        (m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) +
        ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E)) *
          ((m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)))) := by
      have hTE : ((Tu D u : ℕ) : D.host.E) = (π : D.host.E) * D.host.conj (π : D.host.E) := hπ.symm
      have h := congrArg (D.s.atP p).ιE hTE
      rw [map_natCast, map_mul, hιπ, hιπc] at h
      rw [h]
      ring
    have hc0 := (D.s.atP p).char0
    have hℓ0 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ≠ 0 :=
      Nat.cast_ne_zero.mpr (D.s.atP p).ellPrime.out.ne_zero
    have hℓ2 : ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2 ≠ 0 := pow_ne_zero 2 hℓ0
    have hw0 : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((((Tu D u : ℕ) : (D.s.atP p).Fp) - 1) / ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2) ∈
        (D.s.atP p).O := by
      have hu : IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2)) :=
        (isUnit_iff_ne_zero.mpr hℓ2).map _
      have he : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
          ((((Tu D u : ℕ) : (D.s.atP p).Fp) - 1) / ((Loc.resChar p : ℕ) : (D.s.atP p).Fp) ^ 2) =
          (m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E) +
          (m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E)) +
          ((Loc.resChar p : ℕ) : (D.s.atP p).Ep) ^ 2 * ((m' : (D.s.atP p).Ep) * (D.s.atP p).ιE (x : D.host.E)) *
            ((m' : (D.s.atP p).Ep) * (D.s.atP p).cj ((D.s.atP p).ιE (x : D.host.E))) := by
        apply hu.mul_left_cancel
        rw [← map_mul, mul_div_cancel₀ _ hℓ2, map_sub, map_natCast, map_one, map_pow, map_natCast, hT]
        ring
      rw [he]
      exact hYO
    refine ⟨⟨_, Formalism.L2.SG.Pf.LocFacts.lf_int_of_alg p _ hw0⟩, ?_⟩
    rw [hq]
    field_simp
    ring

end GlobalTheory.LocBaseRel

namespace GlobalTheory.LocBaseRel
open ValuativeRel
variable {D : D7}
/- English proof (translation)
Introduce `hA hB`. Establish `hc0` using `(D.s.atP p).char0`. Establish `hn : Tu D u ≠ 0` using `(D.mem u).A.T_prime.ne_zero`. Establish `hn' : Tu D u' ≠ 0` using `(D.mem u').A.T_prime.ne_zero`. Establish `hU : ∀ (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (w : 𝒪[(D.s.atP p).Fp]), IsUnit (1 + g.q ^ 2 * w)`.

Introduce `g w`. Break down `IsLocalRing.isUnit_or_isUnit_one_sub_self (-(g.q ^ 2 * w)) with h | h` into its components or cases. Establish `h2 : IsUnit (g.q ^ 2 * w)` using `by simpa using h.neg`. Conclude with `absurd ((isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left h2)) g.q_irr.not_isUnit`. Simplify `h` using `[sub_neg_eq_add]`.

Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hA]`. Conclude with `natCast_mem _ _`. Rewrite using `[hA]`. Conclude with `hn` after adjusting the coercions.

Rewrite using `[hB]`. Conclude with `natCast_mem _ _`. Rewrite using `[hB]`. Conclude with `hn'` after adjusting the coercions. Introduce `g hg`.

Take `⟨w, hw⟩` from `exists_Tu_eq_one_add_sq_mul Z p u g hg`. Take `⟨w', hw'⟩` from `exists_Tu_eq_one_add_sq_mul Z p u' g hg`. Use `⟨?_, w - w', ?_⟩` and prove the remaining obligations. Take `⟨U, hU1⟩` from `hU g w`. Take `⟨U', hU1'⟩` from `hU g w'`.

Use `⟨((U⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ((U'⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg Subtype.val U.inv_mul`. Rewrite `h1` using `[hU1]`. Rewrite using `[hA, hw]`. Simplify using `using h1`.

Establish `h1` using `congrArg Subtype.val U'.inv_mul`. Rewrite `h1` using `[hU1']`. Rewrite using `[hB, hw']`. Simplify using `using h1`. Rewrite using `[hA, hB, hw, hw']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normsOK_of (Z : LocDat D) (p : PlF D) (u u' : D.what₂.Word) (P : Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS) :
    P.A.T = ((Tu D u : ℕ) : (D.s.atP p).Fp) → P.B.T = ((Tu D u' : ℕ) : (D.s.atP p).Fp) → P.NormsOK := by
  intro hA hB
  have hc0 := (D.s.atP p).char0
  have hn : Tu D u ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hn' : Tu D u' ≠ 0 := (D.mem u').A.T_prime.ne_zero
  have hU : ∀ (g : Formalism.MainNotions.S.Loc.SplitG (Z.M p).L) (w : 𝒪[(D.s.atP p).Fp]), IsUnit (1 + g.q ^ 2 * w) := by
    intro g w
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (-(g.q ^ 2 * w)) with h | h
    · have h2 : IsUnit (g.q ^ 2 * w) := by simpa using h.neg
      exact absurd ((isUnit_pow_iff two_ne_zero).mp (isUnit_of_mul_isUnit_left h2)) g.q_irr.not_isUnit
    · simpa [sub_neg_eq_add] using h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hA]
    exact natCast_mem _ _
  · rw [hA]
    exact_mod_cast hn
  · rw [hB]
    exact natCast_mem _ _
  · rw [hB]
    exact_mod_cast hn'
  · intro g hg
    obtain ⟨w, hw⟩ := exists_Tu_eq_one_add_sq_mul Z p u g hg
    obtain ⟨w', hw'⟩ := exists_Tu_eq_one_add_sq_mul Z p u' g hg
    refine ⟨?_, w - w', ?_⟩
    · obtain ⟨U, hU1⟩ := hU g w
      obtain ⟨U', hU1'⟩ := hU g w'
      refine ⟨((U⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]),
        ((U'⁻¹ : (𝒪[(D.s.atP p).Fp])ˣ) : 𝒪[(D.s.atP p).Fp]), ?_, ?_⟩
      · have h1 := congrArg Subtype.val U.inv_mul
        rw [hU1] at h1
        rw [hA, hw]
        simpa using h1
      · have h1 := congrArg Subtype.val U'.inv_mul
        rw [hU1'] at h1
        rw [hB, hw']
        simpa using h1
    · rw [hA, hB, hw, hw']
      push_cast
      ring
end GlobalTheory.LocBaseRel

namespace GlobalTheory.LocBaseRel

variable {D : D7}

/- English proof (translation)
Rewrite using `[finrank_Vp]`. Take `⟨j, hj⟩` from `D.R.m_even`. Establish `h2` using `D.R.two_le_m`. Simplify using `only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, hj]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_eq (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS, hj]
  omega

/- English proof (translation)
Set `Ψ : (VS D).V →ₗ[D.host.E] (Fin r → D.host.E)` to `LinearMap.pi (fun i => (VS D).hT (F.e i))`. Establish `hΨ : ∀ y i, Ψ y i = (VS D).hT (F.e i) y` using `fun _ _ => rfl`. Establish `hsurj : Function.Surjective Ψ`. Rewrite using `[← LinearMap.range_eq_top]`. Assume the negation of the conclusion as `hne`.

Take `⟨φ, hφ0, hφ⟩` from `(LinearMap.range Ψ).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)`. Apply `hφ0` to reduce the goal to its premises. Establish `hsum : ∀ v : Fin r → D.host.E, φ v = ∑ i, v i * φ (fun j => if i = j then 1 else 0)`. Introduce `v`. Rewrite using `[LinearMap.pi_apply_eq_sum_univ φ v]`.

Simplify using `only [smul_eq_mul]`. Establish `hz : ∀ y, ∑ i, (VS D).hT (F.e i) y * φ (fun j => if i = j then 1 else 0) = 0`. Introduce `y`. Establish `h` using `hφ (LinearMap.mem_range_self Ψ y)`. Rewrite `h` using `[LinearMap.mem_ker, hsum]`.

Simplify `h` using `only [hΨ]`. Establish `hx : ∀ y, (VS D).hT (∑ i, star (φ (fun j => if i = j then 1 else 0)) • F.e i) y = 0`. Introduce `y`. Rewrite using `[map_sum, LinearMap.sum_apply]`. Use `(Finset.sum_congr rfl (fun i _ => ?_)).trans (hz y)` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]`. Establish `hx0` using `(VS D).nondeg.1 _ hx`. Establish `hc : ∀ i, φ (fun j => if i = j then 1 else 0) = 0`. Introduce `i`. Establish `h` using `Fintype.linearIndependent_iff.mp F.e_indep _ hx0 i`.

Simplify using `using h`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[hsum]`. Simplify using `[hc]`. Use `choose y hy using fun j => hsurj (fun i => if i = j then (1 : D.host.E) else 0)`.

Use `⟨y, fun i j => ?_⟩` and prove the remaining obligations. Establish `h1 : (VS D).hT (F.e i) (y j) = if i = j then 1 else 0`. Rewrite using `[← hΨ, hy j]`. Establish `h2` using `LinearMap.isSymm_def.mp (VS D).herm (F.e i) (y j)`. Rewrite using `[brS, ← h2, h1, starRingEnd_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem exists_dual_family_of_flag {r : ℕ} {T : D.host.E} (F : FlagG (VS D) r T) :
    ∃ y : Fin r → (VS D).V, ∀ i j, brS (VS D) (F.e i) (y j) = if i = j then 1 else 0 := by
  let Ψ : (VS D).V →ₗ[D.host.E] (Fin r → D.host.E) := LinearMap.pi (fun i => (VS D).hT (F.e i))
  have hΨ : ∀ y i, Ψ y i = (VS D).hT (F.e i) y := fun _ _ => rfl
  have hsurj : Function.Surjective Ψ := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := (LinearMap.range Ψ).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hne)
    apply hφ0
    have hsum : ∀ v : Fin r → D.host.E, φ v = ∑ i, v i * φ (fun j => if i = j then 1 else 0) := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      simp only [smul_eq_mul]
    have hz : ∀ y, ∑ i, (VS D).hT (F.e i) y * φ (fun j => if i = j then 1 else 0) = 0 := by
      intro y
      have h := hφ (LinearMap.mem_range_self Ψ y)
      rw [LinearMap.mem_ker, hsum] at h
      simpa only [hΨ] using h
    have hx : ∀ y, (VS D).hT (∑ i, star (φ (fun j => if i = j then 1 else 0)) • F.e i) y = 0 := by
      intro y
      rw [map_sum, LinearMap.sum_apply]
      refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (hz y)
      rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul, mul_comm]
    have hx0 := (VS D).nondeg.1 _ hx
    have hc : ∀ i, φ (fun j => if i = j then 1 else 0) = 0 := by
      intro i
      have h := Fintype.linearIndependent_iff.mp F.e_indep _ hx0 i
      simpa using h
    refine LinearMap.ext fun v => ?_
    rw [hsum]
    simp [hc]
  choose y hy using fun j => hsurj (fun i => if i = j then (1 : D.host.E) else 0)
  refine ⟨y, fun i j => ?_⟩
  have h1 : (VS D).hT (F.e i) (y j) = if i = j then 1 else 0 := by
    rw [← hΨ, hy j]
  have h2 := LinearMap.isSymm_def.mp (VS D).herm (F.e i) (y j)
  rw [brS, ← h2, h1, starRingEnd_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hU : ∀ a, IsUnit (frFac Z.δ p a)`. Introduce `a`. Conclude with `((Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow (D.R.rS - a.val)).ringInverse`. Establish `hlast : frFac Z.δ p (Fin.last D.R.rS) = 1` using `by simp [frFac]`. Establish `hsym : ∀ x y : (VS D).V, (VS D).hT y x = star ((VS D).hT x y)`.

Introduce `x y`. Rewrite using `[← LinearMap.isSymm_def.mp (VS D).herm x y, starRingEnd_apply]`. Take `⟨y, hy⟩` from `exists_dual_family_of_flag F.fl`. Use `(D.s.atP p).char0` as an intermediate fact. Use `GlobalTheory.LocDual.frameD_exists (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (scaled Z p (frame F)) (n : (D.s.atP p).Fp) (by exact_mod_cast _hn) ?_ ?_ ?_` and prove the remaining obligations.

Introduce `a b hab`. Simplify using `only [scaled]`. Rewrite using `[hs_lemma]`. Establish `h0 : brS (VS D) (frame F a) (frame F b) = 0`. Simplify using `only [frame, FlagG.fvec, brS]`.

Apply the tactic sequence `rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>`. Break down `Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl` into its components or cases. Simplify using `only [Fin.snoc_castSucc]`. Conclude with `F.fl.e_iso b' a'`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last]`.

Rewrite using `[hsym, F.fl.z_orth a', star_zero]`. Simplify using `only [Fin.snoc_castSucc, Fin.snoc_last]`. Conclude with `F.fl.z_orth b'`. Simplify using `at hab`. Rewrite using `[h0, map_zero, mul_zero]`.

Simplify using `only [scaled]`. Rewrite using `[hs_lemma, hlast, map_one, one_mul, one_mul]`. Simplify using `only [frame, FlagG.fvec, brS, Fin.snoc_last]`. Rewrite using `[F.fl.z_norm, map_neg, map_natCast, map_natCast]`. Use `⟨fun j => (Z.M p).L.cj (Ring.inverse (frFac Z.δ p j.castSucc)) • baseChange₂ D p (y j), fun i j => ?_⟩` and prove the remaining obligations.

Simplify using `only [scaled]`. Rewrite using `[hs_lemma, (Z.M p).L.cj_cj]`. Establish `hf : frame F i.castSucc = F.fl.e i`. Simplify using `only [frame, FlagG.fvec, Fin.snoc_castSucc]`. Rewrite using `[hf, hy]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[map_one, mul_one]`. Conclude with `Ring.mul_inverse_cancel _ (hU _)`. Rewrite using `[map_zero, mul_zero]`.
-/
theorem frame_ex (Z : LocDat D) (p : PlF D) (n : ℕ) (_hn : n ≠ 0) (F : LFlag (VS D) D.R.rS ((n : ℕ) : D.host.E)) :
    ∃ Fr : Formalism.MainNotions.S.LocNG.FrameD (locH Z p) D.R.rS, Fr.f = scaled Z p (frame F) ∧ Fr.T = (n : (D.s.atP p).Fp) := by
  have hU : ∀ a, IsUnit (frFac Z.δ p a) := by
    intro a
    exact ((Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow (D.R.rS - a.val)).ringInverse
  have hlast : frFac Z.δ p (Fin.last D.R.rS) = 1 := by simp [frFac]
  have hsym : ∀ x y : (VS D).V, (VS D).hT y x = star ((VS D).hT x y) := by
    intro x y
    rw [← LinearMap.isSymm_def.mp (VS D).herm x y, starRingEnd_apply]
  obtain ⟨y, hy⟩ := exists_dual_family_of_flag F.fl
  have := (D.s.atP p).char0
  refine GlobalTheory.LocDual.frameD_exists (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (scaled Z p (frame F))
    (n : (D.s.atP p).Fp) (by exact_mod_cast _hn) ?_ ?_ ?_
  · intro a b hab
    simp only [scaled]
    rw [hs_lemma]
    have h0 : brS (VS D) (frame F a) (frame F b) = 0 := by
      simp only [frame, FlagG.fvec, brS]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.snoc_castSucc]
        exact F.fl.e_iso b' a'
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [hsym, F.fl.z_orth a', star_zero]
      · simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact F.fl.z_orth b'
      · simp at hab
    rw [h0, map_zero, mul_zero]
  · simp only [scaled]
    rw [hs_lemma, hlast, map_one, one_mul, one_mul]
    simp only [frame, FlagG.fvec, brS, Fin.snoc_last]
    rw [F.fl.z_norm, map_neg, map_natCast, map_natCast]
  · refine ⟨fun j => (Z.M p).L.cj (Ring.inverse (frFac Z.δ p j.castSucc)) • baseChange₂ D p (y j), fun i j => ?_⟩
    simp only [scaled]
    rw [hs_lemma, (Z.M p).L.cj_cj]
    have hf : frame F i.castSucc = F.fl.e i := by
      simp only [frame, FlagG.fvec, Fin.snoc_castSucc]
    rw [hf, hy]
    split_ifs with h
    · subst h
      rw [map_one, mul_one]
      exact Ring.mul_inverse_cancel _ (hU _)
    · rw [map_zero, mul_zero]

/- English proof (translation)
Introduce `D Z u u' w F00 F'0 hw hG p`. Establish `hn : Tu D u ≠ 0` using `(D.mem u).A.T_prime.ne_zero`. Establish `hn' : Tu D u' ≠ 0` using `(D.mem u').A.T_prime.ne_zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨A, hA1, hA2⟩` from `frame_ex Z p (Tu D u) hn F00`.

Take `⟨B, hB1, hB2⟩` from `frame_ex Z p (Tu D u') hn' F'0`. Conclude with `⟨⟨A, B⟩, hA1, hB1, hA2, hB2⟩`. Introduce and unpack `P ⟨h1, h2, h3, h4⟩`. Conclude with `GlobalTheory.RelGPoint.relG_of_point (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k P (finrank_eq p) (GlobalTheory.LocOver.isPoint_of_scaled D Z p F00 F'0 w P hw h1 h2) (normsOK_of Z p u u' P h3 h4) (gv_ne_of Z p (Tu D u) (Tu D u') F00 F'0 P h1 h2 h3 h4 hG)`.
-/
theorem atBase_relG : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))
    (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)),
    ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → ∀ p : PlF D,
      (∃ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P) ∧
        ∀ P, AtBase Z p F00 F'0 (Tu D u) (Tu D u') P → P.RelG (LocNG.theta (Z.M p)) := by
  intro D Z u u' w F00 F'0 hw hG p
  have hn : Tu D u ≠ 0 := (D.mem u).A.T_prime.ne_zero
  have hn' : Tu D u' ≠ 0 := (D.mem u').A.T_prime.ne_zero
  refine ⟨?_, ?_⟩
  · obtain ⟨A, hA1, hA2⟩ := frame_ex Z p (Tu D u) hn F00
    obtain ⟨B, hB1, hB2⟩ := frame_ex Z p (Tu D u') hn' F'0
    exact ⟨⟨A, B⟩, hA1, hB1, hA2, hB2⟩
  · rintro P ⟨h1, h2, h3, h4⟩
    exact GlobalTheory.RelGPoint.relG_of_point (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k P (finrank_eq p)
      (GlobalTheory.LocOver.isPoint_of_scaled D Z p F00 F'0 w P hw h1 h2) (normsOK_of Z p u u' P h3 h4)
      (gv_ne_of Z p (Tu D u) (Tu D u') F00 F'0 P h1 h2 h3 h4 hG)

end GlobalTheory.LocBaseRel

end
