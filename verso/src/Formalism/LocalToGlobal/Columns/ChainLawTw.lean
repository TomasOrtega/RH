import Formalism.LocalToGlobal.Columns.ChainLawPsi
import Formalism.LocalToGlobal.Columns.ChainLawXiF
import Formalism.LocalToGlobal.Columns.ChainTwMain
import Formalism.LocalToGlobal.Columns.ChainTopLawB
import Formalism.LocalToGlobal.Columns.RowFormsSym
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional
import Formalism.LocalToGlobal.KernelLattices.KerHypAll
import Formalism.LocalToGlobal.Columns.ChainTwTop

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section TwG

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

open Classical in

/- English proof (translation)
Establish `hB` using `clL_base hok hX hPr hCh hs`. Establish `hpat : ocbXPat R.k R.rS j R.t g.1`. Take `⟨g', hg', hred'⟩` from `(hok.grpG j b w g.1).1 g.2`. Rewrite `hg'` using `[hb]`. Conclude with `(ocbGrpGLoc_holds Ch sel mu cst m2 hB j hj w g.1).1 ⟨g', hg', hred'⟩`.

Take `⟨hk, hr, hrN, -⟩` from `ranks_frame_inequalities R hB.hm hj`. Establish `hq` using `ciQ_mem w.1`. Establish `hu` using `ciQ_notMem_sq hB.hX hB.hPr w.2`. Establish `hq0` using `ciQ_ne_zero hu`. Establish `hmS : R.m = 2 * R.rS + 2`.

Unfold `Ranks.rS`. Take `⟨a, ha⟩` from `R.m_even`. Use `R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hrr : R.r = R.k + 2 * R.rS + 1`.

Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `hcj : cOf R j + j = 2 * R.rS + 1`. Use `hB.hm` as an intermediate fact. Unfold `cOf`.

Use linear arithmetic over natural numbers and integers. Establish `hJat : Jat (Pr` using `Pr) cst.sharp j w.1 = LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by`. Unfold `Jat`. Rewrite using `[if_pos w.2, hB.sharp, if_pos rfl]`. Use `set Gm := LinearMap.toMatrix' κ.toLinearMap with hGm`.

Establish `hκi : κ.symm ∈ GLint X.E (R.N j) w.1` using `(GLint X.E (R.N j) w.1).inv_mem hκ`. Establish `hGi : ∀ i i', IntAt w.1 (Gm i i')`. Introduce `i i'`. Rewrite using `[hGm, LinearMap.toMatrix'_apply]`. Conclude with `(ciMem_stdAt w.1 _).1 ((hκ _).2 (ciSingle_mem i')) i`.

Establish `hGii : ∀ i i', IntAt w.1 (LinearMap.toMatrix' κ.symm.toLinearMap i i')`. Introduce `i i'`. Rewrite using `[LinearMap.toMatrix'_apply]`. Conclude with `(ciMem_stdAt w.1 _).1 ((hκi _).2 (ciSingle_mem i')) i`. Establish `hGred : ∀ i i', redP w.1 (Gm i i') = g.1.1 i i'`.

Introduce `i i'`. Apply the tactic sequence `rw [ciEntry hred i i', hGm, LinearMap.toMatrix'_apply]`. Both sides reduce to the same expression. Establish `hE1` using `clL_extM_mul (cOf R j) κ`. Establish `hE2` using `clL_extM_mul' (cOf R j) κ`.

Establish `hap : ∀ v, clL_ext (cOf R j) κ v = (ciExtM (cOf R j) Gm).mulVec v` using `fun v => clL_ext_apply _ κ v`. Establish `he : ∀ (A : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E), (∀ i i', IntAt w.1 (A i i')) → ∀ l l' : Fin (R.N j), IntAt w.1 (A l l' * ((qOf w.1 : ℕ) : X.E) ^ (LocE.scE (R.N j) (fun i => i + 1) l'.1 - LocE.scE (R.N j) (fun i => i + 1) l.1))`. Introduce `A hA l l'`. Rewrite using `[ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]`. Conclude with `hA _ _`.

Establish `hS : clL_ext (cOf R j) κ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1)` using `ciEquiv_stab (fun v hv => ciExtM_maps hq0 Gm _ (he Gm hGi) v hv) (fun v hv => ciExtM_maps hq0 _ _ (he _ hGii) v hv)`. Establish `hM` using `reducedMatrix_blockExtension (P := w.1) (q := qOf w.1) Gm _ hap`. Establish `hJ : clL_ext (cOf R j) κ ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j)`. Use `mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hS ?_ ?_ ?_` and prove the remaining obligations. Introduce `y y' hlt`.

Rewrite using `[hM]`. Use `split_ifs with h1 h2`. Rewrite using `[hGred]`. Assume the negation of the conclusion as `hnz`. Establish `hne : y.1 ≠ y'.1` using `fun he' => by`.

Establish `hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y'.1) < betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y.1)` using `hlt`. Rewrite `hlt'` using `[he']`. Conclude with `lt_irrefl _ hlt'`. Establish `hall` using `hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)`. Use `not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inl ?_) hall` and prove the remaining obligations.

Rewrite using `[← hrr]`. Conclude with `hlt`. Substitute `h2` using the available equality. Conclude with `absurd hlt (lt_irrefl _)`. Both sides reduce to the same expression.

Introduce `y hy`. Rewrite using `[hM]`. Use `split_ifs with h1 h2`. Rewrite using `[hGred]`. Establish `hyk : y.1 < R.k + j`.

Rewrite `hy` using `[framePos_of_lt_dim h1.1, hrr]`. Apply the tactic sequence `split_ifs at hy <;> omega`. Establish `h3` using `hpat.1 y.1 hyk`. Unfold `ocbM at h3`. Rewrite `h3` using `[dif_pos ⟨h1.1, h1.1⟩]`.

Conclude with `h3`. Both sides reduce to the same expression. Conclude with `absurd rfl h2`. Introduce `y y' hy hy'`. Rewrite using `[hM]`.

Use `split_ifs with h1 h2`. Rewrite using `[hGred]`. Assume the negation of the conclusion as `hnz`. Establish `hne : y.1 ≠ y'.1`. Introduce `he'`.

Rewrite `hy` using `[he']`. Use linear arithmetic over natural numbers and integers. Establish `hall` using `hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)`. Conclude with `not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inr ⟨hy, hy'⟩) hall`. Substitute `h2` using the available equality.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Use `⟨hJ, ?_⟩` and prove the remaining obligations. Establish `hr1 : clL_ext (cOf R j) κ ∈ Loc.Cbe (Jat (Pr` using `Pr) cst.sharp j w.1) (L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩) := by`. Rewrite using `[hb]`.

Use `Subgroup.mem_inf.2 ⟨extended_matrix_in_reduction _ _ hE1 hE2, Subgroup.mem_comap.2 ?_⟩` and prove the remaining obligations. Simplify `hJ` using `[MulAut.conj_apply, hJat]`. Establish `hlam` using `hok.chrG j b w g κ (clL_ext (cOf R j) κ) hr1 (fun x => clL_ext_inX _ κ x) hred`. Rewrite using `[hlam]`. Unfold `chiInv`.

Rewrite using `[hb]`. Establish `hn1 : Loc.n1Arg (clL_ext (cOf R j) κ) = 0`. Unfold `Loc.n1Arg`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i < cOf R j - 1` using `Finset.mem_range.1 hi`.

Unfold `Loc.atN`. Rewrite using `[dif_pos (by omega)]`. Establish `e1 : (⟨R.N j + i, by omega⟩ : Fin (R.N j + cOf R j)) = Fin.natAdd (R.N j) ⟨i, by omega⟩` using `rfl`. Rewrite using `[e1, clL_ext_natAdd]`. Unfold `Loc.eN`.

Simplify using the standard rewrite rules. Rewrite using `[hn1, hok.cst_ok.psi_int _ 0 (ChainCounts.intAt_zero _), inv_one, one_mul]`. Unfold `lamRow`. Rewrite using `[if_pos w.2, hs, if_pos rfl]`. Simplify using the standard rewrite rules.
-/
theorem clW_bridge (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true)
    {j : ℕ} (hj : j ≤ m2 + 1) (b : L.β j) (w : {w // w ∈ Pr.vGs}) (hb : L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩ = 1) (g : ↥(L.levG j b w).H)
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w.1)
    (hred : ∀ x ∈ stdAt X.E (R.N j) w.1, redV w.1 (κ x) = g.1.1.mulVec (redV w.1 x)) :
    clL_ext (cOf R j) κ ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) ∧
      LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t j (R.N j) (cOf R j) (clL_ext (cOf R j) κ).toLinearMap =
        (((L.levG j b w).lam g : X.Kˣ) : X.K) := by
  classical
  have hB := clL_base hok hX hPr hCh hs

  have hpat : ocbXPat R.k R.rS j R.t g.1 := by
    obtain ⟨g', hg', hred'⟩ := (hok.grpG j b w g.1).1 g.2
    rw [hb] at hg'
    exact (ocbGrpGLoc_holds Ch sel mu cst m2 hB j hj w g.1).1 ⟨g', hg', hred'⟩
  obtain ⟨hk, hr, hrN, -⟩ := ranks_frame_inequalities R hB.hm hj
  have hq := ciQ_mem w.1
  have hu := ciQ_notMem_sq hB.hX hB.hPr w.2
  have hq0 := ciQ_ne_zero hu
  have hmS : R.m = 2 * R.rS + 2 := by
    unfold Ranks.rS
    obtain ⟨a, ha⟩ := R.m_even
    have := R.two_le_m
    omega
  have hrr : R.r = R.k + 2 * R.rS + 1 := by
    unfold Ranks.r
    omega
  have hcj : cOf R j + j = 2 * R.rS + 1 := by
    have := hB.hm
    unfold cOf
    omega
  have hJat : Jat (Pr := Pr) cst.sharp j w.1 = LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    unfold Jat
    rw [if_pos w.2, hB.sharp, if_pos rfl]

  set Gm := LinearMap.toMatrix' κ.toLinearMap with hGm
  have hκi : κ.symm ∈ GLint X.E (R.N j) w.1 := (GLint X.E (R.N j) w.1).inv_mem hκ
  have hGi : ∀ i i', IntAt w.1 (Gm i i') := by
    intro i i'
    rw [hGm, LinearMap.toMatrix'_apply]
    exact (ciMem_stdAt w.1 _).1 ((hκ _).2 (ciSingle_mem i')) i
  have hGii : ∀ i i', IntAt w.1 (LinearMap.toMatrix' κ.symm.toLinearMap i i') := by
    intro i i'
    rw [LinearMap.toMatrix'_apply]
    exact (ciMem_stdAt w.1 _).1 ((hκi _).2 (ciSingle_mem i')) i
  have hGred : ∀ i i', redP w.1 (Gm i i') = g.1.1 i i' := by
    intro i i'
    rw [ciEntry hred i i', hGm, LinearMap.toMatrix'_apply]
    rfl
  have hE1 := clL_extM_mul (cOf R j) κ
  have hE2 := clL_extM_mul' (cOf R j) κ
  have hap : ∀ v, clL_ext (cOf R j) κ v = (ciExtM (cOf R j) Gm).mulVec v := fun v => clL_ext_apply _ κ v
  have he : ∀ (A : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E), (∀ i i', IntAt w.1 (A i i')) → ∀ l l' : Fin (R.N j),
      IntAt w.1 (A l l' * ((qOf w.1 : ℕ) : X.E) ^ (LocE.scE (R.N j) (fun i => i + 1) l'.1 - LocE.scE (R.N j) (fun i => i + 1) l.1)) := by
    intro A hA l l'
    rw [ciScE_lt _ l.2, ciScE_lt _ l'.2, sub_self, zpow_zero, mul_one]
    exact hA _ _
  have hS : clL_ext (cOf R j) κ ∈ stabL X.E _ (LocE.lamY w.1 (qOf w.1) (R.N j) (cOf R j) fun i => i + 1) :=
    ciEquiv_stab (fun v hv => ciExtM_maps hq0 Gm _ (he Gm hGi) v hv)
      (fun v hv => ciExtM_maps hq0 _ _ (he _ hGii) v hv)
  have hM := reducedMatrix_blockExtension (P := w.1) (q := qOf w.1) Gm _ hap
  have hJ : clL_ext (cOf R j) κ ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N j) (cOf R j) := by
    refine mem_parahoric_of_blockTriangular hq hu hk hr (by omega) hS ?_ ?_ ?_
    · intro y y' hlt
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        by_contra hnz
        have hne : y.1 ≠ y'.1 := fun he' => by
          have hlt' : betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y'.1) <
              betaExponentOfRanks R.k R.rS R.r R.t (LocE.fPos R.k (cOf R j) (R.N j) y.1) := hlt
          rw [he'] at hlt'
          exact lt_irrefl _ hlt'
        have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
        refine not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inl ?_) hall
        rw [← hrr]
        exact hlt
      · subst h2
        exact absurd hlt (lt_irrefl _)
      · rfl
    · intro y hy
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        have hyk : y.1 < R.k + j := by
          rw [framePos_of_lt_dim h1.1, hrr] at hy
          split_ifs at hy <;> omega
        have h3 := hpat.1 y.1 hyk
        unfold ocbM at h3
        rw [dif_pos ⟨h1.1, h1.1⟩] at h3
        exact h3
      · rfl
      · exact absurd rfl h2
    · intro y y' hy hy'
      rw [hM]
      split_ifs with h1 h2
      · rw [hGred]
        by_contra hnz
        have hne : y.1 ≠ y'.1 := by
          intro he'
          rw [he'] at hy
          omega
        have hall := hpat.2 y.1 y'.1 h1.1 h1.2 hne (by unfold ocbM; rw [dif_pos h1]; exact hnz)
        exact not_allowed_of_beta_lt (t := R.t) hcj h1.1 h1.2 (Or.inr ⟨hy, hy'⟩) hall
      · subst h2
        omega
      · rfl
  refine ⟨hJ, ?_⟩

  have hr1 : clL_ext (cOf R j) κ ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (L.h j b ⟨w.1, Finset.mem_union_left _ w.2⟩) := by
    rw [hb]
    refine Subgroup.mem_inf.2 ⟨extended_matrix_in_reduction _ _ hE1 hE2, Subgroup.mem_comap.2 ?_⟩
    simpa [MulAut.conj_apply, hJat] using hJ
  have hlam := hok.chrG j b w g κ (clL_ext (cOf R j) κ) hr1 (fun x => clL_ext_inX _ κ x) hred
  rw [hlam]
  unfold chiInv
  rw [hb]
  have hn1 : Loc.n1Arg (clL_ext (cOf R j) κ) = 0 := by
    unfold Loc.n1Arg
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : i < cOf R j - 1 := Finset.mem_range.1 hi
    unfold Loc.atN
    rw [dif_pos (by omega)]
    have e1 : (⟨R.N j + i, by omega⟩ : Fin (R.N j + cOf R j)) = Fin.natAdd (R.N j) ⟨i, by omega⟩ := rfl
    rw [e1, clL_ext_natAdd]
    unfold Loc.eN
    simp
  rw [hn1, hok.cst_ok.psi_int _ 0 (ChainCounts.intAt_zero _), inv_one, one_mul]
  unfold lamRow
  rw [if_pos w.2, hs, if_pos rfl]
  simp

/- English proof (translation)
Introduce `i hi al be P hP h h' κ κ' hκ hκ' y`. Establish `hal` using `hone i (by omega) al P hP`. Establish `hbe` using `hone (i + 1) (by omega) be P hP`. Take `⟨hJ, hlam⟩` from `clW_bridge hok hX hPr hCh hs (j := i) (by omega) al ⟨P.1, hP⟩ hal h⁻¹ κ.1 κ.2 (fun x hx => by rw [hκ x hx]; rfl)`. Take `⟨hJ', -⟩` from `clW_bridge hok hX hPr hCh hs (j := i + 1) (by omega) be ⟨P.1, hP⟩ hbe h'⁻¹ κ'.1 κ'.2 (fun x hx => by rw [hκ' x hx]; rfl)`.

Establish `hκs : κ'.1.symm ∈ GLint X.E (R.N (i + 1)) P.1` using `(GLint X.E (R.N (i + 1)) P.1).inv_mem κ'.2`. Take `⟨-, hlam'⟩` from `clW_bridge hok hX hPr hCh hs (j := i + 1) (by omega) be ⟨P.1, hP⟩ hbe h' κ'.1.symm hκs (fun x hx => by`. Establish `hy : κ'.1.symm x ∈ stdAt X.E (R.N (i + 1)) P.1` using `(hκs x).2 hx`. Establish `e` using `hκ' _ hy`. Rewrite `e` using `[LinearEquiv.apply_symm_apply]`.

Rewrite using `[e, Matrix.mulVec_mulVec]`. Establish `hm1 : (h'.1.1 : Matrix (Fin (R.N (i + 1))) (Fin (R.N (i + 1))) (𝓞 X.E ⧸ P.1.asIdeal)) * (h'.1⁻¹).1 = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Rewrite using `[hm1, Matrix.one_mulVec])`. Establish `hE` using `hXi i hi P hP κ.1 κ'.1 κ.2 κ'.2 hJ hJ' y`.

Establish `hXiAt : ∀ x, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x = (Loc.volN X.K (Loc.Cbe (Jat (Pr` using `Pr) cst.sharp (i + 1) P.1) 1) (Loc.N1 X.E (R.N (i + 1)) (cOf R (i + 1)) ⊓ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)))⁻¹ * E1at Ch sel mu cst i P 1 1 x := by`. Introduce `x`. Unfold `XiAt`. Rewrite using `[hal, hbe]`. Rewrite using `[hXiAt, hXiAt, hE]`.

Establish `hd` using `intAt_det κ.1 κ.2`. Establish `hd'` using `intAt_det_inv κ.1 κ.2`. Establish `hd0 : ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) ≠ 0` using `Units.ne_zero _`. Establish `he` using `intAt_det κ'.1 κ'.2`. Establish `he'` using `intAt_det_inv κ'.1 κ'.2`.

Establish `he0 : ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E) ≠ 0` using `Units.ne_zero _`. Establish `hu` using `clX_unitV_ne (chiP Ch P.1 i) (isUnit_reduction_of_integralAt_inv hd hd' hd0)`. Establish `hv` using `clX_unitV_ne (chiP Ch P.1 i) (isUnit_reduction_of_integralAt_inv he he' he0)`. Establish `hsymm : ((LinearEquiv.det κ'.1.symm : X.Eˣ) : X.E) = ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E)⁻¹`. Rewrite using `[LinearEquiv.det_symm]`.

Apply the tactic sequence `try rw [map_inv]`. Rewrite using `[Units.val_inv_eq_inv_val]`. Establish `hS : rhoS Ch sel mu i P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ.1 : X.Eˣ) : X.E)`. Unfold `rhoS`. Rewrite using `[if_pos hP]`.

Establish `hT : rhoT Ch sel mu i P ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E) = (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E))⁻¹`. Unfold `rhoT`. Rewrite using `[if_pos hP, unitV_inv]`. Rewrite using `[hS, hT, hsymm, clX_unitV_inv _ he he' he0, hlam, hlam', map_inv, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.
-/
theorem clW_xiLaw (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true)
    (hone : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) (hXi : ∀ i, i < m2 → FirstUnfoldingJInvarianceLaw Ch sel mu cst i) :
    ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLaw Ch sel mu cst L i al be := by
  intro i hi al be P hP h h' κ κ' hκ hκ' y
  have hal := hone i (by omega) al P hP
  have hbe := hone (i + 1) (by omega) be P hP
  obtain ⟨hJ, hlam⟩ := clW_bridge hok hX hPr hCh hs (j := i) (by omega) al ⟨P.1, hP⟩ hal h⁻¹ κ.1 κ.2
    (fun x hx => by rw [hκ x hx]; rfl)
  obtain ⟨hJ', -⟩ := clW_bridge hok hX hPr hCh hs (j := i + 1) (by omega) be ⟨P.1, hP⟩ hbe h'⁻¹ κ'.1 κ'.2
    (fun x hx => by rw [hκ' x hx]; rfl)
  have hκs : κ'.1.symm ∈ GLint X.E (R.N (i + 1)) P.1 := (GLint X.E (R.N (i + 1)) P.1).inv_mem κ'.2
  obtain ⟨-, hlam'⟩ := clW_bridge hok hX hPr hCh hs (j := i + 1) (by omega) be ⟨P.1, hP⟩ hbe h' κ'.1.symm hκs
    (fun x hx => by
      have hy : κ'.1.symm x ∈ stdAt X.E (R.N (i + 1)) P.1 := (hκs x).2 hx
      have e := hκ' _ hy
      rw [LinearEquiv.apply_symm_apply] at e
      rw [e, Matrix.mulVec_mulVec]
      have hm1 : (h'.1.1 : Matrix (Fin (R.N (i + 1))) (Fin (R.N (i + 1))) (𝓞 X.E ⧸ P.1.asIdeal)) * (h'.1⁻¹).1 = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hm1, Matrix.one_mulVec])
  have hE := hXi i hi P hP κ.1 κ'.1 κ.2 κ'.2 hJ hJ' y
  have hXiAt : ∀ x, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) x =
      (Loc.volN X.K (Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) P.1) 1)
        (Loc.N1 X.E (R.N (i + 1)) (cOf R (i + 1)) ⊓ stabL X.E _ (lamYat (Pr := Pr) (i + 1) P.1)))⁻¹ * E1at Ch sel mu cst i P 1 1 x := by
    intro x
    unfold XiAt
    rw [hal, hbe]
  rw [hXiAt, hXiAt, hE]

  have hd := intAt_det κ.1 κ.2
  have hd' := intAt_det_inv κ.1 κ.2
  have hd0 : ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have he := intAt_det κ'.1 κ'.2
  have he' := intAt_det_inv κ'.1 κ'.2
  have he0 : ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have hu := clX_unitV_ne (chiP Ch P.1 i) (isUnit_reduction_of_integralAt_inv hd hd' hd0)
  have hv := clX_unitV_ne (chiP Ch P.1 i) (isUnit_reduction_of_integralAt_inv he he' he0)
  have hsymm : ((LinearEquiv.det κ'.1.symm : X.Eˣ) : X.E) = ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E)⁻¹ := by
    rw [LinearEquiv.det_symm]
    try rw [map_inv]
    rw [Units.val_inv_eq_inv_val]
  have hS : rhoS Ch sel mu i P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    rw [if_pos hP]
  have hT : rhoT Ch sel mu i P ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E) =
      (LocE.unitV (chiP Ch P.1 i) ((LinearEquiv.det κ'.1 : X.Eˣ) : X.E))⁻¹ := by
    unfold rhoT
    rw [if_pos hP, unitV_inv]
  rw [hS, hT, hsymm, clX_unitV_inv _ he he' he0, hlam, hlam', map_inv, Units.val_inv_eq_inv_val]
  field_simp

/- English proof (translation)
Introduce `P hP h₀ h κ₀ κ hκ₀ hκ x₀ y'`. Establish `hal` using `hone m2 (by omega) al P hP`. Establish `hb` using `hone (m2 + 1) le_rfl b P hP`. Take `⟨hJ₀, hlam₀⟩` from `clW_bridge hok hX hPr hCh hs (j := m2) (by omega) al ⟨P.1, hP⟩ hal h₀⁻¹ κ₀.1 κ₀.2 (fun x hx => by rw [hκ₀ x hx]; rfl)`. Establish `hκs : κ.1.symm ∈ GLint X.E (R.N (m2 + 1)) P.1` using `(GLint X.E (R.N (m2 + 1)) P.1).inv_mem κ.2`.

Take `⟨hJ, hlam⟩` from `clW_bridge hok hX hPr hCh hs (j := m2 + 1) le_rfl b ⟨P.1, hP⟩ hb h κ.1.symm hκs (fun x hx => by`. Establish `hy : κ.1.symm x ∈ stdAt X.E (R.N (m2 + 1)) P.1` using `(hκs x).2 hx`. Establish `e` using `hκ _ hy`. Rewrite `e` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[e, Matrix.mulVec_mulVec]`.

Establish `hm1 : (h.1.1 : Matrix (Fin (R.N (m2 + 1))) (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ P.1.asIdeal)) * (h.1⁻¹).1 = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Rewrite using `[hm1, Matrix.one_mulVec])`. Establish `hPsi : ∀ (z₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (z : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 P (L.h m2 al P) z₀ z = (muAt Ch sel mu cst m2 P ((LinearEquiv.det (1 : AutY X R m2) : X.Eˣ) : X.E) * (muAt Ch sel mu cst m2 P ((LinearEquiv.det (1 : AutY X R (m2 + 1)) : X.Eˣ) : X …`. Introduce `z₀ z`.

Rewrite using `[hal]`. Unfold `PsiAt omPhi Loc.om PhiAt`. Rewrite using `[if_pos hP, hs, if_pos rfl]`. Both sides reduce to the same expression. Rewrite using `[hPsi, hPsi, clPsi_joinCol, hΦ P.1 hP _ hJ _ hJ₀]`.

Simplify using `only [Nat.add_sub_cancel]`. Apply the tactic sequence `try simp only [Subtype.coe_mk] at hlam hlam₀`. Rewrite using `[hlam, hlam₀]`. Establish `he` using `intAt_det κ.1 κ.2`. Establish `he'` using `intAt_det_inv κ.1 κ.2`.

Establish `he0 : ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) ≠ 0` using `Units.ne_zero _`. Establish `hd` using `intAt_det κ₀.1 κ₀.2`. Establish `hd'` using `intAt_det_inv κ₀.1 κ₀.2`. Establish `hd0 : ((LinearEquiv.det κ₀.1 : X.Eˣ) : X.E) ≠ 0` using `Units.ne_zero _`. Establish `hu` using `clX_unitV_ne (chiP Ch P.1 m2) (isUnit_reduction_of_integralAt_inv hd hd' hd0)`.

Establish `hv` using `clX_unitV_ne (chiP Ch P.1 m2) (isUnit_reduction_of_integralAt_inv he he' he0)`. Establish `hsymm : ((LinearEquiv.det κ.1.symm : X.Eˣ) : X.E) = ((LinearEquiv.det κ.1 : X.Eˣ) : X.E)⁻¹`. Rewrite using `[LinearEquiv.det_symm]`. Apply the tactic sequence `try rw [map_inv]`. Rewrite using `[Units.val_inv_eq_inv_val]`.

Establish `hS : rhoS Ch sel mu m2 P ((LinearEquiv.det κ₀.1 : X.Eˣ) : X.E) = LocE.unitV (chiP Ch P.1 m2) ((LinearEquiv.det κ₀.1 : X.Eˣ) : X.E)`. Unfold `rhoS`. Rewrite using `[if_pos hP]`. Establish `hT : rhoT Ch sel mu m2 P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = (LocE.unitV (chiP Ch P.1 m2) ((LinearEquiv.det κ.1 : X.Eˣ) : X.E))⁻¹`. Unfold `rhoT`.

Rewrite using `[if_pos hP, unitV_inv]`. Rewrite using `[hS, hT, clL_ext_det, clL_ext_det, hsymm, clX_unitV_inv _ he he' he0, map_inv, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.
-/
theorem clW_psiLaw (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true)
    (hone : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1)
    (hΦ : ∀ P ∈ Pr.vGs, PhiGSLaw P (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.rS R.r R.t (m2 + 1) (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1)))
    (al : L.β m2) (b : L.β (m2 + 1)) : PsiLaw Ch sel mu cst L m2 al b := by
  intro P hP h₀ h κ₀ κ hκ₀ hκ x₀ y'
  have hal := hone m2 (by omega) al P hP
  have hb := hone (m2 + 1) le_rfl b P hP
  obtain ⟨hJ₀, hlam₀⟩ := clW_bridge hok hX hPr hCh hs (j := m2) (by omega) al ⟨P.1, hP⟩ hal h₀⁻¹ κ₀.1 κ₀.2
    (fun x hx => by rw [hκ₀ x hx]; rfl)
  have hκs : κ.1.symm ∈ GLint X.E (R.N (m2 + 1)) P.1 := (GLint X.E (R.N (m2 + 1)) P.1).inv_mem κ.2
  obtain ⟨hJ, hlam⟩ := clW_bridge hok hX hPr hCh hs (j := m2 + 1) le_rfl b ⟨P.1, hP⟩ hb h κ.1.symm hκs
    (fun x hx => by
      have hy : κ.1.symm x ∈ stdAt X.E (R.N (m2 + 1)) P.1 := (hκs x).2 hx
      have e := hκ _ hy
      rw [LinearEquiv.apply_symm_apply] at e
      rw [e, Matrix.mulVec_mulVec]
      have hm1 : (h.1.1 : Matrix (Fin (R.N (m2 + 1))) (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ P.1.asIdeal)) * (h.1⁻¹).1 = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      rw [hm1, Matrix.one_mulVec])

  have hPsi : ∀ (z₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (z : Sp X.E (R.N (m2 + 1))),
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) z₀ z =
        (muAt Ch sel mu cst m2 P ((LinearEquiv.det (1 : AutY X R m2) : X.Eˣ) : X.E) *
            (muAt Ch sel mu cst m2 P ((LinearEquiv.det (1 : AutY X R (m2 + 1)) : X.Eˣ) : X.E))⁻¹ *
            cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) ((LinearEquiv.det (1 : AutY X R m2) : X.Eˣ) : X.E)) * (R.N (m2 + 1) + cOf R (m2 + 1))) *
            cst.sq P ^ (LocE.vP P.1 (qOf P.1) ((LinearEquiv.det (1 : AutY X R (m2 + 1)) : X.Eˣ) : X.E) * (R.N m2 + cOf R m2))) *
          LocE.PhiGS (qOf P.1) (psi0P Ch P.1) (chiP Ch P.1) R.k R.rS R.r R.t (m2 + 1) (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1))
            (joinCol z₀ z) := by
    intro z₀ z
    rw [hal]
    unfold PsiAt omPhi Loc.om PhiAt
    rw [if_pos hP, hs, if_pos rfl]
    rfl
  rw [hPsi, hPsi, clPsi_joinCol, hΦ P.1 hP _ hJ _ hJ₀]
  simp only [Nat.add_sub_cancel]
  try simp only [Subtype.coe_mk] at hlam hlam₀
  rw [hlam, hlam₀]
  have he := intAt_det κ.1 κ.2
  have he' := intAt_det_inv κ.1 κ.2
  have he0 : ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have hd := intAt_det κ₀.1 κ₀.2
  have hd' := intAt_det_inv κ₀.1 κ₀.2
  have hd0 : ((LinearEquiv.det κ₀.1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have hu := clX_unitV_ne (chiP Ch P.1 m2) (isUnit_reduction_of_integralAt_inv hd hd' hd0)
  have hv := clX_unitV_ne (chiP Ch P.1 m2) (isUnit_reduction_of_integralAt_inv he he' he0)
  have hsymm : ((LinearEquiv.det κ.1.symm : X.Eˣ) : X.E) = ((LinearEquiv.det κ.1 : X.Eˣ) : X.E)⁻¹ := by
    rw [LinearEquiv.det_symm]
    try rw [map_inv]
    rw [Units.val_inv_eq_inv_val]
  have hS : rhoS Ch sel mu m2 P ((LinearEquiv.det κ₀.1 : X.Eˣ) : X.E) = LocE.unitV (chiP Ch P.1 m2) ((LinearEquiv.det κ₀.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    rw [if_pos hP]
  have hT : rhoT Ch sel mu m2 P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) =
      (LocE.unitV (chiP Ch P.1 m2) ((LinearEquiv.det κ.1 : X.Eˣ) : X.E))⁻¹ := by
    unfold rhoT
    rw [if_pos hP, unitV_inv]
  rw [hS, hT, clL_ext_det, clL_ext_det, hsymm, clX_unitV_inv _ he he' he0, map_inv, Units.val_inv_eq_inv_val]
  field_simp

end TwG

section TopG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

/- English proof (translation)
Establish `hsub : (padM Rg n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A`. Use extensionality with `i j`. Simplify using `[padM, Fin.succAbove_last]`. Rewrite using `[Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc, hsub]`. Simplify using `[padM, Fin.val_last, ← two_mul, pow_mul]`.
-/
theorem clW_det_padM {Rg : Type} [CommRing Rg] {n : ℕ} (A : Matrix (Fin n) (Fin n) Rg) : (padM Rg n A).det = A.det := by
  have hsub : (padM Rg n A).submatrix (Fin.last n).succAbove (Fin.last n).succAbove = A := by
    ext i j
    simp [padM, Fin.succAbove_last]
  rw [Matrix.det_succ_row _ (Fin.last n), Fin.sum_univ_castSucc, hsub]
  simp [padM, Fin.val_last, ← two_mul, pow_mul]

/- English proof (translation)
Substitute `hN` using the available equality. Conclude with `clW_det_padM _`.
-/
theorem clW_det_extGH {n N : ℕ} (hN : N = n + 1) {SG : Finset (HeightOneSpectrum (𝓞 E))} (h : GLG E n SG) (w : SG) :
    ((extGH hN h w : GL (Fin N) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin N) (Fin N) (𝓞 E ⧸ w.1.asIdeal)).det =
      ((h w : GL (Fin n) (𝓞 E ⧸ w.1.asIdeal)) : Matrix (Fin n) (Fin n) (𝓞 E ⧸ w.1.asIdeal)).det := by
  subst hN
  exact clW_det_padM _

/- English proof (translation)
Unfold `LocE.unitV`. Use `split_ifs with h1 h2 h2`. Rewrite using `[show h1.unit = h2.unit from Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])]`. Rewrite `h1` using `[h]`. Conclude with `absurd h1 h2`.

Rewrite `h1` using `[h]`. Conclude with `absurd h2 h1`. Both sides reduce to the same expression.
-/
theorem clW_unitV_congr {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E} (h : redP P a = redP P b) :
    LocE.unitV χ a = LocE.unitV χ b := by
  unfold LocE.unitV
  split_ifs with h1 h2 h2
  · rw [show h1.unit = h2.unit from Units.ext (by rw [IsUnit.unit_spec, IsUnit.unit_spec, h])]
  · rw [h] at h1; exact absurd h1 h2
  · rw [h] at h1; exact absurd h2 h1
  · rfl

/- English proof (translation)
Substitute `hr` using the available equality. Apply `σ₀.injective` to reduce the goal to its premises. Rewrite using `[ctl_lamGBS_lamJ (RingEquiv.refl _) σ₀ ψ₀ χ hkr hn hκ hred, ctl_lamJsym_lamJ σ₀ ψ₀ χ ht hn h M]`.
-/
theorem clW_lamGBS_lamJsym {K : Type} [Field K] (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {n k₀ r t j rS : ℕ} (hr : r = k₀ + 2 * rS + 1) (ht : 0 < t) (hn : r + j * t ≤ n) (h : r ≤ n) (hkr : k₀ < r)
    (M : ↥(HJsym (𝓞 E ⧸ P.asIdeal) n k₀ r t j rS h)) (κ : Sp E n ≃ₗ[E] Sp E n) (hκ : κ ∈ GLint E n P)
    (hred : ∀ x ∈ stdAt E n P, redV P (κ x) = M.1.1.mulVec (redV P x)) :
    LocE.lamGBS q ψ₀ χ k₀ r t j n 0 κ.toLinearMap = ((lamJsym ψ₀ χ n k₀ r t j rS h M : Kˣ) : K) := by
  subst hr
  apply σ₀.injective
  rw [ctl_lamGBS_lamJ (RingEquiv.refl _) σ₀ ψ₀ χ hkr hn hκ hred, ctl_lamJsym_lamJ σ₀ ψ₀ χ ht hn h M]

end TopG

section TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

/- English proof (translation)
Introduce `w hw h h₁ hh₁ κ κr κt hκ hκr hκt y`. Take `⟨σ₀⟩ : Nonempty (X.K →+* ℂ)` from `inferInstance`. Establish `hB` using `clL_base hok hX hPr hCh hs`. Establish `hm` using `hB.hm`. Establish `hq` using `ciQ_mem w.1`.

Establish `hu` using `ciQ_notMem_sq hX hPr hw`. Establish `ht` using `t_pos R`. Establish `hrr` using `r_eq_sym R`. Establish `hX'` using `rank_X'_eq R`. Take `⟨hk1, hr1, hN1, -⟩` from `ranks_frame_inequalities R hm (j := m2 + 1) le_rfl`.

Take `⟨hJ, hlam⟩` from `clW_bridge hok hX hPr hCh hs (j := m2 + 1) le_rfl b ⟨w.1, hw⟩ (hb w hw) h⁻¹ κ.1 κ.2 (fun x hx => by rw [hκ x hx]; rfl)`. Establish `hH : h₁ w ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R)`. Establish `h2` using `hh₁`. Express the relevant statement in the definitionally equal form `h₁ w ∈ ((rowTyG Ch (rPsymF Ch)).glue (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K))) w).H at h2`. Rewrite `h2` using `[LevFam.glue_of_mem _ _ w hw]`.

Conclude with `h2`. Establish `hκrs : κr.1.symm ∈ GLint X.E (R.N R.m - 1) w.1` using `(GLint X.E (R.N R.m - 1) w.1).inv_mem κr.2`. Establish `hredr : ∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (κr.1.symm x) = (h₁ w).1.mulVec (redV w.1 x)`. Introduce `x hx`. Establish `hy : κr.1.symm x ∈ stdAt X.E (R.N R.m - 1) w.1` using `(hκrs x).2 hx`.

Establish `e` using `hκr _ hy`. Rewrite `e` using `[LinearEquiv.apply_symm_apply]`. Rewrite using `[e, Matrix.mulVec_mulVec]`. Establish `hm1 : ((h₁ w).1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) * ((h₁ w)⁻¹).1 = 1`. Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Rewrite using `[hm1, Matrix.one_mulVec]`. Establish `hγ : κr.1.symm ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0` using `ctl_mem_JGsym hq hu hr1 (by omega) (r_le_X' R) ht (by omega) hκrs hH hredr`. Establish `e1 : psi0P Ch w.1 = Ch.psi0 ⟨w.1, hw⟩`. Unfold `psi0P`. Rewrite using `[dif_pos hw]`.

Establish `e2 : chiP Ch w.1 = chiAt Ch ⟨w.1, hw⟩`. Unfold `chiP`. Rewrite using `[dif_pos hw]`. Establish `hlamT : LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 κr.1.symm.toLinearMap = ((lamJsym (Ch.psi0 ⟨w.1, hw⟩) (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h₁ w, hH⟩ : X.Kˣ) : X.K)`. Rewrite using `[e1, e2]`.

Conclude with `clW_lamGBS_lamJsym σ₀ _ _ hrr ht (by omega) (r_le_X' R) (by omega) ⟨h₁ w, hH⟩ κr.1.symm hκrs hredr`. Establish `hlamR : ((((rowTy Ch sel mu (rPsymF Ch)).inv w).lam ⟨h₁ w, hh₁⟩)⁻¹ : X.Kˣ) = lamJsym (Ch.psi0 ⟨w.1, hw⟩) (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h₁ w, hH⟩`. Establish `key : ∀ (l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N R.m - 1)), l = rowTy Ch sel mu (rPsymF Ch) w → ∀ (M : ↥l.H) (hM : M.1 ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R)), (l.inv.lam M)⁻¹ = lamJsym (Ch.psi0 ⟨w.1, hw⟩) (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R. …`. Introduce `l hl M hM`. Establish `hl' : l = rowTyG Ch (rPsymF Ch) ⟨w.1, hw⟩`.

Rewrite using `[hl]`. Conclude with `LevFam.glue_of_mem _ _ w hw`. Substitute `hl'` using the available equality. Use `show ((lamJsym _ _ _ _ _ _ _ _ _ M)⁻¹)⁻¹ = _`. Rewrite using `[inv_inv]`.

Both sides reduce to the same expression. Conclude with `key _ rfl ⟨h₁ w, hh₁⟩ hH`. Establish `hPhi : PhiTop Ch mu cst.sharp m2 w.1 = LocE.PhiGS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.rS R.r R.t R.m (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1)`. Unfold `PhiTop`. Rewrite using `[if_pos hw, hs, if_pos rfl]`.

Establish `harg : κr.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) = κr.1.symm.toLinearMap ∘ₗ (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) ∘ₗ (clL_ext (cOf R (m2 + 1)) κ.1).toLinearMap`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe]`. Rewrite using `[clPsi_restr]`.

Establish `hyp : PhiGSLawHyp w.1 (qOf w.1) R.k R.rS R.r R.t R.m (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1)` using `⟨hq, hu, by omega, hk1, by omega, hr1, ht, by rw [show R.m - 1 = m2 + 1 by omega]; exact hN1.symm, by omega⟩`. Establish `hlaw` using `clPf_phiGSLaw hyp (psi0P Ch w.1) (chiP Ch w.1) _ hγ _ hJ (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))`. Rewrite `hlaw` using `[show R.m - 1 = m2 + 1 by omega]`. Establish `hd` using `intAt_det κ.1 κ.2`. Establish `hd'` using `intAt_det_inv κ.1 κ.2`.

Establish `hd0 : ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) ≠ 0` using `Units.ne_zero _`. Establish `he` using `intAt_det κr.1 κr.2`. Establish `he'` using `intAt_det_inv κr.1 κr.2`. Establish `he0 : ((LinearEquiv.det κr.1 : X.Eˣ) : X.E) ≠ 0` using `Units.ne_zero _`. Establish `hu1` using `clX_unitV_ne (chiP Ch w.1 (m2 + 1)) (isUnit_reduction_of_integralAt_inv hd hd' hd0)`.

Establish `hu2` using `clX_unitV_ne (chiP Ch w.1 (m2 + 1)) (isUnit_reduction_of_integralAt_inv he he' he0)`. Establish `hsymm : ((LinearEquiv.det κr.1.symm : X.Eˣ) : X.E) = ((LinearEquiv.det κr.1 : X.Eˣ) : X.E)⁻¹`. Rewrite using `[LinearEquiv.det_symm]`. Apply the tactic sequence `try rw [map_inv]`. Rewrite using `[Units.val_inv_eq_inv_val]`.

Establish `hdt : LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κt.1 : X.Eˣ) : X.E) = LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κr.1 : X.Eˣ) : X.E)`. Apply `clW_unitV_congr` to reduce the goal to its premises. Rewrite using `[(ctl_det_red κt.2 hκt).2, (ctl_det_red κr.2 hκr).2]`. Rewrite using `[show (extGH (N_m_succ R) h₁ w)⁻¹ = extGH (N_m_succ R) h₁⁻¹ w by rw [map_inv]; rfl, clW_det_extGH]`. Both sides reduce to the same expression.

Establish `hS : rhoS Ch sel mu (m2 + 1) w ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) = LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κ.1 : X.Eˣ) : X.E)`. Unfold `rhoS`. Rewrite using `[if_pos hw]`. Establish `hT : rhoT Ch sel mu (m2 + 1) w ((LinearEquiv.det κt.1 : X.Eˣ) : X.E) = (LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κt.1 : X.Eˣ) : X.E))⁻¹`. Unfold `rhoT`.

Rewrite using `[if_pos hw, unitV_inv]`. Rewrite using `[hPhi, harg, hlaw, hlamT, hlam, hS, hT, hdt, clL_ext_det, hsymm, clX_unitV_inv _ he he' he0, hlamR, map_inv, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts.
-/
theorem clW_topLaw (hok : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true)
    (b : L.β (m2 + 1)) (hb : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → L.h (m2 + 1) b P = 1) :
    TopLaw Ch sel mu cst L (rPsymF Ch) m2 b := by
  intro w hw h h₁ hh₁ κ κr κt hκ hκr hκt y
  classical
  obtain ⟨σ₀⟩ : Nonempty (X.K →+* ℂ) := inferInstance
  have hB := clL_base hok hX hPr hCh hs
  have hm := hB.hm
  have hq := ciQ_mem w.1
  have hu := ciQ_notMem_sq hX hPr hw
  have ht := t_pos R
  have hrr := r_eq_sym R
  have hX' := rank_X'_eq R
  obtain ⟨hk1, hr1, hN1, -⟩ := ranks_frame_inequalities R hm (j := m2 + 1) le_rfl

  obtain ⟨hJ, hlam⟩ := clW_bridge hok hX hPr hCh hs (j := m2 + 1) le_rfl b ⟨w.1, hw⟩ (hb w hw) h⁻¹ κ.1 κ.2
    (fun x hx => by rw [hκ x hx]; rfl)

  have hH : h₁ w ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := by
    have h2 := hh₁
    change h₁ w ∈ ((rowTyG Ch (rPsymF Ch)).glue (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K))) w).H at h2
    rw [LevFam.glue_of_mem _ _ w hw] at h2
    exact h2
  have hκrs : κr.1.symm ∈ GLint X.E (R.N R.m - 1) w.1 := (GLint X.E (R.N R.m - 1) w.1).inv_mem κr.2
  have hredr : ∀ x ∈ stdAt X.E (R.N R.m - 1) w.1, redV w.1 (κr.1.symm x) = (h₁ w).1.mulVec (redV w.1 x) := by
    intro x hx
    have hy : κr.1.symm x ∈ stdAt X.E (R.N R.m - 1) w.1 := (hκrs x).2 hx
    have e := hκr _ hy
    rw [LinearEquiv.apply_symm_apply] at e
    rw [e, Matrix.mulVec_mulVec]
    have hm1 : ((h₁ w).1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) (𝓞 X.E ⧸ w.1.asIdeal)) * ((h₁ w)⁻¹).1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hm1, Matrix.one_mulVec]
  have hγ : κr.1.symm ∈ LocE.JGsym w.1 (qOf w.1) R.k R.rS R.r R.t (R.N R.m - 1) 0 :=
    ctl_mem_JGsym hq hu hr1 (by omega) (r_le_X' R) ht (by omega) hκrs hH hredr
  have e1 : psi0P Ch w.1 = Ch.psi0 ⟨w.1, hw⟩ := by
    unfold psi0P
    rw [dif_pos hw]
  have e2 : chiP Ch w.1 = chiAt Ch ⟨w.1, hw⟩ := by
    unfold chiP
    rw [dif_pos hw]
  have hlamT : LocE.lamGBS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.r R.t R.m (R.N R.m - 1) 0 κr.1.symm.toLinearMap =
      ((lamJsym (Ch.psi0 ⟨w.1, hw⟩) (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h₁ w, hH⟩ : X.Kˣ) : X.K) := by
    rw [e1, e2]
    exact clW_lamGBS_lamJsym σ₀ _ _ hrr ht (by omega) (r_le_X' R) (by omega) ⟨h₁ w, hH⟩ κr.1.symm hκrs hredr
  have hlamR : ((((rowTy Ch sel mu (rPsymF Ch)).inv w).lam ⟨h₁ w, hh₁⟩)⁻¹ : X.Kˣ) =
      lamJsym (Ch.psi0 ⟨w.1, hw⟩) (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨h₁ w, hH⟩ := by
    have key : ∀ (l : Lev (𝓞 X.E ⧸ w.1.asIdeal) X.K (R.N R.m - 1)), l = rowTy Ch sel mu (rPsymF Ch) w →
        ∀ (M : ↥l.H) (hM : M.1 ∈ HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R)),
          (l.inv.lam M)⁻¹ = lamJsym (Ch.psi0 ⟨w.1, hw⟩) (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) ⟨M.1, hM⟩ := by
      intro l hl M hM
      have hl' : l = rowTyG Ch (rPsymF Ch) ⟨w.1, hw⟩ := by
        rw [hl]
        exact LevFam.glue_of_mem _ _ w hw
      subst hl'
      show ((lamJsym _ _ _ _ _ _ _ _ _ M)⁻¹)⁻¹ = _
      rw [inv_inv]
      rfl
    exact key _ rfl ⟨h₁ w, hh₁⟩ hH
  have hPhi : PhiTop Ch mu cst.sharp m2 w.1 = LocE.PhiGS (qOf w.1) (psi0P Ch w.1) (chiP Ch w.1) R.k R.rS R.r R.t R.m
      (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) := by
    unfold PhiTop
    rw [if_pos hw, hs, if_pos rfl]
  have harg : κr.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) =
      κr.1.symm.toLinearMap ∘ₗ (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) ∘ₗ
        (clL_ext (cOf R (m2 + 1)) κ.1).toLinearMap := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [clPsi_restr]
  have hyp : PhiGSLawHyp w.1 (qOf w.1) R.k R.rS R.r R.t R.m (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) :=
    ⟨hq, hu, by omega, hk1, by omega, hr1, ht, by rw [show R.m - 1 = m2 + 1 by omega]; exact hN1.symm, by omega⟩
  have hlaw := clPf_phiGSLaw hyp (psi0P Ch w.1) (chiP Ch w.1) _ hγ _ hJ (y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))
  rw [show R.m - 1 = m2 + 1 by omega] at hlaw

  have hd := intAt_det κ.1 κ.2
  have hd' := intAt_det_inv κ.1 κ.2
  have hd0 : ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have he := intAt_det κr.1 κr.2
  have he' := intAt_det_inv κr.1 κr.2
  have he0 : ((LinearEquiv.det κr.1 : X.Eˣ) : X.E) ≠ 0 := Units.ne_zero _
  have hu1 := clX_unitV_ne (chiP Ch w.1 (m2 + 1)) (isUnit_reduction_of_integralAt_inv hd hd' hd0)
  have hu2 := clX_unitV_ne (chiP Ch w.1 (m2 + 1)) (isUnit_reduction_of_integralAt_inv he he' he0)
  have hsymm : ((LinearEquiv.det κr.1.symm : X.Eˣ) : X.E) = ((LinearEquiv.det κr.1 : X.Eˣ) : X.E)⁻¹ := by
    rw [LinearEquiv.det_symm]
    try rw [map_inv]
    rw [Units.val_inv_eq_inv_val]
  have hdt : LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κt.1 : X.Eˣ) : X.E) =
      LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κr.1 : X.Eˣ) : X.E) := by
    apply clW_unitV_congr
    rw [(ctl_det_red κt.2 hκt).2, (ctl_det_red κr.2 hκr).2]
    rw [show (extGH (N_m_succ R) h₁ w)⁻¹ = extGH (N_m_succ R) h₁⁻¹ w by rw [map_inv]; rfl, clW_det_extGH]
    rfl
  have hS : rhoS Ch sel mu (m2 + 1) w ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) =
      LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    rw [if_pos hw]
  have hT : rhoT Ch sel mu (m2 + 1) w ((LinearEquiv.det κt.1 : X.Eˣ) : X.E) =
      (LocE.unitV (chiP Ch w.1 (m2 + 1)) ((LinearEquiv.det κt.1 : X.Eˣ) : X.E))⁻¹ := by
    unfold rhoT
    rw [if_pos hw, unitV_inv]
  rw [hPhi, harg, hlaw, hlamT, hlam, hS, hT, hdt, clL_ext_det, hsymm, clX_unitV_inv _ he he' he0, hlamR, map_inv,
    Units.val_inv_eq_inv_val]
  field_simp

end TopLaw

section TwIdx

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} {m2 : ℕ}

end TwIdx

section TwTop

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {G : ChGlob X R.m} {m2 : ℕ}
  {Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs} {Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K))}

end TwTop

end Formalism.L2.Col
