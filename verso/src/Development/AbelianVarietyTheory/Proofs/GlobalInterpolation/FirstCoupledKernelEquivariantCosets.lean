import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulCompSmul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacterArgumentFirstParabolicShift
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep GlobalTheory.TopLaw

noncomputable section

namespace GlobalTheory.CoupledLaw

section Join

variable {E : Type} [Field E] {n' c' n c : ℕ}

/- English proof (translation)
Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Unfold `joinCol`. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe]`. Rewrite using `[h, map_add g, map_smul]`.
-/
theorem joinCol_target (r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)) (g : Sp E n ≃ₗ[E] Sp E n)
    (h : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) (x : HomE E n' n) (y : Sp E n) :
    joinCol (c' := c') (c := c) (g.toLinearMap ∘ₗ x) (g y) = r.toLinearMap ∘ₗ joinCol x y := by
  refine LinearMap.ext fun v => ?_
  unfold joinCol
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe]
  rw [h, map_add g, map_smul]

/- English proof (translation)
Substitute `hc` using the available equality. Use `⟨LinearMap.ext fun v => ?_, by simp [Loc.n1Arg]⟩` and prove the remaining obligations. Establish `e : v = Loc.inX E n' 1 (LinearMap.funLeft E E (Fin.castAdd 1) v) + v (Fin.last n') • Loc.eN E (n' + 1) n'`. Use function extensionality and compare the values at `l`. Rewrite using `[Pi.add_apply, CongLevel.inX_apply, Pi.smul_apply, Loc.eN, smul_eq_mul]`.

Distinguish the cases in `hl : l.1 < n'`. Rewrite using `[dif_pos hl, if_neg hl.ne, mul_zero, add_zero]`. Both sides reduce to the same expression. Take `rfl : l = Fin.last n'` from `Fin.ext (by have := l.2; rw [Fin.val_last]; omega)`. Rewrite using `[dif_neg hl, if_pos (Fin.val_last _), mul_one, zero_add]`.

Establish `e1 : r v = Loc.inX E n' 1 (g (LinearMap.funLeft E E (Fin.castAdd 1) v)) + v (Fin.last n') • Loc.eN E (n' + 1) n'` using `by conv_lhs => rw [e]`. Rewrite using `[map_add, map_smul, h, hr.2.1]`. Establish `e2 : LinearMap.funLeft E E (Fin.castAdd 1) (r v) = g (LinearMap.funLeft E E (Fin.castAdd 1) v)`. Use function extensionality and compare the values at `l`. Rewrite using `[LinearMap.funLeft_apply, e1, Pi.add_apply, CongLevel.inX_apply, Pi.smul_apply, Loc.eN, smul_eq_mul, dif_pos (show (Fin.castAdd 1 l).1 < n' from l.2), if_neg (show (Fin.castAdd 1 l).1 ≠ n' from l.2.ne), mul_zero, add_zero]`.

Both sides reduce to the same expression. Establish `e3 : atNL E (n' + 1) n' (r v) = atNL E (n' + 1) n' v`. Unfold `atNL`. Rewrite using `[dif_pos (Nat.lt_succ_self _), LinearMap.proj_apply, LinearMap.proj_apply, e1, Pi.add_apply, CongLevel.inX_apply, Pi.smul_apply, Loc.eN, smul_eq_mul, dif_neg (lt_irrefl _), if_pos rfl, mul_one, zero_add]`. Both sides reduce to the same expression.

Unfold `joinCol`. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe]`. Rewrite using `[e2, e3]`.
-/
theorem joinCol_source (hc : c' = 1) (r : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')) (g : Sp E n' ≃ₗ[E] Sp E n')
    (hr : Loc.R1cond E n' c' r) (h : ∀ x, r (Loc.inX E n' c' x) = Loc.inX E n' c' (g x)) (x : HomE E n' n) (y : Sp E n) :
    joinCol (c' := c') (c := c) (x ∘ₗ g.toLinearMap) y = joinCol x y ∘ₗ r.toLinearMap ∧ Loc.n1Arg r = 0 := by
  subst hc
  refine ⟨LinearMap.ext fun v => ?_, by simp [Loc.n1Arg]⟩
  have e : v = Loc.inX E n' 1 (LinearMap.funLeft E E (Fin.castAdd 1) v) + v (Fin.last n') • Loc.eN E (n' + 1) n' := by
    funext l
    rw [Pi.add_apply, CongLevel.inX_apply, Pi.smul_apply, Loc.eN, smul_eq_mul]
    by_cases hl : l.1 < n'
    · rw [dif_pos hl, if_neg hl.ne, mul_zero, add_zero]
      rfl
    · obtain rfl : l = Fin.last n' := Fin.ext (by have := l.2; rw [Fin.val_last]; omega)
      rw [dif_neg hl, if_pos (Fin.val_last _), mul_one, zero_add]
  have e1 : r v = Loc.inX E n' 1 (g (LinearMap.funLeft E E (Fin.castAdd 1) v)) + v (Fin.last n') • Loc.eN E (n' + 1) n' := by
    conv_lhs => rw [e]
    rw [map_add, map_smul, h, hr.2.1]
  have e2 : LinearMap.funLeft E E (Fin.castAdd 1) (r v) = g (LinearMap.funLeft E E (Fin.castAdd 1) v) := by
    funext l
    rw [LinearMap.funLeft_apply, e1, Pi.add_apply, CongLevel.inX_apply, Pi.smul_apply, Loc.eN, smul_eq_mul,
      dif_pos (show (Fin.castAdd 1 l).1 < n' from l.2), if_neg (show (Fin.castAdd 1 l).1 ≠ n' from l.2.ne), mul_zero, add_zero]
    rfl
  have e3 : atNL E (n' + 1) n' (r v) = atNL E (n' + 1) n' v := by
    unfold atNL
    rw [dif_pos (Nat.lt_succ_self _), LinearMap.proj_apply, LinearMap.proj_apply, e1, Pi.add_apply, CongLevel.inX_apply,
      Pi.smul_apply, Loc.eN, smul_eq_mul, dif_neg (lt_irrefl _), if_pos rfl, mul_one, zero_add]
    rfl
  unfold joinCol
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe]
  rw [e2, e3]

end Join

section Local

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

/- English proof (translation)
Distinguish the cases in `hP : P.1 ∈ Pr.vGs`. Take `⟨h, rfl⟩` from `hk.1 hP`. Take `⟨g, hg, hred⟩` from `(hL.grpG j b ⟨P.1, hP⟩ _).1 h`. Establish `hgi : g ∈ GLint X.E (R.N j) P.1` using `hL.int j b P hg`. Establish `e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ` using `redGL_eq _ hred`.

Establish `h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ) = 1`. Rewrite using `[map_mul, map_inv, e, inv_mul_cancel]`. Establish `h2` using `CongLevel.cong_mem_prCat X Pr R cst.sharp j P.1 hP (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG j b P hP) _ ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ).2 fun x hx => by`. Rewrite using `[redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]`. Establish `h3 : κ.1 ∈ prCat (Pr` using `Pr) cst.sharp j P.1 (L.h j b P) := by`.

Use `mul_mem hg h2` as an intermediate fact. Rewrite `this` using `[Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]`. Then use the resulting hypothesis. Take `⟨r, hr, hrx⟩` from `h3`. Conclude with `⟨r, hr, hrx, hL.chrG j b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩`. Establish `hP'` using `(@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP`.

Take `⟨h, rfl⟩` from `hk.2 hP' hP`. Establish `h3` using `h`. Rewrite `h3` using `[hL.grpQ, Subgroup.mem_subgroupOf]`. Take `⟨r, hr, hrx⟩` from `h3`. Conclude with `⟨r, hr, hrx, hL.chrQ j b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩`.
-/
theorem exists_lift (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {j : ℕ} {b : L.β j} {P : rowSG Pr sel mu}
    {κ : GLint X.E (R.N j) P.1} {c : X.Kˣ} (hk : LevAt (L.levG j b) (L.levQ j b) P κ c) :
    ∃ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j P.1) (L.h j b P),
      (∀ x, r (Loc.inX X.E _ (cOf R j) x) = Loc.inX X.E _ (cOf R j) (κ.1 x)) ∧
        (c : X.K) = chiInv Ch sel mu cst j P (L.h j b P) r := by
  by_cases hP : P.1 ∈ Pr.vGs
  · obtain ⟨h, rfl⟩ := hk.1 hP
    obtain ⟨g, hg, hred⟩ := (hL.grpG j b ⟨P.1, hP⟩ _).1 h
    have hgi : g ∈ GLint X.E (R.N j) P.1 := hL.int j b P hg
    have e : redGL _ P.1 ⟨g, hgi⟩ = redGL _ P.1 κ := redGL_eq _ hred
    have h1 : redGL _ P.1 ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ) = 1 := by
      rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 := CongLevel.cong_mem_prCat X Pr R cst.sharp j P.1 hP
      (fun a ha h0 => intAt_div_of_redP (qOf_notMem_sq hX hPr hP) ha h0) _ (hL.stabG j b P hP)
      _ ((⟨g, hgi⟩ : GLint X.E (R.N j) P.1)⁻¹ * κ).2 fun x hx => by
        rw [redV_redGL _ hx, h1, Units.val_one, Matrix.one_mulVec]
    have h3 : κ.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 (L.h j b P) := by
      have := mul_mem hg h2
      rwa [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left] at this
    obtain ⟨r, hr, hrx⟩ := h3
    exact ⟨r, hr, hrx, hL.chrG j b ⟨P.1, hP⟩ ⟨_, h⟩ κ.1 r hr hrx fun x hx => redV_redGL κ hx⟩
  · have hP' := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    obtain ⟨h, rfl⟩ := hk.2 hP' hP
    have h3 := h
    rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
    obtain ⟨r, hr, hrx⟩ := h3
    exact ⟨r, hr, hrx, hL.chrQ j b ⟨P.1, hP'⟩ ⟨_, h⟩ r hr hrx⟩

/- English proof (translation)
Unfold `muAt rhoS`. Rewrite using `[LastSteps.locChar_unit _ _ ha]`.
-/
theorem muAt_unit (i : ℕ) (P : rowSG Pr sel mu) {a : X.E} (ha : IsUnit (redP P.1 a)) :
    muAt Ch sel mu cst i P a = rhoS Ch sel mu i P a := by
  unfold muAt rhoS
  rw [LastSteps.locChar_unit _ _ ha]

/- English proof (translation)
Establish `hm` using `hL.hm`. Take `⟨r, hr, hrx, hc⟩` from `exists_lift hX hPr hL hk`. Generalize the expression as in `L.h m2 al P = h at *`. Establish `hJ : h⁻¹ * r * h ∈ Jat (Pr` using `Pr) cst.sharp m2 P.1 := by simpa [Subgroup.mem_comap] using hr.2`. Establish `hdet : LinearEquiv.det (h⁻¹ * r * h) = LinearEquiv.det κ.1`.

Rewrite using `[map_mul, map_mul, map_inv, inv_mul_cancel_comm, GlobalTheory.UnfoldLaw.det_first_parabolic_eq_det_block hr.1.1 hrx]`. Take `⟨e1, e2⟩` from `joinCol_source (c := cOf R (m2 + 1)) (by unfold cOf; omega) r κ.1 hr.1.1 hrx x y`. Establish `law` using `DatumLaw.phiAt_source Ch sel mu cst cst.sharp (i := m2) (by omega) P hJ ((1 : AutY X R (m2 + 1)).symm.toLinearMap ∘ₗ joinCol x y ∘ₗ h.toLinearMap)`. Rewrite `law` using `[muAt_unit _ _ (DatumLaw.isUnit_det hJ), hdet]`. Unfold `chiInv at hc`.

Rewrite `hc` using `[e2, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul]`. Unfold `PsiAt omPhi Loc.om`. Rewrite using `[e1, hc, mul_assoc, mul_left_comm (lamRow _ _ _ _ _ _), ← law]`. Use `congr 3`. Conclude with `LinearMap.ext fun v => congrArg (fun w => (1 : AutY X R (m2 + 1)).symm (joinCol x y w)) (LinearEquiv.apply_symm_apply h (r (h v))).symm`.
-/
theorem psiAt_source (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {al : L.β m2} {P : rowSG Pr sel mu}
    {κ : GLint X.E (R.N m2) P.1} {a : X.Kˣ} (hk : LevAt (L.levG m2 al) (L.levQ m2 al) P κ a)
    (x : HomE X.E (R.N m2) (R.N (m2 + 1))) (y : Sp X.E (R.N (m2 + 1))) :
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) (x ∘ₗ κ.1.toLinearMap) y * rhoS Ch sel mu m2 P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) =
      (a : X.K) * PsiAt Ch sel mu cst m2 P (L.h m2 al P) x y := by
  have hm := hL.hm
  obtain ⟨r, hr, hrx, hc⟩ := exists_lift hX hPr hL hk
  generalize L.h m2 al P = h at *
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) cst.sharp m2 P.1 := by simpa [Subgroup.mem_comap] using hr.2
  have hdet : LinearEquiv.det (h⁻¹ * r * h) = LinearEquiv.det κ.1 := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm, GlobalTheory.UnfoldLaw.det_first_parabolic_eq_det_block hr.1.1 hrx]
  obtain ⟨e1, e2⟩ := joinCol_source (c := cOf R (m2 + 1)) (by unfold cOf; omega) r κ.1 hr.1.1 hrx x y
  have law := DatumLaw.phiAt_source Ch sel mu cst cst.sharp (i := m2) (by omega) P hJ
    ((1 : AutY X R (m2 + 1)).symm.toLinearMap ∘ₗ joinCol x y ∘ₗ h.toLinearMap)
  rw [muAt_unit _ _ (DatumLaw.isUnit_det hJ), hdet] at law
  unfold chiInv at hc
  rw [e2, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul] at hc
  unfold PsiAt omPhi Loc.om
  rw [e1, hc, mul_assoc, mul_left_comm (lamRow _ _ _ _ _ _), ← law]
  congr 3
  exact LinearMap.ext fun v => congrArg (fun w => (1 : AutY X R (m2 + 1)).symm (joinCol x y w))
    (LinearEquiv.apply_symm_apply h (r (h v))).symm

/- English proof (translation)
Establish `hm` using `hL.hm`. Take `⟨r, hr, hrx, hc⟩` from `exists_lift hX hPr hL hk`. Rewrite `hr`, `hc` using `[hL.last_h]`. Establish `hJ : r ∈ Jat (Pr` using `Pr) cst.sharp (m2 + 1) P.1 := by simpa using hr.2`. Take `⟨-, e2, e3⟩` from `TopSrc.of_zero (by unfold cOf; omega) r κ.1 hrx`.

Unfold `chiInv at hc`. Rewrite `hc` using `[e3, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul, inv_one, one_mul, mul_one]`. Establish `law` using `DatumLaw.phiAt_target Ch sel mu cst cst.sharp (i := m2) (by omega) P hJ ((1 : AutY X R (m2 + 1)).symm.toLinearMap ∘ₗ joinCol x y ∘ₗ h.toLinearMap)`. Rewrite `law` using `[muAt_unit _ _ (DatumLaw.isUnit_det hJ), ← e2]`. Unfold `PsiAt omPhi Loc.om`.

Rewrite using `[joinCol_target r κ.1 hrx, hc, mul_assoc, mul_left_comm (lamRow _ _ _ _ _ _), ← law]`. Both sides reduce to the same expression.
-/
theorem psiAt_target (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) {b : L.β (m2 + 1)} {P : rowSG Pr sel mu}
    {κ : GLint X.E (R.N (m2 + 1)) P.1} {a : X.Kˣ} (hk : LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P κ a) (h : AutY X R m2)
    (x : HomE X.E (R.N m2) (R.N (m2 + 1))) (y : Sp X.E (R.N (m2 + 1))) :
    PsiAt Ch sel mu cst m2 P h (κ.1.toLinearMap ∘ₗ x) (κ.1 y) * rhoS Ch sel mu m2 P ((LinearEquiv.det κ.1 : X.Eˣ) : X.E) =
      (a : X.K) * PsiAt Ch sel mu cst m2 P h x y := by
  have hm := hL.hm
  obtain ⟨r, hr, hrx, hc⟩ := exists_lift hX hPr hL hk
  rw [hL.last_h] at hr hc
  have hJ : r ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) P.1 := by simpa using hr.2
  obtain ⟨-, e2, e3⟩ := TopSrc.of_zero (by unfold cOf; omega) r κ.1 hrx
  unfold chiInv at hc
  rw [e3, hL.cst_ok.psi_int P 0 intAt_zero, inv_one, one_mul, inv_one, one_mul, mul_one] at hc
  have law := DatumLaw.phiAt_target Ch sel mu cst cst.sharp (i := m2) (by omega) P hJ
    ((1 : AutY X R (m2 + 1)).symm.toLinearMap ∘ₗ joinCol x y ∘ₗ h.toLinearMap)
  rw [muAt_unit _ _ (DatumLaw.isUnit_det hJ), ← e2] at law
  unfold PsiAt omPhi Loc.om
  rw [joinCol_target r κ.1 hrx, hc, mul_assoc, mul_left_comm (lamRow _ _ _ _ _ _), ← law]
  rfl

end Local

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

/- English proof (translation)
Take `⟨y₀, hy₀, rfl⟩` from `hy`. Use `set c : ℕ := cBof sel mu cst u with hcdef`. Express the relevant statement in the definitionally equal form `XiCpl1 Ch sel mu cst L m2 al p p' Y (x + (c : 𝓞 X.E) • y₀) = _`. Unfold `XiCpl1`. Use `congrArg₂ (· * ·) ?_ ?_` and prove the remaining obligations.

Use `GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv` and prove the remaining obligations. Establish `h1 : Pr.piT u ∈ P.1.asIdeal`. Establish `h` using `P.2`. Unfold `Primes.vT divs at h`. Use `split_ifs at h with hf`.

Simplify using `using h`. Simplify using `at h`. Rewrite using `[hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)`. Use `Finset.prod_congr rfl fun P _ => ?_` and prove the remaining obligations.

Establish `hq0` using `GlobalTheory.TopInv.qOf_ne P.1`. Rewrite using `[GlobalTheory.TopInv.inFr_add]`. Use `hL.psiInvX al P _ _ _ fun s l => ?_` and prove the remaining obligations. Establish `h1 : frsF sel mu p P (Pi.single s 1) ∈ p.deco.1.at P.1` using `(frsF_mem p P _).2 ((mem_localization_standardLattice _ _).2 (GlobalTheory.TopInv.single_int s))`. Establish `h2` using `hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1`.

Establish `h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) ∈ stdAt X.E _ P.1`. Use `(frsF_mem p' P _).1 ?_` and prove the remaining obligations. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `h2`. Establish `h4` using `(mem_localization_standardLattice _ _).1 h3 l`.

Take `⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c` from `Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _`. Establish `h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) (Pi.single s 1) l = (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) l`. Express the relevant statement in the definitionally equal form `(frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P (Pi.single s 1))) l = _`. Rewrite using `[equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]`. Rewrite using `[h5, hc']`.

Use `(GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem xiCpl1_invariant {u : Pr.Word} (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2) (al : L.β m2) (p : ChPt (R := R) sel mu u m2)
    (p' : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1)))) (x y : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hy : y ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiCpl1 Ch sel mu cst L m2 al p p' Y (x + y) = XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  classical
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  set c : ℕ := cBof sel mu cst u with hcdef
  change XiCpl1 Ch sel mu cst L m2 al p p' Y (x + (c : 𝓞 X.E) • y₀) = _
  unfold XiCpl1
  refine congrArg₂ (· * ·) ?_ ?_
  · refine GlobalTheory.TopInv.phiT_add _ _ p'.deco.2 x y₀ _ (fun P => ?_) fun P v hv => hy₀ P.1 (Finset.mem_union_left _ P.2) v hv
    have h1 : Pr.piT u ∈ P.1.asIdeal := by
      have h := P.2
      unfold Primes.vT divs at h
      split_ifs at h with hf
      · simpa using h
      · simp at h
    rw [hcdef, cBof, Nat.cast_mul, ← hPr.piT_norm]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h1)
  · refine Finset.prod_congr rfl fun P _ => ?_
    have hq0 := GlobalTheory.TopInv.qOf_ne P.1
    rw [GlobalTheory.TopInv.inFr_add]
    refine hL.psiInvX al P _ _ _ fun s l => ?_
    have h1 : frsF sel mu p P (Pi.single s 1) ∈ p.deco.1.at P.1 :=
      (frsF_mem p P _).2 ((mem_localization_standardLattice _ _).2 (GlobalTheory.TopInv.single_int s))
    have h2 := hy₀ P.1 (Finset.mem_union_right _ P.2) _ h1
    have h3 : (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) ∈ stdAt X.E _ P.1 := by
      refine (frsF_mem p' P _).1 ?_
      rw [LinearEquiv.apply_symm_apply]
      exact h2
    have h4 := (mem_localization_standardLattice _ _).1 h3 l
    obtain ⟨c', hc'⟩ : qOf P.1 ^ cst.B ∣ c :=
      Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem (fun Q : rowSG Pr sel mu => qOf Q.1) (Finset.mem_univ P)) _) _
    have h5 : inFr (frsF sel mu p P) (frsF sel mu p' P) ((c : 𝓞 X.E) • y₀) (Pi.single s 1) l =
        (c : X.E) * (frsF sel mu p' P).symm (y₀ (frsF sel mu p P (Pi.single s 1))) l := by
      change (frsF sel mu p' P).symm ((c : 𝓞 X.E) • y₀ (frsF sel mu p P (Pi.single s 1))) l = _
      rw [equiv_osmul, Nat.cast_smul_eq_nsmul, Pi.smul_apply, nsmul_eq_mul]
    rw [h5, hc']
    convert (GlobalTheory.TopInv.intAt_nat (P := P.1) c').mul h4 using 1
    push_cast
    field_simp

/- English proof (translation)
Unfold `XiCpl1`. Rewrite using `[e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Units.coe_prod, ← Finset.prod_mul_distrib]`. Use `congrArg _ (Finset.prod_congr rfl fun P _ => ?_)` and prove the remaining obligations. Take `⟨v, hv, ev⟩` from `TopLaw.repY_mem hp2`. Establish `e1 : inFr (frsF sel mu q P) (frsF sel mu q' P) (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = (κ' P).1.toLinearMap ∘ₗ (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap)`.

Rewrite using `[hκ, hκ']`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Use `show (κ' P).1 ((frsF sel mu p' P).symm (γ'.1.symm (γ'.1 (x (γ.1.symm (γ.1 (frsF sel mu p P (((κ P)⁻¹).1 w)))))))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.

Establish `e2 : (frsF sel mu q' P).symm (repY ((fun v => γ'.1 v) '' Y)) = (κ' P).1 ((frsF sel mu p' P).symm v)`. Rewrite using `[hκ', ← ev]`. Use `show (κ' P).1 ((frsF sel mu p' P).symm (γ'.1.symm (γ'.1 v))) = _`. Rewrite using `[LinearEquiv.symm_apply_apply]`. Establish `hs` using `coset_sub p' hp1 hv (TopLaw.repY_mem hp1) P`.

Establish `h0` using `hL.psiInv al P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p' P).symm (repY Y)) ((frsF sel mu p' P).symm v - (frsF sel mu p' P).symm (repY Y)) fun i => by split_ifs with hP`. Rewrite using `[pow_zero, inv_one, one_mul]`. Conclude with `mem_stdAt.1 (hs.1 hP) i`. Conclude with `mem_stdAt.1 (hs.2 hP) i`. Rewrite `h0` using `[add_sub_cancel]`.

Establish `h1` using `psiAt_source hX hPr hL (ha P).inv (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p' P).symm v)`. Establish `h2` using `psiAt_target hX hPr hL (ha' P) (L.h m2 al P) (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap) ((frsF sel mu p' P).symm v)`. Rewrite using `[e1, e2, Pi.inv_apply, Pi.inv_apply, rhoT_inv, mul_comm (rhoS _ _ _ _ _ _), ← mul_assoc, h2, mul_assoc, h1, h0, Units.val_mul, mul_assoc]`.
-/
theorem xiCpl1_law {u : Pr.Word} {al : L.β m2} {b : L.β (m2 + 1)} (hX : X.Ok) (hPr : Pr.Ok) (hL : L.Ok Ch sel mu cst G m2)
    {γ : UF X.E (R.N m2)} {γ' : UF X.E (R.N (m2 + 1))} {p q : ChPt (R := R) sel mu u m2} {p' q' : ChPt (R := R) sel mu u (m2 + 1)}
    {Y : Set (Sp X.E (R.N (m2 + 1)))} (hp1 : Y ∈ ybSet sel mu cst p'.deco.1.N)
    (hp2 : (fun v => γ'.1 v) '' Y ∈ ybSet sel mu cst q'.deco.1.N)
    {κ : GLQ X.E (R.N m2) (rowSG Pr sel mu)} {κ' : GLQ X.E (R.N (m2 + 1)) (rowSG Pr sel mu)} {a a' : rowSG Pr sel mu → X.Kˣ}
    (hκ : ∀ P, frsF sel mu q P = γ.1 * (frsF sel mu p P * ((κ P)⁻¹).1))
    (hκ' : ∀ P, frsF sel mu q' P = γ'.1 * (frsF sel mu p' P * ((κ' P)⁻¹).1))
    (ha : ∀ P, LevAt (L.levG m2 al) (L.levQ m2 al) P (κ P) (a P))
    (ha' : ∀ P, LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P (κ' P) (a' P)) (x : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (e0 : phiT X.K q.deco.1 q'.deco.1 (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) = phiT X.K p.deco.1 p'.deco.1 x) :
    XiCpl1 Ch sel mu cst L m2 al q q' ((fun v => γ'.1 v) '' Y) (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) *
        ∏ P : rowSG Pr sel mu, (rhoS Ch sel mu m2 P ((LinearEquiv.det (κ⁻¹ P).1 : X.Eˣ) : X.E) *
          rhoT Ch sel mu m2 P ((LinearEquiv.det (κ'⁻¹ P).1 : X.Eˣ) : X.E)) =
      (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K) * XiCpl1 Ch sel mu cst L m2 al p p' Y x := by
  unfold XiCpl1
  rw [e0, mul_assoc, mul_left_comm _ (phiT _ _ _ _), ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun P _ => ?_)
  obtain ⟨v, hv, ev⟩ := TopLaw.repY_mem hp2
  have e1 : inFr (frsF sel mu q P) (frsF sel mu q' P) (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) =
      (κ' P).1.toLinearMap ∘ₗ (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap) := by
    rw [hκ, hκ']
    refine LinearMap.ext fun w => ?_
    show (κ' P).1 ((frsF sel mu p' P).symm (γ'.1.symm (γ'.1 (x (γ.1.symm (γ.1 (frsF sel mu p P (((κ P)⁻¹).1 w)))))))) = _
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    rfl
  have e2 : (frsF sel mu q' P).symm (repY ((fun v => γ'.1 v) '' Y)) = (κ' P).1 ((frsF sel mu p' P).symm v) := by
    rw [hκ', ← ev]
    show (κ' P).1 ((frsF sel mu p' P).symm (γ'.1.symm (γ'.1 v))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hs := coset_sub p' hp1 hv (TopLaw.repY_mem hp1) P
  have h0 := hL.psiInv al P (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p' P).symm (repY Y))
    ((frsF sel mu p' P).symm v - (frsF sel mu p' P).symm (repY Y)) fun i => by
      split_ifs with hP
      · rw [pow_zero, inv_one, one_mul]
        exact mem_stdAt.1 (hs.1 hP) i
      · exact mem_stdAt.1 (hs.2 hP) i
  rw [add_sub_cancel] at h0
  have h1 := psiAt_source hX hPr hL (ha P).inv (inFr (frsF sel mu p P) (frsF sel mu p' P) x) ((frsF sel mu p' P).symm v)
  have h2 := psiAt_target hX hPr hL (ha' P) (L.h m2 al P)
    (inFr (frsF sel mu p P) (frsF sel mu p' P) x ∘ₗ ((κ P)⁻¹).1.toLinearMap) ((frsF sel mu p' P).symm v)
  rw [e1, e2, Pi.inv_apply, Pi.inv_apply, rhoT_inv, mul_comm (rhoS _ _ _ _ _ _), ← mul_assoc, h2, mul_assoc, h1, h0, Units.val_mul,
    mul_assoc]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hd` using `(tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2`. Establish `hp2 : (fun v => g₁.1.1 v) '' Y ∈ ybSet sel mu cst (g₁ • p').deco.1.N` using `(ybSet_gmap sel mu cst _ g₁.1.1 Y).2 hp1`. Take `⟨κ, a, hκ, ha, ea⟩` from `exists_pass hd g p`. Take `⟨κ', a', hκ', ha', ea'⟩` from `exists_pass hd g₁ p'`. Establish `key` using `GlobalTheory.kerOf_gmap_frames (T.th m2) (Sall sel mu u) _ (cAof sel mu cst) (cBof sel mu cst u) _ _ _ _ (hT.th m2 le_rfl) g.1 g₁.1 p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') κ⁻¹ κ'⁻¹ (XiCpl1 Ch sel mu cst L m2 al p p' Y) (XiCpl1 Ch sel mu cst L m2 al (g • p) (g₁ • p …`.

Establish `e1 : cp1K W Ch sel mu cst L T al p p' Y = _` using `if_pos hp1`. Establish `e2 : cp1K W Ch sel mu cst L T al (g • p) (g₁ • p') ((fun v => g₁.1.1 v) '' Y) = _` using `if_pos hp2`. Use `e2.trans ?_` and prove the remaining obligations. Rewrite using `[e1, funext hκ, funext hκ']`. Use `key.trans ?_` and prove the remaining obligations.

Rewrite using `[ea, ea', mul_inv, ← map_inv (L.levG m2 al).chr, ← map_inv (L.levQ m2 al).chr]`. Conclude with `smul_comp_smul _ _ _ _ _`.
-/
theorem firstCoupledKernel_equivariant_cosets {u : Pr.Word} {T : ChTh W sel mu u m2} (b : L.β (m2 + 1))
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (hT : ChTh.Ok (Ch := Ch) cst T) (al : L.β m2) (g : FrmG (L.levG m2 al) (L.levQ m2 al))
    (g₁ : FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)) (p : ChPt (R := R) sel mu u m2) (p' : ChPt (R := R) sel mu u (m2 + 1))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (hp1 : Y ∈ ybSet sel mu cst p'.deco.1.N) :
    cp1K W Ch sel mu cst L T al (g • p) (g₁ • p') ((fun v => g₁.1.1 v) '' Y) =
      frmRho (colValF W sel mu u (m2 + 1)) _ _ g₁ ∘ₗ cp1K W Ch sel mu cst L T al p p' Y ∘ₗ frmRho (colValF W sel mu u m2) _ _ g⁻¹ := by
  have hd := (tilOk_of_avoid (mu := mu) hPr hsel u hS).2.2
  have hp2 : (fun v => g₁.1.1 v) '' Y ∈ ybSet sel mu cst (g₁ • p').deco.1.N := (ybSet_gmap sel mu cst _ g₁.1.1 Y).2 hp1
  obtain ⟨κ, a, hκ, ha, ea⟩ := exists_pass hd g p
  obtain ⟨κ', a', hκ', ha', ea'⟩ := exists_pass hd g₁ p'
  have key := GlobalTheory.kerOf_gmap_frames (T.th m2) (Sall sel mu u) _ (cAof sel mu cst) (cBof sel mu cst u) _ _ _ _ (hT.th m2 le_rfl) g.1 g₁.1
    p.deco.1.N (frsF sel mu p) p'.deco.1.N (frsF sel mu p') κ⁻¹ κ'⁻¹ (XiCpl1 Ch sel mu cst L m2 al p p' Y)
    (XiCpl1 Ch sel mu cst L m2 al (g • p) (g₁ • p') ((fun v => g₁.1.1 v) '' Y)) (((∏ P, a' P) * (∏ P, a P)⁻¹ : X.Kˣ) : X.K)
    ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩
    (xiCpl1_invariant hPr hL al p p' Y) fun x =>
      xiCpl1_law hX hPr hL hp1 hp2 hκ hκ' ha ha' x (phiT_act _ _ _ _ _ _ _)
  have e1 : cp1K W Ch sel mu cst L T al p p' Y = _ := if_pos hp1
  have e2 : cp1K W Ch sel mu cst L T al (g • p) (g₁ • p') ((fun v => g₁.1.1 v) '' Y) = _ := if_pos hp2
  refine e2.trans ?_
  rw [e1, funext hκ, funext hκ']
  refine key.trans ?_
  rw [ea, ea', mul_inv, ← map_inv (L.levG m2 al).chr, ← map_inv (L.levQ m2 al).chr]
  exact smul_comp_smul _ _ _ _ _

/- English proof (translation)
Introduce `al g g₁ p p' Y hp` and use `firstCoupledKernel_equivariant_cosets b hX hPr hsel hS hL hT al g g₁ p p' Y hp`.
-/
theorem cp1EquivOn {u : Pr.Word} {T : ChTh W sel mu u m2} (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : Pr.T u ∈ S ∧ ∀ i, Pr.g i ∈ S) (hL : L.Ok Ch sel mu cst G m2)
    (hT : ChTh.Ok (Ch := Ch) cst T) : Cp1EquivOn W Ch sel mu cst L T b hY :=
  fun al g g₁ p p' Y hp => firstCoupledKernel_equivariant_cosets b hX hPr hsel hS hL hT al g g₁ p p' Y hp

end Main

open GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built in

/- English proof (translation)
Introduce `X Pr R W Ch sel S mu cst L G m2 u i A hX hPr _ hsel hT hg hL _ hTh hi b b' g g' d d'`. Take `rfl : m2 = i` from `by have := hL.hm; omega`. Take `⟨al, rfl⟩ : ∃ al, b = Idx.of al (by omega)` from `⟨_, (b.of_get (by omega) _).symm⟩`. Take `⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega)` from `⟨_, (b'.of_get (by omega) _).symm⟩`. Establish `e : ∀ p p', kAt W Ch sel mu cst L A u m2 (Idx.of al (by omega)) (Idx.of be (by omega)) p p' = cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p.1.1 p'.1.1 p'.1.2` using `fun p p' => by`.

Rewrite using `[firstCoupledKernel_eq_columnChainDatum W Ch sel mu cst L _ hi al (Idx.of be (by omega))]`. Unfold `kAt GlobalTheory.KerT.ker`. Rewrite using `[← stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u m2 (by omega)]`. Both sides reduce to the same expression. Rewrite using `[e, e]`.

Conclude with `firstCoupledKernel_equivariant_cosets be hX hPr hsel ⟨hT, hg⟩ hL hTh al g g' d.1.1 d'.1.1 d'.1.2 (PtAt.mem_ybSet d' hi)`.
-/
theorem kAt_equiv : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ) (A : Formalism.L2.Ker.Amb X), X.Ok → Pr.Ok → Ch.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ChTh.Ok (Ch := Ch) cst (Formalism.L2.Ker.chTh W Ch sel mu cst A u m2) → i + 2 = R.m → ∀ b b' (g : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).G b) (g' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).G b') (d : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).D b) (d' : (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).D b'), kAt W Ch sel mu cst L A u i b b' (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).actD b; g • d) (letI := (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).actD b'; g' • d') = (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u (i + 1)).rho X.emb (W.lamTrue u (i + 1)) b' g' ∘ₗ kAt W Ch sel mu cst L A u i b b' d d' ∘ₗ (stepAt sel mu cst L (topLev Ch sel mu cst (rPsymF (R := R) Ch)) u i).rho X.emb (W.lamTrue u i) b g⁻¹ := by
  intro X Pr R W Ch sel S mu cst L G m2 u i A hX hPr _ hsel hT hg hL _ hTh hi b b' g g' d d'
  obtain rfl : m2 = i := by have := hL.hm; omega
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al (by omega) := ⟨_, (b.of_get (by omega) _).symm⟩
  obtain ⟨be, rfl⟩ : ∃ be, b' = Idx.of be (by omega) := ⟨_, (b'.of_get (by omega) _).symm⟩
  have e : ∀ p p', kAt W Ch sel mu cst L A u m2 (Idx.of al (by omega)) (Idx.of be (by omega)) p p' =
      cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p.1.1 p'.1.1 p'.1.2 := fun p p' => by
    rw [firstCoupledKernel_eq_columnChainDatum W Ch sel mu cst L _ hi al (Idx.of be (by omega))]
    unfold kAt GlobalTheory.KerT.ker
    rw [← stepC_eq_stepT W Ch sel mu cst (muqTie_of_ok Ch sel mu cst L hL) A u m2 (by omega)]
    rfl
  rw [e, e]
  exact firstCoupledKernel_equivariant_cosets be hX hPr hsel ⟨hT, hg⟩ hL hTh al g g' d.1.1 d'.1.1 d'.1.2
    (PtAt.mem_ybSet d' hi)

end GlobalTheory.CoupledLaw
