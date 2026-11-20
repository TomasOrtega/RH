import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerHypAll
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RatKDeg
import Formalism.LocalToGlobal.Columns.ChainLawXiF
import Formalism.LocalToGlobal.Columns.ChainLawPsi
import Formalism.LocalToGlobal.Columns.ChainLawTw

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section InvA

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word}

open Classical in

/- English proof (translation)
Establish `h1 : frsF sel mu p P (Pi.single s 1) ∈ localization₂ P.1.asIdeal p.deco.1.N` using `(frsF_isFr sel mu p P _).2 (xqSingle_mem (P := P.1) s)`. Establish `h2` using `hw P.1 (Finset.mem_union_right _ P.2) _ h1`. Establish `h3 : (frsF sel mu p' P).symm (w (frsF sel mu p P (Pi.single s 1))) ∈ stdAt X.E (R.N j) P.1` using `(frsF_isFr sel mu p' P _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h2)`. Conclude with `(xqMem_stdAt (P := P.1) _).1 h3 l`.
-/
theorem inFr_intA {i j : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu)
    (w : HomE X.E (R.N i) (R.N j)) (hw : w ∈ homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) (s : Fin (R.N i)) (l : Fin (R.N j)) :
    IntAt P.1 ((inFr (frsF sel mu p P) (frsF sel mu p' P) w) (Pi.single s 1) l) := by
  have h1 : frsF sel mu p P (Pi.single s 1) ∈ localization₂ P.1.asIdeal p.deco.1.N := (frsF_isFr sel mu p P _).2 (xqSingle_mem (P := P.1) s)
  have h2 := hw P.1 (Finset.mem_union_right _ P.2) _ h1
  have h3 : (frsF sel mu p' P).symm (w (frsF sel mu p P (Pi.single s 1))) ∈ stdAt X.E (R.N j) P.1 :=
    (frsF_isFr sel mu p' P _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h2)
  exact (xqMem_stdAt (P := P.1) _).1 h3 l

open Classical in

/- English proof (translation)
Establish `e2 : (inFr (frsF sel mu p P) (frsF sel mu p' P) (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) (Pi.single s 1) l = ((cBof sel mu cst u : ℕ) : X.E) * (inFr (frsF sel mu p P) (frsF sel mu p' P) w) (Pi.single s 1) l`. Simplify using `only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply]`. Rewrite using `[← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, Pi.smul_apply, smul_eq_mul, map_natCast]`. Rewrite using `[e2, ← mul_assoc]`. Conclude with `(cB_div_int sel mu cst P).mul (inFr_intA sel mu p p' P w hw s l)`.
-/
theorem inFr_cB_int {i j : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu)
    (w : HomE X.E (R.N i) (R.N j)) (hw : w ∈ homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) (s : Fin (R.N i)) (l : Fin (R.N j)) :
    IntAt P.1 (((qOf P.1 : X.E) ^ cst.B)⁻¹ *
      (inFr (frsF sel mu p P) (frsF sel mu p' P) (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) (Pi.single s 1) l) := by
  have e2 : (inFr (frsF sel mu p P) (frsF sel mu p' P) (((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) (Pi.single s 1) l =
      ((cBof sel mu cst u : ℕ) : X.E) * (inFr (frsF sel mu p P) (frsF sel mu p' P) w) (Pi.single s 1) l := by
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply]
    rw [← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, Pi.smul_apply, smul_eq_mul, map_natCast]
  rw [e2, ← mul_assoc]
  exact (cB_div_int sel mu cst P).mul (inFr_intA sel mu p p' P w hw s l)

open Classical in

/- English proof (translation)
Use `phiT_add_mul X.K p.deco p'.deco (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_` and prove the remaining obligations. Establish `h1 : Pr.piT u ∈ P.1.asIdeal` using `mem_divs_of P.2`. Rewrite using `[← hPr.piT_norm u]`. Conclude with `P.1.asIdeal.mul_mem_right _ h1`. Use `(mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w, Submodule.smul_mem _ _ hw, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Unfold `cBof`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem phiT_cB (hPr : Pr.Ok) {i j : ℕ} (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u j)
    (x w : HomE X.E (R.N i) (R.N j)) (hw : w ∈ homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) :
    phiT X.K p.deco.1 p'.deco.1 (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w) = phiT X.K p.deco.1 p'.deco.1 x := by
  refine phiT_add_mul X.K p.deco p'.deco (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_
  · have h1 : Pr.piT u ∈ P.1.asIdeal := mem_divs_of P.2
    rw [← hPr.piT_norm u]
    exact P.1.asIdeal.mul_mem_right _ h1
  · refine (mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w,
      Submodule.smul_mem _ _ hw, ?_⟩
    rw [smul_smul]
    unfold cBof
    push_cast
    rfl

open Classical in

/- English proof (translation)
Take `⟨w, hw, rfl⟩` from `(mem_mulLat _ _ _).1 hz`. Establish `hxi : ∀ P : rowSG Pr sel mu, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr (frsF sel mu p P) (frsF sel mu p' P) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) = XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr (frsF sel mu p P) (frsF sel mu p' P) x)`. Introduce `P`. Rewrite using `[inFr_add]`. Conclude with `hL.xiInv i hi al be P _ _ fun s l => inFr_cB_int sel mu cst p p' P w hw s l`.

Unfold `XiEntry`. Rewrite using `[phiT_cB sel mu cst hPr p p' x w hw, Finset.prod_congr rfl fun P _ => hxi P]`.
-/
theorem xiEntry_invA (hPr : Pr.Ok) {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2)
    (i : ℕ) (hi : i < m2) (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
    (x z : HomE X.E (R.N i) (R.N (i + 1)))
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiEntry Ch sel mu cst L i al be p p' (x + z) = XiEntry Ch sel mu cst L i al be p p' x := by
  obtain ⟨w, hw, rfl⟩ := (mem_mulLat _ _ _).1 hz
  have hxi : ∀ P : rowSG Pr sel mu, XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P)
      (inFr (frsF sel mu p P) (frsF sel mu p' P) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) =
      XiAt Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) (inFr (frsF sel mu p P) (frsF sel mu p' P) x) := by
    intro P
    rw [inFr_add]
    exact hL.xiInv i hi al be P _ _ fun s l => inFr_cB_int sel mu cst p p' P w hw s l
  unfold XiEntry
  rw [phiT_cB sel mu cst hPr p p' x w hw, Finset.prod_congr rfl fun P _ => hxi P]

open Classical in

/- English proof (translation)
Take `⟨w, hw, rfl⟩` from `(mem_mulLat _ _ _).1 hz`. Establish `hpsi : ∀ P : rowSG Pr sel mu, PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) ((frsF sel mu p P).symm (repY Y)) = PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x) (( …`. Introduce `P`. Rewrite using `[inFr_add]`. Conclude with `hL.psiInvX al P _ _ _ fun s l => inFr_cB_int sel mu cst p₀ p P w hw s l`.

Unfold `XiCpl1`. Rewrite using `[phiT_cB sel mu cst hPr p₀ p x w hw, Finset.prod_congr rfl fun P _ => hpsi P]`.
-/
theorem xiCpl1_invA (hPr : Pr.Ok) {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2)
    (al : L.β m2) (p₀ : ChPt (R := R) sel mu u m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (Y : Set (Sp X.E (R.N (m2 + 1))))
    (x z : HomE X.E (R.N m2) (R.N (m2 + 1)))
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p₀.deco.1.N p.deco.1.N)) :
    XiCpl1 Ch sel mu cst L m2 al p₀ p Y (x + z) = XiCpl1 Ch sel mu cst L m2 al p₀ p Y x := by
  obtain ⟨w, hw, rfl⟩ := (mem_mulLat _ _ _).1 hz
  have hpsi : ∀ P : rowSG Pr sel mu, PsiAt Ch sel mu cst m2 P (L.h m2 al P)
      (inFr (frsF sel mu p₀ P) (frsF sel mu p P) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w)) ((frsF sel mu p P).symm (repY Y)) =
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) (inFr (frsF sel mu p₀ P) (frsF sel mu p P) x) ((frsF sel mu p P).symm (repY Y)) := by
    intro P
    rw [inFr_add]
    exact hL.psiInvX al P _ _ _ fun s l => inFr_cB_int sel mu cst p₀ p P w hw s l
  unfold XiCpl1
  rw [phiT_cB sel mu cst hPr p₀ p x w hw, Finset.prod_congr rfl fun P _ => hpsi P]

open Classical in

/- English proof (translation)
Establish `hrepY : γ.symm (repY ((fun v => γ v) '' Y)) ∈ Y`. Take `⟨v, hv, hve⟩ : repY ((fun v => γ v) '' Y) ∈ (fun v => γ v) '' Y` from `Classical.epsilon_spec ((nonempty_of_ybSet sel mu cst hY).image _)`. Rewrite using `[← hve, LinearEquiv.symm_apply_apply]`. Conclude with `hv`. Establish `hrep0 : repY Y ∈ Y` using `Classical.epsilon_spec (nonempty_of_ybSet sel mu cst hY)`.

Establish `hdiff` using `sub_mem_of_ybSet sel mu cst hY hrepY hrep0`. Establish `hwP` using `(mem_locLat _ _ _ _).1 hdiff P`. Establish `hz` using `(frsF_isFr sel mu p P ((frsF sel mu p P).symm _)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hwP)`. Establish `hz'` using `(xqMem_stdAt (P := P.1) _).1 hz`. Establish `e : (frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y))) = (frsF sel mu p P).symm (repY Y) + (frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y)) - repY Y)`.

Rewrite using `[← map_add, add_sub_cancel]`. Rewrite using `[e]`. Use `hL.psiInv al P x₀ _ _ fun i => ?_` and prove the remaining obligations. Establish `h` using `hz' i`. Rewrite `h` using `[map_smul, Pi.smul_apply, smul_eq_mul]`.

Distinguish the cases in `hP : P.1 ∈ Pr.vGs`. Simplify `h` using `only [if_pos hP, zpow_zero, pow_zero]`. Simplify `h` using `only [if_neg hP, zpow_natCast]`.
-/
theorem psiAt_repYA {G : ChGlob X R.m} {m2 : ℕ} (hL : L.Ok Ch sel mu cst G m2)
    (al : L.β m2) (p : ChPt (R := R) sel mu u (m2 + 1)) (γ : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1)))
    (Y : Set (Sp X.E (R.N (m2 + 1)))) (hY : Y ∈ ybSet sel mu cst p.deco.1.N) (P : rowSG Pr sel mu)
    (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) :
    PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ ((frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y)))) =
      PsiAt Ch sel mu cst m2 P (L.h m2 al P) x₀ ((frsF sel mu p P).symm (repY Y)) := by
  have hrepY : γ.symm (repY ((fun v => γ v) '' Y)) ∈ Y := by
    obtain ⟨v, hv, hve⟩ : repY ((fun v => γ v) '' Y) ∈ (fun v => γ v) '' Y :=
      Classical.epsilon_spec ((nonempty_of_ybSet sel mu cst hY).image _)
    rw [← hve, LinearEquiv.symm_apply_apply]
    exact hv
  have hrep0 : repY Y ∈ Y := Classical.epsilon_spec (nonempty_of_ybSet sel mu cst hY)
  have hdiff := sub_mem_of_ybSet sel mu cst hY hrepY hrep0
  have hwP := (mem_locLat _ _ _ _).1 hdiff P
  have hz := (frsF_isFr sel mu p P ((frsF sel mu p P).symm _)).1 (by rw [LinearEquiv.apply_symm_apply]; exact hwP)
  have hz' := (xqMem_stdAt (P := P.1) _).1 hz
  have e : (frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y))) =
      (frsF sel mu p P).symm (repY Y) + (frsF sel mu p P).symm (γ.symm (repY ((fun v => γ v) '' Y)) - repY Y) := by
    rw [← map_add, add_sub_cancel]
  rw [e]
  refine hL.psiInv al P x₀ _ _ fun i => ?_
  have h := hz' i
  rw [map_smul, Pi.smul_apply, smul_eq_mul] at h
  by_cases hP : P.1 ∈ Pr.vGs
  · simpa only [if_pos hP, zpow_zero, pow_zero] using h
  · simpa only [if_neg hP, zpow_natCast] using h

end InvA

section Scal

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

open Classical in

def locChr {n : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K))) (g : FrmG Λ Θ)
    (w : rowSG Pr sel mu) : X.K :=
  if hw : w.1 ∈ Pr.vGs then (((Λ ⟨w.1, hw⟩).lam ⟨(g.2.1 : GLG X.E n Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)
  else (((Θ ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam
    ⟨(g.2.2 : GLQ X.E n (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)

open Classical in
/- English proof (translation)
Establish `h` using `prod_uSG_dite hS (fun w => (((Λ w).lam ⟨(g.2.1 : GLG X.E n Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)) (fun Q => (((Θ Q).lam ⟨(g.2.2 : GLQ X.E n (QE sel (mu : Chr X.F X.E X.K))) Q, g.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))`. Establish `hq : ((Θ.chr g.2.2 : X.Kˣ) : X.K) = ∏ Q, (((Θ Q).lam ⟨(g.2.2 : GLQ X.E n (QE sel (mu : Chr X.F X.E X.K))) Q, g.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K)` using `piChar_apply_coe' _ _ g.2.2`. Rewrite using `[Units.val_mul, levFam_chr_apply_coe, hq]`. Conclude with `h.symm`.
-/
theorem locChr_prod (hS : QSep Pr sel mu) {n : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K)))
    (g : FrmG Λ Θ) : ((Λ.chr g.2.1 * Θ.chr g.2.2 : X.Kˣ) : X.K) = ∏ w : rowSG Pr sel mu, locChr sel mu Λ Θ g w := by
  have h := prod_uSG_dite hS
    (fun w => (((Λ w).lam ⟨(g.2.1 : GLG X.E n Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))
    (fun Q => (((Θ Q).lam ⟨(g.2.2 : GLQ X.E n (QE sel (mu : Chr X.F X.E X.K))) Q, g.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K))
  have hq : ((Θ.chr g.2.2 : X.Kˣ) : X.K) =
      ∏ Q, (((Θ Q).lam ⟨(g.2.2 : GLQ X.E n (QE sel (mu : Chr X.F X.E X.K))) Q, g.2.2.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) :=
    piChar_apply_coe' _ _ g.2.2
  rw [Units.val_mul, levFam_chr_apply_coe, hq]
  exact h.symm

open Classical in
/- English proof (translation)
Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, locChr_prod sel mu hS, locChr_prod sel mu hS, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`.
-/
theorem locChr_ratio (hS : QSep Pr sel mu) {n n' : ℕ} (Λ : LevFam X.E X.K n Pr.vGs) (Θ : LevQFam X.E X.K n (QE sel (mu : Chr X.F X.E X.K)))
    (Λ' : LevFam X.E X.K n' Pr.vGs) (Θ' : LevQFam X.E X.K n' (QE sel (mu : Chr X.F X.E X.K))) (g : FrmG Λ Θ) (g' : FrmG Λ' Θ') :
    (((Λ'.chr g'.2.1 * Θ'.chr g'.2.2) * (Λ.chr g.2.1 * Θ.chr g.2.2)⁻¹ : X.Kˣ) : X.K) =
      ∏ w : rowSG Pr sel mu, locChr sel mu Λ' Θ' g' w * (locChr sel mu Λ Θ g w)⁻¹ := by
  rw [Units.val_mul, Units.val_inv_eq_inv_val, locChr_prod sel mu hS, locChr_prod sel mu hS, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Scal

section MatQ

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

open Classical in

/- English proof (translation)
Unfold `locChr`. Distinguish the cases in `hw : w.1 ∈ Pr.vGs`. Rewrite using `[dif_pos hw, dif_pos hw, ← Units.val_inv_eq_inv_val]`. Conclude with `hX w hw _ _ κ κ' (hκr hw) (hκr' hw) y`. Rewrite using `[dif_neg hw, dif_neg hw, ← Units.val_inv_eq_inv_val]`.

Establish `hk` using `hκQ hw`. Establish `hk'` using `hκQ' hw`. Substitute `hk` using the available equality. Substitute `hk'` using the available equality. Conclude with `hXQ w hw ⟨(g.2.2 : GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g.2.2.2 _ (Set.mem_univ _)⟩ ⟨(g'.2.2 : GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g'.2.2.2 _ (Set.me …`.
-/
theorem xi_localQ (i : ℕ) (al : L.β i) (be : L.β (i + 1)) (hX : XiLaw Ch sel mu cst L i al be) (hXQ : XiLawQ Ch sel mu cst L i al be)
    (g : FrmG (L.levG i al) (L.levQ i al)) (g' : FrmG (L.levG (i + 1) be) (L.levQ (i + 1) be)) (w : rowSG Pr sel mu)
    (κ : ↥(GLint X.E (R.N i) w.1)) (κ' : ↥(GLint X.E (R.N (i + 1)) w.1))
    (hκr : ∀ hw : w.1 ∈ Pr.vGs, ∀ x ∈ stdAt X.E (R.N i) w.1, redV w.1 (κ.1 x) =
      (((g.2.1 : GLG X.E (R.N i) Pr.vGs) ⟨w.1, hw⟩)⁻¹ : GL _ _).1.mulVec (redV w.1 x))
    (hκQ : ∀ hw : w.1 ∉ Pr.vGs, κ = ((g.2.2 : GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩)⁻¹)
    (hκr' : ∀ hw : w.1 ∈ Pr.vGs, ∀ x ∈ stdAt X.E (R.N (i + 1)) w.1, redV w.1 (κ'.1 x) =
      (((g'.2.1 : GLG X.E (R.N (i + 1)) Pr.vGs) ⟨w.1, hw⟩)⁻¹ : GL _ _).1.mulVec (redV w.1 x))
    (hκQ' : ∀ hw : w.1 ∉ Pr.vGs, κ' = ((g'.2.2 : GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩)⁻¹)
    (y : HomE X.E (R.N i) (R.N (i + 1))) :
    rhoS Ch sel mu i w (LinearEquiv.det κ.1 : X.Eˣ) * rhoT Ch sel mu i w (LinearEquiv.det κ'.1 : X.Eˣ) *
        XiAt Ch sel mu cst i w (L.h i al w) (L.h (i + 1) be w) (κ'.1.symm.toLinearMap ∘ₗ y ∘ₗ κ.1.toLinearMap) =
      locChr sel mu (L.levG (i + 1) be) (L.levQ (i + 1) be) g' w * (locChr sel mu (L.levG i al) (L.levQ i al) g w)⁻¹ *
        XiAt Ch sel mu cst i w (L.h i al w) (L.h (i + 1) be w) y := by
  unfold locChr
  by_cases hw : w.1 ∈ Pr.vGs
  · rw [dif_pos hw, dif_pos hw, ← Units.val_inv_eq_inv_val]
    exact hX w hw _ _ κ κ' (hκr hw) (hκr' hw) y
  · rw [dif_neg hw, dif_neg hw, ← Units.val_inv_eq_inv_val]
    have hk := hκQ hw
    have hk' := hκQ' hw
    subst hk
    subst hk'
    exact hXQ w hw
      ⟨(g.2.2 : GLQ X.E (R.N i) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g.2.2.2 _ (Set.mem_univ _)⟩
      ⟨(g'.2.2 : GLQ X.E (R.N (i + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g'.2.2.2 _ (Set.mem_univ _)⟩ y

open Classical in

/- English proof (translation)
Unfold `locChr`. Distinguish the cases in `hw : w.1 ∈ Pr.vGs`. Rewrite using `[dif_pos hw, dif_pos hw, ← Units.val_inv_eq_inv_val]`. Conclude with `hPsi w hw _ _ κ₀ κ (hκr₀ hw) (hκr hw) x₀ y'`. Rewrite using `[dif_neg hw, dif_neg hw, ← Units.val_inv_eq_inv_val]`.

Establish `hk` using `hκQ₀ hw`. Establish `hk'` using `hκQ hw`. Substitute `hk` using the available equality. Substitute `hk'` using the available equality. Conclude with `hPsiQ w hw ⟨(g₀.2.2 : GLQ X.E (R.N m2) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g₀.2.2.2 _ (Set.mem_univ _)⟩ ⟨(g.2.2 : GLQ X.E (R.N (m2 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g.2.2.2 _ (Se …`.
-/
theorem psi_localQ (al : L.β m2) (b : L.β (m2 + 1)) (hPsi : PsiLaw Ch sel mu cst L m2 al b) (hPsiQ : PsiLawQ Ch sel mu cst L m2 al b)
    (g₀ : FrmG (L.levG m2 al) (L.levQ m2 al)) (g : FrmG (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b)) (w : rowSG Pr sel mu)
    (κ₀ : ↥(GLint X.E (R.N m2) w.1)) (κ : ↥(GLint X.E (R.N (m2 + 1)) w.1))
    (hκr₀ : ∀ hw : w.1 ∈ Pr.vGs, ∀ x ∈ stdAt X.E (R.N m2) w.1, redV w.1 (κ₀.1 x) =
      (((g₀.2.1 : GLG X.E (R.N m2) Pr.vGs) ⟨w.1, hw⟩)⁻¹ : GL _ _).1.mulVec (redV w.1 x))
    (hκQ₀ : ∀ hw : w.1 ∉ Pr.vGs, κ₀ = ((g₀.2.2 : GLQ X.E (R.N m2) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩)⁻¹)
    (hκr : ∀ hw : w.1 ∈ Pr.vGs, ∀ x ∈ stdAt X.E (R.N (m2 + 1)) w.1, redV w.1 (κ.1 x) =
      (((g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩)⁻¹ : GL _ _).1.mulVec (redV w.1 x))
    (hκQ : ∀ hw : w.1 ∉ Pr.vGs, κ = ((g.2.2 : GLQ X.E (R.N (m2 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩)⁻¹)
    (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1))) :
    rhoS Ch sel mu m2 w (LinearEquiv.det κ₀.1 : X.Eˣ) * rhoT Ch sel mu m2 w (LinearEquiv.det κ.1 : X.Eˣ) *
        PsiAt Ch sel mu cst m2 w (L.h m2 al w) (κ.1.symm.toLinearMap ∘ₗ x₀ ∘ₗ κ₀.1.toLinearMap) (κ.1.symm y') =
      locChr sel mu (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w * (locChr sel mu (L.levG m2 al) (L.levQ m2 al) g₀ w)⁻¹ *
        PsiAt Ch sel mu cst m2 w (L.h m2 al w) x₀ y' := by
  unfold locChr
  by_cases hw : w.1 ∈ Pr.vGs
  · rw [dif_pos hw, dif_pos hw, ← Units.val_inv_eq_inv_val]
    exact hPsi w hw _ _ κ₀ κ (hκr₀ hw) (hκr hw) x₀ y'
  · rw [dif_neg hw, dif_neg hw, ← Units.val_inv_eq_inv_val]
    have hk := hκQ₀ hw
    have hk' := hκQ hw
    subst hk
    subst hk'
    exact hPsiQ w hw
      ⟨(g₀.2.2 : GLQ X.E (R.N m2) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g₀.2.2.2 _ (Set.mem_univ _)⟩
      ⟨(g.2.2 : GLQ X.E (R.N (m2 + 1)) (QE sel (mu : Chr X.F X.E X.K))) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩, g.2.2.2 _ (Set.mem_univ _)⟩ x₀ y'

set_option maxHeartbeats 400000 in
open Classical in

/- English proof (translation)
Introduce `i hi al be g g' p p'`. Use `choose κ hκ hκr hκQ using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p (L.levG i al) (L.levQ i al) g w`. Use `choose κ' hκ' hκr' hκQ' using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p' (L.levG (i + 1) be) (L.levQ (i + 1) be) g' w`. Establish `hfr : frsF sel mu (g • p) = fun P => g.1.1 * frsF sel mu p P * (κ P).1` using `funext hκ`. Establish `hfr' : frsF sel mu (g' • p') = fun P => g'.1.1 * frsF sel mu p' P * (κ' P).1` using `funext hκ'`.

Establish `hN : IsSdLat p.deco.1.N` using `⟨p.deco.2.lat, p.deco.2.uni⟩`. Establish `hN' : IsSdLat p'.deco.1.N` using `⟨p'.deco.2.lat, p'.deco.2.uni⟩`. Establish `hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N i) Pr.vGs)) • p.deco` using `rfl`. Establish `hdeco' : (g' • p').deco = (g'.1, (g'.2.1 : GLG X.E (R.N (i + 1)) Pr.vGs)) • p'.deco` using `rfl`. Apply the tactic sequence `have hΞ : ∀ x, (∏ P : rowSG Pr sel mu, rhoS Ch sel mu i P (LinearEquiv.det (κ P).1 : X.Eˣ) * rhoT Ch sel mu i P (LinearEquiv.det (κ' P).1 : X.Eˣ)) * XiEntry Ch sel mu cst L i al be (g • p) (g' • p') (g'.1.1.toLinearMap ∘ₗ x ∘ₗ g.1.1.symm.toLinearMap) = (((((L.levG (i + 1) be).chr …`.

Introduce `x`. Unfold `XiEntry`. Rewrite using `[hfr, hfr', hdeco, hdeco', phiT_smul]`. Simplify using `only [inFr_move]`. Rewrite using `[locChr_ratio sel mu hS]`.

Conclude with `prod_law_alg _ _ _ _ _ fun w => xi_localQ Ch sel mu cst L i al be (hX i hi al be) (hXQ i hi al be) g g' w (κ w) (κ' w) (hκr w) (hκQ w) (hκr' w) (hκQ' w) _`. Apply the tactic sequence `have key := kerOf_move (hOk.th i hi.le) (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsF sel mu p') g.1 g'.1 κ κ' (XiEntry Ch sel mu cst L i al be p p') (XiEntry Ch sel mu cst L i al be (g • p) (g' • p')) _ (hinv i hi al be p p') hΞ`. Use `show matK W Ch sel mu cst L _ i al be (g • p) (g' • p') = _`. Unfold `matK`. Rewrite using `[hfr, hfr']`.

Use `key.trans ?_` and prove the remaining obligations. Use `show _ = (frmRho (colValF W sel mu u (i + 1)) (L.levG (i + 1) be) (L.levQ (i + 1) be) g') ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u i) (L.levG i al) (L.levQ i al) g⁻¹)`. Simplify using `only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_inv, Prod.snd_inv, map_inv, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]`. Use `congr 1`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem matEquiv_ofQ (hS : QSep Pr sel mu) (hT : 0 < Pr.T u)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (hinv : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)) (p : ChPt (R := R) sel mu u i) (p' : ChPt (R := R) sel mu u (i + 1))
      (x z : HomE X.E (R.N i) (R.N (i + 1))),
      z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N) →
        XiEntry Ch sel mu cst L i al be p p' (x + z) = XiEntry Ch sel mu cst L i al be p p' x)
    (hX : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLaw Ch sel mu cst L i al be)
    (hXQ : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLawQ Ch sel mu cst L i al be) :
    MatEquiv W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) := by
  intro i hi al be g g' p p'
  choose κ hκ hκr hκQ using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p (L.levG i al) (L.levQ i al) g w
  choose κ' hκ' hκr' hκQ' using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p' (L.levG (i + 1) be) (L.levQ (i + 1) be) g' w
  have hfr : frsF sel mu (g • p) = fun P => g.1.1 * frsF sel mu p P * (κ P).1 := funext hκ
  have hfr' : frsF sel mu (g' • p') = fun P => g'.1.1 * frsF sel mu p' P * (κ' P).1 := funext hκ'
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hN' : IsSdLat p'.deco.1.N := ⟨p'.deco.2.lat, p'.deco.2.uni⟩
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N i) Pr.vGs)) • p.deco := rfl
  have hdeco' : (g' • p').deco = (g'.1, (g'.2.1 : GLG X.E (R.N (i + 1)) Pr.vGs)) • p'.deco := rfl
  have hΞ : ∀ x, (∏ P : rowSG Pr sel mu, rhoS Ch sel mu i P (LinearEquiv.det (κ P).1 : X.Eˣ) *
        rhoT Ch sel mu i P (LinearEquiv.det (κ' P).1 : X.Eˣ)) *
      XiEntry Ch sel mu cst L i al be (g • p) (g' • p') (g'.1.1.toLinearMap ∘ₗ x ∘ₗ g.1.1.symm.toLinearMap) =
      (((((L.levG (i + 1) be).chr g'.2.1 * (L.levQ (i + 1) be).chr g'.2.2) *
        ((L.levG i al).chr g.2.1 * (L.levQ i al).chr g.2.2)⁻¹ : X.Kˣ)) : X.K) * XiEntry Ch sel mu cst L i al be p p' x := by
    intro x
    unfold XiEntry
    rw [hfr, hfr', hdeco, hdeco', phiT_smul]
    simp only [inFr_move]
    rw [locChr_ratio sel mu hS]
    exact prod_law_alg _ _ _ _ _ fun w => xi_localQ Ch sel mu cst L i al be (hX i hi al be) (hXQ i hi al be) g g' w (κ w) (κ' w)
      (hκr w) (hκQ w) (hκr' w) (hκQ' w) _
  have key := kerOf_move (hOk.th i hi.le) (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsF sel mu p') g.1 g'.1 κ κ'
    (XiEntry Ch sel mu cst L i al be p p') (XiEntry Ch sel mu cst L i al be (g • p) (g' • p')) _ (hinv i hi al be p p') hΞ
  show matK W Ch sel mu cst L _ i al be (g • p) (g' • p') = _
  unfold matK
  rw [hfr, hfr']
  refine key.trans ?_
  show _ = (frmRho (colValF W sel mu u (i + 1)) (L.levG (i + 1) be) (L.levQ (i + 1) be) g') ∘ₗ _ ∘ₗ
    (frmRho (colValF W sel mu u i) (L.levG i al) (L.levQ i al) g⁻¹)
  simp only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_inv, Prod.snd_inv, map_inv,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ring

set_option maxHeartbeats 400000 in
open Classical in

/- English proof (translation)
Introduce `al g₀ g p₀ p (Y : Set (Sp X.E (R.N (m2 + 1)))) hYm`. Establish `hYm0 : Y ∈ ybSet sel mu cst p.deco.1.N` using `hYm`. Establish `hY1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N` using `(ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm0`. Use `choose κ₀ hκ₀ hκr₀ hκQ₀ using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p₀ (L.levG m2 al) (L.levQ m2 al) g₀ w`. Use `choose κ hκ hκr hκQ using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w`.

Establish `hfr₀ : frsF sel mu (g₀ • p₀) = fun P => g₀.1.1 * frsF sel mu p₀ P * (κ₀ P).1` using `funext hκ₀`. Establish `hfr : frsF sel mu (g • p) = fun P => g.1.1 * frsF sel mu p P * (κ P).1` using `funext hκ`. Establish `hN₀ : IsSdLat p₀.deco.1.N` using `⟨p₀.deco.2.lat, p₀.deco.2.uni⟩`. Establish `hN : IsSdLat p.deco.1.N` using `⟨p.deco.2.lat, p.deco.2.uni⟩`. Establish `hdeco₀ : (g₀ • p₀).deco = (g₀.1, (g₀.2.1 : GLG X.E (R.N m2) Pr.vGs)) • p₀.deco` using `rfl`.

Establish `hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco` using `rfl`. Establish `hrep` using `psiAt_repYA Ch sel mu cst L hL al p g.1.1 Y hYm0`. Establish `hΞ : ∀ x, (∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P (LinearEquiv.det (κ₀ P).1 : X.Eˣ) * rhoT Ch sel mu m2 P (LinearEquiv.det (κ P).1 : X.Eˣ)) * XiCpl1 Ch sel mu cst L m2 al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y) (g.1.1.toLinearMap ∘ₗ x ∘ₗ g₀.1.1.symm.toLinearMap) = (((((L. …`. Introduce `x`. Unfold `XiCpl1`.

Rewrite using `[hfr₀, hfr, hdeco₀, hdeco, phiT_smul]`. Simplify using `only [inFr_move1, mul_three_symm_apply]`. Rewrite using `[locChr_ratio sel mu hS]`. Use `prod_mul_eq_of_pointwise_cross _ _ _ _ _ fun w => ?_` and prove the remaining obligations. Rewrite using `[← hrep w (inFr (frsF sel mu p₀ w) (frsF sel mu p w) x)]`.

Conclude with `psi_localQ Ch sel mu cst L m2 al b (hPsi al) (hPsiQ al) g₀ g w (κ₀ w) (κ w) (hκr₀ w) (hκQ₀ w) (hκr w) (hκQ w) _ _`. Establish `key` using `kerOf_move (hOk.th m2 le_rfl) (cBof_pos sel mu cst u hT) hN₀ hN (frsF sel mu p₀) (frsF sel mu p) g₀.1 g.1 κ₀ κ (XiCpl1 Ch sel mu cst L m2 al p₀ p Y) (XiCpl1 Ch sel mu cst L m2 al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y)) _ (fun x z hz => xiCpl1_invA Ch sel mu cst L hPr hL al p …`. Use `show cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y) = (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g) ∘ₗ cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y ∘ₗ (frmRho (colValF W sel …`. Unfold `cp1K`. Rewrite using `[if_pos hY1, if_pos hYm0, hfr₀, hfr]`.

Use `key.trans ?_` and prove the remaining obligations. Simplify using `only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_inv, Prod.snd_inv, map_inv, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]`. Use `congr 1`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cp1EquivOn_ofQ (hS : QSep Pr sel mu) (hT : 0 < Pr.T u) (hPr : Pr.Ok)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2)
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (hPsi : ∀ al : L.β m2, PsiLaw Ch sel mu cst L m2 al b) (hPsiQ : ∀ al : L.β m2, PsiLawQ Ch sel mu cst L m2 al b) :
    Cp1EquivOn W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) b hY := by
  intro al g₀ g p₀ p (Y : Set (Sp X.E (R.N (m2 + 1)))) hYm
  have hYm0 : Y ∈ ybSet sel mu cst p.deco.1.N := hYm
  have hY1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N :=
    (ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm0
  choose κ₀ hκ₀ hκr₀ hκQ₀ using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p₀ (L.levG m2 al) (L.levQ m2 al) g₀ w
  choose κ hκ hκr hκQ using fun w : rowSG Pr sel mu => frsF_smulQ sel mu u p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w
  have hfr₀ : frsF sel mu (g₀ • p₀) = fun P => g₀.1.1 * frsF sel mu p₀ P * (κ₀ P).1 := funext hκ₀
  have hfr : frsF sel mu (g • p) = fun P => g.1.1 * frsF sel mu p P * (κ P).1 := funext hκ
  have hN₀ : IsSdLat p₀.deco.1.N := ⟨p₀.deco.2.lat, p₀.deco.2.uni⟩
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hdeco₀ : (g₀ • p₀).deco = (g₀.1, (g₀.2.1 : GLG X.E (R.N m2) Pr.vGs)) • p₀.deco := rfl
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco := rfl
  have hrep := psiAt_repYA Ch sel mu cst L hL al p g.1.1 Y hYm0
  have hΞ : ∀ x, (∏ P : rowSG Pr sel mu, rhoS Ch sel mu m2 P (LinearEquiv.det (κ₀ P).1 : X.Eˣ) *
        rhoT Ch sel mu m2 P (LinearEquiv.det (κ P).1 : X.Eˣ)) *
      XiCpl1 Ch sel mu cst L m2 al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y) (g.1.1.toLinearMap ∘ₗ x ∘ₗ g₀.1.1.symm.toLinearMap) =
      (((((L.levG (m2 + 1) b).chr g.2.1 * (L.levQ (m2 + 1) b).chr g.2.2) *
        ((L.levG m2 al).chr g₀.2.1 * (L.levQ m2 al).chr g₀.2.2)⁻¹ : X.Kˣ)) : X.K) * XiCpl1 Ch sel mu cst L m2 al p₀ p Y x := by
    intro x
    unfold XiCpl1
    rw [hfr₀, hfr, hdeco₀, hdeco, phiT_smul]
    simp only [inFr_move1, mul_three_symm_apply]
    rw [locChr_ratio sel mu hS]
    refine prod_mul_eq_of_pointwise_cross _ _ _ _ _ fun w => ?_
    rw [← hrep w (inFr (frsF sel mu p₀ w) (frsF sel mu p w) x)]
    exact psi_localQ Ch sel mu cst L m2 al b (hPsi al) (hPsiQ al) g₀ g w (κ₀ w) (κ w) (hκr₀ w) (hκQ₀ w) (hκr w) (hκQ w) _ _
  have key := kerOf_move (hOk.th m2 le_rfl) (cBof_pos sel mu cst u hT) hN₀ hN (frsF sel mu p₀) (frsF sel mu p) g₀.1 g.1 κ₀ κ
    (XiCpl1 Ch sel mu cst L m2 al p₀ p Y) (XiCpl1 Ch sel mu cst L m2 al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y)) _
    (fun x z hz => xiCpl1_invA Ch sel mu cst L hPr hL al p₀ p Y x z hz) hΞ
  show cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al (g₀ • p₀) (g • p) ((fun v => g.1.1 v) '' Y) =
    (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g) ∘ₗ
      cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) al p₀ p Y ∘ₗ
      (frmRho (colValF W sel mu u m2) (L.levG m2 al) (L.levQ m2 al) g₀⁻¹)
  unfold cp1K
  rw [if_pos hY1, if_pos hYm0, hfr₀, hfr]
  refine key.trans ?_
  simp only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_inv, Prod.snd_inv, map_inv,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
  congr 1
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  ring

end MatQ

section FrameOrd

def fE (k₀ c n : ℕ) (h : k₀ ≤ n) : Fin (n + c) ≃ Fin (n + c) where
  toFun p := ⟨LocE.fIdx k₀ c n p.1, by have := p.2; unfold LocE.fIdx; split_ifs <;> omega⟩
  invFun l := ⟨LocE.fPos k₀ c n l.1, by have := l.2; unfold LocE.fPos; split_ifs <;> omega⟩
  left_inv p := by
    apply Fin.ext
    have := p.2
    simp only [LocE.fIdx, LocE.fPos]
    split_ifs <;> omega
  right_inv l := by
    apply Fin.ext
    have := l.2
    simp only [LocE.fIdx, LocE.fPos]
    split_ifs <;> omega

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fE_val (k₀ c n : ℕ) (h : k₀ ≤ n) (p : Fin (n + c)) : (fE k₀ c n h p).1 = LocE.fIdx k₀ c n p.1 := rfl

/- English proof (translation)
Substitute `hN` using the available equality. Conclude with `det_LLz A hA`.
-/
theorem det_LLzC {k : Type} [CommRing k] {N r d : ℕ} (hN : N = r + d) (hr : r ≤ N) (A : Matrix (Fin N) (Fin N) k) (hA : LLz r A) :
    A.det = (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det * (A.submatrix (brI hN) (brI hN)).det := by
  subst hN
  exact det_LLz A hA

/- English proof (translation)
Take `⟨u, rfl⟩` from `ha`. Rewrite using `[xiZ_unit]`. Conclude with `Units.ne_zero _`.
-/
theorem xiZ_ne_zero {k K : Type} [CommRing k] [Field K] (ξ : kˣ →* Kˣ) {a : k} (ha : IsUnit a) : xiZ ξ a ≠ 0 := by
  obtain ⟨u, rfl⟩ := ha
  rw [xiZ_unit]
  exact Units.ne_zero _

/- English proof (translation)
Take `⟨u, rfl⟩` from `ha`. Rewrite using `[xiZ_unit, xiZ_unit, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]`.
-/
theorem xiZ_inv_mul {k K : Type} [CommRing k] [Field K] (ξ : kˣ →* Kˣ) {a : k} (ha : IsUnit a) : xiZ ξ⁻¹ a * xiZ ξ a = 1 := by
  obtain ⟨u, rfl⟩ := ha
  rw [xiZ_unit, xiZ_unit, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/- English proof (translation)
Rewrite using `[← xiZ_mul, h, ← Units.val_one, xiZ_unit, map_one, Units.val_one]`.
-/
theorem xiZ_mul_one {k K : Type} [CommRing k] [Field K] (ξ : kˣ →* Kˣ) {a b : k} (h : a * b = 1) : xiZ ξ a * xiZ ξ b = 1 := by
  rw [← xiZ_mul, h, ← Units.val_one, xiZ_unit, map_one, Units.val_one]

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

/- English proof (translation)
Establish `s1 : ∀ m l, LocE.scE m 0 l = 0`. Introduce `m l`. Unfold `LocE.scE`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hlt' : LocE.fIdx k₀ c' n' p' < n' + c'` using `(fE k₀ c' n' h' ⟨p', hp'⟩).2`.

Establish `hlt : LocE.fIdx k₀ c n p < n + c` using `(fE k₀ c n h ⟨p, hp⟩).2`. Unfold `LocE.entB`. Rewrite using `[s1, s1, sub_zero, zpow_zero, mul_one, eN_inB _ _ hlt']`. Unfold `Loc.atN`. Rewrite using `[dif_pos hlt]`.

Both sides reduce to the same expression.
-/
theorem entB_frame (q k₀ c' n' c n : ℕ) (h' : k₀ ≤ n') (h : k₀ ≤ n) (x : HomE E (n' + c') (n + c)) (p p' : ℕ) (hp : p < n + c) (hp' : p' < n' + c') :
    LocE.entB q k₀ c' n' c n 0 0 x p p' = x (Pi.single (fE k₀ c' n' h' ⟨p', hp'⟩) 1) (fE k₀ c n h ⟨p, hp⟩) := by
  have s1 : ∀ m l, LocE.scE m 0 l = 0 := by
    intro m l
    unfold LocE.scE
    split_ifs <;> simp
  have hlt' : LocE.fIdx k₀ c' n' p' < n' + c' := (fE k₀ c' n' h' ⟨p', hp'⟩).2
  have hlt : LocE.fIdx k₀ c n p < n + c := (fE k₀ c n h ⟨p, hp⟩).2
  unfold LocE.entB
  rw [s1, s1, sub_zero, zpow_zero, mul_one, eN_inB _ _ hlt']
  unfold Loc.atN
  rw [dif_pos hlt]
  rfl

open Classical in

/- English proof (translation)
Establish `hq0` using `ciQ_ne_zero hu`. Establish `hent` using `entB_frame (E := E) q k₀ c' n' c n h' h x`. Unfold `LocE.PhiQ`. Distinguish the cases in `hI : ∀ s l, IntAt P (x (Pi.single s 1) l)`. Rewrite using `[if_pos hI]`.

Establish `hC1 : ∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB q k₀ c' n' c n 0 0 x p p')` using `fun p p' hp hp' => by`. Rewrite using `[hent p p' hp hp']`. Conclude with `hI _ _`. Establish `hC2 : (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (LocE.entB q k₀ c' n' c n 0 0 x p p' / (q : E))) ↔ LLz r ((redMQ P x).submatrix (fE k₀ c n h) (fE k₀ c' n' h'))`. Prove the components needed by the constructor for the conclusion.

Introduce `hh i j hi hj`. Establish `h1` using `hh i.1 j.1 hi i.2 hj`. Rewrite `h1` using `[hent _ _ i.2 j.2]`. Conclude with `(ciRed_of_div hq hq0 h1).2`. Introduce `hh p p' hp1 hp2 hp'`.

Establish `hp'' : p' < n' + c'` using `lt_of_lt_of_le hp' hr'`. Rewrite using `[hent p p' hp2 hp'']`. Conclude with `ciIntAt_div hq hu (hI _ _) (hh ⟨p, hp2⟩ ⟨p', hp''⟩ hp1 hp')`. Unfold `phiZ`. Distinguish the cases in `hL : LLz r ((redMQ P x).submatrix (fE k₀ c n h) (fE k₀ c' n' h'))`.

Rewrite using `[if_pos ⟨hC1, hC2.2 hL⟩, if_pos hL]`. Establish `hmat : (Matrix.of fun s t : Fin r => LocE.entB q k₀ c' n' c n 0 0 x s.1 t.1) = Matrix.of fun s t : Fin r => x (Pi.single (fE k₀ c' n' h' (Fin.castLE hr' t)) 1) (fE k₀ c n h (Fin.castLE hr s))`. Use extensionality with `s t`. Conclude with `hent _ _ _ _`. Rewrite using `[hmat, unitV_eq, redP_det (Matrix.of fun s t : Fin r => x (Pi.single (fE k₀ c' n' h' (Fin.castLE hr' t)) 1) (fE k₀ c n h (Fin.castLE hr s))) fun s t => hI _ _]`.

Conclude with `congrArg (fun N => xiZ ξ (Matrix.det N)) (Matrix.ext fun _ _ => rfl)`. Rewrite using `[if_neg (fun hh => hL (hC2.1 hh.2)), if_neg hL]`. Rewrite using `[if_neg hI, if_neg]`. Introduce `hh`. Conclude with `hI fun s l => by`.

Establish `h1` using `hh.1 ((fE k₀ c n h).symm l).1 ((fE k₀ c' n' h').symm s).1 (Fin.is_lt _) (Fin.is_lt _)`. Rewrite `h1` using `[hent _ _ (Fin.is_lt _) (Fin.is_lt _)]`. Simplify `h1` using `only [Fin.eta, Equiv.apply_symm_apply]`.
-/
theorem phiQ_eqG {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r c' n' c n : ℕ) (h' : k₀ ≤ n') (h : k₀ ≤ n) (hr' : r ≤ n' + c') (hr : r ≤ n + c) (x : HomE E (n' + c') (n + c)) :
    LocE.PhiQ q ξ k₀ r c' n' c n x = if (∀ s l, IntAt P (x (Pi.single s 1) l)) then
      phiZ ξ hr hr' ((redMQ P x).submatrix (fE k₀ c n h) (fE k₀ c' n' h')) else 0 := by
  have hq0 := ciQ_ne_zero hu
  have hent := entB_frame (E := E) q k₀ c' n' c n h' h x
  unfold LocE.PhiQ
  by_cases hI : ∀ s l, IntAt P (x (Pi.single s 1) l)
  · rw [if_pos hI]
    have hC1 : ∀ p p', p < n + c → p' < n' + c' → IntAt P (LocE.entB q k₀ c' n' c n 0 0 x p p') := fun p p' hp hp' => by
      rw [hent p p' hp hp']
      exact hI _ _
    have hC2 : (∀ p p', r ≤ p → p < n + c → p' < r → IntAt P (LocE.entB q k₀ c' n' c n 0 0 x p p' / (q : E))) ↔
        LLz r ((redMQ P x).submatrix (fE k₀ c n h) (fE k₀ c' n' h')) := by
      constructor
      · intro hh i j hi hj
        have h1 := hh i.1 j.1 hi i.2 hj
        rw [hent _ _ i.2 j.2] at h1
        exact (ciRed_of_div hq hq0 h1).2
      · intro hh p p' hp1 hp2 hp'
        have hp'' : p' < n' + c' := lt_of_lt_of_le hp' hr'
        rw [hent p p' hp2 hp'']
        exact ciIntAt_div hq hu (hI _ _) (hh ⟨p, hp2⟩ ⟨p', hp''⟩ hp1 hp')
    unfold phiZ
    by_cases hL : LLz r ((redMQ P x).submatrix (fE k₀ c n h) (fE k₀ c' n' h'))
    · rw [if_pos ⟨hC1, hC2.2 hL⟩, if_pos hL]
      have hmat : (Matrix.of fun s t : Fin r => LocE.entB q k₀ c' n' c n 0 0 x s.1 t.1) =
          Matrix.of fun s t : Fin r => x (Pi.single (fE k₀ c' n' h' (Fin.castLE hr' t)) 1) (fE k₀ c n h (Fin.castLE hr s)) := by
        ext s t
        exact hent _ _ _ _
      rw [hmat, unitV_eq, redP_det (Matrix.of fun s t : Fin r => x (Pi.single (fE k₀ c' n' h' (Fin.castLE hr' t)) 1) (fE k₀ c n h (Fin.castLE hr s)))
        fun s t => hI _ _]
      exact congrArg (fun N => xiZ ξ (Matrix.det N)) (Matrix.ext fun _ _ => rfl)
    · rw [if_neg (fun hh => hL (hC2.1 hh.2)), if_neg hL]
  · rw [if_neg hI, if_neg]
    intro hh
    exact hI fun s l => by
      have h1 := hh.1 ((fE k₀ c n h).symm l).1 ((fE k₀ c' n' h').symm s).1 (Fin.is_lt _) (Fin.is_lt _)
      rw [hent _ _ (Fin.is_lt _) (Fin.is_lt _)] at h1
      simpa only [Fin.eta, Equiv.apply_symm_apply] using h1

/- English proof (translation)
Introduce `i j hi hj`. Establish `hi1 : kj ≤ (fE k₀ c n h i).1 ∧ (fE k₀ c n h i).1 < n`. Use `i.2` as an intermediate fact. Rewrite using `[fE_val]`. Unfold `LocE.fIdx`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `hj1 : ¬ (kj ≤ (fE k₀ c n h j).1 ∧ (fE k₀ c n h j).1 < n)`. Use `j.2` as an intermediate fact. Rewrite using `[fE_val]`. Unfold `LocE.fIdx`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `h1 : (Pi.single (fE k₀ c n h j) 1 : Sp E (n + c)) ∈ LocE.parL P q kj n c`. Unfold `LocE.parL`. Rewrite using `[ciMem_sclLat]`. Introduce `l`.

Distinguish the cases in `hl : l = fE k₀ c n h j`. Rewrite using `[hl, Pi.single_eq_same, if_neg hj1, zpow_zero, inv_one, one_mul]`. Conclude with `ciIntAt_one`. Rewrite using `[Pi.single_eq_of_ne hl, mul_zero]`. Conclude with `ciIntAt_zero`.

Establish `h2` using `(hg.2 _).2 h1`. Unfold `LocE.parL at h2`. Rewrite `h2` using `[ciMem_sclLat]`. Establish `h3` using `h2 (fE k₀ c n h i)`. Use `beta_reduce at h3`.

Rewrite `h3` using `[if_pos hi1, zpow_one, inv_mul_eq_div]`. Conclude with `(ciRed_of_div hq hq0 h3).2`.
-/
theorem jq_LLzG {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {k₀ kj n c : ℕ} (h : k₀ ≤ n) (hk : k₀ ≤ kj)
    {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ LocE.JQ P q kj n c) :
    LLz (kj + c) ((redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h)) := by
  intro i j hi hj
  have hi1 : kj ≤ (fE k₀ c n h i).1 ∧ (fE k₀ c n h i).1 < n := by
    have := i.2
    rw [fE_val]
    unfold LocE.fIdx
    split_ifs <;> omega
  have hj1 : ¬ (kj ≤ (fE k₀ c n h j).1 ∧ (fE k₀ c n h j).1 < n) := by
    have := j.2
    rw [fE_val]
    unfold LocE.fIdx
    split_ifs <;> omega
  have h1 : (Pi.single (fE k₀ c n h j) 1 : Sp E (n + c)) ∈ LocE.parL P q kj n c := by
    unfold LocE.parL
    rw [ciMem_sclLat]
    intro l
    by_cases hl : l = fE k₀ c n h j
    · rw [hl, Pi.single_eq_same, if_neg hj1, zpow_zero, inv_one, one_mul]
      exact ciIntAt_one
    · rw [Pi.single_eq_of_ne hl, mul_zero]
      exact ciIntAt_zero
  have h2 := (hg.2 _).2 h1
  unfold LocE.parL at h2
  rw [ciMem_sclLat] at h2
  have h3 := h2 (fE k₀ c n h i)
  beta_reduce at h3
  rw [if_pos hi1, zpow_one, inv_mul_eq_div] at h3
  exact (ciRed_of_div hq hq0 h3).2

/- English proof (translation)
Establish `h` using `redMQ_mul_inv P ((GLint E n P).inv_mem hf)`. Rewrite `h` using `[inv_inv]`. Then use the resulting hypothesis.
-/
theorem redMQ_inv_mul {n : ℕ} {f : Sp E n ≃ₗ[E] Sp E n} (hf : f ∈ GLint E n P) :
    redMQ P f.toLinearMap * redMQ P (f⁻¹ : Sp E n ≃ₗ[E] Sp E n).toLinearMap = 1 := by
  have h := redMQ_mul_inv P ((GLint E n P).inv_mem hf)
  rwa [inv_inv] at h

/- English proof (translation)
Establish `hq0` using `ciQ_ne_zero hu`. Establish `hfG : f ∈ GLint E (n' + c') P` using `hf.1`. Establish `hgG : g ∈ GLint E (n + c) P` using `hg.1`. Establish `lA` using `jq_LLzG hq hq0 h hk hg`. Establish `lAi` using `jq_LLzG hq hq0 h hk ((LocE.JQ P q kj n c).inv_mem hg)`.

Establish `lB` using `jq_LLzG hq hq0 h' hk' hf`. Establish `lBi` using `jq_LLzG hq hq0 h' hk' ((LocE.JQ P q kj' n' c').inv_mem hf)`. Rewrite `lA`, `lAi` using `[e]`. Rewrite `lB`, `lBi` using `[e']`. Establish `h1 : (redMQ P (g⁻¹ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h) * (redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h) = 1`.

Rewrite using `[Matrix.submatrix_mul_equiv, redMQ_mul_inv P hgG, Matrix.submatrix_one_equiv]`. Establish `h2 : (redMQ P f.toLinearMap).submatrix (fE k₀ c' n' h') (fE k₀ c' n' h') * (redMQ P (f⁻¹ : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')).toLinearMap).submatrix (fE k₀ c' n' h') (fE k₀ c' n' h') = 1`. Rewrite using `[Matrix.submatrix_mul_equiv, redMQ_inv_mul hfG, Matrix.submatrix_one_equiv]`. Rewrite using `[phiQ_eqG hq hu ξ k₀ r c' n' c n h' h hr' hr, phiQ_eqG hq hu ξ k₀ r c' n' c n h' h hr' hr]`. Use `split_ifs with k1 k2 k2`.

Establish `es` using `redMQ_sandwich P hfG g (redMQ P g.toLinearMap) (fun v hv => redV_map P g.toLinearMap (glint_int P hgG) hv) y k2`. Establish `es2 : (redMQ P (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap)).submatrix (fE k₀ c n h) (fE k₀ c' n' h') = (redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h) * (redMQ P y).submatrix (fE k₀ c n h) (fE k₀ c' n' h') * (redMQ P f.toLinearMap).submatrix (fE k₀ c' n' h') (fE k₀ c' n' …`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, es]`. Rewrite using `[es2]`. Conclude with `phiZ_law ξ hr hr' _ _ _ _ lA lAi lB lBi h1 h2 _`.

Conclude with `absurd ((intM_sandwich P hfG hgG y).1 k1) k2`. Conclude with `absurd ((intM_sandwich P hfG hgG y).2 k2) k1`. Rewrite using `[mul_zero]`.
-/
theorem phiQ_lawG {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r c' n' c n kj' kj : ℕ) (h' : k₀ ≤ n') (h : k₀ ≤ n) (hk' : k₀ ≤ kj') (hk : k₀ ≤ kj) (e' : kj' + c' = r) (e : kj + c = r)
    (hr' : r ≤ n' + c') (hr : r ≤ n + c)
    {f : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hf : f ∈ LocE.JQ P q kj' n' c') {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ LocE.JQ P q kj n c)
    (y : HomE E (n' + c') (n + c)) :
    LocE.PhiQ q ξ k₀ r c' n' c n (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) =
      xiZ ξ (((redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h)).submatrix (Fin.castLE hr) (Fin.castLE hr)).det *
        xiZ ξ (((redMQ P f.toLinearMap).submatrix (fE k₀ c' n' h') (fE k₀ c' n' h')).submatrix (Fin.castLE hr') (Fin.castLE hr')).det *
        LocE.PhiQ q ξ k₀ r c' n' c n y := by
  classical
  have hq0 := ciQ_ne_zero hu
  have hfG : f ∈ GLint E (n' + c') P := hf.1
  have hgG : g ∈ GLint E (n + c) P := hg.1
  have lA := jq_LLzG hq hq0 h hk hg
  have lAi := jq_LLzG hq hq0 h hk ((LocE.JQ P q kj n c).inv_mem hg)
  have lB := jq_LLzG hq hq0 h' hk' hf
  have lBi := jq_LLzG hq hq0 h' hk' ((LocE.JQ P q kj' n' c').inv_mem hf)
  rw [e] at lA lAi
  rw [e'] at lB lBi
  have h1 : (redMQ P (g⁻¹ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)).toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h) *
      (redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h) = 1 := by
    rw [Matrix.submatrix_mul_equiv, redMQ_mul_inv P hgG, Matrix.submatrix_one_equiv]
  have h2 : (redMQ P f.toLinearMap).submatrix (fE k₀ c' n' h') (fE k₀ c' n' h') *
      (redMQ P (f⁻¹ : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')).toLinearMap).submatrix (fE k₀ c' n' h') (fE k₀ c' n' h') = 1 := by
    rw [Matrix.submatrix_mul_equiv, redMQ_inv_mul hfG, Matrix.submatrix_one_equiv]
  rw [phiQ_eqG hq hu ξ k₀ r c' n' c n h' h hr' hr, phiQ_eqG hq hu ξ k₀ r c' n' c n h' h hr' hr]
  split_ifs with k1 k2 k2
  · have es := redMQ_sandwich P hfG g (redMQ P g.toLinearMap) (fun v hv => redV_map P g.toLinearMap (glint_int P hgG) hv) y k2
    have es2 : (redMQ P (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap)).submatrix (fE k₀ c n h) (fE k₀ c' n' h') =
        (redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h) * (redMQ P y).submatrix (fE k₀ c n h) (fE k₀ c' n' h') *
          (redMQ P f.toLinearMap).submatrix (fE k₀ c' n' h') (fE k₀ c' n' h') := by
      rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, es]
    rw [es2]
    exact phiZ_law ξ hr hr' _ _ _ _ lA lAi lB lBi h1 h2 _
  · exact absurd ((intM_sandwich P hfG hgG y).1 k1) k2
  · exact absurd ((intM_sandwich P hfG hgG y).2 k2) k1
  · rw [mul_zero]

/- English proof (translation)
Substitute `e` using the available equality. Establish `hgG : g ∈ GLint E (n + c) P` using `hg.1`. Establish `hN : n + c = (kj + c) + (n - kj)` using `by omega`. Establish `lA` using `jq_LLzG hq hq0 h hk hg`. Establish `hdet` using `det_LLzC hN hr _ lA`.

Rewrite `hdet` using `[Matrix.det_submatrix_equiv_self]`. Establish `hu1 : IsUnit (redMQ P g.toLinearMap).det` using `IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, redMQ_inv_mul hgG, Matrix.det_one])`. Establish `hDD : LocE.lamQB ξ kj n g.toLinearMap = (xiZ ξ (((redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h)).submatrix (brI hN) (brI hN)).det)⁻¹`. Establish `hm : (Matrix.of fun s t : Fin (n - kj) => Loc.atN (g.toLinearMap (Loc.eN E (n + c) (kj + t.1))) (kj + s.1)) = Matrix.of fun s t : Fin (n - kj) => g.toLinearMap (Pi.single (fE k₀ c n h (brI hN t)) 1) (fE k₀ c n h (brI hN s))`. Use extensionality with `s t`.

Establish `ht : kj + t.1 < n + c` using `by have := t.2; omega`. Establish `hs : kj + s.1 < n + c` using `by have := s.2; omega`. Establish `et : fE k₀ c n h (brI hN t) = ⟨kj + t.1, ht⟩`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[fE_val]`.

Use `show LocE.fIdx k₀ c n (kj + c + t.1) = kj + t.1`. Unfold `LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`. Establish `es : fE k₀ c n h (brI hN s) = ⟨kj + s.1, hs⟩`. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[fE_val]`. Use `show LocE.fIdx k₀ c n (kj + c + s.1) = kj + s.1`. Unfold `LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[Matrix.of_apply, Matrix.of_apply, et, es, eN_inB _ _ ht]`.

Unfold `Loc.atN`. Rewrite using `[dif_pos hs]`. Unfold `LocE.lamQB`. Rewrite using `[hm, unitV_eq, redP_det (Matrix.of fun s t : Fin (n - kj) => g.toLinearMap (Pi.single (fE k₀ c n h (brI hN t)) 1) (fE k₀ c n h (brI hN s))) fun s t => glint_int P hgG _ _]`. Conclude with `congrArg (fun N => (xiZ ξ (Matrix.det N))⁻¹) (Matrix.ext fun _ _ => rfl)`.

Rewrite using `[hDD, hdet, xiZ_mul, mul_assoc, mul_inv_cancel₀, mul_one]`. Rewrite `hu1` using `[hdet]`. Conclude with `xiZ_ne_zero ξ (isUnit_of_mul_isUnit_right hu1)`.
-/
theorem jq_scal {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ kj n c : ℕ} (h : k₀ ≤ n) (hk : k₀ ≤ kj)
    (hkn : kj ≤ n) {r : ℕ} (e : kj + c = r) (hr : r ≤ n + c) {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ LocE.JQ P q kj n c) :
    xiZ ξ (((redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h)).submatrix (Fin.castLE hr) (Fin.castLE hr)).det =
      xiZ ξ (redMQ P g.toLinearMap).det * LocE.lamQB ξ kj n g.toLinearMap := by
  subst e
  have hgG : g ∈ GLint E (n + c) P := hg.1
  have hN : n + c = (kj + c) + (n - kj) := by omega
  have lA := jq_LLzG hq hq0 h hk hg
  have hdet := det_LLzC hN hr _ lA
  rw [Matrix.det_submatrix_equiv_self] at hdet
  have hu1 : IsUnit (redMQ P g.toLinearMap).det :=
    IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, redMQ_inv_mul hgG, Matrix.det_one])
  have hDD : LocE.lamQB ξ kj n g.toLinearMap =
      (xiZ ξ (((redMQ P g.toLinearMap).submatrix (fE k₀ c n h) (fE k₀ c n h)).submatrix (brI hN) (brI hN)).det)⁻¹ := by
    have hm : (Matrix.of fun s t : Fin (n - kj) => Loc.atN (g.toLinearMap (Loc.eN E (n + c) (kj + t.1))) (kj + s.1)) =
        Matrix.of fun s t : Fin (n - kj) => g.toLinearMap (Pi.single (fE k₀ c n h (brI hN t)) 1) (fE k₀ c n h (brI hN s)) := by
      ext s t
      have ht : kj + t.1 < n + c := by have := t.2; omega
      have hs : kj + s.1 < n + c := by have := s.2; omega
      have et : fE k₀ c n h (brI hN t) = ⟨kj + t.1, ht⟩ := by
        apply Fin.ext
        rw [fE_val]
        show LocE.fIdx k₀ c n (kj + c + t.1) = kj + t.1
        unfold LocE.fIdx
        split_ifs <;> omega
      have es : fE k₀ c n h (brI hN s) = ⟨kj + s.1, hs⟩ := by
        apply Fin.ext
        rw [fE_val]
        show LocE.fIdx k₀ c n (kj + c + s.1) = kj + s.1
        unfold LocE.fIdx
        split_ifs <;> omega
      rw [Matrix.of_apply, Matrix.of_apply, et, es, eN_inB _ _ ht]
      unfold Loc.atN
      rw [dif_pos hs]
    unfold LocE.lamQB
    rw [hm, unitV_eq, redP_det (Matrix.of fun s t : Fin (n - kj) => g.toLinearMap (Pi.single (fE k₀ c n h (brI hN t)) 1) (fE k₀ c n h (brI hN s)))
      fun s t => glint_int P hgG _ _]
    exact congrArg (fun N => (xiZ ξ (Matrix.det N))⁻¹) (Matrix.ext fun _ _ => rfl)
  rw [hDD, hdet, xiZ_mul, mul_assoc, mul_inv_cancel₀, mul_one]
  rw [hdet] at hu1
  exact xiZ_ne_zero ξ (isUnit_of_mul_isUnit_right hu1)

/- English proof (translation)
Establish `hq0` using `ciQ_ne_zero hu`. Rewrite using `[phiQ_lawG hq hu ξ k₀ r c' n' c n kj' kj (hk'.trans hkn') (hk.trans hkn) hk' hk e' e (by omega) (by omega) hf hg, jq_scal hq hq0 ξ (hk.trans hkn) hk hkn e (by omega) hg, jq_scal hq hq0 ξ (hk'.trans hkn') hk' hkn' e' (by omega) hf, unitV_eq, unitV_eq, redP_detEquiv P hg.1, redP_de …`.
-/
theorem phiQ_law_lam {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ r c' n' c n kj' kj : ℕ) (hk' : k₀ ≤ kj') (hk : k₀ ≤ kj) (hkn' : kj' ≤ n') (hkn : kj ≤ n) (e' : kj' + c' = r) (e : kj + c = r)
    {f : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hf : f ∈ LocE.JQ P q kj' n' c') {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hg : g ∈ LocE.JQ P q kj n c)
    (y : HomE E (n' + c') (n + c)) :
    LocE.PhiQ q ξ k₀ r c' n' c n (g.toLinearMap ∘ₗ y ∘ₗ f.toLinearMap) =
      (LocE.unitV ξ ((LinearEquiv.det g : Eˣ) : E) * LocE.lamQB ξ kj n g.toLinearMap) *
        (LocE.unitV ξ ((LinearEquiv.det f : Eˣ) : E) * LocE.lamQB ξ kj' n' f.toLinearMap) * LocE.PhiQ q ξ k₀ r c' n' c n y := by
  have hq0 := ciQ_ne_zero hu
  rw [phiQ_lawG hq hu ξ k₀ r c' n' c n kj' kj (hk'.trans hkn') (hk.trans hkn) hk' hk e' e (by omega) (by omega) hf hg,
    jq_scal hq hq0 ξ (hk.trans hkn) hk hkn e (by omega) hg, jq_scal hq hq0 ξ (hk'.trans hkn') hk' hkn' e' (by omega) hf,
    unitV_eq, unitV_eq, redP_detEquiv P hg.1, redP_detEquiv P hf.1]

end FrameOrd

section R1

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Establish `h` using `ciEN (E := E) (c := c) j.2`. Rewrite `h` using `[eN_inB _ _ (by have := j.2; omega)]`. Conclude with `h`.
-/
theorem single_castAdd_inX {n c : ℕ} (j : Fin n) : (Pi.single (Fin.castAdd c j) 1 : Sp E (n + c)) = Loc.inX E n c (Pi.single j 1) := by
  have h := ciEN (E := E) (c := c) j.2
  rw [eN_inB _ _ (by have := j.2; omega)] at h
  exact h

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[LinearEquiv.coe_det, LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← LinearMap.det_toMatrix']`. Establish `hM : ∀ (N : ℕ) (f : Sp E N →ₗ[E] Sp E N) i j, LinearMap.toMatrix' f i j = f (Pi.single j 1) i`. Introduce `N f i j`. Simplify using `[LinearMap.toMatrix'_apply]`.

Establish `hL : LLz n (LinearMap.toMatrix' r.toLinearMap)`. Introduce `i j hi hj`. Establish `e : (Pi.single j 1 : Sp E (n + c)) = Loc.inX E n c (Pi.single ⟨j.1, hj⟩ 1)` using `single_castAdd_inX ⟨j.1, hj⟩`. Rewrite using `[hM, e]`. Use `show r (Loc.inX E n c _) i = 0`.

Rewrite using `[hx, ciInX_apply, dif_neg (by omega)]`. Rewrite using `[det_LLz _ hL]`. Establish `e1 : (LinearMap.toMatrix' r.toLinearMap).submatrix (Fin.castAdd c) (Fin.castAdd c) = LinearMap.toMatrix' g.toLinearMap`. Use extensionality with `i j`. Rewrite using `[Matrix.submatrix_apply, hM, hM, single_castAdd_inX]`.

Use `show r (Loc.inX E n c _) _ = _`. Rewrite using `[hx, ciInX_castAdd]`. Both sides reduce to the same expression. Establish `hb : ∀ s t : Fin c, t.1 ≤ s.1 → ((LinearMap.toMatrix' r.toLinearMap).submatrix (Fin.natAdd n) (Fin.natAdd n)) s t = if s.1 = t.1 then 1 else 0`. Introduce `s t hst`.

Establish `h1` using `hr.2.2 t.1 (Fin.natAdd n s) (by show ¬ (n + s.1 < n + t.1) omega)`. Rewrite `h1` using `[Pi.sub_apply, sub_eq_zero]`. Establish `ht : n + t.1 < n + c` using `by have := t.2; omega`. Rewrite using `[Matrix.submatrix_apply, hM]`. Establish `e : (Pi.single (Fin.natAdd n t) 1 : Sp E (n + c)) = Loc.eN E (n + c) (n + t.1)` using `(eN_inB _ _ ht).symm`.

Rewrite using `[e]`. Use `h1.trans ?_` and prove the remaining obligations. Unfold `Loc.eN`. Establish `e2 : ((Fin.natAdd n s).1 = n + t.1) ↔ s.1 = t.1` using `by show n + s.1 = n + t.1 ↔ _`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [e2]`. Establish `e2 : ((LinearMap.toMatrix' r.toLinearMap).submatrix (Fin.natAdd n) (Fin.natAdd n)).det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular]`. Conclude with `Finset.prod_eq_one fun s _ => by rw [hb s s le_rfl, if_pos rfl]`. Introduce `s t hst`.

Establish `hst' : t.1 < s.1` using `hst`. Rewrite using `[hb s t hst'.le, if_neg (by omega)]`. Rewrite using `[e1, e2, mul_one]`.
-/
theorem det_first_parabolic_eq_det_block {n c : ℕ} {r : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hr : Loc.R1cond E n c r) {g : Sp E n ≃ₗ[E] Sp E n}
    (hx : ∀ x, r (Loc.inX E n c x) = Loc.inX E n c (g x)) : LinearEquiv.det r = LinearEquiv.det g := by
  apply Units.ext
  rw [LinearEquiv.coe_det, LinearEquiv.coe_det, ← LinearMap.det_toMatrix', ← LinearMap.det_toMatrix']
  have hM : ∀ (N : ℕ) (f : Sp E N →ₗ[E] Sp E N) i j, LinearMap.toMatrix' f i j = f (Pi.single j 1) i := by
    intro N f i j
    simp [LinearMap.toMatrix'_apply]
  have hL : LLz n (LinearMap.toMatrix' r.toLinearMap) := by
    intro i j hi hj
    have e : (Pi.single j 1 : Sp E (n + c)) = Loc.inX E n c (Pi.single ⟨j.1, hj⟩ 1) := single_castAdd_inX ⟨j.1, hj⟩
    rw [hM, e]
    show r (Loc.inX E n c _) i = 0
    rw [hx, ciInX_apply, dif_neg (by omega)]
  rw [det_LLz _ hL]
  have e1 : (LinearMap.toMatrix' r.toLinearMap).submatrix (Fin.castAdd c) (Fin.castAdd c) = LinearMap.toMatrix' g.toLinearMap := by
    ext i j
    rw [Matrix.submatrix_apply, hM, hM, single_castAdd_inX]
    show r (Loc.inX E n c _) _ = _
    rw [hx, ciInX_castAdd]
    rfl
  have hb : ∀ s t : Fin c, t.1 ≤ s.1 →
      ((LinearMap.toMatrix' r.toLinearMap).submatrix (Fin.natAdd n) (Fin.natAdd n)) s t = if s.1 = t.1 then 1 else 0 := by
    intro s t hst
    have h1 := hr.2.2 t.1 (Fin.natAdd n s) (by
      show ¬ (n + s.1 < n + t.1)
      omega)
    rw [Pi.sub_apply, sub_eq_zero] at h1
    have ht : n + t.1 < n + c := by have := t.2; omega
    rw [Matrix.submatrix_apply, hM]
    have e : (Pi.single (Fin.natAdd n t) 1 : Sp E (n + c)) = Loc.eN E (n + c) (n + t.1) := (eN_inB _ _ ht).symm
    rw [e]
    refine h1.trans ?_
    unfold Loc.eN
    have e2 : ((Fin.natAdd n s).1 = n + t.1) ↔ s.1 = t.1 := by
      show n + s.1 = n + t.1 ↔ _
      omega
    simp only [e2]
  have e2 : ((LinearMap.toMatrix' r.toLinearMap).submatrix (Fin.natAdd n) (Fin.natAdd n)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · exact Finset.prod_eq_one fun s _ => by rw [hb s s le_rfl, if_pos rfl]
    · intro s t hst
      have hst' : t.1 < s.1 := hst
      rw [hb s t hst'.le, if_neg (by omega)]
  rw [e1, e2, mul_one]

/- English proof (translation)
Substitute `hc'` using the available equality. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Establish `haN : ∀ v : Sp E (n' + 1), atNL E (n' + 1) n' v = v (Fin.last n')`. Introduce `v`. Unfold `atNL`.

Rewrite using `[dif_pos (Nat.lt_succ_self _)]`. Both sides reduce to the same expression. Establish `hdec : v = Loc.inX E n' 1 (LinearMap.funLeft E E (Fin.castAdd 1) v) + (v (Fin.last n')) • Loc.eN E (n' + 1) n'`. Use function extensionality and compare the values at `l`. Rewrite using `[Pi.add_apply, Pi.smul_apply, smul_eq_mul, ciInX_apply]`.

Unfold `Loc.eN`. Distinguish the cases in `hl : l.1 < n'`. Rewrite using `[dif_pos hl, if_neg (by omega), mul_zero, add_zero]`. Both sides reduce to the same expression. Establish `hl2 : l = Fin.last n'` using `Fin.ext (by`.

Use `l.2` as an intermediate fact. Use `show l.1 = n'`. Use the proof step `omega)`. Rewrite using `[dif_neg hl, if_pos (by rw [hl2]; rfl), mul_one, zero_add, hl2]`. Establish `hπ : ∀ z : Sp E n', LinearMap.funLeft E E (Fin.castAdd 1) (Loc.inX E n' 1 z) = z` using `fun z => funext fun i => ciInX_castAdd z i`.

Establish `hπe : LinearMap.funLeft E E (Fin.castAdd 1) (Loc.eN E (n' + 1) n') = (0 : Sp E n')`. Use function extensionality and compare the values at `i`. Use `show Loc.eN E (n' + 1) n' (Fin.castAdd 1 i) = 0`. Unfold `Loc.eN`. Rewrite using `[if_neg]`.

Use `i.2` as an intermediate fact. Use `show ¬ (i.1 = n')`. Use linear arithmetic over natural numbers and integers. Establish `ha : ∀ z : Sp E n', (Loc.inX E n' 1 z) (Fin.last n') = 0`. Introduce `z`.

Rewrite using `[ciInX_apply, dif_neg]`. Use `show ¬ (n' < n')`. Use linear arithmetic over natural numbers and integers. Establish `hae : (Loc.eN E (n' + 1) n') (Fin.last n') = 1` using `by show (if (Fin.last n').1 = n' then (1 : E) else 0) = 1`. Conclude with `if_pos rfl`.

Establish `hriv : ri v = Loc.inX E n' 1 (gi (LinearMap.funLeft E E (Fin.castAdd 1) v)) + (v (Fin.last n')) • Loc.eN E (n' + 1) n'` using `by conv_lhs => rw [hdec]`. Rewrite using `[map_add, map_smul, hxi, hri.2.1]`. Establish `h1 : LinearMap.funLeft E E (Fin.castAdd 1) (ri v) = gi (LinearMap.funLeft E E (Fin.castAdd 1) v)`. Rewrite using `[hriv, map_add, map_smul, hπ, hπe, smul_zero, add_zero]`. Establish `h2 : (ri v) (Fin.last n') = v (Fin.last n')`.

Rewrite using `[hriv, Pi.add_apply, Pi.smul_apply, ha, hae, smul_eq_mul, mul_one, zero_add]`. Simplify using `only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe, haN]`. Rewrite using `[hxc, h1, h2]`. Simplify using `only [map_add, map_smul]`.
-/
theorem joinCol_move {n' c' n c : ℕ} (hc' : c' = 1) {ri : Sp E (n' + c') ≃ₗ[E] Sp E (n' + c')} (hri : Loc.R1cond E n' c' ri)
    {gi : Sp E n' ≃ₗ[E] Sp E n'} (hxi : ∀ x, ri (Loc.inX E n' c' x) = Loc.inX E n' c' (gi x))
    {rc : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} {g : Sp E n ≃ₗ[E] Sp E n} (hxc : ∀ x, rc (Loc.inX E n c x) = Loc.inX E n c (g x))
    (x₀ : HomE E n' n) (y' : Sp E n) :
    (joinCol (g.toLinearMap ∘ₗ x₀ ∘ₗ gi.toLinearMap) (g y') : HomE E (n' + c') (n + c)) =
      rc.toLinearMap ∘ₗ joinCol x₀ y' ∘ₗ ri.toLinearMap := by
  subst hc'
  refine LinearMap.ext fun v => ?_
  have haN : ∀ v : Sp E (n' + 1), atNL E (n' + 1) n' v = v (Fin.last n') := by
    intro v
    unfold atNL
    rw [dif_pos (Nat.lt_succ_self _)]
    rfl
  have hdec : v = Loc.inX E n' 1 (LinearMap.funLeft E E (Fin.castAdd 1) v) + (v (Fin.last n')) • Loc.eN E (n' + 1) n' := by
    funext l
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ciInX_apply]
    unfold Loc.eN
    by_cases hl : l.1 < n'
    · rw [dif_pos hl, if_neg (by omega), mul_zero, add_zero]
      rfl
    · have hl2 : l = Fin.last n' := Fin.ext (by
        have := l.2
        show l.1 = n'
        omega)
      rw [dif_neg hl, if_pos (by rw [hl2]; rfl), mul_one, zero_add, hl2]
  have hπ : ∀ z : Sp E n', LinearMap.funLeft E E (Fin.castAdd 1) (Loc.inX E n' 1 z) = z := fun z => funext fun i => ciInX_castAdd z i
  have hπe : LinearMap.funLeft E E (Fin.castAdd 1) (Loc.eN E (n' + 1) n') = (0 : Sp E n') := by
    funext i
    show Loc.eN E (n' + 1) n' (Fin.castAdd 1 i) = 0
    unfold Loc.eN
    rw [if_neg]
    have := i.2
    show ¬ (i.1 = n')
    omega
  have ha : ∀ z : Sp E n', (Loc.inX E n' 1 z) (Fin.last n') = 0 := by
    intro z
    rw [ciInX_apply, dif_neg]
    show ¬ (n' < n')
    omega
  have hae : (Loc.eN E (n' + 1) n') (Fin.last n') = 1 := by
    show (if (Fin.last n').1 = n' then (1 : E) else 0) = 1
    exact if_pos rfl
  have hriv : ri v = Loc.inX E n' 1 (gi (LinearMap.funLeft E E (Fin.castAdd 1) v)) + (v (Fin.last n')) • Loc.eN E (n' + 1) n' := by
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, hxi, hri.2.1]
  have h1 : LinearMap.funLeft E E (Fin.castAdd 1) (ri v) = gi (LinearMap.funLeft E E (Fin.castAdd 1) v) := by
    rw [hriv, map_add, map_smul, hπ, hπe, smul_zero, add_zero]
  have h2 : (ri v) (Fin.last n') = v (Fin.last n') := by
    rw [hriv, Pi.add_apply, Pi.smul_apply, ha, hae, smul_eq_mul, mul_one, zero_add]
  simp only [joinCol, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearEquiv.coe_coe, haN]
  rw [hxc, h1, h2]
  simp only [map_add, map_smul]

end R1

section PsiQ

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

open Classical in

/- English proof (translation)
Rewrite using `[hOk.chrQ j bb ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩ c r hr hx]`. Unfold `chiInv`. Establish `hn1 : Loc.n1Arg r = 0`. Unfold `Loc.n1Arg`. Rewrite using `[hj, Finset.range_zero, Finset.sum_empty]`.

Rewrite using `[hn1, hOk.cst_ok.psi_int _ 0 ciIntAt_zero, inv_one, one_mul]`. Unfold `lamRow`. Rewrite using `[if_neg hw]`.
-/
theorem levQ_lam_eq {G : ChGlob X R.m} {m2 : ℕ} (hOk : L.Ok Ch sel mu cst G m2) (j : ℕ) (hj : cOf R j - 1 = 0) (bb : L.β j) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs)
    (c : ↥(L.levQ j bb ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H) (r : AutY X R j)
    (hr : r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (L.h j bb w))
    (hx : ∀ x, r (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (c.1.1 x)) :
    (((L.levQ j bb ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam c : X.Kˣ) : X.K) =
      LocE.lamQB (resChar (mu : Chr X.F X.E X.K) w.1) (R.k + j) (R.N j) (((L.h j bb w)⁻¹ * r * L.h j bb w : AutY X R j)).toLinearMap := by
  rw [hOk.chrQ j bb ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩ c r hr hx]
  unfold chiInv
  have hn1 : Loc.n1Arg r = 0 := by
    unfold Loc.n1Arg
    rw [hj, Finset.range_zero, Finset.sum_empty]
  rw [hn1, hOk.cst_ok.psi_int _ 0 ciIntAt_zero, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hw]

set_option maxHeartbeats 400000 in
open Classical in

/- English proof (translation)
Introduce `w hw c₀ c x₀ y'`. Establish `hm` using `hOk.hm`. Establish `hwQ : w.1 ∈ QE sel (mu : Chr X.F X.E X.K)` using `(Finset.mem_union.mp w.2).resolve_left hw`. Establish `hq : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal` using `qOf_memB w.1`. Establish `hu` using `hU w.1 hwQ`.

Establish `hq0` using `ciQ_ne_zero hu`. Establish `hgrp : ∀ (j : ℕ) (bb : L.β j) (c' : ↥(GLint X.E (R.N j) w.1)), c' ∈ (L.levQ j bb ⟨w.1, hwQ⟩).H → ∃ rr : AutY X R j, rr ∈ Loc.Cbe (Jat (Pr` using `Pr) cst.sharp j w.1) (L.h j bb w) ∧ ∀ x, rr (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (c'.1 x) := by`. Introduce `j bb c' h1`. Rewrite `h1` using `[hOk.grpQ j bb ⟨w.1, hwQ⟩, Subgroup.mem_subgroupOf]`. Conclude with `h1`.

Establish `hJ : ∀ (j : ℕ) (bb : L.β j) (rr : AutY X R j), rr ∈ Loc.Cbe (Jat (Pr` using `Pr) cst.sharp j w.1) (L.h j bb w) → ((L.h j bb w)⁻¹ * rr * L.h j bb w : AutY X R j) ∈ LocE.JQ w.1 (qOf w.1) (R.k + j) (R.N j) (cOf R j) := by`. Introduce `j bb rr hrr`. Establish `h2 : ((L.h j bb w)⁻¹ * rr * L.h j bb w : AutY X R j) ∈ Jat (Pr` using `Pr) (R := R) cst.sharp j w.1 := by`. Simplify `hrr.2` using `[MulAut.conj_apply]`. Unfold `Jat at h2`.

Rewrite `h2` using `[if_neg hw]`. Then use the resulting hypothesis. Take `⟨rc, hCc, hxc⟩` from `hgrp (m2 + 1) b c.1 c.2`. Take `⟨ri, hCi, hxi⟩` from `hgrp m2 al c₀.1⁻¹ (Subgroup.inv_mem _ c₀.2)`. Establish `hc0 : cOf R m2 = 1` using `by unfold cOf; omega`. Establish `hc1 : cOf R (m2 + 1) = 0` using `cOf_topB hm`.

Establish `hmul : m2 * (R.t + 1) = m2 * R.t + m2` using `by ring`. Establish `hmul1 : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1)` using `by ring`. Establish `a1 : R.k ≤ R.N m2` using `by unfold Ranks.N; omega`. Establish `a2 : R.k ≤ R.N (m2 + 1)` using `by unfold Ranks.N; omega`. Establish `a3 : R.k + m2 ≤ R.N m2` using `by unfold Ranks.N; omega`.

Establish `a4 : R.k + (m2 + 1) ≤ R.N (m2 + 1)` using `by unfold Ranks.N; omega`. Establish `e' : R.k + m2 + cOf R m2 = R.r` using `by unfold Ranks.r; omega`. Establish `e : R.k + (m2 + 1) + cOf R (m2 + 1) = R.r` using `by unfold Ranks.r; omega`. Establish `hr' : R.r ≤ R.N m2 + cOf R m2` using `by omega`. Establish `hr : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1)` using `by omega`.

Establish `hone : ((L.h (m2 + 1) b w)⁻¹ * rc * L.h (m2 + 1) b w : AutY X R (m2 + 1)) = rc`. Rewrite using `[hOk.last_h]`. Simplify using the standard rewrite rules. Establish `hJc : rc ∈ LocE.JQ w.1 (qOf w.1) (R.k + (m2 + 1)) (R.N (m2 + 1)) (cOf R (m2 + 1))`. Use `hJ (m2 + 1) b rc hCc` as an intermediate fact.

Rewrite `this` using `[hone]`. Then use the resulting hypothesis. Establish `hJi` using `hJ m2 al ri hCi`. Establish `hlb` using `levQ_lam_eq Ch sel mu cst L hOk (m2 + 1) (by rw [hc1]) b w hw c rc hCc hxc`. Rewrite `hlb` using `[hone]`. Establish `hla` using `levQ_lam_eq Ch sel mu cst L hOk m2 (by rw [hc0]) al w hw c₀⁻¹ ri hCi hxi`.

Rewrite `hla` using `[map_inv]`. Choose the witnesses or unpack the hypotheses as in `⟨Sc, hSc⟩ : ∃ Sc : X.K, ∀ (x₁ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y₁ : Sp X.E (R.N (m2 + 1))), PsiAt Ch sel mu cst m2 w (L.h m2 al w) x₁ y₁ = Sc * LocE.PhiQ (qOf w.1) (resChar (mu : Chr X.F X.E X.K) w.1) R.k R.r (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1)) (joinCol x₁ y₁ …`. Use `⟨Loc.om (muAt Ch sel mu cst m2 w) (LocE.vP w.1 (qOf w.1)) (cst.sq w) (L.h m2 al w) (1 : AutY X R (m2 + 1)) (fun _ => 1) 0, fun x₁ y₁ => ?_⟩` and prove the remaining obligations. Unfold `PsiAt omPhi Loc.om PhiAt`. Rewrite using `[if_neg hw, mul_one]`.

Both sides reduce to the same expression. Establish `hj` using `joinCol_move hc0 hCi.1.1 hxi hxc x₀ y'`. Establish `e3 : (rc.toLinearMap ∘ₗ joinCol x₀ y' ∘ₗ ri.toLinearMap) ∘ₗ (L.h m2 al w).toLinearMap = rc.toLinearMap ∘ₗ (joinCol x₀ y' ∘ₗ (L.h m2 al w).toLinearMap) ∘ₗ (((L.h m2 al w)⁻¹ * ri * L.h m2 al w : AutY X R m2)).toLinearMap`. Use `LinearMap.ext fun v => ?_` and prove the remaining obligations. Use `show rc (joinCol x₀ y' (ri (L.h m2 al w v))) = rc (joinCol x₀ y' (L.h m2 al w ((L.h m2 al w).symm (ri (L.h m2 al w v)))))`.

Rewrite using `[LinearEquiv.apply_symm_apply]`. Establish `d1 : (redMQ w.1 (((L.h m2 al w)⁻¹ * ri * L.h m2 al w : AutY X R m2)).toLinearMap).det = (redMQ w.1 (c₀.1⁻¹).1.toLinearMap).det`. Rewrite using `[← redP_detEquiv w.1 hJi.1, ← redP_detEquiv w.1 (c₀.1⁻¹).2, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left, det_first_parabolic_eq_det_block hCi.1.1 hxi]`. Establish `d2 : (redMQ w.1 rc.toLinearMap).det = (redMQ w.1 c.1.1.toLinearMap).det`. Rewrite using `[← redP_detEquiv w.1 hJc.1, ← redP_detEquiv w.1 c.1.2, det_first_parabolic_eq_det_block hCc.1.1 hxc]`.

Establish `hs1 : rhoS Ch sel mu m2 w (LinearEquiv.det (c₀.1⁻¹).1 : X.Eˣ) * xiZ (resChar (mu : Chr X.F X.E X.K) w.1) (redMQ w.1 (c₀.1⁻¹).1.toLinearMap).det = 1`. Unfold `rhoS`. Rewrite using `[if_neg hw, unitV_eq, redP_detEquiv w.1 (c₀.1⁻¹).2]`. Conclude with `xiZ_inv_mul _ (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, redMQ_inv_mul (c₀.1⁻¹).2, Matrix.det_one]))`. Establish `hs2 : rhoT Ch sel mu m2 w (LinearEquiv.det (c.1⁻¹).1 : X.Eˣ) * xiZ (resChar (mu : Chr X.F X.E X.K) w.1) (redMQ w.1 c.1.1.toLinearMap).det = 1`.

Unfold `rhoT`. Rewrite using `[if_neg hw, unitV_eq, redP_detEquiv w.1 (c.1⁻¹).2]`. Conclude with `xiZ_mul_one _ (by rw [← Matrix.det_mul]; exact (congrArg Matrix.det (redMQ_mul_inv w.1 c.1.2)).trans Matrix.det_one)`. Rewrite using `[hSc, hSc, hj, e3, phiQ_lawG hq hu _ R.k R.r (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.k + m2) (R.k + (m2 + 1)) a1 a2 (Nat.le_add_right _ _) (Nat.le_add_right _ _) e' e hr' hr hJi hJc, jq_scal hq hq0 _ a2 (Nat.le_add_right _ _) a4 e hr hJc, jq_scal hq hq0 _ a1 (Nat.l …`. Take the linear combination `(Sc * LocE.PhiQ (qOf w.1) (resChar (mu : Chr X.F X.E X.K) w.1) R.k R.r (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1)) (joinCol x₀ y' ∘ₗ (L.h m2 al w).toLinearMap) * LocE.lamQB (resChar (mu : Chr X.F X.E X.K) w.1) (R.k + (m2 + 1)) (R.N (m2 + 1)) rc.toLinearMap * LocE.lamQB (r …`.
-/
theorem psi_local_law_at_Q_primes {G : ChGlob X R.m} {m2 : ℕ} (hOk : L.Ok Ch sel mu cst G m2) (hU : QUnif sel mu)
    (al : L.β m2) (b : L.β (m2 + 1)) : PsiLawQ Ch sel mu cst L m2 al b := by
  intro w hw c₀ c x₀ y'
  have hm := hOk.hm
  have hwQ : w.1 ∈ QE sel (mu : Chr X.F X.E X.K) := (Finset.mem_union.mp w.2).resolve_left hw
  have hq : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := qOf_memB w.1
  have hu := hU w.1 hwQ
  have hq0 := ciQ_ne_zero hu
  have hgrp : ∀ (j : ℕ) (bb : L.β j) (c' : ↥(GLint X.E (R.N j) w.1)), c' ∈ (L.levQ j bb ⟨w.1, hwQ⟩).H →
      ∃ rr : AutY X R j, rr ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (L.h j bb w) ∧
        ∀ x, rr (Loc.inX X.E (R.N j) (cOf R j) x) = Loc.inX X.E (R.N j) (cOf R j) (c'.1 x) := by
    intro j bb c' h1
    rw [hOk.grpQ j bb ⟨w.1, hwQ⟩, Subgroup.mem_subgroupOf] at h1
    exact h1
  have hJ : ∀ (j : ℕ) (bb : L.β j) (rr : AutY X R j), rr ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp j w.1) (L.h j bb w) →
      ((L.h j bb w)⁻¹ * rr * L.h j bb w : AutY X R j) ∈ LocE.JQ w.1 (qOf w.1) (R.k + j) (R.N j) (cOf R j) := by
    intro j bb rr hrr
    have h2 : ((L.h j bb w)⁻¹ * rr * L.h j bb w : AutY X R j) ∈ Jat (Pr := Pr) (R := R) cst.sharp j w.1 := by
      simpa [MulAut.conj_apply] using hrr.2
    unfold Jat at h2
    rwa [if_neg hw] at h2
  obtain ⟨rc, hCc, hxc⟩ := hgrp (m2 + 1) b c.1 c.2
  obtain ⟨ri, hCi, hxi⟩ := hgrp m2 al c₀.1⁻¹ (Subgroup.inv_mem _ c₀.2)
  have hc0 : cOf R m2 = 1 := by unfold cOf; omega
  have hc1 : cOf R (m2 + 1) = 0 := cOf_topB hm
  have hmul : m2 * (R.t + 1) = m2 * R.t + m2 := by ring
  have hmul1 : (m2 + 1) * (R.t + 1) = (m2 + 1) * R.t + (m2 + 1) := by ring
  have a1 : R.k ≤ R.N m2 := by unfold Ranks.N; omega
  have a2 : R.k ≤ R.N (m2 + 1) := by unfold Ranks.N; omega
  have a3 : R.k + m2 ≤ R.N m2 := by unfold Ranks.N; omega
  have a4 : R.k + (m2 + 1) ≤ R.N (m2 + 1) := by unfold Ranks.N; omega
  have e' : R.k + m2 + cOf R m2 = R.r := by unfold Ranks.r; omega
  have e : R.k + (m2 + 1) + cOf R (m2 + 1) = R.r := by unfold Ranks.r; omega
  have hr' : R.r ≤ R.N m2 + cOf R m2 := by omega
  have hr : R.r ≤ R.N (m2 + 1) + cOf R (m2 + 1) := by omega
  have hone : ((L.h (m2 + 1) b w)⁻¹ * rc * L.h (m2 + 1) b w : AutY X R (m2 + 1)) = rc := by
    rw [hOk.last_h]
    simp
  have hJc : rc ∈ LocE.JQ w.1 (qOf w.1) (R.k + (m2 + 1)) (R.N (m2 + 1)) (cOf R (m2 + 1)) := by
    have := hJ (m2 + 1) b rc hCc
    rwa [hone] at this
  have hJi := hJ m2 al ri hCi
  have hlb := levQ_lam_eq Ch sel mu cst L hOk (m2 + 1) (by rw [hc1]) b w hw c rc hCc hxc
  rw [hone] at hlb
  have hla := levQ_lam_eq Ch sel mu cst L hOk m2 (by rw [hc0]) al w hw c₀⁻¹ ri hCi hxi
  rw [map_inv] at hla
  obtain ⟨Sc, hSc⟩ : ∃ Sc : X.K, ∀ (x₁ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y₁ : Sp X.E (R.N (m2 + 1))),
      PsiAt Ch sel mu cst m2 w (L.h m2 al w) x₁ y₁ = Sc * LocE.PhiQ (qOf w.1) (resChar (mu : Chr X.F X.E X.K) w.1) R.k R.r (cOf R m2) (R.N m2)
        (cOf R (m2 + 1)) (R.N (m2 + 1)) (joinCol x₁ y₁ ∘ₗ (L.h m2 al w).toLinearMap) := by
    refine ⟨Loc.om (muAt Ch sel mu cst m2 w) (LocE.vP w.1 (qOf w.1)) (cst.sq w) (L.h m2 al w) (1 : AutY X R (m2 + 1)) (fun _ => 1) 0, fun x₁ y₁ => ?_⟩
    unfold PsiAt omPhi Loc.om PhiAt
    rw [if_neg hw, mul_one]
    rfl
  have hj := joinCol_move hc0 hCi.1.1 hxi hxc x₀ y'
  have e3 : (rc.toLinearMap ∘ₗ joinCol x₀ y' ∘ₗ ri.toLinearMap) ∘ₗ (L.h m2 al w).toLinearMap =
      rc.toLinearMap ∘ₗ (joinCol x₀ y' ∘ₗ (L.h m2 al w).toLinearMap) ∘ₗ
        (((L.h m2 al w)⁻¹ * ri * L.h m2 al w : AutY X R m2)).toLinearMap := by
    refine LinearMap.ext fun v => ?_
    show rc (joinCol x₀ y' (ri (L.h m2 al w v))) = rc (joinCol x₀ y' (L.h m2 al w ((L.h m2 al w).symm (ri (L.h m2 al w v)))))
    rw [LinearEquiv.apply_symm_apply]
  have d1 : (redMQ w.1 (((L.h m2 al w)⁻¹ * ri * L.h m2 al w : AutY X R m2)).toLinearMap).det = (redMQ w.1 (c₀.1⁻¹).1.toLinearMap).det := by
    rw [← redP_detEquiv w.1 hJi.1, ← redP_detEquiv w.1 (c₀.1⁻¹).2, map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left, det_first_parabolic_eq_det_block hCi.1.1 hxi]
  have d2 : (redMQ w.1 rc.toLinearMap).det = (redMQ w.1 c.1.1.toLinearMap).det := by
    rw [← redP_detEquiv w.1 hJc.1, ← redP_detEquiv w.1 c.1.2, det_first_parabolic_eq_det_block hCc.1.1 hxc]
  have hs1 : rhoS Ch sel mu m2 w (LinearEquiv.det (c₀.1⁻¹).1 : X.Eˣ) *
      xiZ (resChar (mu : Chr X.F X.E X.K) w.1) (redMQ w.1 (c₀.1⁻¹).1.toLinearMap).det = 1 := by
    unfold rhoS
    rw [if_neg hw, unitV_eq, redP_detEquiv w.1 (c₀.1⁻¹).2]
    exact xiZ_inv_mul _ (IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, redMQ_inv_mul (c₀.1⁻¹).2, Matrix.det_one]))
  have hs2 : rhoT Ch sel mu m2 w (LinearEquiv.det (c.1⁻¹).1 : X.Eˣ) *
      xiZ (resChar (mu : Chr X.F X.E X.K) w.1) (redMQ w.1 c.1.1.toLinearMap).det = 1 := by
    unfold rhoT
    rw [if_neg hw, unitV_eq, redP_detEquiv w.1 (c.1⁻¹).2]
    exact xiZ_mul_one _ (by rw [← Matrix.det_mul]; exact (congrArg Matrix.det (redMQ_mul_inv w.1 c.1.2)).trans Matrix.det_one)
  rw [hSc, hSc, hj, e3, phiQ_lawG hq hu _ R.k R.r (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1)) (R.k + m2) (R.k + (m2 + 1)) a1 a2
    (Nat.le_add_right _ _) (Nat.le_add_right _ _) e' e hr' hr hJi hJc,
    jq_scal hq hq0 _ a2 (Nat.le_add_right _ _) a4 e hr hJc, jq_scal hq hq0 _ a1 (Nat.le_add_right _ _) a3 e' hr' hJi, d1, d2, hlb, hla]
  linear_combination
    (Sc * LocE.PhiQ (qOf w.1) (resChar (mu : Chr X.F X.E X.K) w.1) R.k R.r (cOf R m2) (R.N m2) (cOf R (m2 + 1)) (R.N (m2 + 1))
        (joinCol x₀ y' ∘ₗ (L.h m2 al w).toLinearMap) *
      LocE.lamQB (resChar (mu : Chr X.F X.E X.K) w.1) (R.k + (m2 + 1)) (R.N (m2 + 1)) rc.toLinearMap *
      LocE.lamQB (resChar (mu : Chr X.F X.E X.K) w.1) (R.k + m2) (R.N m2) (((L.h m2 al w)⁻¹ * ri * L.h m2 al w : AutY X R m2)).toLinearMap) *
    ((rhoT Ch sel mu m2 w (LinearEquiv.det (c.1⁻¹).1 : X.Eˣ) * xiZ (resChar (mu : Chr X.F X.E X.K) w.1) (redMQ w.1 c.1.1.toLinearMap).det) * hs1 + hs2)

end PsiQ

section Close

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

/- English proof (translation)
Assemble the required witnesses or components as `⟨matEquiv_ofQ W Ch sel mu cst L A u m2 hS (hPr.T_prime u).pos hOk (fun i hi al be p p' x z hz => xiEntry_invA Ch sel mu cst L hPr hL i hi al be p p' x z hz) hK.xi hK.xiQ, cp1EquivOn_ofQ W Ch sel mu cst L A u m2 hS (hPr.T_prime u).pos hPr hOk hL b hY hK.psi (fun al => psi_local_la …`.
-/
theorem kerHypOn_of_ok {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) (hPr : Pr.Ok) (hS : QSep Pr sel mu) (hU : QUnif sel mu) (hR : PosT sel mu u)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (hK : KerLaws Ch sel mu cst L P m2 b) :
    KerHypOn W Ch sel mu cst L A u m2 b hY P :=
  ⟨matEquiv_ofQ W Ch sel mu cst L A u m2 hS (hPr.T_prime u).pos hOk
      (fun i hi al be p p' x z hz => xiEntry_invA Ch sel mu cst L hPr hL i hi al be p p' x z hz) hK.xi hK.xiQ,
    cp1EquivOn_ofQ W Ch sel mu cst L A u m2 hS (hPr.T_prime u).pos hPr hOk hL b hY hK.psi (fun al => psi_local_law_at_Q_primes Ch sel mu cst L hL hU al b),
    cp2EquivOn_of_ok W Ch sel mu cst L A u m2 hL hS hU hR (hPr.T_prime u).pos hPr hOk b hY P hK.top⟩

end Close

section Fam

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}

end Fam

section Mu0Closed

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (A : Amb X) (u : Pr.Word) (m2 : ℕ)

end Mu0Closed

section RepOne

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

/- English proof (translation)
Establish `hB` using `clL_base hL hX hPr hCh hs`. Conclude with `{ xi := clW_xiLaw hL hX hPr hCh hs hone (fun i hi => xi_first_law_of_target hs (clT_xiTgtLaw G.σ₀ hB hi (by have := hB.hm; unfold cOf; omega)) (clX_phiLaw_steps hB i hi)) xiQ := hxiQ psi := fun al => clW_psiLaw hL hX hPr hCh hs hone (fun P hP => clPf_phiGSLaw (clPsi_phiHyp hX hPr …`.
-/
theorem kerLaws_of_repOne {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hs : cst.sharp = true)
    (hA : R.m ≤ cst.A) (hone : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1) (b : L.β (m2 + 1))
    (hxiQ : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLawQ Ch sel mu cst L i al be) :
    KerLaws Ch sel mu cst L (rPsymF Ch) m2 b := by
  have hB := clL_base hL hX hPr hCh hs
  exact
    { xi := clW_xiLaw hL hX hPr hCh hs hone (fun i hi =>
        xi_first_law_of_target hs (clT_xiTgtLaw G.σ₀ hB hi (by have := hB.hm; unfold cOf; omega)) (clX_phiLaw_steps hB i hi))
      xiQ := hxiQ
      psi := fun al => clW_psiLaw hL hX hPr hCh hs hone (fun P hP => clPf_phiGSLaw (clPsi_phiHyp hX hPr hL.hm P hP) _ _) al b
      top := clW_topLaw hL hX hPr hCh hs b (fun P hP => hone (m2 + 1) le_rfl b P hP) }

/- English proof (translation)
The claim follows from `kerHypOn_of_ok W Ch sel mu cst L A u m2 hL hPr (qSep_of sel mu hPr hsel hS) (qUnif_of sel mu hX hPr hsel) (posT_of_mem sel mu hPr u hsel (hPr.T_prime u) hST) hOk b hY (rPsymF Ch) (kerLaws_of_repOne Ch sel mu cst L m2 hL hX hPr hCh hs hA hone b hxiQ)`.
-/
theorem kerHypOn_repOne {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel X sel)
    (hS : ∀ i, Pr.g i ∈ S) (hST : Pr.T u ∈ S) (hs : cst.sharp = true) (hA : R.m ≤ cst.A)
    (hone : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (hxiQ : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLawQ Ch sel mu cst L i al be) :
    KerHypOn W Ch sel mu cst L A u m2 b hY (rPsymF Ch) :=
  kerHypOn_of_ok W Ch sel mu cst L A u m2 hL hPr (qSep_of sel mu hPr hsel hS) (qUnif_of sel mu hX hPr hsel)
    (posT_of_mem sel mu hPr u hsel (hPr.T_prime u) hST) hOk b hY (rPsymF Ch)
    (kerLaws_of_repOne Ch sel mu cst L m2 hL hX hPr hCh hs hA hone b hxiQ)

/- English proof (translation)
The claim follows from `kerEquivC_of W Ch sel mu cst L A u m2 b hY (rPsymF Ch) (kerHypOn_repOne W Ch sel mu cst L A u m2 hL hX hPr hCh hsel hS hST hs hA hone hOk b hY hxiQ)`.
-/
theorem kerEquivC_repOne {G : ChGlob X R.m} (hL : L.Ok Ch sel mu cst G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hsel : IsSel X sel)
    (hS : ∀ i, Pr.g i ∈ S) (hST : Pr.T u ∈ S) (hs : cst.sharp = true) (hA : R.m ≤ cst.A)
    (hone : ∀ j, j ≤ m2 + 1 → ∀ (b : L.β j) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs → L.h j b P = 1)
    (hOk : ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (hxiQ : ∀ i, i < m2 → ∀ (al : L.β i) (be : L.β (i + 1)), XiLawQ Ch sel mu cst L i al be) :
    KerEquivC W Ch sel mu cst L A u m2 b hY (rPsymF Ch) :=
  kerEquivC_of W Ch sel mu cst L A u m2 b hY (rPsymF Ch)
    (kerHypOn_repOne W Ch sel mu cst L A u m2 hL hX hPr hCh hsel hS hST hs hA hone hOk b hY hxiQ)

end RepOne

section Mu0Sym

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ)
  (cst : LocCst X (rowSG Pr sel (mu0 X.F X.E X.K S))) (A : Amb X) (u : Pr.Word) (m2 : ℕ)

end Mu0Sym

namespace TestAll

section T1

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

open Classical in

def frInc (E : Type) [Field E] (k₀ r c' n' c n : ℕ) (h' : k₀ ≤ n') (h : k₀ ≤ n) : HomE E (n' + c') (n + c) :=
  LinearMap.pi fun l : Fin (n + c) =>
    if hl : ((fE k₀ c n h).symm l).1 < r ∧ ((fE k₀ c n h).symm l).1 < n' + c' then
      LinearMap.proj (fE k₀ c' n' h' ⟨((fE k₀ c n h).symm l).1, hl.2⟩) else 0

end T1

section T2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

end T2

end TestAll

end Formalism.L2.Ker
