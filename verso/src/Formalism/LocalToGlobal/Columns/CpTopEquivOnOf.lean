import Formalism.LocalToGlobal.Columns.XtSumSingle
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivConcrete

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Inv

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {u : Pr.Word}

open Classical in

/- English proof (translation)
Take `⟨w0, hw0, rfl⟩` from `(mem_mulLat _ _ _).1 hz`. Establish `hG` using `mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ`. Establish `hphi : phiT X.K p.deco.1 p'.deco.1 (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) = phiT X.K p.deco.1 p'.deco.1 x`. Use `phiT_add_mul X.K p.deco p'.deco (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_` and prove the remaining obligations. Establish `h1 : Pr.piT u ∈ P.1.asIdeal` using `mem_asIdeal_of_mem_divs P.2`.

Rewrite using `[← hPr.piT_norm u]`. Conclude with `P.1.asIdeal.mul_mem_right _ h1`. Use `(mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w0, Submodule.smul_mem _ _ hw0, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul]`. Unfold `cBof`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[XiTop_eq, XiTop_eq, hphi]`. Use `congr 1`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations.

Establish `hw` using `hG w`. Establish `hu` using `ciQ_notMem_sq hX hPr hw`. Establish `hq0 : ((qOf w.1 : ℕ) : X.E) ≠ 0` using `ciQ_ne_zero hu`. Establish `ef : frsF sel mu p w = p.deco.1.liftFr ⟨w.1, hw⟩`. Unfold `frsF`.

Rewrite using `[dif_pos hw]`. Take `⟨k, hk⟩ : ∃ k, cst.B = k + 1` from `⟨cst.B - 1, by have := hc.B_pos; omega⟩`. Use `topDat_congr Ch sel mu cst hX hPr hc hn w hw _ _ _ (fun j => by rw [ef]; exact xtRepY_int sel mu cst p.deco Y hYm w hw j) fun j => ?_` and prove the remaining obligations. Establish `h1 : frsF sel mu p w (Pi.single j 1) ∈ p.deco.1.at w.1` using `(frame_mem_lattice_iff_std' sel mu p w hw _).2 (ciSingle_mem j)`. Establish `h2 : w0 (frsF sel mu p w (Pi.single j 1)) ∈ localization₂ w.1.asIdeal p'.deco.1.N` using `hw0 w.1 (Finset.mem_union_right _ w.2) _ h1`.

Establish `h3 : (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) ∈ stdAt X.E (R.N (i + 1)) w.1` using `(frame_mem_lattice_iff_std' sel mu p' w hw _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h2)`. Establish `e : ∀ l, inFr (frsF sel mu p w) (frsF sel mu p' w) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) (Pi.single j 1) l = inFr (frsF sel mu p w) (frsF sel mu p' w) x (Pi.single j 1) l + (qOf w.1 : X.E) * ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X …`. Introduce `l`. Simplify using `only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smul_apply, map_add, Pi.add_apply]`. Rewrite using `[← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, Pi.smul_apply, smul_eq_mul, map_natCast, hk]`.

Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hd : ∀ l, IntAt w.1 ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) * (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) l)` using `fun l => ((xtIntAt_qpow (qOf w.1) k).mul (intAt_inv_qOf_pow_mul_cBof sel mu cst w)).mul ((ciMem_stdAt _ _).1 h3 l)`. Use `⟨forall_congr' fun l => ?_, fun _ l => ?_⟩` and prove the remaining obligations.

Rewrite using `[e l]`. Conclude with `ciIntAt_add_iff ((ciIntAt_q (q := qOf w.1)).mul (hd l))`. Rewrite using `[e l]`. Conclude with `redP_add_natCast_mul (ciQ_mem w.1) (hd l)`.
-/
theorem xiTop_inv (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) {i : ℕ} (hn : TopNum R i)
    (p : ChPt (R := R) sel mu u i) (Y : Set (Sp X.E (R.N i))) (p' : ChPt (R := R) sel mu u (i + 1))
    (x z : HomE X.E (R.N i) (R.N (i + 1))) (hYm : Y ∈ ybSet sel mu cst p.deco.1.N)
    (hz : z ∈ mulLat (cBof sel mu cst u) (homAt (Sall sel mu u) p.deco.1.N p'.deco.1.N)) :
    XiTop Ch sel mu cst i p Y p' (x + z) = XiTop Ch sel mu cst i p Y p' x := by
  obtain ⟨w0, hw0, rfl⟩ := (mem_mulLat _ _ _).1 hz
  have hG := mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ
  have hphi : phiT X.K p.deco.1 p'.deco.1 (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) = phiT X.K p.deco.1 p'.deco.1 x := by
    refine phiT_add_mul X.K p.deco p'.deco (Sall sel mu u) (fun P => Finset.mem_union_left _ P.2) (Pr.T u) (fun P => ?_) x _ ?_
    · have h1 : Pr.piT u ∈ P.1.asIdeal := mem_asIdeal_of_mem_divs P.2
      rw [← hPr.piT_norm u]
      exact P.1.asIdeal.mul_mem_right _ h1
    · refine (mem_mulLat _ _ _).2 ⟨(((∏ P : rowSG Pr sel mu, Col.qOf P.1) ^ cst.B : ℕ) : 𝓞 X.E) • w0,
        Submodule.smul_mem _ _ hw0, ?_⟩
      rw [smul_smul]
      unfold cBof
      push_cast
      rfl
  rw [XiTop_eq, XiTop_eq, hphi]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw := hG w
  have hu := ciQ_notMem_sq hX hPr hw
  have hq0 : ((qOf w.1 : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have ef : frsF sel mu p w = p.deco.1.liftFr ⟨w.1, hw⟩ := by
    unfold frsF
    rw [dif_pos hw]
  obtain ⟨k, hk⟩ : ∃ k, cst.B = k + 1 := ⟨cst.B - 1, by have := hc.B_pos; omega⟩
  refine topDat_congr Ch sel mu cst hX hPr hc hn w hw _ _ _ (fun j => by rw [ef]; exact xtRepY_int sel mu cst p.deco Y hYm w hw j) fun j => ?_

  have h1 : frsF sel mu p w (Pi.single j 1) ∈ p.deco.1.at w.1 := (frame_mem_lattice_iff_std' sel mu p w hw _).2 (ciSingle_mem j)
  have h2 : w0 (frsF sel mu p w (Pi.single j 1)) ∈ localization₂ w.1.asIdeal p'.deco.1.N := hw0 w.1 (Finset.mem_union_right _ w.2) _ h1
  have h3 : (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) ∈ stdAt X.E (R.N (i + 1)) w.1 :=
    (frame_mem_lattice_iff_std' sel mu p' w hw _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h2)
  have e : ∀ l, inFr (frsF sel mu p w) (frsF sel mu p' w) (x + ((cBof sel mu cst u : ℕ) : 𝓞 X.E) • w0) (Pi.single j 1) l =
      inFr (frsF sel mu p w) (frsF sel mu p' w) x (Pi.single j 1) l + (qOf w.1 : X.E) *
        ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) *
          (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) l) := by
    intro l
    simp only [inFr, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smul_apply, map_add, Pi.add_apply]
    rw [← algebraMap_smul X.E (((cBof sel mu cst u : ℕ) : 𝓞 X.E)), map_smul, Pi.smul_apply, smul_eq_mul, map_natCast, hk]
    congr 1
    field_simp
    ring
  have hd : ∀ l, IntAt w.1 ((qOf w.1 : X.E) ^ k * (((qOf w.1 : X.E) ^ cst.B)⁻¹ * ((cBof sel mu cst u : ℕ) : X.E)) *
      (frsF sel mu p' w).symm (w0 (frsF sel mu p w (Pi.single j 1))) l) := fun l =>
    ((xtIntAt_qpow (qOf w.1) k).mul (intAt_inv_qOf_pow_mul_cBof sel mu cst w)).mul ((ciMem_stdAt _ _).1 h3 l)
  refine ⟨forall_congr' fun l => ?_, fun _ l => ?_⟩
  · rw [e l]
    exact ciIntAt_add_iff ((ciIntAt_q (q := qOf w.1)).mul (hd l))
  · rw [e l]
    exact redP_add_natCast_mul (ciQ_mem w.1) (hd l)

end Inv

section Thm

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word} {m2 : ℕ}

def CpTopEquivOn (T : ChTh W sel mu u m2) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (Θm : LevQFam X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K))) : Prop :=
  CplEq2On (S := midGSD W sel mu L u m2 b) (S₁ := frmGSD (colValF W sel mu u (m2 + 1 + 1)) Λm Θm) (ybCpl W sel mu cst L u m2 b hY)
    (fun p Y p' => cpTopK W Ch sel mu cst T (m2 + 1) p Y p')

variable {W Ch sel mu cst L}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `g g' p (Y : Set (Sp X.E (R.N (m2 + 1)))) p' hYm`. Express the relevant statement in the definitionally equal form `Y ∈ ybSet sel mu cst p.deco.1.N at hYm`. Establish `hT : 0 < Pr.T u` using `(hPr.T_prime u).pos`. Establish `hG` using `mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ`. Use `choose κ hκ hκr using fun w : rowSG Pr sel mu => frsF_smul sel mu p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w (hG w)`.

Use `choose κ' hκ' hκr' using fun w : rowSG Pr sel mu => frsF_smul sel mu p' Λm Θm g' w (hG w)`. Establish `hfr : frsF sel mu (g • p) = fun w => g.1.1 * frsF sel mu p w * (κ w).1` using `funext hκ`. Establish `hfr' : frsF sel mu (g' • p') = fun w => g'.1.1 * frsF sel mu p' w * (κ' w).1` using `funext hκ'`. Establish `hN : IsSdLat p.deco.1.N` using `⟨p.deco.2.lat, p.deco.2.uni⟩`. Establish `hN' : IsSdLat p'.deco.1.N` using `⟨p'.deco.2.lat, p'.deco.2.uni⟩`.

Establish `hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco` using `rfl`. Establish `hdeco' : (g' • p').deco = (g'.1, (g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs)) • p'.deco` using `rfl`. Establish `hYm1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (gmap g.1.1 p.deco.1.N)` using `(ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm`. Establish `hcc : (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K) = ∏ w : rowSG Pr sel mu, (((Λm ⟨w.1, hG w⟩).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b ⟨w.1, hG w⟩).lam ⟨(g.2.1 : GLG …`. Rewrite using `[prod_rowSG_eq_prod_vGs_of_QE_empty sel mu hQ (fun w => (((Λm w).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) w, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) * ((((L.levG (m2 + 1) b w).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X. …`.

Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, levFam_chr_apply_coe, levFam_chr_apply_coe, Finset.prod_mul_distrib]`. Simplify using `only [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]`. Use `show cpTopK W Ch sel mu cst T (m2 + 1) (g • p) ((fun v => g.1.1 v) '' (Y : Set (Sp X.E (R.N (m2 + 1))))) (g' • p') = (frmGSD (colValF W sel mu u (m2 + 1 + 1)) Λm Θm).ρ g' ∘ₗ cpTopK W Ch sel mu cst T (m2 + 1) p Y p' ∘ₗ (midGSD W sel mu L u m2 b).ρ g⁻¹`. Unfold `cpTopK`. Rewrite using `[if_pos (show (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N from hYm1), if_pos hYm, hfr, hfr']`.

Use `(kerOf_move hOk (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsF sel mu p') g.1 g'.1 κ κ' _ _ (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K) (fun x z hz => xiTop_inv Ch sel mu cst hX hPr hc hQ hn p Y p' x z hYm hz) ?_).trans ?_` and prove the remaining obligations. Introduce `x`. Rewrite using `[XiTop_eq, XiTop_eq, hdeco, hdeco', phiT_smul]`. Simplify using `only [hfr, hfr', inFr_move]`. Rewrite using `[hcc]`.

Use `prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ _ fun w => ?_` and prove the remaining obligations. Establish `hw` using `hG w`. Take `⟨hne, hdiff, hqm⟩` from `ybSet_props2 sel mu cst hYm w hw`. Establish `hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1`. Introduce `z hz`.

Apply `(frame_mem_lattice_iff_std' sel mu p w hw _).1` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Conclude with `hz`. Take `⟨a, ha, hra⟩ : repY ((fun v => g.1.1 v) '' Y) ∈ (fun v => g.1.1 v) '' Y` from `representative_mem (hne.image _)`. Establish `hr0` using `representative_mem hne`.

Establish `e2 : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (g.1.1 a)) = (frsF sel mu p w).symm a`. Rewrite using `[LinearEquiv.eq_symm_apply]`. Apply `g.1.1.injective` to reduce the goal to its premises. Use `LinearEquiv.apply_symm_apply (g.1.1 * frsF sel mu p w * (κ w).1) (g.1.1 a)` as an intermediate fact. Rewrite `this` using `[LinearEquiv.mul_apply, LinearEquiv.mul_apply]`.

Conclude with `this`. Establish `hδ : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (repY ((fun v => g.1.1 v) '' Y))) - (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1`. Rewrite using `[← hra, e2, ← map_sub]`. Conclude with `hFst _ (hdiff _ ha _ hr0)`. Establish `hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1`.

Rewrite using `[← LinearEquiv.map_smul]`. Conclude with `hFst _ (hqm _ hr0)`. Conclude with `topDat_law hc hn hLaw hRow w hw ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩ ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ (κ w) (κ' w) (hκr w) (hκr' w) (ciQ_notMem_sq hX hPr hw) _ _ _ hδ hq`. Use `show _ = (frmRho (colValF W sel mu u (m2 + 1 + 1)) Λm Θm g') ∘ₗ _ ∘ₗ (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g⁻¹)`. Simplify using `only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, levQFam_chr_eq_one_of_QE_empty sel mu hQ, mul_one, Prod.fst_inv, Prod.snd_inv, map_inv, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]`.

Use `congr 1`. Simplify using `only [Units.val_mul, Units.val_inv_eq_inv_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpTopEquivOn_of (hX : X.Ok) (hPr : Pr.Ok) (hc : cst.Ok) (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (hn : TopNum R (m2 + 1))
    (T : ChTh W sel mu u m2)
    (hOk : ThDist.Ok (T.th (m2 + 1)) (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (colValF W sel mu u (m2 + 1)).rho
      (colValF W sel mu u (m2 + 1 + 1)).rho (rhoS Ch sel mu (m2 + 1)) (rhoT Ch sel mu (m2 + 1)))
    (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b)
    (Λm : LevFam X.E X.K (R.N (m2 + 1 + 1)) Pr.vGs) (Θm : LevQFam X.E X.K (R.N (m2 + 1 + 1)) (QE sel (mu : Chr X.F X.E X.K)))
    (hLaw : TopLawG Ch sel mu cst L m2 Λm b) (hRow : LastRow Λm) :
    CpTopEquivOn W Ch sel mu cst L T b hY Λm Θm := by
  classical
  intro g g' p (Y : Set (Sp X.E (R.N (m2 + 1)))) p' hYm
  change Y ∈ ybSet sel mu cst p.deco.1.N at hYm
  have hT : 0 < Pr.T u := (hPr.T_prime u).pos
  have hG := mem_vGs_of_QE_empty (Pr := Pr) sel mu hQ
  choose κ hκ hκr using fun w : rowSG Pr sel mu => frsF_smul sel mu p (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g w (hG w)
  choose κ' hκ' hκr' using fun w : rowSG Pr sel mu => frsF_smul sel mu p' Λm Θm g' w (hG w)
  have hfr : frsF sel mu (g • p) = fun w => g.1.1 * frsF sel mu p w * (κ w).1 := funext hκ
  have hfr' : frsF sel mu (g' • p') = fun w => g'.1.1 * frsF sel mu p' w * (κ' w).1 := funext hκ'
  have hN : IsSdLat p.deco.1.N := ⟨p.deco.2.lat, p.deco.2.uni⟩
  have hN' : IsSdLat p'.deco.1.N := ⟨p'.deco.2.lat, p'.deco.2.uni⟩
  have hdeco : (g • p).deco = (g.1, (g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs)) • p.deco := rfl
  have hdeco' : (g' • p').deco = (g'.1, (g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs)) • p'.deco := rfl
  have hYm1 : (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (gmap g.1.1 p.deco.1.N) := (ybSet_gmap sel mu cst p.deco.1.N g.1.1 Y).2 hYm
  have hcc : (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K) =
      ∏ w : rowSG Pr sel mu,
        (((Λm ⟨w.1, hG w⟩).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
          ((((L.levG (m2 + 1) b ⟨w.1, hG w⟩).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hG w⟩, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K) := by
    rw [prod_rowSG_eq_prod_vGs_of_QE_empty sel mu hQ (fun w =>
      (((Λm w).lam ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) w, g'.2.1.2 _ (Set.mem_univ _)⟩ : X.Kˣ) : X.K) *
        ((((L.levG (m2 + 1) b w).lam ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) w, g.2.1.2 _ (Set.mem_univ _)⟩)⁻¹ : X.Kˣ) : X.K))]
    rw [Units.val_mul, Units.val_inv_eq_inv_val, levFam_chr_apply_coe, levFam_chr_apply_coe, Finset.prod_mul_distrib]
    simp only [Units.val_inv_eq_inv_val, Finset.prod_inv_distrib]
  show cpTopK W Ch sel mu cst T (m2 + 1) (g • p) ((fun v => g.1.1 v) '' (Y : Set (Sp X.E (R.N (m2 + 1))))) (g' • p') =
    (frmGSD (colValF W sel mu u (m2 + 1 + 1)) Λm Θm).ρ g' ∘ₗ cpTopK W Ch sel mu cst T (m2 + 1) p Y p' ∘ₗ (midGSD W sel mu L u m2 b).ρ g⁻¹
  unfold cpTopK
  rw [if_pos (show (fun v => g.1.1 v) '' Y ∈ ybSet sel mu cst (g • p).deco.1.N from hYm1), if_pos hYm, hfr, hfr']
  refine (kerOf_move hOk (cBof_pos sel mu cst u hT) hN hN' (frsF sel mu p) (frsF sel mu p') g.1 g'.1 κ κ'
    _ _ (((Λm.chr g'.2.1 * ((L.levG (m2 + 1) b).chr g.2.1)⁻¹ : X.Kˣ)) : X.K)
    (fun x z hz => xiTop_inv Ch sel mu cst hX hPr hc hQ hn p Y p' x z hYm hz) ?_).trans ?_
  · intro x
    rw [XiTop_eq, XiTop_eq, hdeco, hdeco', phiT_smul]
    simp only [hfr, hfr', inFr_move]
    rw [hcc]
    refine prod_mul_eq_of_forall_cross_mul_eq _ _ _ _ _ fun w => ?_
    have hw := hG w
    obtain ⟨hne, hdiff, hqm⟩ := ybSet_props2 sel mu cst hYm w hw
    have hFst : ∀ z, z ∈ localization₂ w.1.asIdeal p.deco.1.N → (frsF sel mu p w).symm z ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      intro z hz
      apply (frame_mem_lattice_iff_std' sel mu p w hw _).1
      rw [LinearEquiv.apply_symm_apply]
      exact hz
    obtain ⟨a, ha, hra⟩ : repY ((fun v => g.1.1 v) '' Y) ∈ (fun v => g.1.1 v) '' Y := representative_mem (hne.image _)
    have hr0 := representative_mem hne
    have e2 : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (g.1.1 a)) = (frsF sel mu p w).symm a := by
      rw [LinearEquiv.eq_symm_apply]
      apply g.1.1.injective
      have := LinearEquiv.apply_symm_apply (g.1.1 * frsF sel mu p w * (κ w).1) (g.1.1 a)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
      exact this
    have hδ : (κ w).1 ((g.1.1 * frsF sel mu p w * (κ w).1).symm (repY ((fun v => g.1.1 v) '' Y))) - (frsF sel mu p w).symm (repY Y) ∈
        stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [← hra, e2, ← map_sub]
      exact hFst _ (hdiff _ ha _ hr0)
    have hq : ((qOf w.1 : ℕ) : X.E) • (frsF sel mu p w).symm (repY Y) ∈ stdAt X.E (R.N (m2 + 1)) w.1 := by
      rw [← LinearEquiv.map_smul]
      exact hFst _ (hqm _ hr0)
    exact topDat_law hc hn hLaw hRow w hw ⟨(g.2.1 : GLG X.E (R.N (m2 + 1)) Pr.vGs) ⟨w.1, hw⟩, g.2.1.2 _ (Set.mem_univ _)⟩
      ⟨(g'.2.1 : GLG X.E (R.N (m2 + 1 + 1)) Pr.vGs) ⟨w.1, hw⟩, g'.2.1.2 _ (Set.mem_univ _)⟩ (κ w) (κ' w) (hκr w) (hκr' w)
      (ciQ_notMem_sq hX hPr hw) _ _ _ hδ hq
  · show _ = (frmRho (colValF W sel mu u (m2 + 1 + 1)) Λm Θm g') ∘ₗ _ ∘ₗ
      (frmRho (colValF W sel mu u (m2 + 1)) (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) g⁻¹)
    simp only [frmRho, MonoidHom.coe_mk, OneHom.coe_mk, levQFam_chr_eq_one_of_QE_empty sel mu hQ, mul_one, Prod.fst_inv, Prod.snd_inv, map_inv,
      LinearMap.smul_comp, LinearMap.comp_smul, smul_smul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    ring

end Thm

end Formalism.L2.Col
